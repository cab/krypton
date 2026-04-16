let _liveCount = 0;
let _resolveQuiescent: (() => void) | null = null;
let _keepAlive: ReturnType<typeof setInterval> | null = null;
let _actorIdCounter = 0;

export { _liveCount };

function _updateKeepAlive() {
  if (_liveCount > 0 && !_keepAlive) {
    _keepAlive = setInterval(() => {}, 1 << 30);
  } else if (_liveCount === 0 && _keepAlive) {
    clearInterval(_keepAlive);
    _keepAlive = null;
  }
}

type ExitHandlerEntry = {
  target: Mailbox;
  normal: (id: number) => unknown;
  crash: (id: number, msg: string) => unknown;
  fired: boolean;
};

type ActorState = {
  id: number;
  exitHandlers: ExitHandlerEntry[];
  exiting: boolean;
  crashMessage: string | null;
};

const _actorByMailbox: WeakMap<Mailbox, ActorState> = new WeakMap();

function _fireHandler(entry: ExitHandlerEntry, state: ActorState) {
  if (entry.fired) return;
  entry.fired = true;
  try {
    const msg =
      state.crashMessage === null
        ? entry.normal(state.id)
        : entry.crash(state.id, state.crashMessage);
    entry.target.enqueue(msg);
  } catch {
    // never propagate handler-side failure
  }
}

function _runActor(
  f: (mb: Mailbox) => unknown,
  mb: Mailbox,
  state: ActorState,
) {
  _liveCount += 1;
  _updateKeepAlive();
  Promise.resolve()
    .then(() => f(mb))
    .catch((err: Error) => {
      state.crashMessage = err && err.message ? err.message : "unknown error";
      console.error(`[krypton] actor-${state.id} crashed: ${state.crashMessage}`);
    })
    .finally(() => {
      state.exiting = true;
      for (const entry of state.exitHandlers) _fireHandler(entry, state);
      mb.close();
      _liveCount -= 1;
      _updateKeepAlive();
      if (_liveCount === 0 && _resolveQuiescent) {
        _resolveQuiescent();
        _resolveQuiescent = null;
      }
    });
}

export class Mailbox {
  inbox: unknown[];
  waiting: ((msg: unknown) => void) | null;
  closed: boolean;

  constructor() {
    this.inbox = [];
    this.waiting = null;
    this.closed = false;
  }

  enqueue(msg: unknown) {
    if (this.closed) {
      return;
    }
    if (this.waiting) {
      const resolve = this.waiting;
      this.waiting = null;
      resolve(msg);
    } else {
      this.inbox.push(msg);
    }
  }

  receive() {
    if (this.inbox.length > 0) {
      return Promise.resolve(this.inbox.shift());
    }
    return new Promise((resolve) => {
      this.waiting = resolve;
    });
  }

  receiveTimeout(ms: number) {
    if (this.inbox.length > 0) {
      return Promise.resolve(this.inbox.shift());
    }
    return new Promise((resolve) => {
      const timer = setTimeout(() => {
        this.waiting = null;
        resolve(null);
      }, ms);
      this.waiting = (msg) => {
        clearTimeout(timer);
        resolve(msg);
      };
    });
  }

  ref() {
    return new Ref(this);
  }

  close() {
    this.closed = true;
  }

  size() {
    return this.inbox.length;
  }
}

export class Ref {
  _send: (msg: unknown) => void;
  _targetMailbox: Mailbox | null;

  constructor(targetOrFn: Mailbox | ((msg: unknown) => void)) {
    if (targetOrFn instanceof Mailbox) {
      const target = targetOrFn;
      this._send = (msg) => target.enqueue(msg);
      this._targetMailbox = target;
    } else {
      this._send = targetOrFn;
      this._targetMailbox = null;
    }
  }

  send(msg: unknown) {
    this._send(msg);
  }
}

export function raw_spawn(f: (mb: Mailbox) => unknown) {
  const mb = new Mailbox();
  const state: ActorState = {
    id: _actorIdCounter++,
    exitHandlers: [],
    exiting: false,
    crashMessage: null,
  };
  _actorByMailbox.set(mb, state);
  _runActor(f, mb, state);
  return mb.ref();
}

export function raw_send(ref: Ref, msg: unknown) {
  ref.send(msg);
}

export function raw_receive(mb: Mailbox) {
  return mb.receive();
}

export function raw_receive_timeout(mb: Mailbox, ms: number) {
  return mb.receiveTimeout(ms);
}

export function raw_actor_ref(mb: Mailbox) {
  return mb.ref();
}

export function raw_mailbox_size(mb: Mailbox) {
  return mb.size();
}

export function raw_create_mailbox() {
  return new Mailbox();
}

export function raw_adapter(ref: Ref, wrapper: (msg: unknown) => unknown) {
  return new Ref((msg) => ref.send(wrapper(msg)));
}

export function raw_ask(
  target: Ref,
  wrapperFn: (replyRef: Ref) => unknown,
  timeout: number,
) {
  const replyMb = new Mailbox();
  const replyRef = replyMb.ref();
  const msg = wrapperFn(replyRef);
  target.send(msg);
  return replyMb.receiveTimeout(timeout).then((reply) => {
    replyMb.close();
    return reply;
  });
}

function _stateForRef(ref: Ref): ActorState | null {
  if (!ref._targetMailbox) return null;
  return _actorByMailbox.get(ref._targetMailbox) ?? null;
}

function _registerExitHandler(
  callerMb: Mailbox,
  targetRef: Ref,
  normal: (id: number) => unknown,
  crash: (id: number, msg: string) => unknown,
): ActorState | null {
  const state = _stateForRef(targetRef);
  if (!state) return null;
  const entry: ExitHandlerEntry = {
    target: callerMb,
    normal,
    crash,
    fired: false,
  };
  state.exitHandlers.push(entry);
  if (state.exiting) _fireHandler(entry, state);
  return state;
}

export function raw_link(
  callerMb: Mailbox,
  targetRef: Ref,
  normal: (id: number) => unknown,
  crash: (id: number, msg: string) => unknown,
) {
  _registerExitHandler(callerMb, targetRef, normal, crash);
}

export function raw_monitor(
  callerMb: Mailbox,
  targetRef: Ref,
  normal: (id: number) => unknown,
  crash: (id: number, msg: string) => unknown,
) {
  _registerExitHandler(callerMb, targetRef, normal, crash);
}

export function raw_spawn_link(
  f: (mb: Mailbox) => unknown,
  callerMb: Mailbox,
  normal: (id: number) => unknown,
  crash: (id: number, msg: string) => unknown,
) {
  const mb = new Mailbox();
  const state: ActorState = {
    id: _actorIdCounter++,
    exitHandlers: [
      { target: callerMb, normal, crash, fired: false },
    ],
    exiting: false,
    crashMessage: null,
  };
  _actorByMailbox.set(mb, state);
  _runActor(f, mb, state);
  return mb.ref();
}

export function raw_self_id(mb: Mailbox) {
  const state = _actorByMailbox.get(mb);
  return state ? state.id : -1;
}

export async function runMain(fn: () => Promise<unknown> | unknown) {
  const result = await fn();
  if (_liveCount === 0) {
    return result;
  }
  return new Promise((resolve) => {
    _resolveQuiescent = () => resolve(result);
  });
}
