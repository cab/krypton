let _liveCount = 0;
let _resolveQuiescent: (() => void) | null = null;
let _keepAlive: ReturnType<typeof setInterval> | null = null;

export { _liveCount };

function _updateKeepAlive() {
  if (_liveCount > 0 && !_keepAlive) {
    _keepAlive = setInterval(() => {}, 1 << 30);
  } else if (_liveCount === 0 && _keepAlive) {
    clearInterval(_keepAlive);
    _keepAlive = null;
  }
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

  constructor(targetOrFn: Mailbox | ((msg: unknown) => void)) {
    this._send =
      targetOrFn instanceof Mailbox
        ? (msg) => targetOrFn.enqueue(msg)
        : targetOrFn;
  }

  send(msg: unknown) {
    this._send(msg);
  }
}

export function raw_spawn(f: (mb: Mailbox) => unknown) {
  const mb = new Mailbox();
  _liveCount += 1;
  _updateKeepAlive();
  Promise.resolve()
    .then(() => f(mb))
    .catch((err: Error) => {
      console.error(`[krypton] actor crashed: ${err.message}`);
    })
    .finally(() => {
      mb.close();
      _liveCount -= 1;
      _updateKeepAlive();
      if (_liveCount === 0 && _resolveQuiescent) {
        _resolveQuiescent();
        _resolveQuiescent = null;
      }
    });
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

export async function runMain(fn: () => Promise<unknown> | unknown) {
  const result = await fn();
  if (_liveCount === 0) {
    return result;
  }
  return new Promise((resolve) => {
    _resolveQuiescent = () => resolve(result);
  });
}
