// src/actor.mts
var _liveCount = 0;
var _resolveQuiescent = null;
var _keepAlive = null;
var _actorIdCounter = 0;
function _updateKeepAlive() {
  if (_liveCount > 0 && !_keepAlive) {
    _keepAlive = setInterval(() => {
    }, 1 << 30);
  } else if (_liveCount === 0 && _keepAlive) {
    clearInterval(_keepAlive);
    _keepAlive = null;
  }
}
var _actorByMailbox = /* @__PURE__ */ new WeakMap();
function _fireHandler(entry, state) {
  if (entry.fired) return;
  entry.fired = true;
  try {
    const msg = state.crashMessage === null ? entry.normal(state.id) : entry.crash(state.id, state.crashMessage);
    entry.target.enqueue(msg);
  } catch {
  }
}
function _runActor(f, mb, state) {
  _liveCount += 1;
  _updateKeepAlive();
  Promise.resolve().then(() => f(mb)).catch((err) => {
    state.crashMessage = err && err.message ? err.message : "unknown error";
    console.error(`[krypton] actor-${state.id} crashed: ${state.crashMessage}`);
  }).finally(() => {
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
var Mailbox = class {
  inbox;
  waiting;
  closed;
  constructor() {
    this.inbox = [];
    this.waiting = null;
    this.closed = false;
  }
  enqueue(msg) {
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
  receiveTimeout(ms) {
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
};
var Ref = class {
  _send;
  _targetMailbox;
  constructor(targetOrFn) {
    if (targetOrFn instanceof Mailbox) {
      const target = targetOrFn;
      this._send = (msg) => target.enqueue(msg);
      this._targetMailbox = target;
    } else {
      this._send = targetOrFn;
      this._targetMailbox = null;
    }
  }
  send(msg) {
    this._send(msg);
  }
};
function raw_spawn(f) {
  const mb = new Mailbox();
  const state = {
    id: _actorIdCounter++,
    exitHandlers: [],
    exiting: false,
    crashMessage: null
  };
  _actorByMailbox.set(mb, state);
  _runActor(f, mb, state);
  return mb.ref();
}
function raw_send(ref, msg) {
  ref.send(msg);
}
function raw_receive(mb) {
  return mb.receive();
}
function raw_receive_timeout(mb, ms) {
  return mb.receiveTimeout(ms);
}
function raw_actor_ref(mb) {
  return mb.ref();
}
function raw_mailbox_size(mb) {
  return mb.size();
}
function raw_create_mailbox() {
  return new Mailbox();
}
function raw_adapter(ref, wrapper) {
  return new Ref((msg) => ref.send(wrapper(msg)));
}
function raw_ask(target, wrapperFn, timeout) {
  const replyMb = new Mailbox();
  const replyRef = replyMb.ref();
  const msg = wrapperFn(replyRef);
  target.send(msg);
  return replyMb.receiveTimeout(timeout).then((reply) => {
    replyMb.close();
    return reply;
  });
}
function _stateForRef(ref) {
  if (!ref._targetMailbox) return null;
  return _actorByMailbox.get(ref._targetMailbox) ?? null;
}
function _registerExitHandler(callerMb, targetRef, normal, crash) {
  const state = _stateForRef(targetRef);
  if (!state) return null;
  const entry = {
    target: callerMb,
    normal,
    crash,
    fired: false
  };
  state.exitHandlers.push(entry);
  if (state.exiting) _fireHandler(entry, state);
  return state;
}
function raw_link(callerMb, targetRef, normal, crash) {
  _registerExitHandler(callerMb, targetRef, normal, crash);
}
function raw_monitor(callerMb, targetRef, normal, crash) {
  _registerExitHandler(callerMb, targetRef, normal, crash);
}
function raw_spawn_link(f, callerMb, normal, crash) {
  const mb = new Mailbox();
  const state = {
    id: _actorIdCounter++,
    exitHandlers: [
      { target: callerMb, normal, crash, fired: false }
    ],
    exiting: false,
    crashMessage: null
  };
  _actorByMailbox.set(mb, state);
  _runActor(f, mb, state);
  return mb.ref();
}
function raw_self_id(mb) {
  const state = _actorByMailbox.get(mb);
  return state ? state.id : -1;
}
async function runMain(fn) {
  const result = await fn();
  if (_liveCount === 0) {
    return result;
  }
  return new Promise((resolve) => {
    _resolveQuiescent = () => resolve(result);
  });
}
export {
  Mailbox,
  Ref,
  _liveCount,
  raw_actor_ref,
  raw_adapter,
  raw_ask,
  raw_create_mailbox,
  raw_link,
  raw_mailbox_size,
  raw_monitor,
  raw_receive,
  raw_receive_timeout,
  raw_self_id,
  raw_send,
  raw_spawn,
  raw_spawn_link,
  runMain
};
