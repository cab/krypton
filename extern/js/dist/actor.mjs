// src/actor.mts
var _liveCount = 0;
var _resolveQuiescent = null;
var _keepAlive = null;
function _updateKeepAlive() {
  if (_liveCount > 0 && !_keepAlive) {
    _keepAlive = setInterval(() => {
    }, 1 << 30);
  } else if (_liveCount === 0 && _keepAlive) {
    clearInterval(_keepAlive);
    _keepAlive = null;
  }
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
  constructor(targetOrFn) {
    this._send = targetOrFn instanceof Mailbox ? (msg) => targetOrFn.enqueue(msg) : targetOrFn;
  }
  send(msg) {
    this._send(msg);
  }
};
function raw_spawn(f) {
  const mb = new Mailbox();
  _liveCount += 1;
  _updateKeepAlive();
  Promise.resolve().then(() => f(mb)).catch((err) => {
    console.error(`[krypton] actor crashed: ${err.message}`);
  }).finally(() => {
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
  raw_mailbox_size,
  raw_receive,
  raw_receive_timeout,
  raw_send,
  raw_spawn,
  runMain
};
