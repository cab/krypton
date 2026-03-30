// Krypton JS runtime — actor primitives (event-loop-based)

export class Mailbox {
  constructor() {
    this.inbox = [];
    this.waiting = null;
    this.closed = false;
  }

  enqueue(msg) {
    if (this.closed) return;
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
    return new Promise(resolve => { this.waiting = resolve; });
  }

  receiveTimeout(ms) {
    if (this.inbox.length > 0) {
      return Promise.resolve(this.inbox.shift());
    }
    return new Promise(resolve => {
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

  ref() { return new Ref(this); }
  close() { this.closed = true; }
  size() { return this.inbox.length; }
}

export class Ref {
  constructor(targetOrFn) {
    this._send = (targetOrFn instanceof Mailbox)
      ? (msg) => targetOrFn.enqueue(msg)
      : targetOrFn;
  }
  send(msg) { this._send(msg); }
}

export function raw_spawn(f) {
  const mb = new Mailbox();
  Promise.resolve().then(() => f(mb)).catch(err => {
    console.error(`[krypton] actor crashed: ${err.message}`);
  }).finally(() => {
    mb.close();
  });
  return mb.ref();
}

export function raw_send(ref, msg) {
  ref.send(msg);
}

export function raw_receive(mb) {
  return mb.receive();
}

export function raw_receive_timeout(mb, ms) {
  return mb.receiveTimeout(ms);
}

export function raw_actor_ref(mb) {
  return mb.ref();
}

export function raw_mailbox_size(mb) {
  return mb.size();
}

export function raw_create_mailbox() {
  return new Mailbox();
}

export function raw_adapter(ref, wrapper) {
  return new Ref((msg) => ref.send(wrapper(msg)));
}

export function raw_ask(target, wrapperFn, timeout) {
  const replyMb = new Mailbox();
  const replyRef = replyMb.ref();
  const msg = wrapperFn(replyRef);
  target.send(msg);
  return replyMb.receiveTimeout(timeout).then(reply => {
    replyMb.close();
    return reply;
  });
}
