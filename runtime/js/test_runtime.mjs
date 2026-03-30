// Test script for Krypton JS runtime files
// Run: node runtime/js/test_runtime.mjs

import { CustomType, List, Empty, NonEmpty, toList } from './prelude.mjs';
import { KryptonPanic } from './panic.mjs';
import { staticNew as newArray, staticGet as get, staticSet as set, staticLength as length, staticFreeze as freeze } from './array.mjs';
import { parseIntSafe as parse_int, parseFloatSafe as parse_float, length as string_length, substring, trim } from './string.mjs';
import { toFloat, toInt } from './convert.mjs';
import { raw_println, raw_print } from './io.mjs';
import {
  Mailbox, Ref,
  raw_spawn, raw_send, raw_receive, raw_receive_timeout,
  raw_actor_ref, raw_mailbox_size, raw_create_mailbox,
  raw_adapter, raw_ask,
} from './actor.mjs';

let passed = 0;
let failed = 0;

function assert(cond, msg) {
  if (cond) {
    passed++;
  } else {
    failed++;
    console.error(`FAIL: ${msg}`);
  }
}

// ── prelude.mjs ──

class Point extends CustomType {
  constructor(x, y) { super(); this.x = x; this.y = y; }
}
assert(new Point(1, 2).toString() === 'Point { x: 1, y: 2 }', 'CustomType toString');

const list = toList([1, 2, 3]);
assert(list instanceof List, 'toList returns List');
assert(list instanceof NonEmpty, 'non-empty list is NonEmpty');
assert(list.head === 1, 'list head');
assert(list.tail.head === 2, 'list second element');
assert(list.tail.tail.tail instanceof Empty, 'list terminates with Empty');
assert(list.toArray().join(',') === '1,2,3', 'list toArray');

const doubled = list.map(x => x * 2);
assert(doubled.toArray().join(',') === '2,4,6', 'list map');

assert(Empty.INSTANCE instanceof Empty, 'Empty singleton');
assert(toList([]).toString() === '[]', 'empty list toString');
assert(toList([1, 2]).toString() === '[1, 2]', 'list toString');

// ── panic.mjs ──

const panic = new KryptonPanic('test');
assert(panic instanceof Error, 'KryptonPanic extends Error');
assert(panic.name === 'KryptonPanic', 'KryptonPanic name');
assert(panic.message === 'test', 'KryptonPanic message');

// ── array.mjs ──

const arr = newArray(3);
assert(length(arr) === 3, 'newArray length');
set(arr, 0, 'a');
set(arr, 1, 'b');
set(arr, 2, 'c');
assert(get(arr, 1) === 'b', 'array get/set');
const frozen = freeze(arr);
assert(frozen === arr, 'freeze returns same array');
try { frozen[0] = 'x'; } catch (_) { /* expected in strict mode */ }

// ── string.mjs ──

assert(parse_int('42') === 42, 'parse_int valid');
assert(parse_int('nope') === null, 'parse_int invalid');
assert(parse_float('3.14') === 3.14, 'parse_float valid');
assert(parse_float('nope') === null, 'parse_float invalid');
assert(string_length('hello') === 5, 'string_length');
assert(substring('hello', 1, 3) === 'el', 'substring');
assert(trim('  hi  ') === 'hi', 'trim');

// ── convert.mjs ──

assert(toFloat(42) === 42, 'toFloat identity');
assert(toInt(3.7) === 3, 'toInt truncates');
assert(toInt(-2.9) === -2, 'toInt negative');

// ── io.mjs ──

// Just verify they're callable (output goes to console)
raw_println('io test: println');
raw_print('io test: print\n');

// ── actor.mjs ──

async function runActorTests() {

  // Mailbox basics
  {
    const mb = new Mailbox();
    mb.enqueue('a');
    mb.enqueue('b');
    assert(mb.size() === 2, 'mailbox size after enqueue');
    const msg1 = await mb.receive();
    assert(msg1 === 'a', 'mailbox receive first');
    const msg2 = await mb.receive();
    assert(msg2 === 'b', 'mailbox receive second');
    assert(mb.size() === 0, 'mailbox size after receive');
  }

  // Mailbox receive waits for enqueue
  {
    const mb = new Mailbox();
    const p = mb.receive();
    mb.enqueue('delayed');
    const msg = await p;
    assert(msg === 'delayed', 'mailbox receive waits for enqueue');
  }

  // Mailbox close stops enqueue
  {
    const mb = new Mailbox();
    mb.close();
    mb.enqueue('ignored');
    assert(mb.size() === 0, 'closed mailbox ignores enqueue');
  }

  // Ref/send
  {
    const mb = new Mailbox();
    const ref = mb.ref();
    assert(ref instanceof Ref, 'ref is Ref instance');
    ref.send('hello');
    const msg = await mb.receive();
    assert(msg === 'hello', 'ref send delivers to mailbox');
  }

  // raw_create_mailbox
  {
    const mb = raw_create_mailbox();
    assert(mb instanceof Mailbox, 'raw_create_mailbox returns Mailbox');
  }

  // raw_actor_ref
  {
    const mb = new Mailbox();
    const ref = raw_actor_ref(mb);
    assert(ref instanceof Ref, 'raw_actor_ref returns Ref');
    raw_send(ref, 'test');
    const msg = await raw_receive(mb);
    assert(msg === 'test', 'raw_actor_ref ref delivers messages');
  }

  // raw_mailbox_size
  {
    const mb = new Mailbox();
    assert(raw_mailbox_size(mb) === 0, 'raw_mailbox_size empty');
    mb.enqueue('x');
    assert(raw_mailbox_size(mb) === 1, 'raw_mailbox_size after enqueue');
  }

  // raw_spawn
  {
    let received = null;
    const ref = raw_spawn(async (mb) => {
      received = await mb.receive();
    });
    assert(ref instanceof Ref, 'raw_spawn returns Ref');
    raw_send(ref, 'ping');
    // Allow microtasks to run
    await new Promise(r => setTimeout(r, 10));
    assert(received === 'ping', 'raw_spawn actor receives message');
  }

  // raw_receive_timeout — timeout fires
  {
    const mb = new Mailbox();
    const result = await raw_receive_timeout(mb, 10);
    assert(result === null, 'raw_receive_timeout returns null on timeout');
  }

  // raw_receive_timeout — message arrives before timeout
  {
    const mb = new Mailbox();
    mb.enqueue('fast');
    const result = await raw_receive_timeout(mb, 1000);
    assert(result === 'fast', 'raw_receive_timeout returns message if available');
  }

  // raw_receive_timeout — message arrives during wait
  {
    const mb = new Mailbox();
    const p = raw_receive_timeout(mb, 5000);
    mb.enqueue('mid');
    const result = await p;
    assert(result === 'mid', 'raw_receive_timeout returns message arriving during wait');
  }

  // raw_adapter
  {
    const mb = new Mailbox();
    const ref = mb.ref();
    const adapted = raw_adapter(ref, (msg) => `wrapped:${msg}`);
    assert(adapted instanceof Ref, 'raw_adapter returns Ref');
    adapted.send('hello');
    const msg = await mb.receive();
    assert(msg === 'wrapped:hello', 'raw_adapter wraps messages');
  }

  // raw_ask — successful reply
  {
    const ref = raw_spawn(async (mb) => {
      const msg = await mb.receive();
      // msg is [requestValue, replyRef]
      msg[1].send('reply:' + msg[0]);
    });
    const result = await raw_ask(ref, (replyRef) => ['question', replyRef], 1000);
    assert(result === 'reply:question', 'raw_ask returns reply value');
  }

  // raw_ask — timeout
  {
    const ref = raw_spawn(async (mb) => {
      // Actor never replies
      await mb.receive();
    });
    const result = await raw_ask(ref, (replyRef) => ['ignored', replyRef], 10);
    assert(result === null, 'raw_ask returns null on timeout');
  }

  // Actor crash handling
  {
    const errors = [];
    const origError = console.error;
    console.error = (...args) => errors.push(args.join(' '));
    const ref = raw_spawn(async (_mb) => {
      throw new Error('boom');
    });
    // Allow microtasks to run
    await new Promise(r => setTimeout(r, 10));
    console.error = origError;
    assert(errors.length === 1, 'actor crash logs one error');
    assert(errors[0].includes('boom'), 'actor crash error contains message');
  }
}

await runActorTests();

// ── Summary ──

console.log(`\n${passed} passed, ${failed} failed`);
if (failed > 0) process.exit(1);
