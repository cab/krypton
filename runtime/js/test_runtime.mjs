// Test script for Krypton JS runtime files
// Run: node runtime/js/test_runtime.mjs

import { CustomType, List, Empty, NonEmpty, toList } from './prelude.mjs';
import { KryptonPanic } from './panic.mjs';
import { newArray, get, set, length, freeze } from './array.mjs';
import { parse_int, parse_float, string_length, substring, trim } from './string.mjs';
import { toFloat, toInt } from './convert.mjs';
import { raw_println, raw_print } from './io.mjs';
import { raw_spawn } from './actor.mjs';

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

try {
  raw_spawn(() => {});
  assert(false, 'actor should throw');
} catch (e) {
  assert(e.message.includes('not supported'), 'actor panics with message');
}

// ── Summary ──

console.log(`\n${passed} passed, ${failed} failed`);
if (failed > 0) process.exit(1);
