import { readFile, readdir } from 'node:fs/promises';
import path from 'node:path';

import { afterEach, describe, expect, it, vi } from 'vitest';

import {
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
  runMain,
} from '../src/actor.mjs';
import {
  staticFreeze as freeze,
  staticGet as get,
  staticLength as arrayLength,
  staticNew as newArray,
  staticPush,
  staticSet as set,
} from '../src/array.mjs';
import { toFloat, toInt } from '../src/convert.mjs';
import {
  raw_print,
  raw_println,
  read_file,
  readLine,
  write_file,
} from '../src/io.mjs';
import {
  staticArrPush,
  staticMkBool,
  staticMkNull,
  staticMkNum,
  staticMkStr,
  staticNewArr,
  staticNewObj,
  staticObjPut,
  staticParse,
  staticRawArr,
  staticRawBool,
  staticRawEntries,
  staticRawNum,
  staticRawStr,
  staticRawType,
  staticSerialize,
  toFloat as jsonToFloat,
  toInt as jsonToInt,
} from '../src/json.mjs';
import {
  staticContainsKey,
  staticDelete,
  staticEmpty,
  staticEntries,
  staticGetUnsafe,
  staticKeys,
  staticMerge,
  staticPut,
  staticSize,
  staticValues,
} from '../src/map.mjs';
import { KryptonPanic } from '../src/panic.mjs';
import { CustomType, Empty, List, NonEmpty, toList } from '../src/prelude.mjs';
import {
  charAt,
  concat,
  containsStr,
  endsWith,
  indexOf,
  length as stringLength,
  parseFloatSafe,
  parseIntSafe,
  replaceStr,
  split,
  startsWith,
  substring,
  toLower,
  toUpper,
  trim,
} from '../src/string.mjs';

const sleep = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms));
const distDir = path.resolve(import.meta.dirname, '../dist');
const stableDistFiles = [
  'actor.mjs',
  'array.mjs',
  'convert.mjs',
  'io.mjs',
  'json.mjs',
  'map.mjs',
  'panic.mjs',
  'prelude.mjs',
  'string.mjs',
];

describe('prelude', () => {
  class Point extends CustomType {
    x: number;
    y: number;

    constructor(x: number, y: number) {
      super();
      this.x = x;
      this.y = y;
    }
  }

  it('formats custom types', () => {
    expect(new Point(1, 2).toString()).toBe('Point { x: 1, y: 2 }');
  });

  it('builds and maps lists', () => {
    const list = toList([1, 2, 3]);
    expect(list).toBeInstanceOf(List);
    expect(list).toBeInstanceOf(NonEmpty);
    expect((list as NonEmpty).head).toBe(1);
    expect(((list as NonEmpty).tail as NonEmpty).head).toBe(2);
    expect((((list as NonEmpty).tail as NonEmpty).tail as NonEmpty).tail).toBeInstanceOf(
      Empty,
    );
    expect(list.toArray()).toEqual([1, 2, 3]);
    expect(list.map((x) => (x as number) * 2).toArray()).toEqual([2, 4, 6]);
  });

  it('preserves list string formatting', () => {
    expect(Empty.INSTANCE).toBeInstanceOf(Empty);
    expect(toList([]).toString()).toBe('[]');
    expect(toList([1, 2]).toString()).toBe('[1, 2]');
  });
});

describe('panic', () => {
  it('creates a named error', () => {
    const panic = new KryptonPanic('test');
    expect(panic).toBeInstanceOf(Error);
    expect(panic.name).toBe('KryptonPanic');
    expect(panic.message).toBe('test');
  });
});

describe('array', () => {
  it('supports mutable backing operations', () => {
    const arr = newArray(3);
    expect(arrayLength(arr)).toBe(3);
    set(arr, 0, 'a');
    set(arr, 1, 'b');
    set(arr, 2, 'c');
    expect(get(arr, 1)).toBe('b');
    expect(freeze(arr)).toBe(arr);
  });

  it('pushes immutably', () => {
    expect(staticPush([1, 2], 3)).toEqual([1, 2, 3]);
  });
});

describe('string', () => {
  it('covers parsing and utilities', () => {
    expect(parseIntSafe('42')).toBe(42);
    expect(parseIntSafe('nope')).toBeNull();
    expect(parseFloatSafe('3.14')).toBe(3.14);
    expect(parseFloatSafe('nope')).toBeNull();
    expect(charAt('hello', 1)).toBe('e');
    expect(charAt('hello', 8)).toBeNull();
    expect(stringLength('hello')).toBe(5);
    expect(substring('hello', 1, 3)).toBe('el');
    expect(containsStr('hello', 'ell')).toBe(true);
    expect(startsWith('hello', 'he')).toBe(true);
    expect(endsWith('hello', 'lo')).toBe(true);
    expect(trim('  hi  ')).toBe('hi');
    expect(toLower('HeLLo')).toBe('hello');
    expect(toUpper('HeLLo')).toBe('HELLO');
    expect(indexOf('banana', 'na')).toBe(2);
    expect(replaceStr('a-b-a', '-', ':')).toBe('a:b:a');
    expect(split('a,b,c', ',')).toEqual(['a', 'b', 'c']);
    expect(concat('a', 'b')).toBe('ab');
  });
});

describe('convert', () => {
  it('converts numbers without changing behavior', () => {
    expect(toFloat(42)).toBe(42);
    expect(toInt(3.7)).toBe(3);
    expect(toInt(-2.9)).toBe(-2);
  });
});

describe('io', () => {
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it('writes to console and stdout', () => {
    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const writeSpy = vi
      .spyOn(process.stdout, 'write')
      .mockImplementation(() => true);
    raw_println('io test: println');
    raw_print('io test: print\n');
    expect(logSpy).toHaveBeenCalledWith('io test: println');
    expect(writeSpy).toHaveBeenCalledWith('io test: print\n');
  });

  it('throws for unsupported host io', () => {
    expect(() => readLine()).toThrow('readLine is not supported on the JS target');
    expect(() => read_file('x')).toThrow('read_file is not supported on the JS target');
    expect(() => write_file('x', 'y')).toThrow(
      'write_file is not supported on the JS target',
    );
  });
});

describe('json', () => {
  it('parses, serializes, and inspects values', () => {
    expect(staticParse('{"ok":true}')).toEqual([true, { ok: true }]);
    expect(staticParse('{')).toEqual([false, expect.any(String)]);
    expect(staticSerialize({ ok: true })).toBe('{"ok":true}');
    expect(staticRawType(null)).toBe(0);
    expect(staticRawType(true)).toBe(1);
    expect(staticRawType(1)).toBe(2);
    expect(staticRawType('x')).toBe(3);
    expect(staticRawType([])).toBe(4);
    expect(staticRawType({})).toBe(5);
    expect(staticRawBool(true)).toBe(true);
    expect(staticRawNum(4)).toBe(4);
    expect(staticRawStr('x')).toBe('x');
    expect(staticRawArr([1, 2])).toEqual([1, 2]);
    expect(staticRawEntries({ a: 1, b: 2 })).toEqual(['a', 1, 'b', 2]);
  });

  it('builds raw values', () => {
    expect(staticMkNull()).toBeNull();
    expect(staticMkBool(true)).toBe(true);
    expect(staticMkNum(4)).toBe(4);
    expect(staticMkStr('x')).toBe('x');
    const arr = staticNewArr();
    staticArrPush(arr, 1);
    staticArrPush(arr, 2);
    expect(arr).toEqual([1, 2]);
    const obj = staticNewObj();
    staticObjPut(obj, 'a', 1);
    expect(obj).toEqual({ a: 1 });
    expect(jsonToFloat(5)).toBe(5);
    expect(jsonToInt(5.9)).toBe(5);
  });
});

describe('map', () => {
  it('supports persistent-style map operations', () => {
    const m1 = staticEmpty();
    const m2 = staticPut(m1, 'a', 1, null, null);
    const m3 = staticPut(m2, 'b', 2, null, null);
    expect(staticGetUnsafe(m3, 'a')).toBe(1);
    expect(staticContainsKey(m3, 'b')).toBe(true);
    expect(staticDelete(m3, 'a')).toEqual(new Map([['b', 2]]));
    expect(staticKeys(m3)).toEqual(['a', 'b']);
    expect(staticValues(m3)).toEqual([1, 2]);
    expect(staticEntries(m3)).toEqual(['a', 1, 'b', 2]);
    expect(staticSize(m3)).toBe(2);
    expect(staticMerge(m2, new Map([['c', 3]]))).toEqual(
      new Map([
        ['a', 1],
        ['c', 3],
      ]),
    );
  });
});

describe('actor', () => {
  afterEach(async () => {
    if (_liveCount > 0) {
      await sleep(20);
    }
    vi.restoreAllMocks();
  });

  it('supports mailbox basics', async () => {
    const mb = new Mailbox();
    mb.enqueue('a');
    mb.enqueue('b');
    expect(mb.size()).toBe(2);
    expect(await mb.receive()).toBe('a');
    expect(await mb.receive()).toBe('b');
    expect(mb.size()).toBe(0);
  });

  it('waits for delayed messages and ignores closed mailboxes', async () => {
    const mb = new Mailbox();
    const pending = mb.receive();
    mb.enqueue('delayed');
    expect(await pending).toBe('delayed');
    mb.close();
    mb.enqueue('ignored');
    expect(mb.size()).toBe(0);
  });

  it('supports refs and helper constructors', async () => {
    const mb = new Mailbox();
    const ref = mb.ref();
    expect(ref).toBeInstanceOf(Ref);
    ref.send('hello');
    expect(await mb.receive()).toBe('hello');

    const created = raw_create_mailbox();
    expect(created).toBeInstanceOf(Mailbox);

    const mailboxRef = raw_actor_ref(created);
    raw_send(mailboxRef, 'test');
    expect(await raw_receive(created)).toBe('test');
    expect(raw_mailbox_size(created)).toBe(0);
  });

  it('spawns actors and tracks liveness', async () => {
    let received: unknown = null;
    const before = _liveCount;
    const ref = raw_spawn(async (mb) => {
      received = await mb.receive();
    });
    expect(ref).toBeInstanceOf(Ref);
    expect(_liveCount).toBe(before + 1);
    raw_send(ref, 'ping');
    await sleep(10);
    expect(received).toBe('ping');
    expect(_liveCount).toBe(before);
  });

  it('supports receive timeouts and mid-flight delivery', async () => {
    const mb = new Mailbox();
    expect(await raw_receive_timeout(mb, 10)).toBeNull();
    mb.enqueue('fast');
    expect(await raw_receive_timeout(mb, 1000)).toBe('fast');

    const delayed = new Mailbox();
    const pending = raw_receive_timeout(delayed, 5000);
    delayed.enqueue('mid');
    expect(await pending).toBe('mid');
  });

  it('supports adapters and ask patterns', async () => {
    const mb = new Mailbox();
    const adapted = raw_adapter(mb.ref(), (msg) => `wrapped:${String(msg)}`);
    expect(adapted).toBeInstanceOf(Ref);
    adapted.send('hello');
    expect(await mb.receive()).toBe('wrapped:hello');

    const replying = raw_spawn(async (actorMb) => {
      const msg = (await actorMb.receive()) as [string, Ref];
      msg[1].send(`reply:${msg[0]}`);
    });
    expect(
      await raw_ask(replying, (replyRef) => ['question', replyRef], 1000),
    ).toBe('reply:question');

    const timeoutRef = raw_spawn(async (actorMb) => {
      await actorMb.receive();
    });
    expect(
      await raw_ask(timeoutRef, (replyRef) => ['ignored', replyRef], 10),
    ).toBeNull();
  });

  it('logs crashes and decrements liveness', async () => {
    const errors: string[] = [];
    const spy = vi.spyOn(console, 'error').mockImplementation((...args) => {
      errors.push(args.join(' '));
    });
    const before = _liveCount;
    raw_spawn(async () => {
      throw new Error('boom');
    });
    await sleep(10);
    expect(spy).toHaveBeenCalledTimes(1);
    expect(errors[0]).toContain('boom');
    expect(_liveCount).toBe(before);
  });

  it('waits for actor quiescence in runMain', async () => {
    let done = false;
    const result = await runMain(async () => {
      const ref = raw_spawn(async (mb) => {
        await mb.receive();
        done = true;
      });
      raw_send(ref, 'done');
      return 'result';
    });
    expect(result).toBe('result');
    expect(done).toBe(true);
  });
});

describe('dist artifacts', () => {
  it('contains only the stable bundled runtime module files', async () => {
    const files = (await readdir(distDir)).sort();
    expect(files).toEqual(stableDistFiles);
  });

  it('can be imported as esm runtime modules', async () => {
    const prelude = await import('../dist/prelude.mjs');
    const actor = await import('../dist/actor.mjs');
    expect(typeof prelude.toList).toBe('function');
    expect(typeof actor.runMain).toBe('function');
  });

  it('does not leave bare package imports or chunk imports in bundled output', async () => {
    for (const file of stableDistFiles) {
      const source = await readFile(path.join(distDir, file), 'utf8');
      const importSpecifiers = Array.from(
        source.matchAll(
          /\b(?:import|export)\b[\s\S]*?\bfrom\s*['"]([^'"]+)['"]|\bimport\s*\(\s*['"]([^'"]+)['"]\s*\)/g,
        ),
        (match) => match[1] ?? match[2],
      );

      expect(importSpecifiers).toEqual(
        expect.not.arrayContaining([
          expect.stringMatching(/^(?![./]).+/),
          expect.stringMatching(/(?:^|\/)chunk-[^/]+\.m?js$/),
        ]),
      );
    }
  });
});
