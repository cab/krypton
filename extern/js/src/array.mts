import { List } from 'immutable';

import { KryptonPanic } from './panic.mjs';

export function staticLength(list: List<unknown>): number {
  return list.size;
}

export function staticGet<T>(list: List<T>, i: number): T {
  if (i < 0 || i >= list.size) {
    throw new KryptonPanic(`index out of bounds: ${i} (size: ${list.size})`);
  }
  return list.get(i)!;
}

export function staticPush<T>(list: List<T>, item: T): List<T> {
  return list.push(item);
}
