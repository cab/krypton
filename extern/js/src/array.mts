import { List } from 'immutable';

export function staticLength(list: List<unknown>): number {
  return list.size;
}

export function staticGet<T>(list: List<T>, i: number): T | undefined {
  return list.get(i);
}

export function staticPush<T>(list: List<T>, item: T): List<T> {
  return list.push(item);
}
