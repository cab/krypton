import { List } from 'immutable';

export function staticEmpty<K, V>(): Map<K, V> {
  return new Map<K, V>();
}

export function staticPut<K, V>(
  m: Map<K, V>,
  key: K,
  value: V,
  _eqDict: unknown,
  _hashDict: unknown,
): Map<K, V> {
  const copy = new Map(m);
  copy.set(key, value);
  return copy;
}

export function staticGetUnsafe<K, V>(m: Map<K, V>, key: K): V | undefined {
  return m.get(key);
}

export function staticContainsKey<K, V>(m: Map<K, V>, key: K): boolean {
  return m.has(key);
}

export function staticDelete<K, V>(m: Map<K, V>, key: K): Map<K, V> {
  const copy = new Map(m);
  copy.delete(key);
  return copy;
}

export function staticKeys<K, V>(m: Map<K, V>): List<K> {
  return List([...m.keys()]);
}

export function staticValues<K, V>(m: Map<K, V>): List<V> {
  return List([...m.values()]);
}

export function staticSize(m: Map<unknown, unknown>): number {
  return m.size;
}

export function staticMerge<K, V>(m1: Map<K, V>, m2: Map<K, V>): Map<K, V> {
  return new Map([...m1, ...m2]);
}
