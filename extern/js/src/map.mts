export function staticEmpty() {
  return new Map();
}

export function staticPut<K, V>(
  m: Map<K, V>,
  key: K,
  value: V,
  _eqDict: unknown,
  _hashDict: unknown,
) {
  const copy = new Map(m);
  copy.set(key, value);
  return copy;
}

export function staticGetUnsafe<K, V>(m: Map<K, V>, key: K) {
  return m.get(key);
}

export function staticContainsKey<K, V>(m: Map<K, V>, key: K) {
  return m.has(key);
}

export function staticDelete<K, V>(m: Map<K, V>, key: K) {
  const copy = new Map(m);
  copy.delete(key);
  return copy;
}

export function staticKeys<K, V>(m: Map<K, V>) {
  return [...m.keys()];
}

export function staticValues<K, V>(m: Map<K, V>) {
  return [...m.values()];
}

export function staticSize(m: Map<unknown, unknown>) {
  return m.size;
}

export function staticMerge<K, V>(m1: Map<K, V>, m2: Map<K, V>) {
  return new Map([...m1, ...m2]);
}
