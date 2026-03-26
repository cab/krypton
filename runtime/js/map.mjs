// Krypton JS runtime — Map operations

export function staticEmpty() {
  return new Map();
}

export function staticPut(m, key, value, _eqDict, _hashDict) {
  const copy = new Map(m);
  copy.set(key, value);
  return copy;
}

export function staticGetUnsafe(m, key) {
  return m.get(key);
}

export function staticContainsKey(m, key) {
  return m.has(key);
}

export function staticDelete(m, key) {
  const copy = new Map(m);
  copy.delete(key);
  return copy;
}

export function staticKeys(m) {
  return [...m.keys()];
}

export function staticValues(m) {
  return [...m.values()];
}

export function staticEntries(m) {
  const result = [];
  for (const [k, v] of m) {
    result.push(k, v);
  }
  return result;
}

export function staticSize(m) {
  return m.size;
}

export function staticMerge(m1, m2) {
  return new Map([...m1, ...m2]);
}
