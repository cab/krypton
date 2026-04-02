// src/map.mts
function staticEmpty() {
  return /* @__PURE__ */ new Map();
}
function staticPut(m, key, value, _eqDict, _hashDict) {
  const copy = new Map(m);
  copy.set(key, value);
  return copy;
}
function staticGetUnsafe(m, key) {
  return m.get(key);
}
function staticContainsKey(m, key) {
  return m.has(key);
}
function staticDelete(m, key) {
  const copy = new Map(m);
  copy.delete(key);
  return copy;
}
function staticKeys(m) {
  return [...m.keys()];
}
function staticValues(m) {
  return [...m.values()];
}
function staticEntries(m) {
  const result = [];
  for (const [k, v] of m) {
    result.push(k, v);
  }
  return result;
}
function staticSize(m) {
  return m.size;
}
function staticMerge(m1, m2) {
  return new Map([...m1, ...m2]);
}
export {
  staticContainsKey,
  staticDelete,
  staticEmpty,
  staticEntries,
  staticGetUnsafe,
  staticKeys,
  staticMerge,
  staticPut,
  staticSize,
  staticValues
};
