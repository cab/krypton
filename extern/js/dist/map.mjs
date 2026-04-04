// src/map.mts
function staticEmpty() {
  return /* @__PURE__ */ new Map();
}
function staticPut(m, key, value, _eqDict, _hashDict) {
  const copy = new Map(m);
  copy.set(key, value);
  return copy;
}
function staticGet(m, key) {
  if (!m.has(key)) return null;
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
  staticGet,
  staticKeys,
  staticMerge,
  staticPut,
  staticSize,
  staticValues
};
