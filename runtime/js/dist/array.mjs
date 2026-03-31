// src/array.mts
function staticNew(size) {
  return new Array(size).fill(void 0);
}
function staticGet(arr, i) {
  return arr[i];
}
function staticSet(arr, i, v) {
  arr[i] = v;
}
function staticLength(arr) {
  return arr.length;
}
function staticFreeze(arr) {
  Object.freeze(arr);
  return arr;
}
function staticPush(arr, item) {
  const clone = [...arr];
  clone.push(item);
  return clone;
}
export {
  staticFreeze,
  staticGet,
  staticLength,
  staticNew,
  staticPush,
  staticSet
};
