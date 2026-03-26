// Krypton JS runtime — Vec-backing array operations

export function staticNew(size) {
  return new Array(size).fill(undefined);
}

export function staticGet(arr, i) {
  return arr[i];
}

export function staticSet(arr, i, v) {
  arr[i] = v;
}

export function staticLength(arr) {
  return arr.length;
}

export function staticFreeze(arr) {
  Object.freeze(arr);
  return arr;
}
