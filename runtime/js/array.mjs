// Krypton JS runtime — Vec-backing array operations

export function newArray(size) {
  return new Array(size).fill(undefined);
}

export function get(arr, i) {
  return arr[i];
}

export function set(arr, i, v) {
  arr[i] = v;
}

export function length(arr) {
  return arr.length;
}

export function freeze(arr) {
  Object.freeze(arr);
  return arr;
}
