export function staticNew(size: number) {
  return new Array(size).fill(undefined);
}

export function staticGet<T>(arr: T[], i: number) {
  return arr[i];
}

export function staticSet<T>(arr: T[], i: number, v: T) {
  arr[i] = v;
}

export function staticLength(arr: unknown[]) {
  return arr.length;
}

export function staticFreeze<T>(arr: T[]) {
  Object.freeze(arr);
  return arr;
}

export function staticPush<T>(arr: T[], item: T) {
  const clone = [...arr];
  clone.push(item);
  return clone;
}
