export function staticParse(s: string) {
  try {
    return [true, JSON.parse(s)];
  } catch (e) {
    return [false, (e as Error).message];
  }
}

export function staticSerialize(x: unknown) {
  return JSON.stringify(x);
}

export function staticRawType(x: unknown) {
  if (x === null || x === undefined) {
    return 0;
  }
  if (typeof x === 'boolean') {
    return 1;
  }
  if (typeof x === 'number') {
    return 2;
  }
  if (typeof x === 'string') {
    return 3;
  }
  if (Array.isArray(x)) {
    return 4;
  }
  return 5;
}

export function staticRawBool(x: boolean) {
  return x;
}

export function staticRawNum(x: number) {
  return x;
}

export function staticRawStr(x: string) {
  return x;
}

export function staticRawArr<T>(x: T[]) {
  return x;
}

export function staticRawEntries(x: Record<string, unknown>) {
  const result: unknown[] = [];
  for (const [k, v] of Object.entries(x)) {
    result.push(k, v);
  }
  return result;
}

export function staticMkNull() {
  return null;
}

export function staticMkBool(v: boolean) {
  return v;
}

export function staticMkNum(v: number) {
  return v;
}

export function staticMkStr(v: string) {
  return v;
}

export function staticNewArr() {
  return [];
}

export function staticArrPush(arr: unknown[], item: unknown) {
  arr.push(item);
}

export function staticNewObj() {
  return {};
}

export function staticObjPut(
  obj: Record<string, unknown>,
  key: string,
  value: unknown,
) {
  obj[key] = value;
}

export function toFloat(n: number) {
  return n;
}

export function toInt(f: number) {
  return Math.trunc(f);
}
