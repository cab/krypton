import { List } from 'immutable';

export function staticParse(s: string): List<boolean | unknown> {
  try {
    return List<boolean | unknown>([true, JSON.parse(s)]);
  } catch (e) {
    return List<boolean | unknown>([false, (e as Error).message]);
  }
}

export function staticSerialize(x: unknown): string {
  return JSON.stringify(x);
}

export function staticRawType(x: unknown): number {
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

export function staticRawBool(x: boolean): boolean {
  return x;
}

export function staticRawNum(x: number): number {
  return x;
}

export function staticRawStr(x: string): string {
  return x;
}

export function staticRawArr<T>(x: T[]): List<T> {
  return List(x);
}

export function staticRawEntryKeys(x: Record<string, unknown>): List<string> {
  return List(Object.keys(x));
}

export function staticRawEntryValues(
  x: Record<string, unknown>,
): List<unknown> {
  return List(Object.values(x));
}

export function staticMkNull(): null {
  return null;
}

export function staticMkBool(v: boolean): boolean {
  return v;
}

export function staticMkNum(v: number): number {
  return v;
}

export function staticMkStr(v: string): string {
  return v;
}

export function staticNewArr(): unknown[] {
  return [];
}

export function staticArrPush(arr: unknown[], item: unknown): void {
  arr.push(item);
}

export function staticNewObj(): Record<string, unknown> {
  return {};
}

export function staticObjPut(
  obj: Record<string, unknown>,
  key: string,
  value: unknown,
): void {
  obj[key] = value;
}

export function toFloat(n: number): number {
  return n;
}

export function toInt(f: number): number {
  return Math.trunc(f);
}
