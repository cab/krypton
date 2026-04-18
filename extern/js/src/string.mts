import { List } from 'immutable';

export function parseIntSafe(s: string): number | null {
  const n = Number.parseInt(s, 10);
  return Number.isNaN(n) ? null : n;
}

export function parseFloatSafe(s: string): number | null {
  const n = Number.parseFloat(s);
  return Number.isNaN(n) ? null : n;
}

export function charAt(s: string, i: number): string | null {
  return i >= 0 && i < s.length ? s[i]! : null;
}

export function length(s: string): number {
  return s.length;
}

export function substring(s: string, start: number, end: number): string {
  return s.substring(start, end);
}

export function containsStr(s: string, sub: string): boolean {
  return s.includes(sub);
}

export function startsWith(s: string, prefix: string): boolean {
  return s.startsWith(prefix);
}

export function endsWith(s: string, suffix: string): boolean {
  return s.endsWith(suffix);
}

export function trim(s: string): string {
  return s.trim();
}

export function toLower(s: string): string {
  return s.toLowerCase();
}

export function toUpper(s: string): string {
  return s.toUpperCase();
}

export function indexOf(s: string, sub: string): number {
  return s.indexOf(sub);
}

export function replaceStr(s: string, from: string, to: string): string {
  return s.replaceAll(from, to);
}

export function split(s: string, sep: string): List<string> {
  return List(s.split(sep));
}

export function concat(a: string, b: string): string {
  return a + b;
}
