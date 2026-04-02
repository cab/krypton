export function parseIntSafe(s: string) {
  const n = Number.parseInt(s, 10);
  return Number.isNaN(n) ? null : n;
}

export function parseFloatSafe(s: string) {
  const n = Number.parseFloat(s);
  return Number.isNaN(n) ? null : n;
}

export function charAt(s: string, i: number) {
  return i >= 0 && i < s.length ? s[i] : null;
}

export function length(s: string) {
  return s.length;
}

export function substring(s: string, start: number, end: number) {
  return s.substring(start, end);
}

export function containsStr(s: string, sub: string) {
  return s.includes(sub);
}

export function startsWith(s: string, prefix: string) {
  return s.startsWith(prefix);
}

export function endsWith(s: string, suffix: string) {
  return s.endsWith(suffix);
}

export function trim(s: string) {
  return s.trim();
}

export function toLower(s: string) {
  return s.toLowerCase();
}

export function toUpper(s: string) {
  return s.toUpperCase();
}

export function indexOf(s: string, sub: string) {
  return s.indexOf(sub);
}

export function replaceStr(s: string, from: string, to: string) {
  return s.replaceAll(from, to);
}

export function split(s: string, sep: string) {
  return s.split(sep);
}

export function concat(a: string, b: string) {
  return a + b;
}
