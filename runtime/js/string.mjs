// Krypton JS runtime — string utilities

export function parseIntSafe(s) {
  const n = parseInt(s, 10);
  return Number.isNaN(n) ? null : n;
}

export function parseFloatSafe(s) {
  const n = parseFloat(s);
  return Number.isNaN(n) ? null : n;
}

export function charAt(s, i) {
  return i >= 0 && i < s.length ? s[i] : null;
}

export function length(s) {
  return s.length;
}

export function substring(s, start, end) {
  return s.substring(start, end);
}

export function containsStr(s, sub) {
  return s.includes(sub);
}

export function startsWith(s, prefix) {
  return s.startsWith(prefix);
}

export function endsWith(s, suffix) {
  return s.endsWith(suffix);
}

export function trim(s) {
  return s.trim();
}

export function toLower(s) {
  return s.toLowerCase();
}

export function toUpper(s) {
  return s.toUpperCase();
}

export function indexOf(s, sub) {
  return s.indexOf(sub);
}

export function replaceStr(s, from, to) {
  return s.replaceAll(from, to);
}

export function split(s, sep) {
  return s.split(sep);
}

export function concat(a, b) {
  return a + b;
}
