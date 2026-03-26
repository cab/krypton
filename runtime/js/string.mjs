// Krypton JS runtime — string utilities

export function parse_int(s) {
  const n = parseInt(s, 10);
  return Number.isNaN(n) ? null : n;
}

export function parse_float(s) {
  const n = parseFloat(s);
  return Number.isNaN(n) ? null : n;
}

export function char_at(s, i) {
  return i >= 0 && i < s.length ? s[i] : null;
}

export function string_length(s) {
  return s.length;
}

export function substring(s, start, end) {
  return s.substring(start, end);
}

export function string_contains(s, sub) {
  return s.includes(sub);
}

export function starts_with(s, prefix) {
  return s.startsWith(prefix);
}

export function ends_with(s, suffix) {
  return s.endsWith(suffix);
}

export function trim(s) {
  return s.trim();
}

export function to_lowercase(s) {
  return s.toLowerCase();
}

export function to_uppercase(s) {
  return s.toUpperCase();
}

export function index_of(s, sub) {
  const i = s.indexOf(sub);
  return i === -1 ? null : i;
}

export function replace(s, from, to) {
  return s.replaceAll(from, to);
}

export function split(s, sep) {
  return s.split(sep);
}

export function string_concat(a, b) {
  return a + b;
}

export function char_code_at(s, i) {
  return i >= 0 && i < s.length ? s.charCodeAt(i) : null;
}
