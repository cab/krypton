// src/string.mts
function parseIntSafe(s) {
  const n = Number.parseInt(s, 10);
  return Number.isNaN(n) ? null : n;
}
function parseFloatSafe(s) {
  const n = Number.parseFloat(s);
  return Number.isNaN(n) ? null : n;
}
function charAt(s, i) {
  return i >= 0 && i < s.length ? s[i] : null;
}
function length(s) {
  return s.length;
}
function substring(s, start, end) {
  return s.substring(start, end);
}
function containsStr(s, sub) {
  return s.includes(sub);
}
function startsWith(s, prefix) {
  return s.startsWith(prefix);
}
function endsWith(s, suffix) {
  return s.endsWith(suffix);
}
function trim(s) {
  return s.trim();
}
function toLower(s) {
  return s.toLowerCase();
}
function toUpper(s) {
  return s.toUpperCase();
}
function indexOf(s, sub) {
  return s.indexOf(sub);
}
function replaceStr(s, from, to) {
  return s.replaceAll(from, to);
}
function split(s, sep) {
  return s.split(sep);
}
function concat(a, b) {
  return a + b;
}
export {
  charAt,
  concat,
  containsStr,
  endsWith,
  indexOf,
  length,
  parseFloatSafe,
  parseIntSafe,
  replaceStr,
  split,
  startsWith,
  substring,
  toLower,
  toUpper,
  trim
};
