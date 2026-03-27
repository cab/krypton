// Krypton JS runtime — JSON operations

// HACK: Workaround for JSON.parse("null") returning JS null, which collides
// with the error sentinel. Replace with @throws error handling when available.
const JSON_NULL = { __krypton_json_null: true };

export function staticParse(s) {
  try {
    const parsed = JSON.parse(s);
    return [parsed === null ? JSON_NULL : parsed, null];
  } catch (e) {
    return [null, e.message];
  }
}

export function staticSerialize(x) {
  return JSON.stringify(x);
}

export function staticRawType(x) {
  if (x === null || x === undefined) return 0;
  if (x.__krypton_json_null) return 0;
  if (typeof x === 'boolean') return 1;
  if (typeof x === 'number') return 2;
  if (typeof x === 'string') return 3;
  if (Array.isArray(x)) return 4;
  return 5; // object
}

export function staticRawBool(x) {
  return x;
}

export function staticRawNum(x) {
  return x;
}

export function staticRawStr(x) {
  return x;
}

export function staticRawArr(x) {
  return x;
}

export function staticRawEntries(x) {
  const result = [];
  for (const [k, v] of Object.entries(x)) {
    result.push(k, v);
  }
  return result;
}

export function staticMkNull() {
  return null;
}

export function staticMkBool(v) {
  return v;
}

export function staticMkNum(v) {
  return v;
}

export function staticMkStr(v) {
  return v;
}

export function staticNewArr() {
  return [];
}

export function staticArrPush(arr, item) {
  arr.push(item);
}

export function staticNewObj() {
  return {};
}

export function staticObjPut(obj, key, value) {
  obj[key] = value;
}

// Type conversions (KryptonConvert equivalents)

export function toFloat(n) {
  return n;
}

export function toInt(f) {
  return Math.trunc(f);
}
