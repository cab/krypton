// src/json.mts
function staticParse(s) {
  try {
    return [true, JSON.parse(s)];
  } catch (e) {
    return [false, e.message];
  }
}
function staticSerialize(x) {
  return JSON.stringify(x);
}
function staticRawType(x) {
  if (x === null || x === void 0) {
    return 0;
  }
  if (typeof x === "boolean") {
    return 1;
  }
  if (typeof x === "number") {
    return 2;
  }
  if (typeof x === "string") {
    return 3;
  }
  if (Array.isArray(x)) {
    return 4;
  }
  return 5;
}
function staticRawBool(x) {
  return x;
}
function staticRawNum(x) {
  return x;
}
function staticRawStr(x) {
  return x;
}
function staticRawArr(x) {
  return x;
}
function staticRawEntries(x) {
  const result = [];
  for (const [k, v] of Object.entries(x)) {
    result.push(k, v);
  }
  return result;
}
function staticMkNull() {
  return null;
}
function staticMkBool(v) {
  return v;
}
function staticMkNum(v) {
  return v;
}
function staticMkStr(v) {
  return v;
}
function staticNewArr() {
  return [];
}
function staticArrPush(arr, item) {
  arr.push(item);
}
function staticNewObj() {
  return {};
}
function staticObjPut(obj, key, value) {
  obj[key] = value;
}
function toFloat(n) {
  return n;
}
function toInt(f) {
  return Math.trunc(f);
}
export {
  staticArrPush,
  staticMkBool,
  staticMkNull,
  staticMkNum,
  staticMkStr,
  staticNewArr,
  staticNewObj,
  staticObjPut,
  staticParse,
  staticRawArr,
  staticRawBool,
  staticRawEntries,
  staticRawNum,
  staticRawStr,
  staticRawType,
  staticSerialize,
  toFloat,
  toInt
};
