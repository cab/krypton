// src/prelude.mts
var CustomType = class {
  toString() {
    const name = this.constructor.name;
    const self = this;
    const fields = Object.keys(self).filter((k) => k !== "$tag");
    if (fields.length === 0) {
      return name;
    }
    const parts = fields.map((k) => `${k}: ${formatValue(self[k])}`);
    return `${name} { ${parts.join(", ")} }`;
  }
};
function formatValue(v) {
  if (v instanceof CustomType) {
    return v.toString();
  }
  if (typeof v === "string") {
    return JSON.stringify(v);
  }
  return String(v);
}
var KList = class extends CustomType {
  map(f) {
    let result = KEmpty.INSTANCE;
    const items = [];
    let cur = this;
    while (cur instanceof KNonEmpty) {
      items.push(f(cur.head));
      cur = cur.tail;
    }
    for (let i = items.length - 1; i >= 0; i -= 1) {
      result = new KNonEmpty(items[i], result);
    }
    return result;
  }
  toArray() {
    const arr = [];
    let cur = this;
    while (cur instanceof KNonEmpty) {
      arr.push(cur.head);
      cur = cur.tail;
    }
    return arr;
  }
  toString() {
    const items = this.toArray().map((v) => formatValue(v));
    return `[${items.join(", ")}]`;
  }
};
var KEmpty = class _KEmpty extends KList {
  static INSTANCE = new _KEmpty();
  get $tag() {
    return 1;
  }
};
var KNonEmpty = class extends KList {
  head;
  tail;
  constructor(head, tail) {
    super();
    this.head = head;
    this.tail = tail;
  }
  get $tag() {
    return 0;
  }
};
function toList(array) {
  let result = KEmpty.INSTANCE;
  for (let i = array.length - 1; i >= 0; i -= 1) {
    result = new KNonEmpty(array[i], result);
  }
  return result;
}
export {
  CustomType,
  KEmpty,
  KList,
  KNonEmpty,
  toList
};
