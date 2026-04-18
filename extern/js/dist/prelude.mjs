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
var List = class extends CustomType {
  map(f) {
    let result = Empty.INSTANCE;
    const items = [];
    let cur = this;
    while (cur instanceof NonEmpty) {
      items.push(f(cur.head));
      cur = cur.tail;
    }
    for (let i = items.length - 1; i >= 0; i -= 1) {
      result = new NonEmpty(items[i], result);
    }
    return result;
  }
  toArray() {
    const arr = [];
    let cur = this;
    while (cur instanceof NonEmpty) {
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
var Empty = class _Empty extends List {
  static INSTANCE = new _Empty();
  get $tag() {
    return 1;
  }
};
var NonEmpty = class extends List {
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
  let result = Empty.INSTANCE;
  for (let i = array.length - 1; i >= 0; i -= 1) {
    result = new NonEmpty(array[i], result);
  }
  return result;
}
export {
  CustomType,
  Empty,
  List,
  NonEmpty,
  toList
};
