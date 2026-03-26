// Krypton JS runtime — prelude types

export class CustomType {
  toString() {
    const name = this.constructor.name;
    const fields = Object.keys(this).filter(k => k !== '$tag');
    if (fields.length === 0) return name;
    const parts = fields.map(k => `${k}: ${formatValue(this[k])}`);
    return `${name} { ${parts.join(', ')} }`;
  }
}

function formatValue(v) {
  if (v instanceof CustomType) return v.toString();
  if (typeof v === 'string') return JSON.stringify(v);
  return String(v);
}

// Linked list — base class + Empty / NonEmpty (cons cell)

export class List extends CustomType {
  map(f) {
    let result = Empty.INSTANCE;
    let items = [];
    let cur = this;
    while (cur instanceof NonEmpty) {
      items.push(f(cur.head));
      cur = cur.tail;
    }
    for (let i = items.length - 1; i >= 0; i--) {
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
    const items = this.toArray().map(v => formatValue(v));
    return `[${items.join(', ')}]`;
  }
}

export class Empty extends List {
  static INSTANCE = new Empty();
  get $tag() { return 1; }
}

export class NonEmpty extends List {
  constructor(head, tail) {
    super();
    this.head = head;
    this.tail = tail;
  }
  get $tag() { return 0; }
}

export function toList(array) {
  let result = Empty.INSTANCE;
  for (let i = array.length - 1; i >= 0; i--) {
    result = new NonEmpty(array[i], result);
  }
  return result;
}
