export class CustomType {
  toString(): string {
    const name = this.constructor.name;
    const self = this as unknown as Record<string, unknown>;
    const fields = Object.keys(self).filter((k) => k !== '$tag');
    if (fields.length === 0) {
      return name;
    }
    const parts = fields.map((k) => `${k}: ${formatValue(self[k])}`);
    return `${name} { ${parts.join(', ')} }`;
  }
}

function formatValue(v: unknown): string {
  if (v instanceof CustomType) {
    return v.toString();
  }
  if (typeof v === 'string') {
    return JSON.stringify(v);
  }
  return String(v);
}

export class List extends CustomType {
  map(f: (value: unknown) => unknown): List {
    let result: List = Empty.INSTANCE;
    const items: unknown[] = [];
    let cur: List = this;
    while (cur instanceof NonEmpty) {
      items.push(f(cur.head));
      cur = cur.tail;
    }
    for (let i = items.length - 1; i >= 0; i -= 1) {
      result = new NonEmpty(items[i], result);
    }
    return result;
  }

  toArray(): unknown[] {
    const arr: unknown[] = [];
    let cur: List = this;
    while (cur instanceof NonEmpty) {
      arr.push(cur.head);
      cur = cur.tail;
    }
    return arr;
  }

  override toString(): string {
    const items = this.toArray().map((v) => formatValue(v));
    return `[${items.join(', ')}]`;
  }
}

export class Empty extends List {
  static INSTANCE = new Empty();

  get $tag(): number {
    return 1;
  }
}

export class NonEmpty extends List {
  head: unknown;
  tail: List;

  constructor(head: unknown, tail: List) {
    super();
    this.head = head;
    this.tail = tail;
  }

  get $tag(): number {
    return 0;
  }
}

export function toList(array: unknown[]): List {
  let result: List = Empty.INSTANCE;
  for (let i = array.length - 1; i >= 0; i -= 1) {
    result = new NonEmpty(array[i], result);
  }
  return result;
}
