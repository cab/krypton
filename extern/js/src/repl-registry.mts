/** REPL Var registry — single-threaded JS port of the JVM's Var + Registry. */

const UNBOUND: unique symbol = Symbol("UNBOUND");

class Var {
  private value: unknown = UNBOUND;
  constructor(public readonly name: string) {}
  isBound(): boolean { return this.value !== UNBOUND; }
  get(): unknown {
    if (this.value === UNBOUND) throw new Error(`Var '${this.name}' is unbound`);
    return this.value;
  }
  set(v: unknown): void { this.value = v; }
}

const vars = new Map<string, Var>();

export function intern(name: string): Var {
  let v = vars.get(name);
  if (!v) { v = new Var(name); vars.set(name, v); }
  return v;
}

export function lookup(name: string): Var {
  const v = vars.get(name);
  if (!v) throw new Error(`No Var registered for '${name}'`);
  return v;
}

export function clear(): void { vars.clear(); }
