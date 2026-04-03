// src/repl-registry.mts
var UNBOUND = /* @__PURE__ */ Symbol("UNBOUND");
var Var = class {
  constructor(name) {
    this.name = name;
  }
  value = UNBOUND;
  isBound() {
    return this.value !== UNBOUND;
  }
  get() {
    if (this.value === UNBOUND) throw new Error(`Var '${this.name}' is unbound`);
    return this.value;
  }
  set(v) {
    this.value = v;
  }
};
var vars = /* @__PURE__ */ new Map();
function intern(name) {
  let v = vars.get(name);
  if (!v) {
    v = new Var(name);
    vars.set(name, v);
  }
  return v;
}
function lookup(name) {
  const v = vars.get(name);
  if (!v) throw new Error(`No Var registered for '${name}'`);
  return v;
}
function clear() {
  vars.clear();
}
export {
  clear,
  intern,
  lookup
};
