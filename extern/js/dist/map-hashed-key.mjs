// src/map-hashed-key.mts
var HashedKey = class _HashedKey {
  key;
  hash;
  eqDict;
  constructor(key, hashDict, eqDict) {
    this.key = key;
    this.eqDict = eqDict;
    const raw = hashDict.hash(key);
    this.hash = typeof raw === "bigint" ? Number(BigInt.asIntN(32, raw)) : raw | 0;
  }
  hashCode() {
    return this.hash;
  }
  equals(other) {
    if (other === this) return true;
    if (!(other instanceof _HashedKey)) return false;
    return this.eqDict.eq(this.key, other.key);
  }
};
export {
  HashedKey
};
