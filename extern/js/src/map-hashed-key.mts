import type { ValueObject } from 'immutable';

type HashDict = { hash: (key: unknown) => number | bigint };
type EqDict = { eq: (a: unknown, b: unknown) => boolean };

/**
 * Wraps a user key so Immutable.Map dispatches equality/hashing through
 * Krypton's `Eq`/`Hash` trait dicts (implements Immutable.js `ValueObject`).
 *
 * JS trait dicts are plain objects with named methods (e.g. `{ hash: ... }`),
 * not bare callables, so `hashCode`/`equals` delegate via `.hash`/`.eq`.
 *
 * Emitted as a shared runtime file so every bundle (`map.mjs`,
 * `map-builder.mjs`, ...) imports the same class at load time.
 */
export class HashedKey implements ValueObject {
  readonly key: unknown;
  readonly hash: number;
  readonly eqDict: EqDict;

  constructor(key: unknown, hashDict: HashDict, eqDict: EqDict) {
    this.key = key;
    this.eqDict = eqDict;
    const raw = hashDict.hash(key);
    // Krypton Hash.hash returns Int (BigInt at runtime on JS); coerce to
    // 32-bit int for Immutable.js's hashCode contract.
    this.hash = typeof raw === 'bigint' ? Number(BigInt.asIntN(32, raw)) : (raw | 0);
  }

  hashCode(): number {
    return this.hash;
  }

  equals(other: unknown): boolean {
    if (other === this) return true;
    if (!(other instanceof HashedKey)) return false;
    return this.eqDict.eq(this.key, other.key);
  }
}
