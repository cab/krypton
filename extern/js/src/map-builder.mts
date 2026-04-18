import { Map as IMap } from 'immutable';

import { HashedKey } from './map-hashed-key.mjs';
import type { KryptonMap } from './map.mjs';

type HashDict = { hash: (key: unknown) => number | bigint };
type EqDict = { eq: (a: unknown, b: unknown) => boolean };

/**
 * Transient-mode {@link IMap} from Immutable.js. Single-ownership is enforced
 * by the Krypton `~MapBuilder[k, v]` linear type; that authorizes the
 * in-place mutation. `builderFreeze` returns the builder to immutable mode
 * in O(1).
 *
 * Exports use the `builder*` prefix (rather than the usual `static*`
 * convention) to avoid Krypton import-scope collisions with the `put` on
 * `Map` until the stdlib re-exposes them via overloads.
 */

export interface KryptonMapBuilder {
  data: IMap<HashedKey, unknown>;
  hashDict: HashDict | null;
  eqDict: EqDict | null;
}

export function builderNew(): KryptonMapBuilder {
  return { data: IMap<HashedKey, unknown>().asMutable(), hashDict: null, eqDict: null };
}

export function builderPut(
  b: KryptonMapBuilder,
  key: unknown,
  value: unknown,
  eqDict: EqDict,
  hashDict: HashDict,
): KryptonMapBuilder {
  if (b.hashDict === null) {
    b.hashDict = hashDict;
    b.eqDict = eqDict;
  }
  const wrapped = new HashedKey(key, hashDict, eqDict);
  // On a mutable Immutable.Map, `.set` mutates in place and returns self.
  b.data = b.data.set(wrapped, value);
  return b;
}

export function builderFreeze(b: KryptonMapBuilder): KryptonMap {
  return Object.freeze({
    data: b.data.asImmutable(),
    hashDict: b.hashDict,
    eqDict: b.eqDict,
  });
}
