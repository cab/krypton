import { List, Map as IMap } from 'immutable';

import { HashedKey } from './map-hashed-key.mjs';

type HashDict = { hash: (key: unknown) => number | bigint };
type EqDict = { eq: (a: unknown, b: unknown) => boolean };

/**
 * Persistent-map-backed wrapper. Fields are frozen after construction.
 *
 * The Krypton stdlib's `staticGetUnsafe`/`staticContainsKey`/`staticDelete`
 * do not receive Eq/Hash dicts — they rely on the dicts captured at the
 * first `put`. Empty maps have no dicts (never put-to), matching the JVM
 * `eqFn == null` invariant.
 */
export interface KryptonMap {
  readonly data: IMap<HashedKey, unknown>;
  readonly hashDict: HashDict | null;
  readonly eqDict: EqDict | null;
}

function create(
  data: IMap<HashedKey, unknown>,
  hashDict: HashDict | null,
  eqDict: EqDict | null,
): KryptonMap {
  return Object.freeze({ data, hashDict, eqDict });
}

export function staticEmpty(): KryptonMap {
  return create(IMap<HashedKey, unknown>(), null, null);
}

export function staticPut(
  m: KryptonMap,
  key: unknown,
  value: unknown,
  eqDict: EqDict,
  hashDict: HashDict,
): KryptonMap {
  const wrapped = new HashedKey(key, hashDict, eqDict);
  return create(m.data.set(wrapped, value), hashDict, eqDict);
}

export function staticGetUnsafe(m: KryptonMap, key: unknown): unknown {
  if (m.eqDict === null || m.hashDict === null) return undefined;
  return m.data.get(new HashedKey(key, m.hashDict, m.eqDict));
}

export function staticContainsKey(m: KryptonMap, key: unknown): boolean {
  if (m.eqDict === null || m.hashDict === null) return false;
  return m.data.has(new HashedKey(key, m.hashDict, m.eqDict));
}

export function staticDelete(m: KryptonMap, key: unknown): KryptonMap {
  if (m.eqDict === null || m.hashDict === null) return m;
  const wrapped = new HashedKey(key, m.hashDict, m.eqDict);
  return create(m.data.delete(wrapped), m.hashDict, m.eqDict);
}

export function staticKeys(m: KryptonMap): List<unknown> {
  return List(m.data.keySeq().map((hk) => hk.key));
}

export function staticValues(m: KryptonMap): List<unknown> {
  return List(m.data.valueSeq());
}

export function staticSize(m: KryptonMap): number {
  return m.data.size;
}

export function staticMerge(m1: KryptonMap, m2: KryptonMap): KryptonMap {
  if (m2.eqDict === null) return m1;
  return create(
    m1.data.merge(m2.data),
    m1.hashDict ?? m2.hashDict,
    m1.eqDict ?? m2.eqDict,
  );
}
