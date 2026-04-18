package krypton.runtime;

import org.organicdesign.fp.collections.ImMap;
import org.organicdesign.fp.collections.PersistentHashMap;
import org.organicdesign.fp.collections.UnmodIterator;

/**
 * Persistent-hash-map-backed Map. All fields are {@code final}, so the JMM
 * §17.5 final-field guarantee covers safe publication across actor sends
 * without synchronization.
 *
 * <p>Key-bridging: Paguro's default {@link org.organicdesign.fp.collections.Equator}
 * dispatches through {@code hashCode}/{@code equals}. {@link HashedKey} wraps
 * user keys and delegates to Krypton's {@code Eq}/{@code Hash} trait dicts —
 * keeps the Krypton dict-passing path orthogonal to the backing map choice.
 */
public final class KryptonMap {
    private final ImMap<HashedKey, Object> data;
    private final Fun1 hashFn;
    private final Fun2 eqFn;

    /**
     * Wraps a key to delegate hashCode/equals to the Krypton trait implementations.
     */
    static final class HashedKey {
        final Object key;
        private final int hash;
        private final Fun2 eqFn;

        HashedKey(Object key, Fun1 hashFn, Fun2 eqFn) {
            this.key = key;
            this.eqFn = eqFn;
            // Krypton Hash.hash returns Long; truncate to int for Java hashing
            this.hash = ((Long) hashFn.apply(key)).intValue();
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (!(obj instanceof HashedKey other)) return false;
            Object result = eqFn.apply(this.key, other.key);
            if (result instanceof Boolean b) return b;
            return ((Long) result) != 0;
        }
    }

    KryptonMap(ImMap<HashedKey, Object> data, Fun1 hashFn, Fun2 eqFn) {
        this.data = data;
        this.hashFn = hashFn;
        this.eqFn = eqFn;
    }

    private HashedKey wrap(Object key, Fun1 hashFn, Fun2 eqFn) {
        return new HashedKey(key, hashFn, eqFn);
    }

    public static KryptonMap staticEmpty() {
        return new KryptonMap(PersistentHashMap.empty(), null, null);
    }

    public static KryptonMap staticPut(KryptonMap map, Object key, Object value, Object eqDict, Object hashDict) {
        Fun2 eq = (Fun2) eqDict;
        Fun1 hash = (Fun1) hashDict;
        HashedKey wrapped = new HashedKey(key, hash, eq);
        return new KryptonMap(map.data.assoc(wrapped, value), hash, eq);
    }

    public static Object staticGetUnsafe(KryptonMap map, Object key) {
        if (map.eqFn == null) return null; // empty map, never put-to
        return map.data.get(new HashedKey(key, map.hashFn, map.eqFn));
    }

    public static boolean staticContainsKey(KryptonMap map, Object key) {
        if (map.eqFn == null) return false; // empty map, never put-to
        return map.data.containsKey(new HashedKey(key, map.hashFn, map.eqFn));
    }

    public static KryptonMap staticDelete(KryptonMap map, Object key) {
        if (map.eqFn == null) return map;
        return new KryptonMap(map.data.without(new HashedKey(key, map.hashFn, map.eqFn)), map.hashFn, map.eqFn);
    }

    public static KryptonArray staticKeys(KryptonMap map) {
        java.util.ArrayList<Object> keys = new java.util.ArrayList<>(map.data.size());
        UnmodIterator<HashedKey> it = map.data.keyIterator();
        while (it.hasNext()) {
            keys.add(it.next().key);
        }
        return KryptonArray.fromIterable(keys);
    }

    public static KryptonArray staticValues(KryptonMap map) {
        java.util.ArrayList<Object> values = new java.util.ArrayList<>(map.data.size());
        UnmodIterator<Object> it = map.data.valIterator();
        while (it.hasNext()) {
            values.add(it.next());
        }
        return KryptonArray.fromIterable(values);
    }

    public static long staticSize(KryptonMap map) {
        return map.data.size();
    }

    public static KryptonMap staticMerge(KryptonMap m1, KryptonMap m2) {
        if (m2.eqFn == null) return m1;
        ImMap<HashedKey, Object> merged = m1.data;
        UnmodIterator<HashedKey> it = m2.data.keyIterator();
        while (it.hasNext()) {
            HashedKey k = it.next();
            merged = merged.assoc(k, m2.data.get(k));
        }
        Fun1 hash = m1.hashFn != null ? m1.hashFn : m2.hashFn;
        Fun2 eq = m1.eqFn != null ? m1.eqFn : m2.eqFn;
        return new KryptonMap(merged, hash, eq);
    }
}
