package krypton.runtime;

import java.util.HashMap;

public class KryptonMap {
    private final HashMap<HashedKey, Object> data;
    private Fun1 hashFn;
    private Fun2 eqFn;

    /**
     * Wraps a key to delegate hashCode/equals to the Krypton trait implementations.
     */
    private static final class HashedKey {
        final Object key;
        private final int hash;
        private final Fun2 eqFn;

        HashedKey(Object key, Fun1 hashFn, Fun2 eqFn) {
            this.key = key;
            this.eqFn = eqFn;
            // Krypton Hash.hash returns Long; truncate to int for Java HashMap
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
            // Krypton Eq.eq returns a boolean (boxed as Boolean via intrinsic)
            Object result = eqFn.apply(this.key, other.key);
            if (result instanceof Boolean b) return b;
            // Fallback: some Eq impls may return Long 1/0
            return ((Long) result) != 0;
        }
    }

    private KryptonMap() {
        this.data = new HashMap<>();
    }

    private KryptonMap(HashMap<HashedKey, Object> data, Fun1 hashFn, Fun2 eqFn) {
        this.data = data;
        this.hashFn = hashFn;
        this.eqFn = eqFn;
    }

    private HashedKey wrap(Object key) {
        return new HashedKey(key, hashFn, eqFn);
    }

    @SuppressWarnings("unchecked")
    private KryptonMap copy() {
        return new KryptonMap((HashMap<HashedKey, Object>) data.clone(), hashFn, eqFn);
    }

    public static KryptonMap staticEmpty() {
        return new KryptonMap();
    }

    public static KryptonMap staticPut(KryptonMap map, Object key, Object value, Object eqDict, Object hashDict) {
        KryptonMap m = map.copy();
        m.eqFn = (Fun2) eqDict;
        m.hashFn = (Fun1) hashDict;
        m.data.put(m.wrap(key), value);
        return m;
    }

    public static Object staticGet(KryptonMap map, Object key) {
        if (map.eqFn == null) return null; // empty map, never put-to
        return map.data.get(map.wrap(key));
    }

    public static boolean staticContainsKey(KryptonMap map, Object key) {
        if (map.eqFn == null) return false; // empty map, never put-to
        return map.data.containsKey(map.wrap(key));
    }

    public static KryptonMap staticDelete(KryptonMap map, Object key) {
        KryptonMap m = map.copy();
        m.data.remove(m.wrap(key));
        return m;
    }

    public static KryptonArray staticKeys(KryptonMap map) {
        KryptonArray arr = new KryptonArray(map.data.size());
        int i = 0;
        for (HashedKey k : map.data.keySet()) {
            arr.set(i++, k.key);
        }
        arr.freeze();
        return arr;
    }

    public static KryptonArray staticValues(KryptonMap map) {
        KryptonArray arr = new KryptonArray(map.data.size());
        int i = 0;
        for (Object v : map.data.values()) {
            arr.set(i++, v);
        }
        arr.freeze();
        return arr;
    }

    public static long staticSize(KryptonMap map) {
        return map.data.size();
    }

    public static KryptonMap staticMerge(KryptonMap m1, KryptonMap m2) {
        KryptonMap result = m1.copy();
        result.data.putAll(m2.data);
        return result;
    }
}
