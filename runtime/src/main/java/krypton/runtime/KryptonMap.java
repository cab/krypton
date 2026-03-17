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

    public static Object staticEmpty() {
        return new KryptonMap();
    }

    public static Object staticPut(Object map, Object key, Object value, Object eqFn, Object hashFn) {
        KryptonMap m = ((KryptonMap) map).copy();
        // Lazily set eq/hash fns from the first put
        if (m.eqFn == null) {
            m.eqFn = (Fun2) eqFn;
            m.hashFn = (Fun1) hashFn;
        }
        m.data.put(m.wrap(key), value);
        return m;
    }

    public static Object staticGetUnsafe(Object map, Object key) {
        KryptonMap m = (KryptonMap) map;
        return m.data.get(m.wrap(key));
    }

    public static boolean staticContainsKey(Object map, Object key) {
        KryptonMap m = (KryptonMap) map;
        if (m.eqFn == null) return false; // empty map, never put-to
        return m.data.containsKey(m.wrap(key));
    }

    public static Object staticDelete(Object map, Object key) {
        KryptonMap m = ((KryptonMap) map).copy();
        m.data.remove(m.wrap(key));
        return m;
    }

    public static Object staticKeys(Object map) {
        KryptonMap m = (KryptonMap) map;
        KryptonArray arr = new KryptonArray(m.data.size());
        int i = 0;
        for (HashedKey k : m.data.keySet()) {
            arr.set(i++, k.key);
        }
        arr.freeze();
        return arr;
    }

    public static Object staticValues(Object map) {
        KryptonMap m = (KryptonMap) map;
        KryptonArray arr = new KryptonArray(m.data.size());
        int i = 0;
        for (Object v : m.data.values()) {
            arr.set(i++, v);
        }
        arr.freeze();
        return arr;
    }

    public static Object staticEntries(Object map) {
        KryptonMap m = (KryptonMap) map;
        KryptonArray arr = new KryptonArray(m.data.size() * 2);
        int i = 0;
        for (var e : m.data.entrySet()) {
            arr.set(i++, e.getKey().key);
            arr.set(i++, e.getValue());
        }
        arr.freeze();
        return arr;
    }

    public static long staticSize(Object map) {
        return ((KryptonMap) map).data.size();
    }

    public static Object staticMerge(Object a, Object b) {
        KryptonMap ma = ((KryptonMap) a).copy();
        ma.data.putAll(((KryptonMap) b).data);
        return ma;
    }
}
