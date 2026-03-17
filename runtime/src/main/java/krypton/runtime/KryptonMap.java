package krypton.runtime;

import java.util.HashMap;

public class KryptonMap {
    private final HashMap<Object, Object> data;

    public KryptonMap() {
        this.data = new HashMap<>();
    }

    private KryptonMap(HashMap<Object, Object> data) {
        this.data = data;
    }

    @SuppressWarnings("unchecked")
    private KryptonMap copy() {
        return new KryptonMap((HashMap<Object, Object>) data.clone());
    }

    public static Object staticEmpty() {
        return new KryptonMap();
    }

    public static Object staticPut(Object map, Object key, Object value) {
        KryptonMap m = ((KryptonMap) map).copy();
        m.data.put(key, value);
        return m;
    }

    public static Object staticGetUnsafe(Object map, Object key) {
        return ((KryptonMap) map).data.get(key);
    }

    public static boolean staticContainsKey(Object map, Object key) {
        return ((KryptonMap) map).data.containsKey(key);
    }

    public static Object staticDelete(Object map, Object key) {
        KryptonMap m = ((KryptonMap) map).copy();
        m.data.remove(key);
        return m;
    }

    public static Object staticKeys(Object map) {
        KryptonMap m = (KryptonMap) map;
        KryptonArray arr = new KryptonArray(m.data.size());
        int i = 0;
        for (Object k : m.data.keySet()) {
            arr.set(i++, k);
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
            arr.set(i++, e.getKey());
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
