package krypton.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class KryptonMapTest {
    private static final Fun2<Object, Object, Object> EQ_DICT = (a, b) -> a.equals(b);
    private static final Fun1<Object, Object> HASH_DICT = value -> (long) value.hashCode();

    @Test
    void containsKeyDistinguishesPresentNullValuesFromMissingKeys() {
        KryptonMap map = KryptonMap.staticEmpty();
        map = KryptonMap.staticPut(map, "present", null, EQ_DICT, HASH_DICT);

        assertTrue(KryptonMap.staticContainsKey(map, "present"));
        assertNull(KryptonMap.staticGetUnsafe(map, "present"));
        assertFalse(KryptonMap.staticContainsKey(map, "missing"));
        assertNull(KryptonMap.staticGetUnsafe(map, "missing"));
    }
}
