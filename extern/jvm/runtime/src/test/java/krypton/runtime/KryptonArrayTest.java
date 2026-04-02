package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonArrayTest {
    @Test
    void newArrayHasZeroLength() {
        KryptonArray arr = new KryptonArray(10);
        assertEquals(0, arr.length());
    }

    @Test
    void getSetRoundTrip() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "hello");
        arr.set(1, 42);
        assertEquals("hello", arr.get(0));
        assertEquals(42, arr.get(1));
    }

    @Test
    void lengthTracksSetElements() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "a");
        assertEquals(1, arr.length());
        arr.set(1, "b");
        assertEquals(2, arr.length());
        arr.set(3, "d");
        assertEquals(4, arr.length());
    }

    @Test
    void copyCreatesIndependentArray() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "original");
        KryptonArray copy = arr.copy();
        copy.set(0, "modified");
        assertEquals("original", arr.get(0));
        assertEquals("modified", copy.get(0));
    }

    @Test
    void copyPreservesLength() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "a");
        arr.set(1, "b");
        KryptonArray copy = arr.copy();
        assertEquals(2, copy.length());
    }

    @Test
    void freezePreventsSet() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "a");
        arr.freeze();
        assertThrows(KryptonPanic.class, () -> arr.set(0, "b"));
        assertThrows(KryptonPanic.class, () -> arr.set(1, "c"));
    }

    @Test
    void getAfterFreezeStillWorks() {
        KryptonArray arr = new KryptonArray(4);
        arr.set(0, "a");
        arr.freeze();
        assertEquals("a", arr.get(0));
    }

    @Test
    void outOfBoundsGetThrows() {
        KryptonArray arr = new KryptonArray(4);
        assertThrows(KryptonPanic.class, () -> arr.get(0));
        assertThrows(KryptonPanic.class, () -> arr.get(-1));
        assertThrows(KryptonPanic.class, () -> arr.get(4));
    }

    @Test
    void outOfBoundsSetThrows() {
        KryptonArray arr = new KryptonArray(4);
        assertThrows(KryptonPanic.class, () -> arr.set(-1, "x"));
        assertThrows(KryptonPanic.class, () -> arr.set(4, "x"));
    }
}
