package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonArrayTest {
    @Test
    void builderRoundTrip() {
        KryptonArrayBuilder b = KryptonArrayBuilder.builderNew();
        KryptonArrayBuilder.builderPush(b, "hello");
        KryptonArrayBuilder.builderPush(b, 42);
        KryptonArray arr = KryptonArrayBuilder.builderFreeze(b);
        assertEquals(2, KryptonArray.staticLength(arr));
        assertEquals("hello", KryptonArray.staticGet(arr, 0));
        assertEquals(42, KryptonArray.staticGet(arr, 1));
    }

    @Test
    void emptyBuilderProducesEmptyArray() {
        KryptonArray arr = KryptonArrayBuilder.builderFreeze(KryptonArrayBuilder.builderNew());
        assertEquals(0, KryptonArray.staticLength(arr));
    }

    @Test
    void staticPushReturnsPersistentCopy() {
        KryptonArray a = KryptonArrayBuilder.builderFreeze(KryptonArrayBuilder.builderNew());
        KryptonArray b = KryptonArray.staticPush(a, "x");
        KryptonArray c = KryptonArray.staticPush(b, "y");
        assertEquals(0, KryptonArray.staticLength(a));
        assertEquals(1, KryptonArray.staticLength(b));
        assertEquals(2, KryptonArray.staticLength(c));
        assertEquals("x", KryptonArray.staticGet(c, 0));
        assertEquals("y", KryptonArray.staticGet(c, 1));
    }

    @Test
    void fromIterableBuildsArray() {
        KryptonArray arr = KryptonArray.fromIterable(java.util.List.of("a", "b", "c"));
        assertEquals(3, KryptonArray.staticLength(arr));
        assertEquals("a", KryptonArray.staticGet(arr, 0));
        assertEquals("c", KryptonArray.staticGet(arr, 2));
    }

    @Test
    void outOfBoundsGetThrows() {
        KryptonArray arr = KryptonArrayBuilder.builderFreeze(KryptonArrayBuilder.builderNew());
        assertThrows(KryptonPanic.class, () -> KryptonArray.staticGet(arr, 0));
        assertThrows(KryptonPanic.class, () -> KryptonArray.staticGet(arr, -1));
    }
}
