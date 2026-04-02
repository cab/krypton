package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonStringTest {
    @Test
    void concatTwoStrings() {
        assertEquals("helloworld", KryptonString.concat("hello", "world"));
    }

    @Test
    void concatWithEmpty() {
        assertEquals("hello", KryptonString.concat("hello", ""));
        assertEquals("world", KryptonString.concat("", "world"));
    }

    @Test
    void lengthAscii() {
        assertEquals(5L, KryptonString.length("hello"));
    }

    @Test
    void lengthEmpty() {
        assertEquals(0L, KryptonString.length(""));
    }

    @Test
    void codepointLengthAscii() {
        assertEquals(5, KryptonString.codepointLength("hello"));
    }

    @Test
    void codepointLengthWithEmoji() {
        // "hi👋" — 3 codepoints, 4 chars
        assertEquals(3, KryptonString.codepointLength("hi\uD83D\uDC4B"));
    }

    @Test
    void codepointLengthEmpty() {
        assertEquals(0, KryptonString.codepointLength(""));
    }

    @Test
    void codepointSliceAscii() {
        assertEquals("ell", KryptonString.codepointSlice("hello", 1, 4));
    }

    @Test
    void codepointSliceWithEmoji() {
        // "hi👋world" — slice(1, 4) should be "i👋w"
        assertEquals("i\uD83D\uDC4Bw", KryptonString.codepointSlice("hi\uD83D\uDC4Bworld", 1, 4));
    }

    @Test
    void codepointSliceFull() {
        assertEquals("abc", KryptonString.codepointSlice("abc", 0, 3));
    }

    @Test
    void codepointSliceEmpty() {
        assertEquals("", KryptonString.codepointSlice("abc", 1, 1));
    }

    @Test
    void splitBasic() {
        KryptonArray result = (KryptonArray) KryptonString.split("a,b,c", ",");
        assertEquals(3, result.length());
        assertEquals("a", result.get(0));
        assertEquals("b", result.get(1));
        assertEquals("c", result.get(2));
    }

    @Test
    void splitEmpty() {
        KryptonArray result = (KryptonArray) KryptonString.split("", ",");
        assertEquals(1, result.length());
        assertEquals("", result.get(0));
    }

    @Test
    void splitNoMatch() {
        KryptonArray result = (KryptonArray) KryptonString.split("hello", ",");
        assertEquals(1, result.length());
        assertEquals("hello", result.get(0));
    }
}
