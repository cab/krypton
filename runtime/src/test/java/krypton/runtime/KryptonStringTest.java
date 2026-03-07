package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonStringTest {
    @Test
    void codepointLengthAscii() {
        KryptonString s = new KryptonString("hello");
        assertEquals(5, s.codepointLength());
    }

    @Test
    void codepointLengthWithEmoji() {
        // "hi\uD83D\uDC4B" is "hi👋" — 3 codepoints, 4 chars
        KryptonString s = new KryptonString("hi\uD83D\uDC4B");
        assertEquals(3, s.codepointLength());
    }

    @Test
    void codepointLengthEmpty() {
        KryptonString s = new KryptonString("");
        assertEquals(0, s.codepointLength());
    }

    @Test
    void codepointSliceAscii() {
        KryptonString s = new KryptonString("hello");
        assertEquals("ell", s.codepointSlice(1, 4));
    }

    @Test
    void codepointSliceWithEmoji() {
        // "hi👋world" — slice(1, 4) should be "i👋w"
        KryptonString s = new KryptonString("hi\uD83D\uDC4Bworld");
        assertEquals("i\uD83D\uDC4Bw", s.codepointSlice(1, 4));
    }

    @Test
    void codepointSliceFull() {
        KryptonString s = new KryptonString("abc");
        assertEquals("abc", s.codepointSlice(0, 3));
    }

    @Test
    void codepointSliceEmpty() {
        KryptonString s = new KryptonString("abc");
        assertEquals("", s.codepointSlice(1, 1));
    }
}
