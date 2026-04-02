package krypton.repl;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class RegistryTest {
    @BeforeEach
    void setUp() {
        Registry.clear();
    }

    @Test
    void internCreatesThenReturns() {
        Var v1 = Registry.intern("x");
        Var v2 = Registry.intern("x");
        assertSame(v1, v2);
    }

    @Test
    void lookupAfterIntern() {
        Var interned = Registry.intern("x");
        Var looked = Registry.lookup("x");
        assertSame(interned, looked);
    }

    @Test
    void lookupUnknownThrows() {
        assertThrows(IllegalStateException.class, () -> Registry.lookup("nope"));
    }

    @Test
    void clearRemovesAll() {
        Registry.intern("a");
        Registry.intern("b");
        Registry.clear();
        assertThrows(IllegalStateException.class, () -> Registry.lookup("a"));
        assertThrows(IllegalStateException.class, () -> Registry.lookup("b"));
    }
}
