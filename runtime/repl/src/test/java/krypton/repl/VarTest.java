package krypton.repl;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class VarTest {
    @Test
    void newVarIsUnbound() {
        Var v = new Var("x");
        assertFalse(v.isBound());
    }

    @Test
    void setThenGet() {
        Var v = new Var("x");
        v.set(42L);
        assertTrue(v.isBound());
        assertEquals(42L, v.get());
    }

    @Test
    void getUnboundThrows() {
        Var v = new Var("x");
        assertThrows(IllegalStateException.class, v::get);
    }

    @Test
    void clearMakesUnbound() {
        Var v = new Var("x");
        v.set(42L);
        v.clear();
        assertFalse(v.isBound());
    }

    @Test
    void nameReturnsName() {
        Var v = new Var("myVar");
        assertEquals("myVar", v.name());
    }
}
