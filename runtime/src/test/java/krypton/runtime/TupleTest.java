package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class TupleTest {
    @Test
    void tuple2FieldAccess() {
        Tuple2 t = new Tuple2(1L, "hello");
        assertEquals(1L, t._0());
        assertEquals("hello", t._1());
    }

    @Test
    void tuple2Equality() {
        Tuple2 a = new Tuple2(1L, "hi");
        Tuple2 b = new Tuple2(1L, "hi");
        assertEquals(a, b);
    }

    @Test
    void tuple3FieldAccess() {
        Tuple3 t = new Tuple3(1L, 2L, 3L);
        assertEquals(1L, t._0());
        assertEquals(2L, t._1());
        assertEquals(3L, t._2());
    }

    @Test
    void tuple4FieldAccess() {
        Tuple4 t = new Tuple4("a", "b", "c", "d");
        assertEquals("a", t._0());
        assertEquals("d", t._3());
    }
}
