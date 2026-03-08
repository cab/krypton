package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonConvertTest {
    @Test
    void toFloatBasic() {
        assertEquals(42.0, KryptonConvert.toFloat(42L));
    }

    @Test
    void toFloatZero() {
        assertEquals(0.0, KryptonConvert.toFloat(0L));
    }

    @Test
    void toFloatNegative() {
        assertEquals(-10.0, KryptonConvert.toFloat(-10L));
    }

    @Test
    void toFloatMaxValue() {
        assertEquals((double) Long.MAX_VALUE, KryptonConvert.toFloat(Long.MAX_VALUE));
    }

    @Test
    void toIntBasic() {
        assertEquals(42L, KryptonConvert.toInt(42.0));
    }

    @Test
    void toIntZero() {
        assertEquals(0L, KryptonConvert.toInt(0.0));
    }

    @Test
    void toIntNegative() {
        assertEquals(-10L, KryptonConvert.toInt(-10.5));
    }

    @Test
    void toIntMaxValue() {
        assertEquals((long) Double.MAX_VALUE, KryptonConvert.toInt(Double.MAX_VALUE));
    }

    @Test
    void intToStringBasic() {
        assertEquals("42", KryptonConvert.intToString(42L));
    }

    @Test
    void intToStringZero() {
        assertEquals("0", KryptonConvert.intToString(0L));
    }

    @Test
    void intToStringNegative() {
        assertEquals("-10", KryptonConvert.intToString(-10L));
    }

    @Test
    void floatToStringBasic() {
        assertEquals("3.14", KryptonConvert.floatToString(3.14));
    }

    @Test
    void floatToStringZero() {
        assertEquals("0.0", KryptonConvert.floatToString(0.0));
    }

    @Test
    void floatToStringNegative() {
        assertEquals("-2.5", KryptonConvert.floatToString(-2.5));
    }

    @Test
    void roundtripIntFloat() {
        long original = 123L;
        assertEquals(original, KryptonConvert.toInt(KryptonConvert.toFloat(original)));
    }

    @Test
    void roundtripIntString() {
        long original = 456L;
        assertEquals("456", KryptonConvert.intToString(original));
    }
}
