package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonPanicTest {
    @Test
    void extendsRuntimeException() {
        KryptonPanic panic = new KryptonPanic("boom");
        assertInstanceOf(RuntimeException.class, panic);
    }

    @Test
    void messageAccessible() {
        KryptonPanic panic = new KryptonPanic("something went wrong");
        assertEquals("something went wrong", panic.getMessage());
    }

    @Test
    void throwableWithMessage() {
        Exception caught = assertThrows(KryptonPanic.class, () -> {
            throw new KryptonPanic("test panic");
        });
        assertEquals("test panic", caught.getMessage());
    }
}
