package krypton.runtime;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonRuntimeTest {
    @Test
    void versionIsSet() {
        assertNotNull(KryptonRuntime.VERSION);
        assertFalse(KryptonRuntime.VERSION.isEmpty());
    }

    @Test
    void initDoesNotThrow() {
        assertDoesNotThrow(KryptonRuntime::init);
    }
}
