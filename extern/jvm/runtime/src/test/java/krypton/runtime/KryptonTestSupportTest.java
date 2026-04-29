package krypton.runtime;

import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class KryptonTestSupportTest {
    @Test
    void runWithTimeoutReturnsForFastBody() {
        AtomicBoolean ran = new AtomicBoolean(false);
        KryptonTestSupport.runWithTimeout(() -> ran.set(true), 1_000L);
        assertTrue(ran.get(), "body should have executed");
    }

    @Test
    void runWithTimeoutThrowsOnTimeout() {
        RuntimeException ex = assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runWithTimeout(() -> {
                while (!Thread.currentThread().isInterrupted()) {
                    // cooperative busy-spin: terminates promptly once
                    // runWithTimeout calls interrupt() on the worker.
                }
            }, 100L));
        assertEquals("test timed out", ex.getMessage());
    }

    @Test
    void runWithTimeoutPropagatesRuntimeException() {
        KryptonPanic original = new KryptonPanic("boom");
        RuntimeException caught = assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runWithTimeout(() -> { throw original; }, 1_000L));
        assertSame(original, caught, "the exact thrown instance must be re-thrown");
    }

    @Test
    void runWithTimeoutSurvivesAfterTimeout() {
        assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runWithTimeout(() -> {
                while (!Thread.currentThread().isInterrupted()) {
                    // spin until interrupted
                }
            }, 100L));

        AtomicBoolean ran = new AtomicBoolean(false);
        KryptonTestSupport.runWithTimeout(() -> ran.set(true), 1_000L);
        assertTrue(ran.get(), "subsequent fast call must complete normally");
    }
}
