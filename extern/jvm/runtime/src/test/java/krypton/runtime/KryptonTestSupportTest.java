package krypton.runtime;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
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

    @Test
    void runTestWithTimeoutDiscardsCapturedStdoutOnPass() {
        PrintStream origOut = System.out;
        PrintStream origErr = System.err;
        ByteArrayOutputStream outerOut = new ByteArrayOutputStream();
        ByteArrayOutputStream outerErr = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outerOut, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(outerErr, true, StandardCharsets.UTF_8));
        try {
            KryptonTestSupport.runTestWithTimeout(
                "krypton/runtime/CaptureFixtures", "passWithStdout");
        } finally {
            System.setOut(origOut);
            System.setErr(origErr);
        }
        assertEquals("", outerOut.toString(StandardCharsets.UTF_8),
            "captured stdout from a passing test must be discarded silently");
        assertEquals("", outerErr.toString(StandardCharsets.UTF_8),
            "no stderr should leak from a passing test");
    }

    @Test
    void runTestWithTimeoutAttachesStdoutOnFailure() {
        RuntimeException ex = assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runTestWithTimeout(
                "krypton/runtime/CaptureFixtures", "panicAfterStdout"));
        assertEquals("boom\ncaptured stdout:\nabc", ex.getMessage());
    }

    @Test
    void runTestWithTimeoutAttachesStderrOnFailure() {
        RuntimeException ex = assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runTestWithTimeout(
                "krypton/runtime/CaptureFixtures", "panicAfterStderr"));
        assertEquals("boom\ncaptured stderr:\nuh oh", ex.getMessage());
    }

    @Test
    void runTestWithTimeoutRestoresStreamsAfterTest() {
        PrintStream origOut = System.out;
        PrintStream origErr = System.err;
        ByteArrayOutputStream outerOut = new ByteArrayOutputStream();
        ByteArrayOutputStream outerErr = new ByteArrayOutputStream();
        System.setOut(new PrintStream(outerOut, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(outerErr, true, StandardCharsets.UTF_8));
        try {
            KryptonTestSupport.runTestWithTimeout(
                "krypton/runtime/CaptureFixtures", "quietPass");
            System.out.print("post-pass-out");
            System.err.print("post-pass-err");
            assertEquals("post-pass-out", outerOut.toString(StandardCharsets.UTF_8),
                "streams must be restored after a passing test");
            assertEquals("post-pass-err", outerErr.toString(StandardCharsets.UTF_8),
                "stderr must be restored after a passing test");

            outerOut.reset();
            outerErr.reset();

            assertThrows(RuntimeException.class, () ->
                KryptonTestSupport.runTestWithTimeout(
                    "krypton/runtime/CaptureFixtures", "panicAfterStdout"));
            System.out.print("post-fail-out");
            System.err.print("post-fail-err");
            assertEquals("post-fail-out", outerOut.toString(StandardCharsets.UTF_8),
                "streams must be restored after a failing test");
            assertEquals("post-fail-err", outerErr.toString(StandardCharsets.UTF_8),
                "stderr must be restored after a failing test");
        } finally {
            System.setOut(origOut);
            System.setErr(origErr);
        }
    }

    @Test
    void runTestWithTimeoutPreservesNewlinesNoTrailingBlankLine() {
        RuntimeException ex = assertThrows(RuntimeException.class, () ->
            KryptonTestSupport.runTestWithTimeout(
                "krypton/runtime/CaptureFixtures", "panicAfterMultilineStdout"));
        assertEquals("boom\ncaptured stdout:\na\nb", ex.getMessage());
    }
}
