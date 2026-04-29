package krypton.runtime;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;

/**
 * Runtime support for {@code core/test} assertions and the {@code krypton test}
 * harness.
 *
 * <p>v0.1 source location is recovered by walking the live thread's stack
 * trace and picking the first frame whose source file ends in {@code _test.kr}.
 * This mirrors how JUnit / ScalaTest surface the user-visible call site for a
 * failing assertion. The compiler emits {@code SourceFile} and
 * {@code LineNumberTable} attributes on every per-module class so the JVM
 * populates {@link StackTraceElement} with usable file names and line numbers.
 *
 * <p>Long-term, this will be replaced by a SourceLoc compiler-inserted caller
 * location (akin to Rust's {@code #[track_caller]}). The migration is a
 * mechanical replacement of the {@code firstTestFrame()} call in
 * {@code core/test} with a lookup of the inserted argument.
 */
public final class KryptonTestSupport {
    private KryptonTestSupport() {}

    /** Per-test wall-clock budget enforced by {@link #runTestWithTimeout}. */
    public static final long TEST_TIMEOUT_MS = 5_000L;

    /**
     * Returns {@code "src/<dir>/<file>:<line>"} for the first stack frame
     * whose source file ends in {@code _test.kr}, or {@code "<unknown>"} if
     * none found.
     *
     * <p>The {@code <dir>} segment is derived from the frame's class name
     * (which the codegen produces as the slash-separated module path) so
     * the rendered location matches the project's on-disk layout.
     */
    public static String firstTestFrame() {
        StackTraceElement[] trace = Thread.currentThread().getStackTrace();
        for (StackTraceElement frame : trace) {
            String fileName = frame.getFileName();
            if (fileName == null || !fileName.endsWith("_test.kr")) {
                continue;
            }
            String cls = frame.getClassName();
            int lastDot = cls.lastIndexOf('.');
            String dir = (lastDot >= 0)
                ? cls.substring(0, lastDot).replace('.', '/') + "/"
                : "";
            int line = frame.getLineNumber();
            return "src/" + dir + fileName + ":" + line;
        }
        return "<unknown>";
    }

    /**
     * Invoke {@code className.methodName()} with the standard 5-second per-test
     * timeout. The class name is the JVM-internal slash-separated form (the
     * harness emits these directly from the codegen's class names).
     *
     * <p>Called from generated harness bytecode. A {@link RuntimeException}
     * with message {@code "test timed out"} is thrown when the test does not
     * complete within {@link #TEST_TIMEOUT_MS}; the harness's existing
     * {@code RuntimeException} catch handler picks this up the same way it
     * picks up assertion panics.
     */
    public static void runTestWithTimeout(String className, String methodName) {
        final Method method;
        try {
            Class<?> cls = Class.forName(className.replace('/', '.'));
            method = cls.getDeclaredMethod(methodName);
            method.setAccessible(true);
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException("test runner: " + e, e);
        }

        PrintStream origOut = System.out;
        PrintStream origErr = System.err;
        ByteArrayOutputStream stdoutBuf = new ByteArrayOutputStream();
        ByteArrayOutputStream stderrBuf = new ByteArrayOutputStream();
        PrintStream capturedOut = new PrintStream(stdoutBuf, true, StandardCharsets.UTF_8);
        PrintStream capturedErr = new PrintStream(stderrBuf, true, StandardCharsets.UTF_8);
        System.setOut(capturedOut);
        System.setErr(capturedErr);
        try {
            runWithTimeout(() -> {
                try {
                    method.invoke(null);
                } catch (InvocationTargetException ex) {
                    Throwable cause = ex.getCause();
                    if (cause instanceof RuntimeException) throw (RuntimeException) cause;
                    if (cause instanceof Error) throw (Error) cause;
                    throw new RuntimeException(cause);
                } catch (IllegalAccessException ex) {
                    throw new RuntimeException("test runner: " + ex, ex);
                }
            }, TEST_TIMEOUT_MS);
        } catch (RuntimeException original) {
            capturedOut.flush();
            capturedErr.flush();
            String stdout = stdoutBuf.toString(StandardCharsets.UTF_8);
            String stderr = stderrBuf.toString(StandardCharsets.UTF_8);
            throw new RuntimeException(
                augmentMessage(original.getMessage(), stdout, stderr),
                original);
        } finally {
            System.setOut(origOut);
            System.setErr(origErr);
        }
    }

    private static String augmentMessage(String original, String stdout, String stderr) {
        StringBuilder msg = new StringBuilder();
        if (original != null) msg.append(original);
        appendCaptureBlock(msg, "captured stdout", stdout);
        appendCaptureBlock(msg, "captured stderr", stderr);
        return msg.toString();
    }

    private static void appendCaptureBlock(StringBuilder msg, String heading, String content) {
        if (content.isEmpty()) return;
        if (msg.length() > 0 && msg.charAt(msg.length() - 1) != '\n') msg.append('\n');
        msg.append(heading).append(":\n");
        // Strip exactly one trailing '\n' (the terminator from the last println)
        // so the harness's own println on the augmented message does not produce
        // a trailing blank line. Internal newlines are preserved verbatim.
        if (content.endsWith("\n")) {
            msg.append(content, 0, content.length() - 1);
        } else {
            msg.append(content);
        }
    }

    /**
     * Run {@code body} on a short-lived daemon worker, joining for at most
     * {@code timeoutMs} milliseconds. On expiry the worker is interrupted
     * (cooperative — a non-cooperative test continues running but does not
     * block the suite, and dies when the harness's {@code System.exit}
     * tears down the JVM) and a {@link RuntimeException} with message
     * {@code "test timed out"} is thrown to the caller.
     *
     * <p>Cross-thread error propagation uses a one-element {@link Throwable}
     * array; the {@link Thread#start} / {@link Thread#join} pair establishes
     * the necessary happens-before edge.
     *
     * <p>Package-private overload exists so unit tests can exercise the
     * timeout mechanic with sub-second deadlines instead of paying the
     * full 5-second wall-clock.
     */
    static void runWithTimeout(Runnable body, long timeoutMs) {
        final Throwable[] thrown = new Throwable[1];
        Thread t = new Thread(() -> {
            try {
                body.run();
            } catch (Throwable ex) {
                thrown[0] = ex;
            }
        }, "krypton-test-runner");
        t.setDaemon(true);
        t.start();
        try {
            t.join(timeoutMs);
        } catch (InterruptedException ie) {
            Thread.currentThread().interrupt();
            throw new RuntimeException("test runner interrupted", ie);
        }
        if (t.isAlive()) {
            t.interrupt();
            throw new RuntimeException("test timed out");
        }
        Throwable err = thrown[0];
        if (err == null) return;
        if (err instanceof RuntimeException) throw (RuntimeException) err;
        if (err instanceof Error) throw (Error) err;
        throw new RuntimeException(err);
    }
}
