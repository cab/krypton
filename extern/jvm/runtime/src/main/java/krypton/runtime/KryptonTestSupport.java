package krypton.runtime;

/**
 * Runtime support for {@code core/test} assertions.
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
}
