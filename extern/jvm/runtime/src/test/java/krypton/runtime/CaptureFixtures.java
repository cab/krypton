package krypton.runtime;

final class CaptureFixtures {
    private CaptureFixtures() {}

    static void passWithStdout() {
        System.out.println("hello");
    }

    static void panicAfterStdout() {
        System.out.print("abc\n");
        throw new KryptonPanic("boom");
    }

    static void panicAfterStderr() {
        System.err.print("uh oh\n");
        throw new KryptonPanic("boom");
    }

    static void panicAfterMultilineStdout() {
        System.out.println("a");
        System.out.println("b");
        throw new KryptonPanic("boom");
    }

    static void quietPass() {
        // no I/O
    }
}
