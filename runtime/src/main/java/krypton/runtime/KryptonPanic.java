package krypton.runtime;

public class KryptonPanic extends RuntimeException {
    public KryptonPanic(String message) {
        super(message);
    }
}
