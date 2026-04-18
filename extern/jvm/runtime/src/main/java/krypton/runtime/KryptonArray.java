package krypton.runtime;

import org.organicdesign.fp.collections.ImList;
import org.organicdesign.fp.collections.PersistentVector;

/**
 * Persistent-vector-backed Vec. The {@code data} field is {@code final}, so the
 * JMM §17.5 final-field guarantee gives safe publication across actor sends
 * without any synchronization.
 */
public final class KryptonArray {
    private final ImList<Object> data;

    KryptonArray(ImList<Object> data) {
        this.data = data;
    }

    public static KryptonArray of(ImList<Object> data) {
        return new KryptonArray(data);
    }

    /** Build from any Iterable. Used by other runtime classes (KryptonMap, JsonRuntime, KryptonString). */
    public static KryptonArray fromIterable(Iterable<?> items) {
        @SuppressWarnings("unchecked")
        Iterable<Object> boxed = (Iterable<Object>) items;
        return new KryptonArray(PersistentVector.ofIter(boxed));
    }

    public static long staticLength(KryptonArray arr) {
        return arr.data.size();
    }

    public static Object staticGet(KryptonArray arr, long index) {
        int i = (int) index;
        if (i < 0 || i >= arr.data.size()) {
            throw new KryptonPanic("index out of bounds: " + i + " (size: " + arr.data.size() + ")");
        }
        return arr.data.get(i);
    }

    public static KryptonArray staticPush(KryptonArray arr, Object value) {
        return new KryptonArray(arr.data.append(value));
    }
}
