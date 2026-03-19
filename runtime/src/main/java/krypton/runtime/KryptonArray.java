package krypton.runtime;

import java.util.Arrays;

public class KryptonArray {
    private final Object[] data;
    private int size;
    private boolean frozen;

    public KryptonArray(int capacity) {
        this.data = new Object[capacity];
        this.size = 0;
        this.frozen = false;
    }

    private KryptonArray(Object[] data, int size) {
        this.data = data;
        this.size = size;
        this.frozen = false;
    }

    public Object get(int index) {
        if (index < 0 || index >= size) {
            throw new KryptonPanic("index out of bounds: " + index + " (size: " + size + ")");
        }
        return data[index];
    }

    public void set(int index, Object value) {
        if (frozen) {
            throw new KryptonPanic("cannot mutate frozen array");
        }
        if (index < 0 || index >= data.length) {
            throw new KryptonPanic("index out of bounds: " + index + " (capacity: " + data.length + ")");
        }
        data[index] = value;
        if (index >= size) {
            size = index + 1;
        }
    }

    public int length() {
        return size;
    }

    public KryptonArray copy() {
        return new KryptonArray(Arrays.copyOf(data, data.length), size);
    }

    public void freeze() {
        this.frozen = true;
    }

    // Static wrappers for extern descriptor convention
    public static long staticLength(Object arr) {
        return ((KryptonArray) arr).length();
    }

    public static Object staticGet(Object arr, long index) {
        return ((KryptonArray) arr).get((int) index);
    }

    public static Object staticNew(long capacity) {
        return new KryptonArray((int) capacity);
    }

    public static void staticSet(Object arr, long index, Object value) {
        ((KryptonArray) arr).set((int) index, value);
    }

    public static Object staticFreeze(Object arr) {
        ((KryptonArray) arr).freeze();
        return arr;
    }
}
