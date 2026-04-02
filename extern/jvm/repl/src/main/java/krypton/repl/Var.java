package krypton.repl;

public final class Var {
    private static final Object UNBOUND = new Object();

    private final String name;
    private volatile Object value = UNBOUND;

    public Var(String name) {
        this.name = name;
    }

    public String name() {
        return name;
    }

    public boolean isBound() {
        return value != UNBOUND;
    }

    public Object get() {
        Object v = value;
        if (v == UNBOUND) {
            throw new IllegalStateException("Var '" + name + "' is unbound");
        }
        return v;
    }

    public void set(Object v) {
        this.value = v;
    }

    public void clear() {
        this.value = UNBOUND;
    }
}
