package krypton.repl;

import java.util.concurrent.ConcurrentHashMap;

public final class Registry {
    private static final ConcurrentHashMap<String, Var> vars = new ConcurrentHashMap<>();

    private Registry() {}

    public static Var intern(String name) {
        return vars.computeIfAbsent(name, Var::new);
    }

    public static Var lookup(String name) {
        Var v = vars.get(name);
        if (v == null) {
            throw new IllegalStateException("No Var registered for '" + name + "'");
        }
        return v;
    }

    public static void clear() {
        vars.clear();
    }
}
