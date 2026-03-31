package krypton.runtime;

@FunctionalInterface
public interface Fun4<A, B, C, D, R> {
    R apply(A a, B b, C c, D d);
}
