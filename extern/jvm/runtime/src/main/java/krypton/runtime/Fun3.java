package krypton.runtime;

@FunctionalInterface
public interface Fun3<A, B, C, R> {
    R apply(A a, B b, C c);
}
