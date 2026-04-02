package krypton.runtime;

@FunctionalInterface
public interface Fun2<A, B, R> {
    R apply(A a, B b);
}
