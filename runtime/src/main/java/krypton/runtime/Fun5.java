package krypton.runtime;

@FunctionalInterface
public interface Fun5<A, B, C, D, E, R> {
    R apply(A a, B b, C c, D d, E e);
}
