package krypton.runtime;

@FunctionalInterface
public interface Fun1<A, R> {
    R apply(A a);
}
