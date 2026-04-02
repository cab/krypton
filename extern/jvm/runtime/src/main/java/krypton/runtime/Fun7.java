package krypton.runtime;

@FunctionalInterface
public interface Fun7<A, B, C, D, E, F, G, R> {
    R apply(A a, B b, C c, D d, E e, F f, G g);
}
