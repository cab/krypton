`shape` is a def-site polymorphism mechanism. It may appear in trait method signatures and top-level `fun` declarations, where the checker enumerates its plain and owned instantiations at definition time. A method declared `fun f(x: shape a) -> shape a` is checked twice: once with `a` bound to a plain value type, and once with `a` bound to an owned resource type. Both checks must succeed before the impl is accepted.

`shape` may **not** appear in first-class function types, closure parameters, or data structure fields. Higher-order code that wants to abstract over both plain and owned values should use a trait. This is analogous to Rust's `Fn` / `FnMut` / `FnOnce` distinction: mode polymorphism lives at the trait level, not in function values. A trait method can be shape-polymorphic because the checker sees its definition; a function value is opaque, so the checker cannot enumerate its cases.

```krypton
trait Identity[a] {
    fun identify(x: shape a) -> shape a
}

impl Identity[a] {
    fun identify(x: shape a) -> shape a = x
}
```

The cost of `shape` is exponential in the number of distinct shape variables per method (2^N forks), so the compiler caps the count at 6. If you find yourself wanting more, the right answer is almost certainly a trait-level redesign rather than stretching the cap.
