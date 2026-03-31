In the previous lesson, we explored What Are Higher-Kinded Types. Now we are going to take a look at Functor, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about the classic abstraction for mapping a function over a wrapped value while preserving the outer shape, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a `Functor` trait usually exposes something like `fmap`, which transforms the element type from `a` to `b` inside some `f[_]` context. Note that even if the name sounds academic at first, the actual behavior is usually very mundane: apply a function inside a box-like structure without unpacking it by hand everywhere. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to standard functor presentations in functional programming, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
type Box[a] = Box(a)

trait Functor[f[_]] {
  fun fmap[a, b](fa: f[a], g: (a) -> b) -> f[b]
}

impl Functor[Box] {
  fun fmap[a, b](fa: Box[a], g: (a) -> b) -> Box[b] = match fa {
    Box(value) => Box(g(value)),
  }
}

fun unbox[a](box: Box[a]) -> a = match box {
  Box(value) => value,
}

fun main() {
  println(unbox(fmap(Box(20), x -> x + 1)))
}

```
