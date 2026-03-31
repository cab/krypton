In the previous lesson, we explored Extern Blocks. Now we are going to take a look at Nullability Annotations, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about describing when a foreign function may return null so Krypton can represent that possibility explicitly, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that `@nullable` on an extern function tells Krypton to expect an `Option[T]` result rather than a bare `T`. Note that this is a very practical interop feature because nullability rules are one of the first places where a typed host language and an external platform can disagree about what is safe. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to nullability adapters at language boundaries, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
extern java "java.lang.Integer" {
  @nullable fun parse_int(s: String) -> Option[Int]
}

fun main() {
  println(parse_int("42"))
  println(parse_int("oops"))
}

```
