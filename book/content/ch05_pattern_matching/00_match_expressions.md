In the previous lesson, we explored Koan Data Types. Now we are going to take a look at Match Expressions, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about branching on the shape or value of data with `match`, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that each `match` arm uses `=>`, and the whole `match` is an expression that returns a value. Note that the important shift is that one construct handles many forms of branching, which reduces the number of special rules the reader has to carry around. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to pattern matching in algebraic data type systems, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun label(n: Int) -> String = match n {
  0 => "zero",
  1 => "one",
  _ => "many",
}

fun main() {
  println(label(0))
  println(label(5))
}

```
