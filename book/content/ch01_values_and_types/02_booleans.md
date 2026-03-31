In the previous lesson, we explored Floats. Now we are going to take a look at Booleans, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about truth values and the logical operators used to combine them, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that `true` and `false` are `Bool` values, and Krypton uses `&&`, `||`, and `!` for logical composition. Note that the sample uses short business-style checks because this makes the expressions easy to read while still showing that boolean code is still ordinary expression code. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to boolean logic in nearly every typed language, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun can_ship(in_stock: Bool, paid: Bool) -> Bool = in_stock && paid

fun main() {
  println(can_ship(true, true))
  println(can_ship(true, false))
  println(!false)
}

```
