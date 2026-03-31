In the previous lesson, we explored Exhaustiveness. Now we are going to take a look at Let Destructuring, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about using patterns directly in `let` bindings to unpack data immediately, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the pattern goes on the left-hand side of the `let`, so tuple and record pieces become local names without a separate `match`. Note that this is often the neatest way to unpack data that definitely has one known shape at that point in the code. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to destructuring lets in modern typed languages, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
type Point = { x: Int, y: Int }

fun main() {
  let pair = (2, 3)
  let (a, b) = pair
  let point = Point { x = 4, y = 5 }
  let Point { x, y } = point
  println(a + b + x + y)
}

```
