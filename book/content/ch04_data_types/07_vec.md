In the previous lesson, we explored Lists. Now we are going to take a look at Vec, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about the vector type for indexed sequences and common collection operations, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that this example imports a few helpers from `core/vec` so the lesson can show indexing, mapping, sorting, and length in one place. Note that vectors are often what readers mean when they say array or list in everyday programming conversation, so it helps to show practical operations instead of only the type name. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to small array utility examples in standard libraries, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
import core/vec.{len, nth, map, sort_by}

fun main() {
  let xs: Vec[Int] = [3, 1, 2]
  println(len(xs))
  println(map(xs, x -> x * 2))
  println(sort_by(xs, x -> x))
  println(nth(xs, 1))
}

```
