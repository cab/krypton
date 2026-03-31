In the previous lesson, we explored Constructor Patterns. Now we are going to take a look at Tuple And Record Patterns, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about destructuring tuples and records inside pattern matches, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that pattern shapes can mirror tuple and record construction syntax so the individual pieces get names immediately. Note that this keeps unpacking code short and local, which is especially useful once data gets passed through several helper functions. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to destructuring patterns in typed functional languages, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
type Point = { x: Int, y: Int }

fun show_pair(data: ((Int, Int), Point)) -> String = match data {
  ((a, b), Point { x, y }) => show(a + b + x + y),
}

fun main() {
  println(show_pair(((1, 2), Point { x = 3, y = 4 })))
}

```
