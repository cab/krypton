In the previous lesson, we explored Tuple And Record Patterns. Now we are going to take a look at Nested Patterns, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about combining several smaller patterns into one larger shape, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a nested pattern simply follows the structure of the data, so a value like `Some(Some(x))` can be matched in one arm. Note that this is valuable because it lets the shape of the data do the branching work instead of forcing the reader to write several layers of manual checks. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to deep pattern matching in languages with algebraic data types, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun describe(opt: Option[Option[Int]]) -> String = match opt {
  Some(Some(value)) => "nested: " + show(value),
  Some(None) => "inner none",
  None => "outer none",
}

fun main() {
  println(describe(Some(Some(9))))
}

```
