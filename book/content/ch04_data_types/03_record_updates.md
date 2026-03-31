In the previous lesson, we explored Constructing Records. Now we are going to take a look at Record Updates, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about creating a modified copy of a record value without mutating the original one, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the update form `{ old | field = new_value }` starts from an existing record and replaces only the named fields. Note that this is a natural fit for immutable data because the reader can see exactly which parts changed while the unchanged fields are inherited from the original value. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to record update syntax in functional languages with persistent data, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
type Point = { x: Int, y: Int }

fun main() {
  let start = Point { x = 1, y = 2 }
  let moved = { start | x = 10 }
  println(start)
  println(moved)
}

```
