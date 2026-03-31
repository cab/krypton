In the previous lesson, we explored Shared Values. Now we are going to take a look at Owned Values, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about marking a value as owned so it can be consumed at most once, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the ownership marker is written as `~T`, and a parameter of that type takes ownership of the argument it receives. Note that the example is intentionally minimal because the first job is simply to make the reader comfortable with the unusual punctuation and the idea of one-time use. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to affine or linear-flavored ownership systems, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun consume(ticket: ~String) -> String = ticket

fun main() {
  let ticket: ~String = "session"
  println(consume(ticket))
}

```
