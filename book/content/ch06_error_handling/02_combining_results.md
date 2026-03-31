In the previous lesson, we explored The Question Mark Operator. Now we are going to take a look at Combining Results, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about sequencing several fallible steps so each successful value feeds the next step, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a `Result`-returning function can use `?` repeatedly inside a block to keep the happy path linear. Note that this is one of those cases where the code often reads much more naturally once the failure plumbing is compressed into the operator. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to railway-style result pipelines written in direct style, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun first_name(ok: Bool) -> Result[String, String] =
  if ok { Ok("Ada") } else { Err("missing first name") }

fun last_name(ok: Bool) -> Result[String, String] =
  if ok { Ok("Lovelace") } else { Err("missing last name") }

fun full_name() -> Result[String, String] = {
  let first = first_name(true)?
  let last = last_name(true)?
  Ok(first + " " + last)
}

fun main() {
  println(full_name())
}

```
