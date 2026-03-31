In the previous lesson, we explored Koan Pattern Matching. Now we are going to take a look at Result And Option Chaining, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about moving through fallible computations without immediately unwrapping every intermediate value by hand, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that this lesson uses a couple of tiny helper functions so the reader can watch `Option` and `Result` values be transformed instead of exploded into nested matches right away. Note that the helpers are intentionally simple because the real lesson is the shape of the data flow, not the cleverness of the utility functions. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to small map-style helpers around option and result types, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
import core/string.{parse_int}

fun map_option[a, b](opt: Option[a], f: (a) -> b) -> Option[b] = match opt {
  Some(value) => Some(f(value)),
  None => None,
}

fun map_result[e, a, b](res: Result[e, a], f: (a) -> b) -> Result[e, b] = match res {
  Ok(value) => Ok(f(value)),
  Err(err) => Err(err),
}

fun unwrap_or[a](opt: Option[a], default: a) -> a = match opt {
  Some(value) => value,
  None => default,
}

fun read_flag(ok: Bool) -> Result[String, Bool] =
  if ok { Ok(true) } else { Err("no flag") }

fun main() {
  let doubled = map_option(parse_int("21"), x -> x * 2)
  let labeled = map_result(read_flag(true), x -> if x { "yes" } else { "no" })
  println(unwrap_or(doubled, 0))
  println(labeled)
}

```
