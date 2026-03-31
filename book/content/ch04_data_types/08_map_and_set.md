In the previous lesson, we explored Vec. Now we are going to take a look at Map And Set, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about keyed collections and the idea that key types need equality and hashing support, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the runnable part of the example focuses on `Map`, while the comments call out the intended nearby `Set` material for later expansion. Note that this is one of the places where a scaffold is especially helpful because the collection concepts matter even if the surrounding library surface is still being filled in. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to dictionary-style collections in standard libraries, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
import core/map.{empty, put, get, keys, size}

fun main() {
  let scores = put(put(empty(), "Ada", 42), "Bob", 17)
  println(size(scores))
  println(get(scores, "Ada"))
  println(keys(scores))
  # TODO: add Set examples when the Set module lands.
}

```
