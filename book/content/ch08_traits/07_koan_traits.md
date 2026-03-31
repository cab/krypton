In the previous lesson, we explored Common Traits. Now we are going to take a look at Koan Traits, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about filling in a tiny trait implementation so a generic-looking call site works again, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the missing expression lives inside an `impl`, which means the reader has to pay attention to both the trait contract and the target type being implemented. Note that it is worth doing at least one of these by hand because trait syntax can look straightforward on a reread while still feeling slippery when you actually have to write it. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to type-class practice exercises, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to the incomplete example. The missing pieces are small on purpose, although it is worth mentioning that they are still large enough to force the reader to actually think about the rule instead of merely recognizing it. You may find it helpful to fill in one blank, run the program, and then fill in the next blank after seeing what changed. Feel free to experiment with the code above and generally notice what kind of compiler complaints or outputs appear.


```krypton
trait Label[a] {
  fun label(x: a) -> String
}

type Status = Ready | Waiting

impl Label[Status] {
  fun label(x: Status) -> String = ???
}

fun main() {
  # TODO: return different text for each constructor.
  println(label(Ready))
}

```
