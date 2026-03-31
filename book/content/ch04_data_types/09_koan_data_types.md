In the previous lesson, we explored Map And Set. Now we are going to take a look at Koan Data Types, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about repairing a small data definition and construction example by filling in the missing values, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the blanks sit inside a record literal so the reader has to pay attention to field names as well as to the expressions on the right-hand side. Note that this is meant to be slightly annoying in a productive way, which is usually when the syntax finally becomes memorable. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to introductory data-modeling exercises, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to the incomplete example. The missing pieces are small on purpose, although it is worth mentioning that they are still large enough to force the reader to actually think about the rule instead of merely recognizing it. You may find it helpful to fill in one blank, run the program, and then fill in the next blank after seeing what changed. Feel free to experiment with the code above and generally notice what kind of compiler complaints or outputs appear.


```krypton
type Point = { x: Int, y: Int }

fun main() {
  let point = Point { x = ???, y = ??? }
  # TODO: make the point use the coordinates 3 and 4.
  println(point)
}

```
