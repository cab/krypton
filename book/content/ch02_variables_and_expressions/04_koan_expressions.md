In the previous lesson, we explored Operator Precedence. Now we are going to take a look at Koan Expressions, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about repairing a small example that mixes bindings, blocks, and conditional expressions, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the blanks are chosen so the reader has to think about expression results instead of only filling in random literals. Note that this kind of exercise is useful because expression-oriented code becomes natural only after a few small corrections have been made by hand. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to guided workbook exercises for language basics, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to the incomplete example. The missing pieces are small on purpose, although it is worth mentioning that they are still large enough to force the reader to actually think about the rule instead of merely recognizing it. You may find it helpful to fill in one blank, run the program, and then fill in the next blank after seeing what changed. Feel free to experiment with the code above and generally notice what kind of compiler complaints or outputs appear.


```krypton
fun main() {
  let value = {
    let x = ???
    if x > 3 { x * 2 } else { ??? }
  }
  # TODO: make value evaluate to 8.
  println(value)
}

```
