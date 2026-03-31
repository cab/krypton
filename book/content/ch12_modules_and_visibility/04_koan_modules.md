In the previous lesson, we explored Public Re-Exports. Now we are going to take a look at Koan Modules, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about repairing a tiny multi-file import sketch so the right public name is available in the consumer module, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the blanks are written as a scaffold because module exercises are naturally spread across files rather than confined to one local expression. Note that even as placeholder content, it is useful to reserve the lesson and describe the shape of the eventual exercise clearly. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to multi-file module drills, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to the incomplete example. The missing pieces are small on purpose, although it is worth mentioning that they are still large enough to force the reader to actually think about the rule instead of merely recognizing it. You may find it helpful to fill in one blank, run the program, and then fill in the next blank after seeing what changed. Feel free to experiment with the code above and generally notice what kind of compiler complaints or outputs appear.


```krypton
# math.kr
pub fun double(x: Int) -> Int = x * 2

# main.kr
import math.{???}

fun main() {
  # TODO: import the right name and call it here.
  println(double(21))
}

```
