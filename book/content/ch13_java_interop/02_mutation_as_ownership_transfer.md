In the previous lesson, we explored Nullability Annotations. Now we are going to take a look at Mutation As Ownership Transfer, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about modeling mutating foreign APIs in a way that still fits Krypton’s ownership rules, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the exact runnable surface is still being settled, so this lesson intentionally stores the intended shape in comments instead of pretending the interop story is more finished than it is. Note that keeping the lesson slot matters because ownership-aware interop is conceptually important even while the final ergonomics are still being polished. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to builder-style mutation modeled as ownership transfer, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
# Planned interop shape:
# extern java "demo.Buffer" {
#   fun append(self: ~Buffer, part: String) -> ~Buffer
# }

fun main() {
  println("ownership-transfer interop scaffold")
}

```
