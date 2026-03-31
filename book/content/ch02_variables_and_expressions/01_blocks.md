In the previous lesson, we explored Let Bindings. Now we are going to take a look at Blocks, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about blocks as expressions that can contain several steps and still produce a value, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a block uses `{ ... }`, and the last expression in the block becomes the result of the whole block. Note that this matters because Krypton prefers expressions over statements, so even a multi-step computation still fits into a place where a value is needed. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to expression blocks in Rust or other expression-oriented languages, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun total() -> Int = {
  let base = 10
  let bonus = 2
  base + bonus
}

fun main() {
  println(total())
}

```
