In the previous lesson, we explored Koan Types. Now we are going to take a look at Let Bindings, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about creating named values with `let` and introducing the idea of shadowing, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a binding is written as `let name = value`, and a later `let` with the same name creates a new binding instead of mutating the old one. Note that the example uses one small shadowing step because it demonstrates the rule without dragging in unrelated details about larger programs. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to immutable local bindings in functional-first languages, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun main() {
  let score = 10
  let score = score + 5
  println(score)
}

```
