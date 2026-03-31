In the previous lesson, we explored Records. Now we are going to take a look at Constructing Records, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about building record values with the constructor syntax that mirrors the declared fields, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that record construction uses `=` inside the braces even though type declarations use `:`. Note that this distinction often looks slightly fussy the first time through, but it becomes routine once the reader recognizes that one context declares a type and the other fills in actual values. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to separate declaration syntax versus construction syntax in other typed systems, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
type Player = { name: String, score: Int }

fun main() {
  let name = "Ada"
  let player = Player { name = name, score = 42 }
  println(player)
}

```
