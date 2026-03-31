In the previous lesson, we explored Implementing Traits. Now we are going to take a look at Where Clauses, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about constraining generic code so it only applies when the needed trait support exists, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a `where` clause names the required trait bounds, such as `where a: Show`. Note that this is the point where generic signatures stop being completely free-floating and start declaring the capabilities they rely on. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to trait bounds and type class constraints, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun show_twice[a](x: a) -> String where a: Show = show(x) + " / " + show(x)

fun main() {
  println(show_twice(5))
  println(show_twice("Ada"))
}

```
