In the previous lesson, we explored Higher-Order Functions. Now we are going to take a look at Ufcs, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about calling a free function with method-like syntax using uniform function call syntax, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that `x.f()` is another way to write `f(x)` when the names line up. Note that this can make pipelines easier to read because the data value stays visually on the left while the transformations read like a sequence of attached steps. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to method chaining, but powered by free functions rather than object methods, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun trim_bang(s: String) -> String = s + "!"
fun double(n: Int) -> Int = n * 2

fun main() {
  println(21.double())
  println("Krypton".trim_bang())
}

```
