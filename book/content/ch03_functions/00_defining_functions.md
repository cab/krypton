In the previous lesson, we explored Koan Expressions. Now we are going to take a look at Defining Functions, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about declaring named functions that transform inputs into outputs, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that a simple definition uses `fun name(params) = body`, and Krypton can often infer the return type from the body. Note that the example is deliberately tiny because the key idea at this stage is the shape of the definition rather than some clever algorithm inside it. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to small function declarations in typed functional languages, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun add(a: Int, b: Int) -> Int = a + b

fun main() {
  println(add(20, 22))
}

```
