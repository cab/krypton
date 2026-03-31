In the previous lesson, we explored Ufcs. Now we are going to take a look at Recursion And Recur, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about repetition through recursive functions and tail-recursive `recur` calls, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that `recur(...)` jumps back to the current function with new arguments, and Krypton uses this as its main structured looping mechanism. Note that this deserves a dedicated example because it is one of the places where Krypton makes a more opinionated choice than languages that teach `for` and `while` first. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to tail-recursive style in languages that optimize recursive loops, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
fun count_down(n: Int) -> Int =
  if n <= 0 { 0 } else { recur(n - 1) }

fun sum_to(n: Int, acc: Int) -> Int =
  if n <= 0 { acc } else { recur(n - 1, acc + n) }

fun main() {
  println(count_down(3))
  println(sum_to(5, 0))
}

```
