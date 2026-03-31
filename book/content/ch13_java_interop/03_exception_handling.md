In the previous lesson, we explored Mutation As Ownership Transfer. Now we are going to take a look at Exception Handling, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about describing how throwing Java methods should appear at the Krypton boundary, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the intended annotation-based syntax is shown as scaffold comments because this part of the interop surface is not yet fully wired into the checked examples in the repo. Note that this is still a useful placeholder because exception behavior changes the shape of every downstream call site, so the documentation arc should acknowledge it early. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to checked wrappers around throwing foreign calls, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
# Planned interop shape:
# extern java "java.nio.file.Files" {
#   @throws(IOException) fun read_string(path: Path) -> Result[IOException, String]
# }

fun main() {
  println("exception-handling interop scaffold")
}

```
