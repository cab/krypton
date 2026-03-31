In the previous lesson, we explored Comments. Now we are going to take a look at Building and Running, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about building and running a Krypton project from the command line, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that `krypton build` compiles a project and `krypton run` builds and then executes the entry point in `src/main.kr`. Note that the important structural idea is that the project has a place for source files and a conventional entry point, so the tooling can do predictable work without much ceremony. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to tooling in languages that use a single main source file and a small project manifest, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
# src/main.kr
fun main() {
  println("Run me with krypton run")
}

# Typical commands:
# krypton build
# krypton run

```
