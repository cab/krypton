In the previous lesson, we explored Request Reply. Now we are going to take a look at Links And Supervision, which is an important concept in Krypton. As you may already be aware, many programming languages have some way of talking about the supervision story for actors and the idea that failures can be observed and handled as part of the system design, and Krypton is no exception to that general pattern. It is worth mentioning, however, that the exact spelling still matters, because small syntax choices tend to shape how comfortably a reader can move through later code.

The example below demonstrates that the code below is an explicit scaffold because the surrounding runtime APIs are still being filled in, but the intended shape is shown in comments so the lesson slot exists in the tour. Note that this is one of those advanced topics where having a placeholder is still useful because the conceptual progression of the chapter matters even before every helper is polished. This may sound somewhat ordinary, and in a sense it is, but that is also why it is useful to see it written out plainly before the lessons get more layered. Interestingly, this is somewhat similar to supervision trees in actor-oriented systems, although the Krypton version has its own punctuation and naming choices that should be read carefully.

With that in mind, let us now turn our attention to what the program is doing at runtime and at compile time. The point is not only that the example works, but also that the surface shape of the code communicates the rule being introduced here in a fairly direct way. It is generally considered best practice to make one small change and see what changes elsewhere, even if the change is something as minor as a different literal, branch, field name, or type annotation. Feel free to experiment with the code above and observe what happens.


```krypton
# Planned supervision example scaffold.
# type WorkerMsg = Crash | Stop
# type SupervisorMsg = Restart
#
# fun supervisor(...) = ...
# fun main() {
#   # TODO: replace this scaffold with a runnable example when link/monitor APIs land.
# }

fun main() {
  println("links and supervision scaffold")
}

```
