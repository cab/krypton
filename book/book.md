# Krypton Language Tour

## Design Decisions

**Format**: Interactive website (not a static book). Each lesson has editable,
runnable code in the browser via the Krypton compiler compiled to WASM.

**SSG**: A small custom static site generator (Rust or Python script). No
mdBook, Hugo, or other framework — the site structure is simple enough that a
purpose-built generator is less complexity than configuring a general-purpose
tool.

**Frontend**: Plain HTML + vanilla JS. No React, no MDX. Every page shares the
same layout:
- CodeMirror editor pane (editable)
- Output pane
- Run button
- Prev/next navigation

The WASM-compiled Krypton compiler runs entirely in-browser. No backend server.

**Content structure**: Gleam tour style — each chapter directory contains flat lesson Markdown files:
- `<lesson>.md` — prose plus inline code fences, for example `ch01_values_and_types/00_integers.md`
- ` ```krypton` / ` ```kr` — editable, runnable snippets embedded directly in the lesson
- ` ```krypton static` / ` ```kr static` — read-only highlighted snippets with no run button
- For koans/exercises, runnable and static Krypton fences still live inline in the same lesson file

**Lesson types**:
- **Tour** — "here's a concept, run this, try changing it"
- **Koan** — "fix this code" / "fill in the blank", checked against expected output
- **Quiz** — "what does this output?" (answered before running)

---

## Structure

### Chapter 0: Hello Krypton
- **00 Hello World** — `fun main`, printing, running a program
- **01 Comments** — `#` line comments
- **02 Building and Running** — `krypton build`, `krypton run`, project structure

### Chapter 1: Values and Types
- **00 Integers** — `Int` literals, basic arithmetic (`+`, `-`, `*`, `/`)
- **01 Floats** — `Float` literals, float arithmetic
- **02 Booleans** — `true`, `false`, logical operators (`&&`, `||`, `!`)
- **03 Strings** — `String` literals, string operations, string interpolation with `"${expr}"`
- **04 Unit** — `()` as the empty value, when it appears
- **05 Type Annotations** — `let x: Int = 5`, when to annotate vs when to let inference work
- **06 Koan: Types** — exercises on basic types and annotations

### Chapter 2: Variables and Expressions
- **00 Let Bindings** — `let x = 5`, immutability, shadowing
- **01 Blocks** — `{ expr; expr }`, block as expression returning last value
- **02 If Expressions** — `if cond { ... } else { ... }`, if as expression (not statement)
- **03 Operator Precedence** — arithmetic, comparison, logical; non-associativity of comparisons
- **04 Koan: Expressions** — exercises on blocks, if-expressions, precedence

### Chapter 3: Functions
- **00 Defining Functions** — `fun name(params) = body`, return type inference
- **01 Type Annotations on Functions** — explicit parameter and return types
- **02 Anonymous Functions** — `x -> x + 1`, `(a, b) -> a + b`, `() -> expr`
- **03 Higher-Order Functions** — functions as arguments and return values
- **04 UFCS** — `x.f()` as `f(x)`, method-style chaining
- **05 Recursion and Recur** — recursive functions, `recur` for tail calls. `recur` is Krypton's primary looping mechanism (no `for`/`while`); show iteration patterns: countdown, accumulator, list traversal
- **06 Koan: Functions** — exercises combining functions, lambdas, UFCS

### Chapter 4: Data Types
- **00 Tuples** — `(1, "hi")`, tuple types, destructuring
- **01 Records** — `type Point = { x: Int, y: Int }`, field access with `.`
- **02 Constructing Records** — `Point { x = 1, y = 2 }`, field punning. Note: `=` is for construction, `:` is for type declarations
- **03 Record Updates** — `{ p | x = 99 }`, creating modified copies
- **04 Sum Types** — `type Option[a] = Some(a) | None`, defining variants
- **05 Constructing and Using Variants** — `Some(42)`, `None`, `Ok(v)`, `Err(e)`
- **06 Lists** — `[1, 2, 3]`, `Cons`/`Nil`, `List[a]`
- **07 Vec** — `[1, 2, 3]` literal syntax, `Vec` as the default sequence type, `push`, `get`, `update`, `filter`, `sort`, `Vec.range`
- **08 Map and Set** — `Map.empty()`, `put`, `get`, `keys`/`values`; `Set` operations (`add`, `union`, `intersection`); `Eq + Hash` requirement for keys/elements
- **09 Koan: Data Types** — exercises on records, sum types, lists, Vec, Map, Set

### Chapter 5: Pattern Matching
- **00 Match Expressions** — `match x { ... }`, basic syntax
- **01 Literal and Variable Patterns** — matching on values, binding names
- **02 Constructor Patterns** — `Some(x)`, `Cons(h, t)`, `None`
- **03 Tuple and Record Patterns** — `(a, b)`, `Point { x, y }`, rest `..`
- **04 Nested Patterns** — `Some(Some(x))`, `Cons(h, Cons(h2, t))`
- **05 Guards** — `Some(x) if x > 0 => ...`
- **06 Exhaustiveness** — the compiler ensures all cases are covered
- **07 Let Destructuring** — `let (a, b) = pair`, `let Point { x, y } = p`
- **08 Koan: Pattern Matching** — exercises: write match arms, fix non-exhaustive matches

### Chapter 6: Error Handling
- **00 Result and Option Chaining** — `.map`, `.flat_map`, `.unwrap_or` on `Result[e, a]` and `Option[a]`
- **01 The Question Mark Operator** — `expr?`, early return on `Err`/`None`; return type determines behavior; compile errors for misuse (`E0401`, `E0403`)
- **02 Combining Results** — chaining multiple fallible operations with `?`: `read_file(path)?`, `parse_json(text)?`, `validate(json)`
- **03 Koan: Error Handling** — exercises: propagate errors through a pipeline, fix missing `?`, convert between `Result` and `Option`

### Chapter 7: Generics
- **00 Generic Functions** — `fun identity[a](x: a) -> a`, type parameters
- **01 Generic Types** — `type Box[a] = Box(a)`, parameterized data types
- **02 Type Inference with Generics** — when you can omit type arguments
- **03 Explicit Type Application** — `identity[Int](42)`, `xs.map[String](f)`. Note: you rarely need explicit type application — inference handles most cases
- **04 Koan: Generics** — exercises on writing and using generic code

### Chapter 8: Traits
- **00 Declaring Traits** — `trait Show[a] { fun show(x: a) -> String }`
- **01 Implementing Traits** — `impl Show[Int] { fun show(x) = ... }`
- **02 Where Clauses** — `where a: Show`, constraining type parameters
- **03 Multiple Bounds** — `where a: Show + Eq`, combining constraints
- **04 Generic Implementations** — `impl[a] Show[List[a]] where a: Show`
- **05 Deriving** — `deriving (Show, Eq)`, automatic implementations
- **06 Common Traits** — `Show`, `Eq`, `Ord`, `Default` — what they do and when to use them
- **07 Koan: Traits** — exercises: implement a trait, add where clauses, fix trait errors

### Chapter 9: Higher-Kinded Types
- **00 What Are Higher-Kinded Types** — `f[_]` as a type that takes a type, motivation. Framing: you probably don't need this yet — HKT is invisible by default, a library-author tool, not an application-code concern
- **01 Functor** — `trait Functor[f[_]]`, `fmap`, mapping over containers
- **02 Writing HKT Code** — using HKT in your own functions and traits; partial application (`Result[e, _]` as a Functor)
- **03 Koan: HKT** — exercises: implement Functor for a custom type

### Chapter 10: Ownership
- **00 Shared Values** — default behavior, values can be reused freely
- **01 Owned Values** — `~T`, affine types, use-at-most-once
- **02 The Resource Trait** — `trait Resource[T] { fun close(x: ~T) -> Unit }`
- **03 Automatic Cleanup** — compiler-inserted `close()` calls
- **04 The Question Mark Operator** — `expr?`, early return on error with cleanup of live `~Resource` values in LIFO order
- **05 Ownership in Practice** — file handles, connections, real-world patterns
- **06 Koan: Ownership** — exercises: spot the use-after-move, fix ownership errors

### Chapter 11: Actors and Concurrency
- **00 Spawning Actors** — `spawn`, `Ref[M]`, basic actor that receives messages; `Mailbox[M]` as first parameter
- **01 Send and Receive** — `send(ref, msg)` fire-and-forget, `receive(mb)` blocks; message types as sum types
- **02 Actor Loops with Recur** — `recur` for stateful actor loops, state threading via `recur(mb, new_state)`
- **03 Request/Reply** — `ask(target, variant_ctor, timeout_ms)` for synchronous-style calls, `Ref` for reply channels; `receive_timeout` returning `Option[M]`
- **04 Links and Supervision** — `link`, `monitor`, `spawn_link`; `Exit(ActorId, ExitReason)` as a user-defined variant; crash propagation and restart patterns
- **05 Koan: Actors** — exercises: build a counter actor, fix a message protocol, add supervision

### Chapter 12: Modules and Visibility
- **00 Imports** — `import core/list.{List, Cons, Nil}`, qualified access
- **01 Unqualified Imports** — bringing names into scope directly
- **02 Visibility** — `pub`, `pub opaque`, private by default
- **03 Public Re-exports** — `pub import`, controlling your module's API surface
- **04 Koan: Modules** — exercises on imports and visibility

### Chapter 13: Java Interop
- **00 Extern Blocks** — `extern java "java.lang.Math" { ... }` syntax, static methods, `as` aliasing for type names
- **01 Nullability Annotations** — `@nullable` → `Option`, `@nonnull` for direct use; missing annotation is a compile error
- **02 Mutation as Ownership Transfer** — `self: ~T` pattern, void-returning mutators return `~Self`; constructors always return `~T`
- **03 Exception Handling** — `@throws(ExType)` wraps return as `Result[ExType, T]`; without it, exceptions become actor panics
- **04 SAM Conversion** — closures as Java functional interfaces, `@sam` annotation
- **05 Subtyping and Coercion** — `: SuperType` declarations in extern headers, automatic upcasts at call sites

### Chapter 14: Putting It Together
- **00 Building a Chat Server** — actor-based project combining data types, pattern matching, traits, ownership, actors, and error handling. Guided walkthrough building a working chat server step by step.

### Appendix
- **A Keywords** — complete keyword list
- **B Operators and Precedence** — table of all operators with precedence/associativity
- **C Error Codes** — reference of compiler error codes (E0xxx)
