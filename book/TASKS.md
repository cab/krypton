# Website Task List

## Phase 1: Homepage (pitch the language)

The current homepage is "the krypton tour" with a single editor. It needs to
sell Krypton to someone who's never heard of it.

- [ ] Write a tagline and 1-sentence pitch (what is Krypton, who is it for)
- [ ] Section 1: Type safety + functional — runnable snippet showing clean syntax
- [ ] Section 2: JVM target — snippet showing interop or ecosystem access
- [ ] Section 3: Ownership without a borrow checker — snippet showing `~T` and auto-close
- [ ] Section 4: Actors — snippet showing spawn/send/receive
- [ ] Section 5: Traits + HKT — snippet showing expressive abstractions
- [ ] "Start the tour" CTA button prominent at top and bottom
- [ ] Add install/GitHub links to nav

## Phase 2: Tour content (the grind)

2 of ~65 lessons exist. Work chapter by chapter. Each lesson lives in a flat
chapter-level Markdown file such as `00_hello_world.md`, with runnable ` ```krypton` fences and optional
` ```krypton static` fences. Test every runnable snippet in the browser before
moving on.

### Ch 0: Hello Krypton
- [x] 00 Hello World
- [x] 01 Comments
- [ ] 02 Building and Running

### Ch 1: Values and Types
- [ ] 00 Integers
- [ ] 01 Floats
- [ ] 02 Booleans
- [ ] 03 Strings
- [ ] 04 Unit
- [ ] 05 Type Annotations
- [ ] 06 Koan: Types

### Ch 2: Variables and Expressions
- [ ] 00 Let Bindings
- [ ] 01 Blocks
- [ ] 02 If Expressions
- [ ] 03 Operator Precedence
- [ ] 04 Koan: Expressions

### Ch 3: Functions
- [ ] 00 Defining Functions
- [ ] 01 Type Annotations on Functions
- [ ] 02 Anonymous Functions
- [ ] 03 Higher-Order Functions
- [ ] 04 UFCS
- [ ] 05 Recursion and Recur
- [ ] 06 Koan: Functions

### Ch 4: Data Types
- [ ] 00 Tuples
- [ ] 01 Records
- [ ] 02 Constructing Records
- [ ] 03 Record Updates
- [ ] 04 Sum Types
- [ ] 05 Constructing and Using Variants
- [ ] 06 Lists
- [ ] 07 Vec
- [ ] 08 Map and Set
- [ ] 09 Koan: Data Types

### Ch 5: Pattern Matching
- [ ] 00 Match Expressions
- [ ] 01 Literal and Variable Patterns
- [ ] 02 Constructor Patterns
- [ ] 03 Tuple and Record Patterns
- [ ] 04 Nested Patterns
- [ ] 05 Guards
- [ ] 06 Exhaustiveness
- [ ] 07 Let Destructuring
- [ ] 08 Koan: Pattern Matching

### Ch 6: Error Handling
- [ ] 00 Result and Option Chaining
- [ ] 01 The Question Mark Operator
- [ ] 02 Combining Results
- [ ] 03 Koan: Error Handling

### Ch 7: Generics
- [ ] 00 Generic Functions
- [ ] 01 Generic Types
- [ ] 02 Type Inference with Generics
- [ ] 03 Explicit Type Application
- [ ] 04 Koan: Generics

### Ch 8: Traits
- [ ] 00 Declaring Traits
- [ ] 01 Implementing Traits
- [ ] 02 Where Clauses
- [ ] 03 Multiple Bounds
- [ ] 04 Generic Implementations
- [ ] 05 Deriving
- [ ] 06 Common Traits
- [ ] 07 Koan: Traits

### Ch 9: Higher-Kinded Types
- [ ] 00 What Are Higher-Kinded Types
- [ ] 01 Functor
- [ ] 02 Writing HKT Code
- [ ] 03 Koan: HKT

### Ch 10: Ownership
- [ ] 00 Shared Values
- [ ] 01 Owned Values
- [ ] 02 The Resource Trait
- [ ] 03 Automatic Cleanup
- [ ] 04 The Question Mark Operator
- [ ] 05 Ownership in Practice
- [ ] 06 Koan: Ownership

### Ch 11: Actors and Concurrency
- [ ] 00 Spawning Actors
- [ ] 01 Send and Receive
- [ ] 02 Actor Loops with Recur
- [ ] 03 Request/Reply
- [ ] 04 Links and Supervision
- [ ] 05 Koan: Actors

### Ch 12: Modules and Visibility
- [ ] 00 Imports
- [ ] 01 Unqualified Imports
- [ ] 02 Visibility
- [ ] 03 Public Re-exports
- [ ] 04 Koan: Modules

### Ch 13: Java Interop
- [ ] 00 Extern Blocks
- [ ] 01 Nullability Annotations
- [ ] 02 Mutation as Ownership Transfer
- [ ] 03 Exception Handling
- [ ] 04 SAM Conversion
- [ ] 05 Subtyping and Coercion

### Ch 14: Putting It Together
- [ ] 00 Building a Chat Server

## Phase 3: Reference pages

- [ ] Getting Started / Install page (template + content)
- [ ] FAQ page (what runtime, what status, what inspired it, is it production-ready)
- [ ] Cheatsheet: Krypton for Rust developers
- [ ] Cheatsheet: Krypton for Kotlin/Scala developers
- [ ] Cheatsheet: Krypton for Java developers

## Phase 4: Community and credibility

- [ ] Community page (Discord/GitHub links)
- [ ] Blog/news section (even one "introducing Krypton" post)
- [ ] Roadmap page
