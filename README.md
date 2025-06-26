# Artifact for Modal Effect Types

This is the artifact for the paper:

*Wenhao Tang, Leo White, Stephen Dolan, Daniel Hillerström, Sam Lindley, Anton Lorenzen,
"Modal Effect Types", Proc. ACM Program. Lang. 9(OOPSLA1), 2025*

This document is in markdown format.


## Introduction

This artifact contains the implementation of the surface language METL
as introduced in Section 2 of the paper. The implementation includes a
parser, type checker (based on the bidirectional type checking
introduced in Section 7 and Appendix D), and an interpreter. This
implementation does **not** include elaboration from METL to MET or
compilation of METL to any other low-level languages.

As claimed in the paper, this implementation type checks all example
programs in the paper.

The implementation is written in Haskell. The artifact itself is a
[Stack](https://docs.haskellstack.org/en/stable/) project, where
* `src` contains the source code (in Haskell), and
* `test` contains test files (in METL).

## Hardware Dependencies

Any laptop should work.

## Getting Started Guide

To evaluate the artifact you will need to build the METL language.

### Downloading the artifact

Check it out from the git repository
```
> git clone https://github.com/thwfhk/met-oopsla25-artifact.git
```

You should now have the following files on your machine
```
> cd met-oopsla25-artifact && ls
app  CHANGELOG.md  METL.cabal  package.yaml  README.md  src  stack.yaml  stack.yaml.lock  test
```

### Building METL

You need to have Stack and Haskell installed first. If you're a
Haskell hacker, go ahead with `stack build` and adapt `stack.yaml`
as you need. If not, follow the below instructions.
1. Install GHCup following [this link](https://www.haskell.org/ghcup/).
2. Run `ghcup tui` to enter a text-based user interface.
3. Install Stack 3.3.1 via the text-based user interface.
4. Install GHC 9.10.1 via the text-based user interface.
5. Enter the root directory of the artifact and run `stack build`.

To check you have successfully built METL, run `stack exec METL` and
you should see a single line:
```
Please provide a program file.
```

## Evaluation Instructions

The evaluation is rather simple. We have collected all example
programs from the paper in `text/paper-examples.me`. To evaluate them,
run
```
stack exec METL test/paper-examples.me
```
We have provided the expected output in `test/paper-examples.me`

We additionally provide three program files, `test/basic.me`,
`test/toss.me`, and `test/nqueens.me`. The second one is taken from
the repository of the [Frank language](https://github.com/frank-lang/frank). The third one implements a
solver for n-queens using effect handlers.

You are welcome to write your own METL programs. The Section 2 of the
paper and the last section of this document provide some guidance to
programming in METL.


## Reusability Guide

This artifact is an implementation of the METL language. Our
implementation follows Adam Gunry's [type inference in
context](https://github.com/adamgundry/type-inference) approach.
The code structure is as follows.
* `src/Syntax.hs` defines the syntax of METL.
* `src/Typer.hs` implements the type checker.
* `src/Interpreter.hs` implements the interpreter.
* `src/Lexer.hs` and `src/Parser.hs` implement the lexer and parser.
* `src/Printer.hs` implements the pretty printer.
* `src/BwdFwd.hs` and `src/Helper.hs` define some helper functions.

Our code is documented and extensible to more features, thanks to
functional programming. This artifact serves as a good start point for
further exploring type inference for modal effect types.


## A Quick Guide to METL

The syntax of METL is almost the same as that in the paper. A few
exceptions (mostly improvements) are as follows.

- Syntax of product types is `A * B` instead of `(A, B)`.
- Syntax of type application is `@A` instead of `{A}`.
- We do not need to write term-level type abstraction for polymorphic
  functions when the type signature is given.
- We adopt the convention that every global definition has an empty
  absolute modality by default. We do not need to write them.
- We implemented real parameterised effect interfaces instead of just
  macros as in the paper. Details can be found in the next section.
- Handler clauses need to be wrapped into braces.
- Handler clauses do not need to annotate the operation type for each
  operation clause. Instead, we can just write the effect interface
  after the `handle` keyword in angle brackets, like
  ```
  asList m = handle<Gen Int> m () with ...
  ```
  for a handler of `Gen Int`. This is omittable for non-parameterised
  effect.
- We do not support effect variables as our formalisation of
  bidirectional typing in Appendix D does not support effect
  variables. As a result, the declaration of effect `Coop e` in
  Section 2.10 is not supported in our implementation. However, this
  effect is not used by any program in the paper.


### More Features

Compared to the paper, our implementation supports some more features.

#### Algebraic Data Types

We support user-defined algebraic data types. Type names are in
uppercase and constructor names are in lowercase. For instance,
```
data Maybe a = nothing | just a
```
defines the famous `Maybe` datatype.

There are some built-in datatypes with special built-in syntax
support.

```
data Unit     = unit                  -- ()
data Bool     = true | false          -- true, false, if-then-else
data Pair a b = pair a b              -- (m, n), fst, snd
data List a   = nil | cons a (List a) -- [m1, m2, ...]
```

#### Parameterised Effects

We support user-defined effect interfaces and parameterised effects.
Effect names are in uppercase and operation names are in lowercase.
For instance,
```
effect State [s] = get : 1 => s | put : s => 1
```
defines an effect interface for a parameterised effect `State` with
two operations `get` and `put`. We use `=>` instead of `->>` for the
operation arrow, and use `|` to separate operations for consistency
with ADT definitions.

#### Printing

We support a built-in print function. For instance, `print "hello
world"` prints hello world.

#### Frank-style notations

We support Frank-style thunking and forcing annotations.
- Instead of writing `fun () -> M` for thunking, we can just write `{M}`.
- Instead of writing `1 -> A` in types, we can just write `{A}`.
- Instead of writing `M ()` for forcing, we can just write `M!`. 
- Instead of writing `f () = ...` for definitions, we can just write `f! = ...`.