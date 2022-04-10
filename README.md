Eval
=====

This is an implementation for a small, strongly-typed functional language with
parametric polymorphism, user-defined datatypes, pattern matching, and general
recursion.

Done:
- Definition of the syntax. See `syntax.ml`.
- Evaluation of terms, including pattern-matching and recursion, and top-level
  declarations. See `eval.ml`.
- Pretty-printing of terms (but it's not very pretty). See `pretty.ml`.

To do:
- Typechecking: presently there are a few runtime checks instead.
- Parsing: for now I use a "shallow embedding" into OCaml to construct sample
  programs. See `main.ml`.
