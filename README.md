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
- Unification. See `unify.ml`.
- Typechecking. See `typecheck.ml`.
- Plenty of sample higher-order polymorphic functions. See `main.ml`.

To do:
- Proper build system: currently I build with a bash script. A real build system
  will be important for parsing as I want to use lexing/parsing libraries
  instead of doing it myself.
- External syntax. So I can finally stop programming ASTs directly in de Bruin
  indices! And also get locations in error messages instead of mostly guessing.
- Scopechecking to translate external syntax to internal syntax.
  Scopechecking should ensure that all references are valid
  (constructors, other functions, types, variables, etc.)
  This will allow me to remove some of these kinds of checks from typechecking.
- Parsing: for now I use a "shallow embedding" into OCaml to construct sample
  programs. See `main.ml`.
