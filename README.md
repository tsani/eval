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
- External syntax. So I can finally stop programming ASTs directly in de Bruin indices! 
- Scope-checking.
- Parsing: for now I use a "shallow embedding" into OCaml to construct sample
  programs. See `main.ml`.
