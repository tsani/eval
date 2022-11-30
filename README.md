Eval
=====

This is an implementation for a small, strongly-typed functional language with
parametric polymorphism, user-defined datatypes, pattern matching, and general
recursion. The implementation uses no dependencies beyond the OCaml standard
library.

Done:
- Definition of the syntax. See `syntax.ml`.
- Evaluation of terms, including pattern-matching and recursion, and top-level
  declarations. See `eval.ml`.
- Pretty-printing of terms (but it's not very pretty). See `pretty.ml`.
- Unification. See `unify.ml`.
- Typechecking. See `typecheck.ml`.
- Some example programs. See `examples/ski.ev`.
- External syntax. This is the syntax recognized by the parser.
- Scopechecking to translate external syntax to internal syntax.
  This pass ensures that all references are valid (constructors, other
  functions, types, variables, etc.)
- Parsing. The parser is a handwritten recursive descent parser using
  combinators. The error messages aren't great!

To do:
- Proper build system: currently I build with a bash script.
