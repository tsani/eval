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
- Pretty-printing of terms. See `pretty.ml`.
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
- Compilation?

Structure
-----------

- `Syntax`: definitions of different ASTs
  * external syntax: this is close to what the user writes
  * internal syntax: what we typecheck
  * values
  * various intermediate representations
- `Loc`: source locations
- `Pretty`: pretty-printing internal syntax and values
- `Parser`: hand-written parser combinators that generate external syntax from a
  string.
- `Scopecheck`: converts external syntax to internal syntax, disambiguates names
  (locals vs references), scope-checks all identifiers.
- `TMVar`: unification variables, aka "type metavariables" (TMVars); type substitutions
- `Unify`: unification of types
- `Typecheck`: Hindley-Milner type inference using unification
- `Eval`: evaluator for internal syntax, turns internal syntax into a value.
- `Util`: miscellaneous
- `Result`: either monad and helpers

The main flow of data is: text -> `Parser` -> `Scopecheck` -> `Typecheck` -> `Eval`
