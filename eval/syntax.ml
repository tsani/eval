(* All Eval syntax and intermediate representations. *)

open BasicSyntax

(** External syntax is essentially the representation stored in text files. *)
module External = Synext

(** Internal syntax is the result of scopechecking, during which various disambiguations are
    performed.
    Internal syntax is the syntax that we typecheck. *)
module Internal = Synint

(** Syntax of terms after closure conversion.
    The point of this syntax is that the construction of anonymous functions capturing their
    definition environment is eliminated.
    The construction of a closure is made explicit via an MkClo node, which specifies the _name_ of
    a function together with an _environment renaming_.

    The operational semantics of an MkClo is to compose the environment renaming with the current
    environment to construct a minimal environment required to later apply the closure.

    The evaluation judgment for closed syntax is:
        rho_e; rho_p |- t !! v
    meaning that in environments `rho_e` and `rho_p`, we evaluate a term `t` to a value `v`.

    There are two environments because in closed syntax there are two kinds of variables:
        - an EVar is an index into the closure environment `rho_e`
        - a BVar is an index into the parameter environment `rho_p`

    A 'pure function' (in contrast with a proper closure) has an empty closure environment `rho_e`
    and the construction of a pure function can be detected when the environment renaming of an
    `MkClo` is also empty.
 *)
module Low = Synlow
