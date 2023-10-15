open RuntimeInfo

type ctor_name = string
type tp_name = string
type tm_name = string
type tvar_name = string
type tmvar_name = string (* of the form a#n for an integer n *)
type var_name = string

type index = int

type ctor_tag = int
type arity = int

type rec_flag = Rec | NonRec

(* Looks up a variable in a context or an environment. (They have the same structure.) *)
let lookup_var : 'a list -> index -> 'a option = List.nth_opt

type boxity = [ `unboxed | `boxed ]

module Prim = struct
  type t = Eq | Lt | Not | And | Or | CharAt | SubString | Plus | Times | Neg | Div

  let arity = function
    | Not | Neg -> 1
    | Eq | Lt | And | Or | CharAt | Plus | Times | Div -> 2
    | SubString -> 3

  let to_string = function
    | Eq -> "eq"
    | Not -> "not"
    | Neg -> "neg"
    | Lt -> "lt"
    | And -> "and"
    | Or -> "or"
    | CharAt -> "char_at"
    | SubString -> "substring"
    | Plus -> "plus"
    | Times -> "times"
    | Div -> "div"
end

(** Built-in types. *)
type builtin_tp = Int | Char | String | Bool

(* Literals L ::= 1 | 2 | ... | 'c' | ... | true | false | "string" | ... *)
type literal =
  | IntLit of value
  | CharLit of char
  | StringLit of string
  | BoolLit of bool
