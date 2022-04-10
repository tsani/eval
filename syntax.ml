type ctor_name = string
type tp_name = string
type var_name = string
type tvar_name = string

type tp
  = Int
  | Arrow of tp * tp
  | TVar of tvar_name
  | Forall of tvar_name * tp
  | Named of tp_name (* an identifier for a user-defined data type *)

type index = int

type tm
  = Num of int
  | Var of index
  | Ref of var_name
  | Fun of tm
  | App of tm * tm
  | Match of tm * case list
  | Const of ctor_name * tm list
  (* | Rec of tm *)
  | Clo of env * tm (* the environment is missing one variable to be able to evaluate this tm *)

and env = tm list

and case =
  | Case of pattern * tm

and pattern =
  | ConstPattern of ctor_name * pattern list
  | NumPattern of int
  | VariablePattern
  | WildcardPattern

type tm_decl = {
  name : var_name;
  typ : tp;
  recursive : bool;
  (* ^ whether the definition is recursive *)
  body : tm option;
  (* ^ for recursive functions, the body is None until we finish evaluating the definition.
    Normally, it will be impossible for the evaluator to encounter a None body
    because we don't evaluate under functions. If we do encounter one, it's an infinite recursion.
  *)
}

(* and here is a single case of a user-defined data-type
* this is the "product" part of sum-of-products, so we have a list of types to
* keep track of
*)
type ctor_decl = {
  name : ctor_name;

  (* The name of the type this constructor belongs to *)
  owner_name : tp_name;

  (* The types of the fields of this constructor, in order *)
  fields : tp list;

  (* the overall type of the constructor is T1 * ... * Tn -> <tp_name> *)
}

(* the type of a user-defined data type is a sum of products
* so here we have all the different cases
*)
type tp_decl = {

  name : tp_name;
  (* The constructors of this datatype.
  * By parser invariant, the owner_name of every ctor is the name as `name`
  * above.
  *)
  constructors : ctor_decl list;
}

type decl =
  | TpDecl of tp_decl
  | TmDecl of tm_decl

(* Convenience functions for constructing ASTs *)
module Sugar = struct
  let v i = Var i
  let n n = Num n
  let r name = Ref name
  let lam e = Fun e
  let case e (cases : (pattern * tm) list) = Match (e, List.map (fun (p, e) -> Case (p, e)) cases)
  (* let fix f = Rec f *)
  let const name spine = Const (name, spine)
  let (@@@) e1 e2 = App (e1, e2)
  let (-->) pat e = (pat, e)

  let ignored = WildcardPattern
  let pconst name pats = ConstPattern (name, pats)
  let pv = VariablePattern
end
