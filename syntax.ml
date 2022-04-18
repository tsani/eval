type ctor_name = string
type tp_name = string
type var_name = string
type tvar_name = string
type tmvar_name = string (* of the form a#n for an integer n *)

type tp
  = Int
  | Arrow of tp * tp
  | TVar of tvar_name
  | TMVar of tmvar_name
  | Named of tp_name * tp list (* an identifier for a user-defined data type and a list of type parameters *)

(* A 'type scheme' is a bunch of quantifiers together with a type.
 * This is in contrast to allowing arbitrary foralls to appear anywhere in a type.
 * Rather than expressing this recursively as is done in the theory,
 * I'll do it as a list of quantified variables together with a type.
 * Invariant: all names in this list are unique.
 * Otherwise we will necessarily end up with some TMVars that never get unified
 * with anything as they're unused!
 *)
type tp_sc = tvar_name list * tp

type index = int

module Ctx = struct
  type t = tp_sc list
  let extend ctx tpsc = tpsc :: ctx
  let empty = []
end

type tm
  = Num of int
  | Var of index
  | Ref of var_name
  | Fun of tm
  | App of tm * tm
  | Let of tm * tm
  | Match of tm * case list
  | Const of ctor_name * spine
  (* | Rec of tm *)
  | Clo of env * tm (* the environment is missing one variable to be able to evaluate this tm *)

and env = tm list

and spine = tm list

and case =
  | Case of pattern * tm

and pattern =
  | ConstPattern of ctor_name * pattern list
  | NumPattern of int
  | VariablePattern
  | WildcardPattern

let case_body (Case (_, e)) = e
let case_pattern (Case (p, _)) = p

type tm_decl = {
  name : var_name;
  typ : tp_sc;
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
 * keep track of.
 * e.g.
 *   type ('e, 'a) result = Fail of 'e | Ok of 'a
 * has its constructors expressed as
 *   { name = "Fail"; owner_name = "result"; fields = [TVar "e"] }
 *   { name = "Ok"; owner_name = "result"; fields = [TVar "a"] }
 *
 *)
type ctor_decl = {
  name : ctor_name;

  (* The name of the type this constructor belongs to *)
  owner_name : tp_name;

  (* The types of the fields of this constructor, in order *)
  fields : tp list;

}

(* the type of a user-defined data type is a sum of products
 * so here we have all the different cases
 * e.g.
 *   type ('e, 'a) result = ...
 * is expressed as
 *   { name = "result"; tvars = ["e"; "a"]; constructors = ... }
 *)
type tp_decl = {
  name : tp_name;

  (* List of type parameter names bound in this type.
   * All names are unique in this list.
   *)
  tvar_binders : tvar_name list;

  (* The constructors of this datatype.
  * By parser invariant, the owner_name of every ctor is the name as `name`
  * above.
  *)
  constructors : ctor_decl list;
}

(* Synthesizes the (polymorphic) type of a constructor from its ctor definition
 * and its owning type's definition.
 * Given cd : ctor_decl belonging to td : tp_decl, form the overall type of the
 * constructor:
 * forall a1 ... an. T1 -> ... -> Tn -> <tp_name> a1 ... an
 *)
let syn_ctor_type (td : tp_decl) (cd : ctor_decl) : tp_sc =
  let decompose_tuple_to_arrows = List.fold_right (fun tp tp' -> Arrow (tp, tp')) in
  ( td.tvar_binders
  , decompose_tuple_to_arrows
      cd.fields
      (Named (td.name, List.map (fun a -> TVar a) td.tvar_binders))
  )

type decl =
  | TpDecl of tp_decl
  | TmDecl of tm_decl

type program = decl list

module Signature = struct
  module StringMap = Map.Make(String)

  type tm_map = tm_decl StringMap.t
  type tp_map = tp_decl StringMap.t
  type ctor_map = ctor_decl StringMap.t

  type t = {
    tps : tp_map;
    ctors : ctor_map;
    tms : tm_map;
  }

  let empty : t = { tps = StringMap.empty; ctors = StringMap.empty; tms = StringMap.empty }

  let extend_tms c d sg : t = { sg with tms = StringMap.add c d sg.tms }
  let extend_tps c d sg : t = { sg with tps = StringMap.add c d sg.tps }
  let extend_ctors c d sg : t = { sg with ctors = StringMap.add c d sg.ctors }

  let lookup_tm c sg = StringMap.find_opt c sg.tms
  let lookup_tp c sg = StringMap.find_opt c sg.tps
  let lookup_ctor c sg = StringMap.find_opt c sg.ctors

  let lookup_tm' c sg = match lookup_tm c sg with
    | None -> raise @@ Util.Invariant ("unknown tm " ^ c)
    | Some x -> x
  let lookup_tp' c sg = match lookup_tp c sg with
    | None -> raise @@ Util.Invariant ("unknown tp " ^ c)
    | Some x -> x
  let lookup_ctor' c sg = match lookup_ctor c sg with
    | None -> raise @@ Util.Invariant ("unknown ctor " ^ c)
    | Some x -> x

  let declare_tp (sg : t) (d : tp_decl) : t =
    List.fold_right
      (fun (d : ctor_decl) -> extend_ctors d.name d)
      d.constructors
      @@ extend_tps d.name d sg

  let declare_tm (sg : t) (d : tm_decl) : t = extend_tms d.name d sg

  let declare (sg : t) : decl -> t = function
    | TmDecl d -> declare_tm sg d
    | TpDecl d -> declare_tp sg d
end

module Env = struct
  type t = env

  let extend tm env = tm :: env
  let empty : env = []
  let concat env1 env2 = env1 @ env2
  let concats l = List.fold_right concat l []
end


(* Convenience functions for constructing ASTs *)
module Sugar = struct
  let v i = Var i
  let n n = Num n
  let r name = Ref name
  let lam e = Fun e
  let case e (cases : (pattern * tm) list) = Match (e, List.map (fun (p, e) -> Case (p, e)) cases)
  let def e1 e2 = Let (e1, e2)
  (* let fix f = Rec f *)
  let const name spine = Const (name, spine)
  let (@@@) e1 e2 = App (e1, e2)
  let (-->) pat e = (pat, e)

  let ignored = WildcardPattern
  let pconst name pats = ConstPattern (name, pats)
  let pv = VariablePattern
end

(* Looks up a variable in a context or an environment. (They have the same structure.) *)
let lookup_var : 'a list -> int -> 'a option = List.nth_opt

(* Constructs a 'dummy' type scheme with no variables from a monotype. *)
let mono (tp : tp) : tp_sc = ([], tp)

(* Constructs a polytype from a list of binders and a monotype. *)
let poly (tvar_binders : tvar_name list) (tp : tp) : tp_sc = (tvar_binders, tp)
