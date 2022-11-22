type ctor_name = string
type tp_name = string
type tm_name = string
type tvar_name = string
type tmvar_name = string (* of the form a#n for an integer n *)
type var_name = string

type index = int

type rec_flag = Rec | NonRec

(* Looks up a variable in a context or an environment. (They have the same structure.) *)
let lookup_var : 'a list -> int -> 'a option = List.nth_opt

module Scope = struct
  type entry = var_name
  type t = entry list

  let empty : t = []
  let single x : t = [x]

  let extend sco x = x :: sco
  (* Extends a scope with a binding only if it's recursive. *)
  let extend_rec rec_flag = match rec_flag with
    | Rec -> extend
    | NonRec -> fun sco x -> sco
  let lookup : t -> index -> entry option = lookup_var

  let extend_many (s : t) (xs : entry list) : t = List.fold_left extend s xs

  let index_of x : t -> index option =
    let rec go i = function
      | [] -> None
      | x' :: xs when x' = x -> Some i
      | _ :: xs -> go (i+1) xs
    in
    go 0
end

module External = struct
  module Type = struct
    type t =
      | Int
      | Arrow of t * t
      | TVar of tvar_name
      | Named of tp_name * t list
  end

  module Term = struct
    type pattern =
      | ConstPattern of ctor_name * pattern list
      | NumPattern of int
      | VariablePattern of var_name
      | WildcardPattern

    type t =
      | Num of int
      | Var of var_name 
      (* in external syntax, we can't tell apart a local var ref from a ref to
      another definition, so there is no case for "ref" *)
      | Fun of var_name * t
      | App of t * t
      | Let of rec_flag * var_name * t * t
      | Match of t * case list
      (* we distinguish function applications from constructor applications since constructors
      use uppercase names. *)
      | Const of ctor_name * spine

     and spine = t list
     and case = Case of pattern * t
  end

  module Decl = struct
    type tm = {
      name : tm_name;
      typ : Type.t;
      recursive : bool;
      body : Term.t;
    }

    type ctor = {
      name : ctor_name;
      fields : Type.t list;
    }

    type tp = {
      name : tp_name;
      tvar_binders : tvar_name list;
      constructors : ctor list;
    }

    type t =
      | TpDecl of tp
      | TmDecl of tm

    type program = t list
  end
end

module Internal = struct
  module Type = struct
    type t
      = Int
      | Arrow of t * t
      | TVar of tvar_name
      | TMVar of tmvar_name
      | Named of tp_name * t list (* an identifier for a user-defined data type and a list of type parameters *)

    (* A 'type scheme' is a bunch of quantifiers together with a type.
    * This is in contrast to allowing arbitrary foralls to appear anywhere in a type.
    * Rather than expressing this recursively as is done in the theory,
    * I'll do it as a list of quantified variables together with a type.
    * Invariant: all names in this list are unique.
    * Otherwise we will necessarily end up with some TMVars that never get unified
    * with anything as they're unused!
    *)
    type sc = tvar_name list * t

    type tp = t

    (* Constructs a 'dummy' type scheme with no variables from a monotype. *)
    let mono (tp : t) : sc = ([], tp)

    (* Constructs a polytype from a list of binders and a monotype. *)
    let poly (tvar_binders : tvar_name list) (tp : t) : sc = (tvar_binders, tp)
  end

  (* A context associates to variables a type, so we can typecheck them. *)
  module Ctx = struct
    type entry = var_name * Type.sc
    type t = entry list
    let extend ctx x = x :: ctx
    let empty = []
    let lookup : t -> index -> entry option = lookup_var

    (* Associates each entry in the context with the index of the variable that refers to that entry. *)
    let enumerate (ctx : t) : (index * entry) list =
      List.fold_right (fun tpsc ctx -> fun n -> (n, tpsc) :: ctx (n + 1)) ctx (fun _ -> []) 0

    type ctx = t

    let to_scope ctx = List.map (fun (x, _) -> x) ctx
  end

  (* A term is a an unevaluated expression. *)
  module Term = struct
    type t
      = Num of int
      | Var of index
      | Ref of tm_name
      | Fun of var_name * t
      | App of t * t
      | Let of rec_flag * var_name * t * t
      | Match of t * case list
      | Const of ctor_name * spine

    and spine = t list

    and case =
      | Case of pattern * t

    and pattern =
      | ConstPattern of ctor_name * pattern list
      | NumPattern of int
      | VariablePattern of var_name
      | WildcardPattern

    type term = t

    let case_body (Case (_, e)) = e
    let case_pattern (Case (p, _)) = p

    (* Extends the given scope with all variables defined in a pattern. *)
    let extend_with_pattern_vars : Scope.t -> pattern -> Scope.t =
      let rec go acc p = match p with
        | WildcardPattern -> acc
        | VariablePattern x -> Scope.extend acc x
        | NumPattern _ -> acc
        | ConstPattern (_, ps) -> List.fold_left go acc ps
      in
      go
  end

  (* A value is the result of evaluating a term. *)
  module Value = struct
    type t =
      | Num of int
      | Const of ctor_name * spine
      | Clo of env * var_name * Term.t

    and spine = t list

    (* To support general recursion, the entries of an environment are mutable
      optional terms.
      The idea is that when evaluating `let rec x = e1 in e2`, we initially assign
      None to x in the environment in which we evaluate e1. If a reference to x is
      not guarded by a delaying construct such as `fun`, then it will be
      encountered during evaluation and looked up as None. We have detected an
      infinite loop! Otherwise, we will succeed in evaluating e1, and we can
      reassign the reference to the value.

      We also store the name of the variable and whether the variable is
      recursively defined. 
    *)
    and env_entry = var_name * rec_flag * t option ref
    and env = env_entry list

    type value = t
  end

  (* A runtime environment is essentially a list of values. *)
  module Env = struct
    type entry = Value.env_entry
    type t = Value.env

    let extend env v = v :: env
    let empty : t = []
    let concat env1 env2 = env1 @ env2
    let concats l = List.fold_right concat l []

    let alloc_entry ?(rec_flag = NonRec) ?(contents = None) name : entry =
      (name, NonRec, ref contents)

    let update_entry (_, _, r) t = match !r with
      | None -> r := (Some t)
      | Some _ -> raise (Util.Invariant "clo ref must be empty when updated")

    let lookup : t -> index -> entry option = lookup_var

    (* Forgets the values associated to the variables, keeping only their names *)
    let to_scope : t -> Scope.t = List.map (fun (x, _, _) -> x)
  end

  (* Top-level declarations. *)
  module Decl = struct
    type 'a tm = {
      name : tm_name;
      typ : Type.sc;
      recursive : bool;
      (* ^ whether the definition is recursive *)
      body : 'a option;
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

    type ctor = {
      name : ctor_name;

      (* The name of the type this constructor belongs to *)
      owner_name : tp_name;

      (* The types of the fields of this constructor, in order *)
      fields : Type.t list;
    }

    (* the type of a user-defined data type is a sum of products
    * so here we have all the different cases
    * e.g.
    *   type ('e, 'a) result = ...
    * is expressed as
    *   { name = "result"; tvars = ["e"; "a"]; constructors = ... }
    *)
    type tp = {
      name : tp_name;

      (* List of type parameter names bound in this type.
      * All names are unique in this list.
      *)
      tvar_binders : tvar_name list;

      (* The constructors of this datatype.
      * By parser invariant, the owner_name of every ctor is the name as `name`
      * above.
      *)
      constructors : ctor list;
    }

    type 'a t =
      | TpDecl of tp
      | TmDecl of 'a tm
    type 'a decl = 'a t

    (* A program is what is submitted to the evaluator.
      The evaluator then produces a signature in which the term declarations
      contain _values_ rather than unevaluated expressions.
    *)
    type program = Term.t t list
  end

  module Signature = struct
    module StringMap = Map.Make(String)

    type 'a tm_map = 'a Decl.tm StringMap.t
    type tp_map = Decl.tp StringMap.t
    type ctor_map = Decl.ctor StringMap.t

    type 'a t = {
      tps : tp_map;
      ctors : ctor_map;
      tms : 'a tm_map;
    }

    let empty : 'a t = { tps = StringMap.empty; ctors = StringMap.empty; tms = StringMap.empty }

    let extend_tms c d sg : 'a t = { sg with tms = StringMap.add c d sg.tms }
    let extend_tps c d sg : 'a t = { sg with tps = StringMap.add c d sg.tps }
    let extend_ctors c d sg : 'a t = { sg with ctors = StringMap.add c d sg.ctors }

    let lookup_tm c sg = StringMap.find_opt c sg.tms
    let lookup_tp c sg = StringMap.find_opt c sg.tps
    let lookup_ctor c sg = StringMap.find_opt c sg.ctors

    let lookup_tm' c sg = match lookup_tm c sg with
      | None -> raise @@ Util.Invariant ("tm " ^ c ^ " is declared")
      | Some x -> x
    let lookup_tp' c sg = match lookup_tp c sg with
      | None -> raise @@ Util.Invariant ("tp " ^ c ^ " is declared")
      | Some x -> x
    let lookup_ctor' c sg = match lookup_ctor c sg with
      | None -> raise @@ Util.Invariant ("ctor " ^ c ^ " is declared")
      | Some x -> x

    let declare_tp (sg : 'a t) (d : Decl.tp) : 'a t =
      List.fold_right
        (fun (d : Decl.ctor) -> extend_ctors d.name d)
        d.constructors
        @@ extend_tps d.name d sg

    let declare_tm (sg : 'a t) (d : 'a Decl.tm) : 'a t = extend_tms d.name d sg

    let declare (sg : 'a t) : 'a Decl.t -> 'a t = function
      | TmDecl d -> declare_tm sg d
      | TpDecl d -> declare_tp sg d
  end

  (* Convenience functions for constructing ASTs *)
  module Sugar = struct
    open Term
    open Type

    let v i = Var i
    let n n = Num n
    let r name = Ref name
    let lam x e = Fun (x, e)
    let rec lams xs e = match xs with
      | [] -> e
      | x :: xs -> Fun (x, lams xs e)
    let case e (cases : (pattern * term) list) = Match (e, List.map (fun (p, e) -> Case (p, e)) cases)
    let def x e1 e2 = Let (NonRec, x, e1, e2)
    let recdef x e1 e2 = Let (Rec, x, e1, e2)
    (* let fix f = Rec f *)
    let const name spine = Const (name, spine)
    let (@@@) e1 e2 = App (e1, e2)
    let (-->) pat e = (pat, e)
    (* Constructs an application of a function of multiple arguments *)
    let apps head spine = List.fold_left (fun head arg -> head @@@ arg) head spine

    (* 'type reference' *)
    let tr c spine = Named (c, spine)
    let tr0 c = Named (c, [])
    let tr1 c tp = Named (c, [tp])

    let arrow t1 t2 = Arrow (t1, t2)

    (* Constructs a nested arrow type for a function of multiple parameters.
    *
    * arrows [] Tr = Tr
    * arrows (T :: Ts) Tr = T -> arrows Ts Tr
    *)
    let arrows arg_tps result_tp = List.fold_right arrow arg_tps result_tp

    let ignored = WildcardPattern
    let pconst name pats = ConstPattern (name, pats)
    let pv x = VariablePattern x

    (* type-specific sugar *)

    let ty_list tp = tr1 "List" tp
    let ty_nat = tr0 "Nat"
    let ty_tree tp = tr1 "Tree" tp

    let zero = const "Z" []
    let succ n = const "S" [n]

    let pzero = pconst "Z" []
    let psucc p = pconst "S" [p]

    let nil = const "Nil" []
    let cons e l = const "Cons" [e; l]

    let pnil = pconst "Nil" []
    let pcons p1 p2 = pconst "Cons" [p1; p2]

    (* Transform an OCaml list of terms into a Eval list *)
    let list es = List.fold_right cons es nil

    let empty_tree = const "Empty" []
    let node e l = const "Node" [e; list l]

    (* Transform a positive OCaml integer into an Eval Nat. *)
    let rec nat = function
      | 0 -> const "Z" []
      | n -> const "S" [nat @@ n - 1]

    (* Decomposes a term consisting of a chain of Cons and Nil into a list of terms. *)
    let rec decompose_list (v : Value.t) : Value.t list option = let open Value in match v with
      | Const (c, _) when c = "Nil" -> Some []
      | Const (c, spine) when c = "Cons" -> begin match spine with
        | [head; tail] -> begin match decompose_list tail with
          | Some tail -> Some (head :: tail)
          | None -> None
        end
        | _ -> None
      end
      | _ -> None

    (* Decomposes a term consisting of a chain of S and Z into a nonnegative integer. *)
    let rec decompose_nat (v : Value.t) : int option = let open Value in match v with
      | Const (c, _) when c = "Z" -> Some 0
      | Const (c, spine) when c = "S" -> begin match spine with
        | [e'] -> begin match decompose_nat e' with
          | Some n -> Some (n + 1)
          | _ -> None
        end
        | _ -> None
      end
      | _ -> None
  end
end
