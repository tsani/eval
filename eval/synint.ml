open BasicSyntax

module Type = struct
  (** The location of a type in a source file.
      Types can appear literally in a program, e.g. as the type of a
      constructor or as an annotation on a definition.
      Or type can be inferred from the syntax of a term.
      To report the best error messages possible, we track which kind of location a type stores.
  *)
  type loc = [
    | `inferred of Loc.span (** The location refers to the syntax from which the type was inferred. *)
    | `literal of Loc.span (** The type literally appears in the source program. *)
    | `fake (** The location is completely made up. *)
  ]

  type t =
    | Builtin of loc * builtin_tp
    | Arrow of loc * t * t
    | TVar of loc * tvar_name
    | TMVar of loc * tmvar_name (* often, the location of a TMVar is fake *)
    | Named of loc * tp_name * t list
    (* ^ an identifier for a user-defined data type and a list of type parameters *)

  (** Gets the location of a type. This implementation doesn't know anything
  about type variable instantiations, so it will report the location of the
  TMVar if it encounters one. Usually, these locations are fake or refer to a
  term, and so are rarely meaningful to a user. *)
  let loc_of_tp : t -> loc = function
    | Builtin (loc, _) -> loc
    | Arrow (loc, _, _) -> loc
    | TVar (loc, _) -> loc
    | TMVar (loc, _) -> loc
    | Named (loc, _, _) -> loc

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

  (** Constructs an arrow type from a list of parameter types and a single return type. *)
  let arrows = List.fold_right (fun a ret -> Arrow (`fake, a, ret))
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

  (** Erases all type annotations a context, simply leaving names. *)
  let to_scope ctx = List.map (fun (x, _) -> x) ctx
end

module EnvRen = struct
  (* A renaming for an environment. This renaming only appears briefly during closure conversion
     before it is translated into a Closed.EnvRen.t *)
  type t = index OSet.t

  let insert x s = OSet.insert_index x s
end

(* A term is a an unevaluated expression. *)
module Term = struct
  type loc = Loc.span
  let fake_loc = Loc.Span.fake

    (* Patterns p ::= ... *)
  type pattern =
    | ConstPattern of Loc.span * ctor_name * pattern list (* C pS *)
    | LiteralPattern of Loc.span * literal                (* L *)
    | VariablePattern of Loc.span * var_name              (* x *)
    | WildcardPattern of Loc.span                         (* _ *)

    (* Heads h ::= ... *)
  type head =
    | Var of loc * index         (* x *)
    | Const of loc * ctor_name   (* C *)
    | Prim of loc * Prim.t       (* + | * | ... *)
    | Ref of loc * tm_name       (* f *)

  let loc_of_head = function
    | Var (loc, _) -> loc
    | Const (loc, _) -> loc
    | Prim (loc, _) -> loc
    | Ref (loc, _) -> loc

    (* Expressions e ::= ... *)
  type t
    = Lit of loc * literal                             (* L *)
    | Fun of loc * (loc * var_name) * t                (* fun x -> e *)
    | App of loc * head * spine                        (* h S *)
    | Let of loc * rec_flag * (loc * var_name) * t * t (* let [rec] x = e1 in e2 *)
    | Match of loc * t * case list                     (* match e with caseS *)

  and spine = t list (* Spines S ::= . | e S *)

    (* Case case ::= p -> e *)
  and case =
    | Case of Loc.span * pattern * t

  type term = t

  let case_body (Case (_, _, e)) = e
  let case_pattern (Case (_, p, _)) = p

  (* Extends the given scope with all variables defined in a pattern. *)
  let extend_with_pattern_vars : Scope.t -> pattern -> Scope.t =
    let rec go acc p = match p with
      | WildcardPattern _ -> acc
      | VariablePattern (_, x) -> Scope.extend acc x
      | LiteralPattern (_, _) -> acc
      | ConstPattern (_, _, ps) -> List.fold_left go acc ps
    in
    go

  let count_pattern_vars : pattern -> int =
      let rec go acc = function
          | ConstPattern (_, _, ps) -> List.fold_left go acc ps
          | VariablePattern (_, _) -> acc + 1
          | WildcardPattern _ | LiteralPattern (_, _) -> acc
      in
      go 0

  (* Expands a sequence of variable names into functions around a given body. *)
  let expand_funs xS e = List.fold_right (fun x e -> Fun (Loc.Span.fake, (Loc.Span.fake, x), e)) xS e

  let loc_of_tm = function
    | Lit (loc, _) -> loc
    | Fun (loc, _, _) -> loc
    | App (loc, _, _) -> loc
    | Let (loc, _, _, _, _) -> loc
    | Match (loc, _, _) -> loc

  let loc_of_pattern = function
    | ConstPattern (loc, _, _) -> loc
    | LiteralPattern (loc, _) -> loc
    | VariablePattern (loc, _) -> loc
    | WildcardPattern loc -> loc

  (** Decomposes nested functions into a sequence of names and the innermost body. *)
  let rec collapse_funs : t -> var_name list * t = function
    | Fun (_, (_, x), e) ->
      let (xs, e) = collapse_funs e in
      (x :: xs, e)
    | e -> ([], e)
end

(* A value is the result of evaluating a term. *)
module Value = struct
  type t =
    | Lit of literal
    | Const of ctor_name * spine
    | Prim of Prim.t (* this is definitely wrong; prims shouldn't be considered values *)
    | Clo of env * var_name list * Term.t

  and spine = t list

  (* To support general recursion, the entries of an environment are mutable
    optional terms.
    The idea is that when evaluating `let rec x = e1 in e2`, we initially assign
    None to x in the environment in which we evaluate e1. If a reference to x is
    not guarded by a delaying construct such as `fun`, then it will be
    encountered during evaluation and looked up as None. We have detected an
    infinite loop! Otherwise, we will succeed in evaluating e1, and we can
    reassign the reference to the value. *)
  and env_entry = var_name * t option ref
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

  let alloc_entry ?(contents = None) name : entry =
    (name, ref contents)

  let update_entry (_, r) t = match !r with
    | None -> r := (Some t)
    | Some _ -> raise (Util.Invariant "clo ref must be empty when updated")

  let lookup : t -> index -> entry option = lookup_var
  let lookup' env i = match lookup env i with
      | Some v -> v
      | None -> Util.invariant "lookup' must succeed"

  (* Forgets the values associated to the variables, keeping only their names *)
  let to_scope : t -> Scope.t = List.map (fun (x, _) -> x)
end

(* Top-level declarations. *)
module Decl = struct
  type 'a tm = {
    name : tm_name;
    typ : Type.sc option;
    rec_flag : rec_flag;
    (* ^ whether the definition is recursive *)
    body : 'a option;
    (* ^ for recursive functions, the body is None until we finish evaluating the definition.
      Normally, it will be impossible for the evaluator to encounter a None body
      because we don't evaluate under functions. If we do encounter one, it's an infinite recursion.
    *)
    loc : Loc.span;
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

    loc : Loc.span;
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

    (** List of type parameter names bound in this type.
     * All names are unique in this list. *)
    tvar_binders : tvar_name list;

    (** The constructors of this datatype.
     * By parser invariant, the owner_name of every ctor is the name as `name`
     * above. *)
    constructors : ctor list;
    loc : Loc.span;
  }

  type 'a t =
    | TpDecl of tp
    | TmDecl of 'a tm
  type 'a decl = 'a t

  let loc_of_decl = function
    | TpDecl { loc } -> loc
    | TmDecl { loc } -> loc

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
    | None -> Util.invariant ("tm " ^ c ^ " is declared")
    | Some x -> x
  let lookup_tp' c sg = match lookup_tp c sg with
    | None -> Util.invariant ("tp " ^ c ^ " is declared")
    | Some x -> x
  let lookup_ctor' c sg = match lookup_ctor c sg with
    | None -> Util.invariant ("ctor " ^ c ^ " is declared")
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

  let v i = Var (Loc.Span.fake, i)
  let n n = Lit (Loc.Span.fake, IntLit n)
  let r name = Ref (Loc.Span.fake, name)
  let lam x e = Fun (Loc.Span.fake, (Loc.Span.fake, x), e)
  let rec lams xs e = match xs with
    | [] -> e
    | x :: xs -> Fun (Loc.Span.fake, (Loc.Span.fake, x), lams xs e)
  let case e (cases : (pattern * term) list) =
    Match (Loc.Span.fake, e, List.map (fun (p, e) -> Case (Loc.Span.fake, p, e)) cases)
  let def x e1 e2 = Let (Loc.Span.fake, NonRec, (Loc.Span.fake, x), e1, e2)
  let recdef x e1 e2 = Let (Loc.Span.fake, Rec, (Loc.Span.fake, x), e1, e2)
  (* let fix f = Rec f *)
  let const name spine = App (Loc.Span.fake, Const (Loc.Span.fake, name), spine)
  let (-->) pat e = (pat, e)
  (* Constructs an application of a function of multiple arguments *)
  let apps head spine = App (Loc.Span.fake, head, spine)

  (* Type variable *)
  let tv x = TVar (`fake, x)

  (* 'type reference' *)
  let tr c spine = Named (`fake, c, spine)
  let tr0 c = Named (`fake, c, [])
  let tr1 c tp = Named (`fake, c, [tp])

  let arrow t1 t2 = Arrow (`fake, t1, t2)

  (* Constructs a nested arrow type for a function of multiple parameters.
  *
  * arrows [] Tr = Tr
  * arrows (T :: Ts) Tr = T -> arrows Ts Tr
  *)
  let arrows arg_tps result_tp = List.fold_right arrow arg_tps result_tp

  let ignored = WildcardPattern Loc.Span.fake
  let pconst name pats = ConstPattern (Loc.Span.fake, name, pats)
  let pv x = VariablePattern (Loc.Span.fake, x)

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
