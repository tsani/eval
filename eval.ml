open Syntax
open Internal
open Term

module P = Pretty.Internal

module State = struct
  type t = {
    (* Used to emit debug messages *)
    debug_ppf : Format.formatter;

    sg : Value.t Signature.t;
  }

  let modify_signature f s = { s with sg = f s.sg }

  let empty debug_ppf = {
    debug_ppf;
    sg = Signature.empty;
  }
end

module RuntimeError = struct
  type t =
    | UnboundVariable of Env.t * index
    | ApplyNonClo of Value.t
    | InfiniteRecursion of tm_name
    | InfiniteLetRec of var_name
    | PatternMatchingFailed of Value.t * Term.pattern list
    | BadEq

  let print ppf : t -> unit = let open Format in function
    | UnboundVariable (env, i) ->
      fprintf ppf "@[<v 2>unbound variable %d in environment@ %a@]"
        i
        P.print_env env
    | ApplyNonClo (v) ->
      fprintf ppf "@[<v>cannot apply non-closure@ %a@]"
        (P.print_value 0) v

    | InfiniteRecursion x ->
      fprintf ppf "infinite recursion detected in top-level definition for %s"
        x

    | InfiniteLetRec x ->
      fprintf ppf "infinite recursion detected in local definition, for %s"
        x

    | PatternMatchingFailed (v, pats) ->
      fprintf ppf "@[<hv>@[<hv 2>failed to match term@ %a]@ @[<v 2>against any of the patterns:@ %a@]@]"
        (P.print_value 0) v
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf -> fprintf ppf "- @[%a@]" (P.print_pattern 0))) pats

    | BadEq ->
      fprintf ppf "equality is only decidable for literals and constructors"

  exception E of t Loc.Span.d

  let unbound_variable loc env index = raise (E (loc, UnboundVariable (env, index)))
  let apply_non_clo loc e = raise (E (loc, ApplyNonClo (e)))
  let infinite_recursion loc x = raise (E (loc, InfiniteRecursion x))
  let pattern_matching_failed loc e pats = raise (E (loc, PatternMatchingFailed (e, pats)))
  let infinite_let_rec loc x = raise (E (loc, InfiniteLetRec x))
  let bad_eq loc = raise (E (loc, BadEq))
end

let debug_print (s : State.t) = Format.fprintf s.debug_ppf

let rec value_eq : Value.t * Value.t -> bool =
  let open Value in
  function
  | Const (c1, vS1), Const (c2, vS2) -> c1 = c2 && List.for_all value_eq (List.combine vS1 vS2)
  | Lit l1, Lit l2 -> l1 = l2
  | _ -> RuntimeError.bad_eq Loc.Span.fake

(* Matches a term against a pattern, extending the given environment with new bindings.
 * Produces None if matching fails.
 *)
let rec match_pattern (env : Env.t) : Value.t * pattern -> Env.t option = function
  | Value.Lit l1, LiteralPattern (_, l2) -> if l1 = l2 then Some env else None
  | v, VariablePattern (_, x) -> Some Env.(extend env @@ alloc_entry ~contents: (Some v) x)
  | _, WildcardPattern _ -> Some env
  | Value.Const (ctor_name, spine), ConstPattern (_, pat_ctor_name, pat_spine) -> begin match () with
    | _ when not (ctor_name = pat_ctor_name) -> None
    | _ when not (List.length spine = List.length pat_spine) ->
      raise @@ Util.Invariant "scopechecking invariant: pattern spine lengths match"
    | _ ->
      List.combine spine pat_spine |> List.fold_left begin fun env (p, e) ->
        match env with
        | Some env -> match_pattern env (p, e)
        | None -> None
      end (Some env)
    end
  | _ -> None

let eval_head (s : State.t) (env : Env.t) : Term.head -> Value.t = function
  | Var (loc, i) -> begin match Env.lookup env i with
      | None -> RuntimeError.unbound_variable loc env i
      | Some (x, r) -> match !r with
        | None -> RuntimeError.infinite_let_rec loc x
        | Some e -> e
    end
  | Ref (loc, f) -> begin match Signature.lookup_tm' f s.sg with
      | { body = Some body; _ } -> body
      | _ -> RuntimeError.infinite_recursion loc f
    end
  | Const (_, c) -> Value.Const (c, [])
  | Prim (_, prim) -> Value.Prim prim

let eval_prim s env (prim, vS) : Value.t =
  let open Prim in
  let open Value in
  match prim, vS with
  | Eq, [v1; v2] -> Lit (BoolLit (value_eq (v1, v2)))
  | Lt, [Lit (IntLit i1); Lit (IntLit i2)] -> Lit (BoolLit (i1 < i2))
  | Not, [Lit (BoolLit b)] -> Lit (BoolLit (not b))
  | And, [Lit (BoolLit b1); Lit (BoolLit b2)] -> Lit (BoolLit (b1 && b2))
  | Or, [Lit (BoolLit b1); Lit (BoolLit b2)] -> Lit (BoolLit (b1 || b2))
  | CharAt, [Lit (StringLit s); Lit (IntLit i)] -> Lit (CharLit (String.get s i))
  | SubString, [Lit (StringLit s); Lit (IntLit i); Lit (IntLit n)] -> Lit (StringLit (String.sub s i n))
  | Plus, [Lit (IntLit n1); Lit (IntLit n2)] -> Lit (IntLit (n1 + n2))
  | Times, [Lit (IntLit n1); Lit (IntLit n2)] -> Lit (IntLit (n1 * n2))
  | Neg, [Lit (IntLit n)] -> Lit (IntLit (-n))
  | Div, [Lit (IntLit n1); Lit (IntLit (n2))] -> Lit (IntLit (n1 / n2))

let rec collapse_funs : Term.t -> var_name list * Term.t = function
  | Fun (_, (_, x), e) ->
    let (xs, e) = collapse_funs e in
    (x :: xs, e)
  | e -> ([], e)

let rec eval (s : State.t) (env : Env.t) : Term.t -> Value.t = function
  | Lit (_, lit) -> Value.Lit lit
  | Fun _ as e_f ->
    let (xs, e) = collapse_funs e_f in
    let v = Value.Clo (env, xs, e) in
    debug_print s "@[<hv 2>Construct closure@ %a@]@," (P.print_value 0) v;
    v
  | App (_, tH, tS) -> eval_app s env (tH, tS)
  | Let (_, NonRec, (_, x), e1, e2) ->
    let v = eval s env e1 in
    eval s Env.(extend env @@ alloc_entry ~contents: (Some v) x) e2
  | Let (_, Rec, (_, x), e1, e2) ->
    let entry = Env.alloc_entry x in
    let env' = Env.extend env entry in
    Env.update_entry entry @@ eval s env' e1;
    eval s env' e2
  | Match (loc, e, cases) -> eval_match loc s env (eval s env e) cases

(** Performs an application of a closure to a spine of values.
    Values from the spine are associated one by one with variables from the
    closure, extending the environment.
    If there are variable and value spines run out together, then we simply
    evaluate the body of the closure.
    If we run out of values first, then we construct a new closure for the
    remaining variables.
    If we run out of variables first, then we evaluate the body of the closure
    and continue applying the remaining value spine to the result. *)
and eval_clo_app s env : var_name list * Term.t * Value.spine -> Value.t = function
  | (x :: xS, t, v :: vS) ->
    let entry = Env.alloc_entry ~contents: (Some v) x in
    eval_clo_app s (Env.extend env entry) (xS, t, vS)
  | ([], t, []) -> eval s env t
  | (xS, t, []) -> Clo (env, xS, t)
  | ([], t, vS) -> eval_val_app s env (eval s env t, vS)

(** Performs the application of a value to a spine of values.
    If the spine is empty, then this simply returns the value head.
    Otherwise, the behaviour depends on the value head.
    Constructors simply accumulate the value spine into their own spine. *)
and eval_val_app s env : Value.t * Value.spine -> Value.t = function
  | vH, [] -> vH
  | Value.Clo (env', xS, t), vS -> eval_clo_app s env' (xS, t, vS)
  | Value.Const (c, vS1), vS2 -> Value.Const (c, vS1 @ vS2)
  | Value.Prim prim, vS -> eval_prim s env (prim, vS)
  | vH, _ -> RuntimeError.apply_non_clo Loc.Span.fake vH

and eval_app (s : State.t) (env : Env.t) : Term.head * Term.spine -> Value.t = function
  | (tH, tS) -> eval_val_app s env (eval_head s env tH, List.map (eval s env) tS)

and eval_match loc (s : State.t) (env : Env.t) (scrutinee : Value.t) (cases : case list) : Value.t =
  let rec go = function
    | [] -> RuntimeError.pattern_matching_failed loc scrutinee (List.map case_pattern cases)
    | Case (_, pattern, body) :: cases -> match match_pattern env (scrutinee, pattern) with
      | Some env' ->
        debug_print s "@[<v 2>@[<hv 2>matched case for pattern@ %a@]@,@[<hv 2>new env is@ %a@]@,@[<hv 2>to evaluate body@ %a@]@]@,"
        (P.print_pattern 0) pattern
        P.print_env env'
        (P.print_tm 0 @@ Env.to_scope env') body;
        eval s env' body
      | None -> go cases
  in
  go cases

let eval_decl (s : State.t) (d : Term.t Decl.t) : State.t = let open Decl in match d with
  | TpDecl d -> List.fold_right
    (fun (d : Decl.ctor) -> State.modify_signature (Signature.extend_ctors d.name d))
    d.constructors
    @@ State.modify_signature (Signature.extend_tps d.name d) s
  | TmDecl { body = None; _ } -> Util.invariant "tm decl has a body"
  | TmDecl ({ name; recursive; body = Some body; _ } as d) ->
    let s = s |> State.modify_signature
      (if recursive then Signature.extend_tms name { d with body = None } else fun x -> x)
    in
    debug_print s "Evaluating definition for %s.@," name;
    let v = eval s Env.empty body in
    s |> State.modify_signature (Signature.extend_tms name { d with body = Some v })

let program initial_state program : (RuntimeError.t Loc.Span.d, State.t) Result.t =
  let open RuntimeError in
  debug_print initial_state "@[<v>";
  let result = try Result.ok (List.fold_left eval_decl initial_state program) with
    | E e -> Result.error e
  in
  debug_print initial_state "@]";
  result
