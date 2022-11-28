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
    | ApplyNonClo of Value.t * (Scope.t * Term.t)
    | InfiniteRecursion of tm_name
    | InfiniteLetRec
    | PatternMatchingFailed of Value.t * Term.pattern list

  let print ppf : t -> unit = let open Format in function
    | UnboundVariable (env, i) ->
      fprintf ppf "@[<v 2>Unbound variable %d in environment@ %a@]" i P.print_env env
    | ApplyNonClo (v, (sco, e)) ->
      fprintf ppf "@[<v>@[<v 2>Cannot apply non-closure@ %a@]@,@[<v 2>to argument@ %a@]@]"
        (P.print_value 0) v
        (P.print_tm 0 sco) e
    | InfiniteRecursion x ->
      fprintf ppf "Infinite recursion detected in definition for %s" x
    | InfiniteLetRec ->
      fprintf ppf "Infinite recursion detected in local definition"
    | PatternMatchingFailed (v, pats) ->
      fprintf ppf "@[<hv>@[<hv 2>Failed to match term@ %a]@ @[<v 2>against any of the patterns:@ %a@]@]"
        (P.print_value 0) v
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf -> fprintf ppf "- @[%a@]" (P.print_pattern 0))) pats

  exception E of t

  let unbound_variable env index = raise (E (UnboundVariable (env, index)))
  let apply_non_clo e e' = raise (E (ApplyNonClo (e, e')))
  let infinite_recursion x = raise (E (InfiniteRecursion x))
  let pattern_matching_failed e pats = raise (E (PatternMatchingFailed (e, pats)))
  let infinite_let_rec () = raise (E (InfiniteLetRec))
end

let debug_print (s : State.t) = Format.fprintf s.debug_ppf

(* Matches a term against a pattern, extending the given environment with new bindings.
 * Produces None if matching fails.
 *)
let rec match_pattern (env : Env.t) : Value.t * pattern -> Env.t option = function
  | Value.Num n1, NumPattern (_, n2) -> if n1 = n2 then Some env else None
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

let rec eval (s : State.t) (env : Env.t) : Term.t -> Value.t = function
  | Num (_, n) -> Value.Num n
  | Var (_, i) -> begin match Env.lookup env i with
    | None -> RuntimeError.unbound_variable env i
    | Some (_, _, r) -> match !r with
      | None -> RuntimeError.infinite_let_rec ()
      | Some e -> e
  end
  | Ref (_, v) -> begin match Signature.lookup_tm' v s.sg with
    | { body = Some body; _ } -> body
    | _ -> RuntimeError.infinite_recursion v
  end
  | Fun (_, (_, x), e) ->
    let v = Value.Clo (env, x, e) in
    debug_print s "@[<hv 2>Construct closure@ %a@]@," (P.print_value 0) v;
    v
  | App (_, e1, e2) as e ->
    let sco = Env.to_scope env in
    debug_print s "@[<hv 2>Evaluate application@ `%a'@ left side.@ "
      (P.print_tm 0 sco) e;
    let v1 = eval s env e1 in
    debug_print s "@]@,";
    begin match v1 with
      | Clo (clo_env, x, e) ->
        debug_print s "@[<hv 2>Evaluate application@ `%a'@ right side.@ "
        (P.print_tm 0 sco) e2;
        let v2 = eval s env e2 in
        debug_print s "@]@,@[<hv>Perform application:@ %a@ to@ %a@]@,"
        (P.print_value 0) v1
        (P.print_value 0) v2;
        let env' = Env.(extend clo_env @@ alloc_entry ~contents: (Some v2) x) in
        debug_print s "@[<v 2>Enter closure with now-full env@ %a@]@,"
          P.print_env env';
        eval s env' e
      | e -> RuntimeError.apply_non_clo v1 (sco, e2)
    end
  | Let (_, NonRec, (_, x), e1, e2) ->
    let v = eval s env e1 in
    eval s Env.(extend env @@ alloc_entry ~contents: (Some v) x) e2
  | Let (_, Rec, (_, x), e1, e2) ->
    let entry = Env.alloc_entry ~rec_flag: Rec x in
    let env' = Env.extend env entry in
    Env.update_entry entry @@ eval s env' e1;
    eval s env' e2
  | Match (_, e, cases) -> eval_match s env (eval s env e) cases
  | Const (_, ctor_name, spine) -> Const (ctor_name, List.map (eval s env) spine)

and eval_match (s : State.t) (env : Env.t) (scrutinee : Value.t) (cases : case list) : Value.t =
  let rec go = function
    | [] -> RuntimeError.pattern_matching_failed scrutinee (List.map case_pattern cases)
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
    debug_print s "Evaluating definition for %s@," name;
    let v = eval s Env.empty body in
    begin let open Format in
      fprintf std_formatter "- @[<hv 2>val %s =@ %a@]%a"
        name
        (P.print_value 0) v
        pp_print_newline ()
    end;
    s |> State.modify_signature (Signature.extend_tms name { d with body = Some v })

let program initial_state program : (RuntimeError.t, State.t) Result.t =
  let open RuntimeError in
  debug_print initial_state "@[<v>";
  let result = try Result.ok (List.fold_left eval_decl initial_state program) with
    | E e -> Result.error e
  in
  debug_print initial_state "@]";
  result
