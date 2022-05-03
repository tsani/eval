open Syntax

module State = struct
  type t = {
    (* Used to emit debug messages *)
    debug_ppf : Format.formatter;

    sg : Signature.t;
  }

  let modify_signature f s = { s with sg = f s.sg }

  let empty debug_ppf = {
    debug_ppf;
    sg = Signature.empty;
  }
end

module RuntimeError = struct
  type t =
    | UnboundVariable of env * index
    | ApplyNonClo of tm * tm
    | InfiniteRecursion of tm_name
    | PatternMatchingFailed of tm * pattern list

  let print ppf : t -> unit = let open Format in function
    | UnboundVariable (env, i) ->
      fprintf ppf "@[<v 2>Unbound variable %d in environment@ %a@]" i Pretty.print_env env
    | ApplyNonClo (e, e') ->
      fprintf ppf "@[<v>@[<v 2>Cannot apply non-closure@ %a@]@,@[<v 2>to argument@ %a@]@]"
        (Pretty.print_tm 0) e
        (Pretty.print_tm 0) e'
    | InfiniteRecursion x ->
      fprintf ppf "Infinite recursion detected in definition for %s" x
    | PatternMatchingFailed (e, pats) ->
      fprintf ppf "@[<hv>@[<hv 2>Failed to match term@ %a]@ @[<v 2>against any of the patterns:@ %a@]@]"
        (Pretty.print_tm 0) e
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf -> fprintf ppf "- @[%a@]" (Pretty.print_pattern 0))) pats

  exception E of t

  let unbound_variable env index = raise (E (UnboundVariable (env, index)))
  let apply_non_clo e e' = raise (E (ApplyNonClo (e, e')))
  let infinite_recursion x = raise (E (InfiniteRecursion x))
  let pattern_matching_failed e pats = raise (E (PatternMatchingFailed (e, pats)))
end

let debug_print (s : State.t) = Format.fprintf s.debug_ppf

(* Matches a term against a pattern, extending the given environment with new bindings.
 * Produces None if matching fails.
 *)
let rec match_pattern (env : env) : tm * pattern -> env option = function
  | Num n1, NumPattern n2 -> if n1 = n2 then Some env else None
  | e, VariablePattern -> Some (Env.extend e env)
  | _, WildcardPattern -> Some env
  | Const (ctor_name, spine), ConstPattern (pat_ctor_name, pat_spine) -> begin match () with
    | _ when not (ctor_name = pat_ctor_name) -> None
    | _ when not (List.length spine = List.length pat_spine) ->
      raise @@ Util.Invariant "typechecking invariant: pattern spine lengths match"
    | _ ->
      List.combine spine pat_spine |> List.fold_left begin fun env (p, e) ->
        match env with
        | Some env -> match_pattern env (p, e)
        | None -> None
      end (Some env)
    end
  | _ -> None

let rec eval (s : State.t) (env : env) : tm -> tm = function
  | Num n -> Num n
  | Var i -> begin match lookup_var env i with
    | Some e -> e
    | None -> RuntimeError.unbound_variable env i
  end
  | Ref v -> begin match Signature.lookup_tm' v s.sg with
    | { body = Some body; _ } -> body
    | _ -> RuntimeError.infinite_recursion v
  end
  | Fun e ->
    debug_print s "@[<hv 2>Construct closure@ %a@]@," (Pretty.print_tm 0) (Clo (env, e));
    Clo (env, e)
  | App (e1, e2) as e ->
    debug_print s "@[<hv 2>Evaluate application@ `%a'@ left side.@ " (Pretty.print_tm 0) e;
    let e1' = eval s env e1 in
    debug_print s "--> %a@," (Pretty.print_tm 0) e1';
    debug_print s "@]@,";
    debug_print s "@[<hv 2>Evaluate application@ `%a'@ right side.@ " (Pretty.print_tm 0) e;
    let e2' = eval s env e2 in
    let e' = App (e1', e2') in
    debug_print s "--> %a@," (Pretty.print_tm 0) e2';
    debug_print s "@]@,@[<hv>Perform application:@ `%a'@]@," (Pretty.print_tm 0) e';
    begin match eval s env e1 with
      | Clo (clo_env, e) ->
        let env' = Env.extend e2' clo_env in
        debug_print s "@[<v>@[<v 2>Enter closure@ %a@]@,@[<v 2>with now-full env@ %a@]@]@,"
          (Pretty.print_tm 0) e
          Pretty.print_env env';
        eval s env' e
      | e -> RuntimeError.apply_non_clo e1' e2'
    end
  | Let (e1, e2) ->
    let x = eval s env e1 in
    eval s (Env.extend x env) e2
  | Match (e, cases) -> eval_match s env (eval s env e) cases
  (* | Rec e ->
    eval s (Env.extend e env) e *)
  | Clo (env, e) -> Clo (env, e)
  | Const (ctor_name, spine) -> Const (ctor_name, List.map (eval s env) spine)

and eval_match (s : State.t) (env : env) (scrutinee : tm) (cases : case list) : tm =
  let rec go = function
    | [] -> RuntimeError.pattern_matching_failed scrutinee (List.map case_pattern cases)
    | Case (pattern, body) :: cases -> match match_pattern env (scrutinee, pattern) with
      | Some env' ->
        debug_print s "@[<v 2>@[<hv 2>matched case for pattern@ %a@]@,@[<hv 2>new env is@ %a@]@,@[<hv 2>to evaluate body@ %a@]@]@,"
        (Pretty.print_pattern 0) pattern
        (Pretty.print_env) env'
        (Pretty.print_tm 0) body;
        eval s env' body
      | None -> go cases
  in
  go cases

let eval_decl (s : State.t) (d : decl) : State.t = match d with
  | TpDecl d -> List.fold_right
    (fun (d : ctor_decl) -> State.modify_signature (Signature.extend_ctors d.name d))
    d.constructors
    @@ State.modify_signature (Signature.extend_tps d.name d) s
  | TmDecl { body = None; _ } -> failwith "tm decl has no body"
  | TmDecl ({ name; recursive; body = Some body; _ } as d) ->
    let s = s |> State.modify_signature
      (if recursive then Signature.extend_tms name d else fun x -> x)
    in
    debug_print s "Evaluating definition for %s@," name;
    let body = eval s Env.empty body in
    begin let open Format in
      fprintf std_formatter "- @[<hv 2>val %s =@, %a@]%a"
        name
        (Pretty.print_tm 0) body
        pp_print_newline ()
    end;
    s |> State.modify_signature (Signature.extend_tms name { d with body = Some body })

let eval_program initial_state program : (RuntimeError.t, State.t) Result.t =
  let open RuntimeError in
  debug_print initial_state "@[<v>";
  let result = try Result.ok (List.fold_left eval_decl initial_state program) with
    | E e -> Result.error e
  in
  debug_print initial_state "@]";
  result
