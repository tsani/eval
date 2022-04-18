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
    | ApplyNonClo of tm
    | InfiniteRecursion of var_name

  let print_runtime_error ppf : t -> unit = let open Format in function
    | UnboundVariable (env, i) ->
      fprintf ppf "Unbound variable %d in environment %a" i Pretty.print_env env
    | ApplyNonClo e ->
      fprintf ppf "Cannot apply non-closure %a" (Pretty.print_tm 0) e
    | InfiniteRecursion x ->
      fprintf ppf "Infinite recursion detected in definition for %s" x

  exception E of t

  let unbound_variable env index = raise (E (UnboundVariable (env, index)))
  let apply_non_clo e = raise (E (ApplyNonClo e))
  let infinite_recursion x = raise (E (InfiniteRecursion x))
end

let debug_print (s : State.t) = Format.fprintf s.debug_ppf

let rec match_pattern : tm * pattern -> env option = function
  | Num n1, NumPattern n2 -> if n1 = n2 then Some [] else None
  | e, VariablePattern -> Some [e]
  | _, WildcardPattern -> Some []
  | Const (ctor_name, spine), ConstPattern (pat_ctor_name, pat_spine) -> begin match () with
    | _ when not (ctor_name = pat_ctor_name) -> None
    | _ when not (List.length spine = List.length pat_spine) -> failwith "constructor spine mismatch"
    | _ -> Util.(map_option Env.concats (sequence_options (List.map match_pattern @@ List.combine spine pat_spine)))
    end
  | _ -> failwith "pattern matching failed"

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
  | Fun e -> Clo (env, e)
  | App (e1, e2) -> begin match eval s env e1 with
    | Clo (clo_env, e) ->
      let e' = eval s env e2 in
      let env' = Env.extend e' clo_env in
      debug_print s "entering closure with now-full env %a@," Pretty.print_env env';
      eval s env' e
    | e -> RuntimeError.apply_non_clo e
  end
  | Let (e1, e2) ->
    let x = eval s env e1 in
    eval s (Env.extend x env) e2
  | Match (e, cases) -> eval_match s env (eval s env e) cases
  (* | Rec e ->
    eval s (extend_env e env) e *)
  | Clo (env, e) -> Clo (env, e)
  | Const (ctor_name, spine) -> Const (ctor_name, List.map (eval s env) spine)

and eval_match (s : State.t) (env : env) (scrutinee : tm) : case list -> tm = function
  | [] -> failwith "pattern matching failed"
  | Case (pattern, body) :: cases -> match match_pattern (scrutinee, pattern) with
    | Some env' ->
      let env'' = Env.concat env' env in
      debug_print s "matched case for pattern @[%a@], new env is @[%a@]@,"
       (Pretty.print_pattern 0) pattern
       (Pretty.print_env) env'';
      eval s env'' body
    | None -> eval_match s env scrutinee cases

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
    let body = eval s Env.empty body in
    begin let open Format in
      fprintf std_formatter "- @[<hv 2>val %s =@, %a@]%a"
        name
        (Pretty.print_tm 0) body
        pp_print_newline ()
    end;
    s |> State.modify_signature (Signature.extend_tms name { d with body = Some body })

let eval_program initial_state program : State.t option =
  let open RuntimeError in
  debug_print initial_state "@[<v>";
  let result = try Some (List.fold_left eval_decl initial_state program) with
  | E e ->
    Format.(fprintf err_formatter) "%a" print_runtime_error e;
    None
  in
  debug_print initial_state "@]";
  result
