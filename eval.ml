open Syntax

module StringMap = Map.Make(String)

type tm_map = tm_decl StringMap.t
type tp_map = tp_decl StringMap.t
type ctor_map = ctor_decl StringMap.t

let (extend_tm_map, extend_tp_map, extend_ctor_map) = (StringMap.add, StringMap.add, StringMap.add)
let (empty_tm_map, empty_tp_map, empty_ctor_map) = let x = StringMap.empty in (x, x, x)
let extend_env var env = var :: env
let lookup = StringMap.find_opt
let lookup' map key = StringMap.find key map
let empty_env : env = []
let concat_env env1 env2 = env1 @ env2
let concat_envs l = List.fold_right concat_env l []

type eval_state = {
  (* Used to emit debug messages *)
  debug_ppf : Format.formatter;
  tps : tp_map;
  ctors : ctor_map;
  tms : tm_map;
}

let empty_state debug_ppf = {
  debug_ppf;
  tps = empty_tp_map;
  ctors = empty_ctor_map;
  tms = empty_tm_map
}

let lookup_var env i : tm option =
  let rec go = function
    | e :: _, 0 -> Some e
    | [], i' -> None
    | _ :: env, i' -> go (env, i' - 1)
  in
  go (env, i)

let rec sequence_options (l : 'a option list) : 'a list option = match l with
  | [] -> Some []
  | None :: _ -> None
  | Some x :: xs -> match sequence_options xs with
    | None -> None
    | Some xs -> Some (x :: xs)

let map_option (f : 'a -> 'b) (o : 'a option) : 'b option = match o with
  | Some x -> Some (f x)
  | None -> None

let rec match_pattern : tm * pattern -> env option = function
  | Num n1, NumPattern n2 -> if n1 = n2 then Some [] else None
  | e, VariablePattern -> Some [e]
  | _, WildcardPattern -> Some []
  | Const (ctor_name, spine), ConstPattern (pat_ctor_name, pat_spine) -> begin match () with
    | _ when not (ctor_name = pat_ctor_name) -> None
    | _ when not (List.length spine = List.length pat_spine) -> failwith "constructor spine mismatch"
    | _ -> map_option concat_envs (sequence_options (List.map match_pattern @@ List.combine spine pat_spine))
    end
  | _ -> failwith "pattern matching failed"

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

let debug_print (s : eval_state) = Format.fprintf s.debug_ppf

let rec eval (s : eval_state) (env : env) : tm -> tm = function
  | Num n -> Num n
  | Var i -> begin match lookup_var env i with
    | Some e -> e
    | None -> RuntimeError.unbound_variable env i
  end
  | Ref v -> begin match lookup' s.tms v with
    | { body = Some body; _ } -> body
    | _ -> RuntimeError.infinite_recursion v
  end
  | Fun e -> Clo (env, e)
  | App (e1, e2) -> begin match eval s env e1 with
    | Clo (clo_env, e) ->
      let e' = eval s env e2 in
      let env' = extend_env e' clo_env in
      debug_print s "entering closure with now-full env %a@," Pretty.print_env env';
      eval s env' e
    | e -> RuntimeError.apply_non_clo e
  end
  | Match (e, cases) -> eval_match s env (eval s env e) cases
  (* | Rec e ->
    eval s (extend_env e env) e *)
  | Clo (env, e) -> Clo (env, e)
  | Const (ctor_name, spine) -> Const (ctor_name, List.map (eval s env) spine)

and eval_match (s : eval_state) (env : env) (scrutinee : tm) : case list -> tm = function
  | [] -> failwith "pattern matching failed"
  | Case (pattern, body) :: cases -> match match_pattern (scrutinee, pattern) with
    | Some env' ->
      let env'' = concat_env env' env in
      debug_print s "matched case for pattern @[%a@], new env is @[%a@]@,"
       (Pretty.print_pattern 0) pattern
       (Pretty.print_env) env'';
      eval s env'' body
    | None -> eval_match s env scrutinee cases

let eval_decl (s : eval_state) (d : decl) : eval_state = match d with
  | TpDecl d -> List.fold_right
    (fun (ctor : ctor_decl) s -> { s with ctors = extend_ctor_map ctor.name ctor s.ctors })
    d.constructors
    { s with tps = extend_tp_map d.name d s.tps }
  | TmDecl { body = None; _ } -> failwith "tm decl has no body"
  | TmDecl { name; typ; recursive; body = Some body } ->
    let s =
      if recursive
      then { s with tms = extend_tm_map name { name; typ; recursive; body = None } s.tms }
      else s
    in
    let body = eval s empty_env body in
    begin let open Format in
      fprintf std_formatter "- @[<hv 2>val %s =@, %a@]%a"
        name
        (Pretty.print_tm 0) body
        pp_print_newline ()
    end;
    { s with tms = extend_tm_map name { name; typ; recursive; body = Some body } s.tms }

let eval_program initial_state program : eval_state option =
  let open RuntimeError in
  let open Format in
  fprintf initial_state.debug_ppf "@[<v>";
  let result = try Some (List.fold_left eval_decl initial_state program) with
  | E e ->
    fprintf err_formatter "%a" print_runtime_error e;
    None
  in
  fprintf initial_state.debug_ppf "@]";
  result
