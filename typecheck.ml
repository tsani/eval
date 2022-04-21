open Syntax

type infer_env = {
  ppf : Format.formatter;
  sg : Signature.t;
  ctx : Ctx.t;
}

type infer_state = {
  tmvars : TMVar.sub;
}

let map_tmvars (f : TMVar.sub -> TMVar.sub) (s : infer_state) : infer_state =
  { s with tmvars = f s.tmvars }

(* Examines the current TMVar substitution to compute something and possibly transform the substitution. *)
let with_tmvars (f : TMVar.sub -> TMVar.sub * 'a) (s : infer_state) : infer_state * 'a =
  let tmvars, x = f s.tmvars in
  { s with tmvars }, x

let fresh_tmvar (s : infer_state) (prefix : string) : infer_state * tmvar_name =
  s |> with_tmvars (fun tmvars -> TMVar.fresh tmvars prefix)

(* Transforms teh context according to a function. *)
let map_ctx (f : Ctx.t -> Ctx.t) (env : infer_env) : infer_env =
  { env with ctx = f env.ctx }

let extend_ctx (env : infer_env) (d : tp_sc) : infer_env =
  env |> map_ctx (fun ctx -> Ctx.extend ctx d)

let apply_sub_to_ctx (tmvars : TMVar.sub) : infer_env -> infer_env =
  map_ctx (TMVar.apply_sub_to_ctx tmvars)

(* A Type MetaVariable is essentially a free type variable, together with
   a possible instantiation
   A TMVar is written like a#n where n is a number.
 *)

(* Instantiates a type scheme to a type by substituting all (bound) TVars into TMVars.
 * The input TMVar.sub is extended with new uninstantiated TMVars for each
 * 'instantiated' bound tvar.
 *
 * Util.Invariant: The resulting monotype contains no TVar, i.e. it is a genuine monotype.
 *)
let instantiate (s : infer_state) ((tbinders, tp) : tp_sc) : infer_state * tp =
  match tbinders with
  (* Optimization: if there are no binders, skip doing anything *)
  | [] -> (s, tp)
  | _ ->
  (* Otherwise we need to scan some lists, build a map, and traverse the type *)
    let go prefix (s, tmvar_name_pairings) =
      let (s, x) = fresh_tmvar s prefix in
      (s, (prefix, x) :: tmvar_name_pairings)
    in
    let s, tmvar_name_pairings = List.fold_right go tbinders (s, []) in
    let rec rename_tvars_to_tmvars : tp -> tp = function
      | TVar a -> begin match List.assoc_opt a tmvar_name_pairings with
        | None -> raise (Util.Invariant "no free TVars allowed")
        | Some x -> TMVar x
      end
      | Arrow (t1, t2) -> Arrow (rename_tvars_to_tmvars t1, rename_tvars_to_tmvars t2)
      | Named (c, ts) -> Named (c, List.map rename_tvars_to_tmvars ts)
      | TMVar x -> TMVar x
      | Int -> Int
    in
    (s, rename_tvars_to_tmvars tp)

let instantiate_ctor_type (env : infer_env) (s : infer_state) (c : ctor_name) : infer_state * tp =
  let cd = Signature.lookup_ctor' c env.sg in
  let td = Signature.lookup_tp' cd.owner_name env.sg in
  instantiate s (syn_ctor_type td cd)

(* Constructs a polytype from a monotype having only uninstantiated TMVars by
 * converting into TVars those uninstantiated TMVars not appearing in the given
 * list of "outer TMVars" into TVars.
 *)
let generalize (outer : tmvar_name list) (tp : tp) : tp_sc =
  (* The names of all the TMVars to be converted to TVars *)
  let tmvar_names = List.filter (fun x -> not @@ List.mem x outer) @@ TMVar.all_in tp in
  (* Construct a substitution that eliminates the TMVars into TVars *)
  let next tmvars x = match TMVar.lookup tmvars x with
    | `not_found ->
      let prefix, n = TMVar.parse x in
      TMVar.extend_sub tmvars x ~inst: (Some (TVar (prefix ^ string_of_int n)))
      (* TODO something better than this trash *)
    | `inst t -> tmvars (* in case of duplicates do nothing *)
    | `uninst -> raise @@ Util.Invariant "wat"
  in
  let tmvars = List.fold_left next TMVar.empty_sub tmvar_names in
  (* The substitution is in fact a renaming of TMVars to TVars and contains no
     uninstantiated vars, so the following partial matching is justified. *)
  let binders = List.map (fun (_, Some (TVar x)) -> x) @@ TMVar.list_of_sub tmvars in
  (binders, TMVar.apply_sub tmvars tp)

type unify_kind = [
  (* Unifying the inferred type of a pattern with the inferred type the case scrutinee. *)
  | `scru_pat of (tm * tp) * (pattern * tp)

  (* Unifying the subject of an application with a function type. *)
  | `app of tm

  (* Unifying a synthesized spine function type against the constructor type. *)
  | `ctor_spine of (ctor_name * tp) * (spine * tp)

  (* Unifying a synthesized pattern-spine function type against the constructor type. *)
  | `ctor_pat_spine of (ctor_name * tp) * (pattern list * tp)

  (* Unifying a case body type with the type of the match statement. *)
  | `case_body of tm * tp * tp

  (* Unifying a user-supplied annotation with the inferred type of a declared term. *)
  | `decl of tm_name * tp * tp
]

module TypeError = struct
  type t = [
    | `mismatch of unify_kind * tp * tp
    | `infinite_type of tmvar_name * tp
  ]

  type term_stack = tm list

  type report = {
    (* The stack of (sub)terms that leads to the error. *)
    term_stack : term_stack;

    (* The actual error encountered. *)
    error : t;
  }

  let report (error : t) = { error; term_stack = [] }
end

type 'a result = (TypeError.report, 'a) Result.t

(* Pushes a term onto the error term stack in case the given Result is an Error. *)
let push e r = Result.map_error TypeError.(fun r -> { r with term_stack = e :: r.term_stack }) r

(* Interprets a unification result as a typechecking result. *)
let unify (k : unify_kind) : 'a Unify.result -> 'a result =
  let f : Unify.unify_error -> TypeError.t = function 
    | `occurs_check (x, tp) -> `infinite_type (x, tp)
    | `mismatch (t1, t2) -> `mismatch (k, t1, t2)
  in
  Result.map_error (fun err -> TypeError.report @@ f err)

let rec infer_tm (env : infer_env) (s : infer_state) : tm -> (infer_state * tp) result = function
  | Num _ -> Result.ok (s, Int)
  | Var i -> begin match lookup_var env.ctx i with
    | None -> raise (Util.Invariant "unbound variable")
    | Some tpsc -> Result.ok (instantiate s tpsc)
  end
  | Ref c -> begin match Signature.lookup_tm c env.sg with
    | None -> raise (Util.Invariant "unbound reference")
    | Some ({ typ }) -> Result.ok (instantiate s typ)
  end
  | Const (c, spine) ->
    let s, ctor_tp = instantiate_ctor_type env s c in
    Result.bind (infer_ctor_from_spine env s spine) @@ fun (s, inferred_ctor_tp, result_tp) ->
    Format.fprintf env.ppf "Unifying constructor type@.";
    let ctor_tp' = TMVar.apply_sub s.tmvars ctor_tp in
    let inferred_ctor_tp' = TMVar.apply_sub s.tmvars inferred_ctor_tp in
    Result.bind (unify (`ctor_spine ((c, ctor_tp'), (spine, inferred_ctor_tp'))) (Unify.types s.tmvars (ctor_tp, inferred_ctor_tp))) @@ fun tmvars ->
    Result.ok ({ s with tmvars }, result_tp)
  | Fun e ->
    let s, x = fresh_tmvar s "a" in
    let tp_a = TMVar x in
    let env = extend_ctx env @@ mono tp_a in
    Format.fprintf env.ppf "Entering function.@.";
    Result.bind (push e @@ infer_tm env s e) @@ fun (s, tp_b) ->
    Result.ok (s, Arrow (tp_a, tp_b))
  | App (e1, e2) ->
    Result.bind (push e1 @@ infer_tm env s e1) @@ fun (s, f_tp) ->
    Result.bind (push e2 @@ infer_tm env s e2) @@ fun (s, arg_tp) ->
    let s, x = fresh_tmvar s "a" in
    let inferred_f_tp = Arrow (arg_tp, TMVar x) in
    Format.fprintf env.ppf "Unifying application with function type.@.";
    Result.bind (unify (`app e1) (Unify.types s.tmvars (f_tp, inferred_f_tp))) @@ fun tmvars ->
    Result.ok ({ s with tmvars }, TMVar x)
  | Match (e1, cases) ->
    let open Result in
    bind (push e1 @@ infer_tm env s e1) @@ fun (s, scru_tp) ->
    let s, x = fresh_tmvar s "b" in
    let rec go s = function
      | [] -> Result.ok s
      | Case (pat, body) :: cases ->
        Format.fprintf env.ppf "Inferring pattern type.@.";
        bind (infer_pat env s pat) @@ fun (env', s, pat_tp) ->
        let scru_tp' = TMVar.apply_sub s.tmvars scru_tp in
        bind (unify (`scru_pat ((e1, scru_tp'), (pat, pat_tp))) (Unify.types s.tmvars (scru_tp, pat_tp))) @@ fun tmvars ->
        Format.fprintf env.ppf "Inferring body type.@.";
        bind (infer_tm env' { s with tmvars } body) @@ fun (s, body_tp) ->
        Format.fprintf env.ppf "Unifying body type.@.";
        let body_tp' = TMVar.apply_sub s.tmvars body_tp in
        let other_body_tp = TMVar.apply_sub s.tmvars (TMVar x) in
        bind (unify (`case_body (body, body_tp', other_body_tp)) (Unify.types s.tmvars (TMVar x, body_tp))) @@ fun tmvars ->
        Format.fprintf env.ppf "On to the next case...@.";
        go { s with tmvars } cases
    in
    Format.fprintf env.ppf "Processing match cases@.";
    bind (go s cases) @@ fun s ->
    Format.fprintf env.ppf "Done processing cases.@.";
    Result.ok (s, TMVar x)
  | Let (e1, e2) ->
    Result.bind (push e1 @@ infer_tm env s e1) @@ fun (s, scru_tp) ->
    let env = apply_sub_to_ctx s.tmvars env in
    let scru_tp = TMVar.apply_sub s.tmvars scru_tp in
    let outer_tmvars = TMVar.all_in_ctx env.ctx in
    let tp_sc = generalize outer_tmvars scru_tp in
    let s = map_tmvars TMVar.prune_sub s in
    let env = extend_ctx env tp_sc in
    push e2 @@ infer_tm env s e2

(* Infers the type of a function this spine would be applicable to.
 * infer_ctor_from_spine E S sp = (S', T_f, T_return)
 * where T_f = T1 -> ... -> Tn -> T_return
 * and each Ti is inferred from the corresponding sp[i]
 * and T_return is a fresh TMVar
 *)
and infer_ctor_from_spine (env : infer_env) (s : infer_state) : spine -> (infer_state * tp * tp) result =
  function
  | [] ->
    let s, x = fresh_tmvar s "s" in
    Result.ok @@ (s, TMVar x, TMVar x)
  | e :: es ->
    Result.bind (push e @@ infer_tm env s e) @@ fun (s, arg_tp) ->
    Result.bind (infer_ctor_from_spine env s es) @@ fun (s, f_tp, result_tp) ->
    Result.ok (s, Arrow (arg_tp, f_tp), result_tp)

(* Infers the type of a pattern. The pattern type must then be unified with the scrutinee type.
 * Extends the given context with bindings for the variables defined in the pattern.
 *)
and infer_pat (env : infer_env) (s : infer_state) : pattern -> (infer_env * infer_state * tp) result =
  function
  | WildcardPattern ->
    let s, x = fresh_tmvar s "p" in
    Result.ok (env, s, TMVar x)
  | VariablePattern ->
    let s, x = fresh_tmvar s "p" in
    Result.ok (extend_ctx env (mono @@ TMVar x), s, TMVar x)
  | NumPattern _ ->
    Result.ok (env, s, Int)
  | ConstPattern (c, pat_spine) ->
    let s, ctor_tp = instantiate_ctor_type env s c in
    Result.bind (infer_ctor_from_pat_spine env s pat_spine) @@ fun (env, s, inferred_ctor_tp, result_tp) ->
    let ctor_tp' = TMVar.apply_sub s.tmvars ctor_tp in
    let inferred_ctor_tp' = TMVar.apply_sub s.tmvars inferred_ctor_tp in
    Result.bind (unify (`ctor_pat_spine ((c, ctor_tp'), (pat_spine, inferred_ctor_tp'))) (Unify.types s.tmvars (ctor_tp, inferred_ctor_tp))) @@ fun tmvars ->
    Result.ok (env, { s with tmvars }, result_tp)

(* Given a spine t1, ..., tn, constructs the type of a constructor that would accept this spine.
 * Let T1, ..., Tn be the types of the spine's elements. Then the type T1 -> ... -> Tn -> X
 * would be the type of such a constructor, where X is an undetermined type.
 * That makes sense because it's the constructor that decides what the type being constructed in.
 * The same spine can be used on various different constructors to make different types.
 *)
and infer_ctor_from_pat_spine (env : infer_env) (s : infer_state) : pattern list -> (infer_env * infer_state * tp * tp) result =
  function
  | [] ->
    let s, x = fresh_tmvar s "s" in
    Result.ok (env, s, TMVar x, TMVar x)
  | pat :: pat_spine ->
    Result.bind (infer_pat env s pat) @@ fun (env, s, arg_tp) ->
    Result.bind (infer_ctor_from_pat_spine env s pat_spine) @@ fun (env, s, f_tp, result_tp) ->
    Result.ok (env, s, Arrow (arg_tp, f_tp), result_tp)

let make_env ppf (sg : Signature.t) : infer_env =
  { sg; ctx = Ctx.empty; ppf }

let check_decl ppf (sg : Signature.t) : decl -> Signature.t result = function
  | TpDecl d -> Result.ok @@ Signature.declare_tp sg d
  | TmDecl ({ recursive; typ; name; body } as d) ->
    let tmvars, x = TMVar.fresh TMVar.empty_sub "a" in
    let sg = Signature.declare_tm sg { d with typ = mono @@ TMVar x } in
    match body with
    | None -> Result.ok @@ sg
    | Some body ->
      let open Result.Syntax in
      Format.fprintf ppf "Inferring body of declaration for %s@." name;
      infer_tm (make_env ppf sg) { tmvars } body $ fun (s, tp) ->
      (* Unify the user-supplied type as expected type *)
      let s, user_tp = instantiate s typ in
      Format.fprintf ppf "Unifying user type @[%a@] with inferred type @[%a@]@."
       (Pretty.print_tp 0) user_tp
       (Pretty.print_tp 0) tp;
      unify (`decl (name, user_tp, tp)) (Unify.types s.tmvars (user_tp, tp)) $ fun tmvars ->
      (* by unification, [tmvars]typ = [tmvars]tp *)
      Format.fprintf ppf "@[<v>@[<v 2>Applying substitution:@,%a@]@,@[<v 2>to user type:@,%a@]@."
        TMVar.print_sub tmvars
        (Pretty.print_tp 0) user_tp;
      let tp = TMVar.apply_sub tmvars user_tp in
      Format.fprintf ppf "Generalizing.@.";
      let tpsc = generalize [] tp in
      Format.fprintf ppf "Done.@.";
      Result.ok @@ Signature.declare_tm sg { d with typ = tpsc }

let check_program ppf (sg : Signature.t) : program -> Signature.t result =
  List.fold_left (fun sg d -> Result.bind sg @@ fun sg -> check_decl ppf sg d) (Result.ok sg)
