open Syntax

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
let instantiate (tmvars : TMVar.sub) ((tbinders, tp) : tp_sc) : TMVar.sub * tp =
  match tbinders with
  (* Optimization: if there are no binders, skip doing anything *)
  | [] -> (tmvars, tp)
  | _ ->
  (* Otherwise we need to scan some lists, build a map, and traverse the type *)
    let go prefix (tmvars, tmvar_name_pairings) =
      let (tmvars', x) = TMVar.fresh tmvars prefix in
      (tmvars', (prefix, x) :: tmvar_name_pairings)
    in
    let tmvars, tmvar_name_pairings = List.fold_right go tbinders (tmvars, []) in
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
    (tmvars, rename_tvars_to_tmvars tp)

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

(* The errors for unbound var, ref, and const should all be impossible by invariant.
 * Normally, we would have an external syntax and 'scope-check' that syntax to ensure
 * all bindings are valid. Scope-checking will produce the internal syntax we're currently
 * working with, and so we can simply raise invariant failures instead of
 * generating type errors.
 *)

type type_error = [
  | `mismatch of tp * tp
  | `infinite_type of tmvar_name * tp
]

type 'a result = (type_error, 'a) Result.t

let unify : 'a Unify.result -> 'a result =
  let f : Unify.unify_error -> type_error = function 
    | `occurs_check (x, tp) -> `infinite_type (x, tp)
    | `mismatch (t1, t2) -> `mismatch (t1, t2)
  in
  Result.map_error f

let rec infer_tm (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) : tm -> (TMVar.sub * tp) result = function
  | Num _ -> Result.ok (tmvars, Int)
  | Var i -> begin match lookup_var ctx i with
    | None -> raise (Util.Invariant "unbound variable")
    | Some tpsc -> Result.ok (instantiate tmvars tpsc)
  end
  | Ref c -> begin match Signature.lookup_tm c sg with
    | None -> raise (Util.Invariant "unbound reference")
    | Some ({ typ }) -> Result.ok (instantiate tmvars typ)
  end
  | Const (c, spine) -> begin match Signature.lookup_ctor c sg with
    | None -> raise (Util.Invariant "unbound constructor")
    | Some ({ owner_name } as cd) ->
      (* by invariant, each owner_name is valid *)
      let td = Signature.lookup_tp' owner_name sg in
      let tmvars, ctor_tp = instantiate tmvars (syn_ctor_type td cd) in
      Result.bind (infer_spine sg tmvars ctx spine) @@ fun (tmvars, spine_tps) ->
      infer_app_spine sg tmvars ctx ctor_tp spine_tps
  end
  | Fun e ->
    let tmvars, x = TMVar.fresh tmvars "a" in
    let tp_a = TMVar x in
    let ctx = Ctx.extend ctx @@ mono tp_a in
    Result.bind (infer_tm sg tmvars ctx e) @@ fun (tmvars, tp_b) ->
    Result.ok (tmvars, Arrow (tp_a, tp_b))
  | App (e1, e2) ->
    Result.bind (infer_tm sg tmvars ctx e1) @@ fun (tmvars, f_tp) ->
    Result.bind (infer_tm sg tmvars ctx e2) @@ fun (tmvars, arg_tp) ->
    infer_app_spine sg tmvars ctx f_tp [arg_tp]
  | Match (e1, cases) ->
    Result.bind (infer_tm sg tmvars ctx e1) @@ fun (tmvars, scru_tp) ->
    infer_match sg tmvars ctx scru_tp cases
  | Let (e1, e2) ->
    Result.bind (infer_tm sg tmvars ctx e1) @@ fun (tmvars, scru_tp) ->
    let ctx = TMVar.apply_sub_to_ctx tmvars ctx in
    let scru_tp = TMVar.apply_sub tmvars scru_tp in
    let outer_tmvars = TMVar.all_in_ctx ctx in
    let tp_sc = generalize outer_tmvars scru_tp in
    let tmvars = TMVar.prune_sub tmvars in
    let ctx = Ctx.extend ctx tp_sc in
    infer_tm sg tmvars ctx e2

and infer_spine (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) : spine -> (TMVar.sub * tp list) result =
  function
  | [] -> Result.ok @@ (tmvars, [])
  | e :: es ->
    Result.bind (infer_tm sg tmvars ctx e) @@ fun (tmvars, tp) ->
    Result.bind (infer_spine sg tmvars ctx es) @@ fun (tmvars, tps) ->
    Result.ok (tmvars, tp :: tps)

and infer_match (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) (scru_tp : tp) : case list -> (TMVar.sub * tp) result = function
  | [] ->
    let tmvars, x = TMVar.fresh tmvars "a" in
    Result.ok (tmvars, TMVar x)
  | case :: cases ->
    let open Result.Syntax in
    infer_case sg tmvars ctx scru_tp case $ fun (tmvars, body_tp) ->
    infer_match sg tmvars ctx scru_tp cases $ fun (tmvars, body_tp') ->
    unify (Unify.types tmvars (body_tp, body_tp')) $ fun tmvars ->
    Result.ok (tmvars, body_tp)

and infer_case (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) (scru_tp : tp) : case -> (TMVar.sub * tp) result =
  fun (Case (pat, body)) ->
  let open Result.Syntax in
  infer_pat sg tmvars ctx pat $ fun (ctx', tmvars, tp) ->
  unify (Unify.types tmvars (scru_tp, tp)) $ fun tmvars ->
  infer_tm sg tmvars ctx' body

(* Infers the type of a pattern. The pattern type must then be unified with the scrutinee type.
 * Extends the given context with bindings for the variables defined in the pattern.
 *)
and infer_pat (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) : pattern -> (Ctx.t * TMVar.sub * tp) result =
  function
  | WildcardPattern ->
    let tmvars, x = TMVar.fresh tmvars "p" in
    Result.ok (ctx, tmvars, TMVar x)
  | VariablePattern ->
    let tmvars, x = TMVar.fresh tmvars "p" in
    Result.ok (Ctx.extend ctx (mono @@ TMVar x), tmvars, TMVar x)
  | NumPattern _ ->
    Result.ok (Ctx.empty, tmvars, Int)
  | ConstPattern (c, pat_spine) ->
    let cd = Signature.lookup_ctor' c sg in
    let td = Signature.lookup_tp' cd.owner_name sg in
    let tmvars, ctor_tp = instantiate tmvars (syn_ctor_type td cd) in
    Result.bind (infer_pat_spine sg tmvars ctx pat_spine) @@ fun (ctx, tmvars, pat_spine_tps) ->
    Result.bind (infer_app_spine sg tmvars ctx ctor_tp pat_spine_tps) @@ fun (tmvars, tp) ->
    Result.ok (ctx, tmvars, tp)

and infer_pat_spine (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) : pattern list -> (Ctx.t * TMVar.sub * tp list) result =
  function
  | [] -> Result.ok (ctx, tmvars, [])
  | pat :: pat_spine ->
    Result.bind (infer_pat sg tmvars ctx pat) @@ fun (ctx, tmvars, tp) ->
    Result.bind (infer_pat_spine sg tmvars ctx pat_spine) @@ fun (ctx, tmvars, tps) ->
    Result.ok (ctx, tmvars, tp :: tps)

(* Given a spine ts consisting of n types, tp1 ... tpn, unify
 * the given function type f_tp against tp1 -> ... -> tpn -> B
 * The result is the leftover type B.
 *)
and infer_app_spine (sg : Signature.t) (tmvars : TMVar.sub) (ctx : Ctx.t) (f_tp : tp) : tp list -> (TMVar.sub * tp) result = function
  | [] -> Result.ok (tmvars, f_tp)
  | tp_arg :: spine ->
    let open Result.Syntax in
    let tmvars, tp_b = TMVar.fresh tmvars "b" in
    let t_arr = Arrow (tp_arg, TMVar tp_b) in
    unify (Unify.types tmvars (t_arr, f_tp)) $ fun tmvars ->
    infer_app_spine sg tmvars ctx (TMVar tp_b) spine

let check_decl (sg : Signature.t) : decl -> Signature.t result = function
  | TpDecl d -> Result.ok @@ Signature.declare_tp sg d
  | TmDecl ({ recursive; typ; name; body } as d) ->
    let tmvars, x = TMVar.fresh TMVar.empty_sub "a" in
    let sg = Signature.declare_tm sg { d with typ = mono @@ TMVar x } in
    match body with
    | None -> Result.ok @@ sg
    | Some body ->
      let open Result.Syntax in
      infer_tm sg tmvars Ctx.empty body $ fun (tmvars, tp) ->
      (* Unify the user-supplied type as expected type *)
      let tmvars, user_tp = instantiate tmvars typ in
      unify (Unify.types tmvars (user_tp, tp)) $ fun tmvars ->
      (* by unification, [tmvars]typ = [tmvars]tp *)
      let tp = TMVar.apply_sub tmvars user_tp in
      let tpsc = generalize [] tp in
      Result.ok @@ Signature.declare_tm sg { d with typ = tpsc }

let check_program (sg : Signature.t) : program -> Signature.t result =
  List.fold_left (fun sg d -> Result.bind sg @@ fun sg -> check_decl sg d) (Result.ok sg)
