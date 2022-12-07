open Syntax
open Internal

module P = Pretty.Internal

(** This version of loc_of_tp accounts for type variables, and will chase them if necessary. *)
let loc_of_tp (tmvars : TMVar.sub) (t : Type.t) = let open Type in match TMVar.chase tmvars t with
  | Builtin (loc, _) -> loc
  | Arrow (loc, _, _) -> loc
  | TVar (loc, _) -> loc
  | Named (loc, _, _) -> loc
  | TMVar (loc, a) -> (* the TMVar must be uninstantiated by postcondition of chase *)
    loc

(* Synthesizes the (polymorphic) type of a constructor from its ctor definition
 * and its owning type's definition.
 * Given cd : ctor_decl belonging to td : tp_decl, form the overall type of the
 * constructor:
 * forall a1 ... an. T1 -> ... -> Tn -> <tp_name> a1 ... an
 *)
let syn_ctor_type (td : Decl.tp) (cd : Decl.ctor) : Type.sc =
  let open Type in
  let decompose_tuple_to_arrows = List.fold_right (fun tp tp' -> Arrow (`inferred cd.loc, tp, tp')) in
  ( td.tvar_binders
  , decompose_tuple_to_arrows
      cd.fields
      (Named (`inferred cd.loc, td.name, List.map (fun a -> TVar (`inferred td.loc, a)) td.tvar_binders))
  )

type infer_env = {
  ppf : Format.formatter;
  sg : Term.t Signature.t;
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

let extend_ctx (env : infer_env) (d : Ctx.entry) : infer_env =
  env |> map_ctx (fun ctx -> Ctx.extend ctx d)

let apply_sub_to_ctx (tmvars : TMVar.sub) : infer_env -> infer_env =
  map_ctx (TMVar.apply_sub_to_ctx tmvars)

(* Instantiates a type scheme to a type by substituting all (bound) TVars into TMVars.
 * The input TMVar.sub is extended with new uninstantiated TMVars for each
 * 'instantiated' bound tvar.
 *
 * Util.Invariant: The resulting monotype contains no TVar, i.e. it is a genuine monotype.
 *)
let instantiate (s : infer_state) ((tbinders, tp) : Type.sc) : infer_state * Type.t =
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
    let rec rename_tvars_to_tmvars : Type.t -> Type.t = let open Type in function
      | TVar (loc, a) -> begin match List.assoc_opt a tmvar_name_pairings with
        | None -> raise (Util.Invariant "no free TVars allowed")
        | Some x -> TMVar (loc, x)
      end
      | Arrow (loc, t1, t2) -> Arrow (loc, rename_tvars_to_tmvars t1, rename_tvars_to_tmvars t2)
      | Named (loc, c, ts) -> Named (loc, c, List.map rename_tvars_to_tmvars ts)
      | TMVar (loc, x) -> TMVar (loc, x)
      | Builtin (loc, bt) -> Builtin (loc, bt)
    in
    (s, rename_tvars_to_tmvars tp)

let instantiate_ctor_type (env : infer_env) (s : infer_state) (c : ctor_name) : infer_state * Type.t =
  let cd = Signature.lookup_ctor' c env.sg in
  let td = Signature.lookup_tp' cd.owner_name env.sg in
  instantiate s (syn_ctor_type td cd)

let letters : tvar_name list = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"]

(* Constructs a polytype from a monotype having only uninstantiated TMVars by
 * converting into TVars those uninstantiated TMVars not appearing in the given
 * list of "outer TMVars" into TVars.
 *)
let generalize (outer : (Type.loc * tmvar_name) list) (tp : Type.t) : Type.sc =
  (* The names of all the TMVars to be converted to TVars *)
  let tmvar_locd_names =
    TMVar.all_in tp |>
    List.filter (fun (_, x) -> not @@ List.exists (fun (_, y) -> x = y) outer)
  in
  (* Construct a substitution that eliminates the TMVars into TVars *)
  let next (a :: letters, tmvars) (loc, x) = match TMVar.lookup tmvars x with
    | `not_found ->
      let prefix, n = TMVar.parse x in
      (letters, TMVar.extend_sub tmvars x ~inst: (Some (TVar (loc, a))))
      (* TODO something better than this trash *)
    | `inst t -> (letters, tmvars) (* in case of duplicates do nothing *)

    (* Since we are constructing the substitution right here, and every entry we
       put in it is instantiated, we have the invariant that `uninst is an
       impossible case. *)
    | `uninst -> raise @@ Util.Invariant "every tmvar is instantiated in the substitution we are building"
  in
  let (_, tmvars) = List.fold_left next (letters, TMVar.empty_sub) tmvar_locd_names in
  (* The substitution is in fact a renaming of TMVars to TVars and contains no
     uninstantiated vars, so the following partial matching is justified. *)
  let binders = List.map (fun (_, Some (Type.TVar (_, x))) -> x) @@ TMVar.list_of_sub tmvars in
  (binders, TMVar.apply_sub tmvars tp)

type unify_kind = [
  (* Unifying the inferred type of a pattern with the inferred type the case scrutinee. *)
  | `scru_pat of Scope.t * (Term.t * Type.t) * (Term.pattern * Type.t)

  (* Unifying the subject of an application with a function type. *)
  | `app of Scope.t * Term.t

  (* Unifying a synthesized function type against the head type. *)
  | `head_spine of Scope.t * (Term.head * Type.t) * (Term.spine * Type.t)

  (* Unifying a synthesized pattern-spine function type against the constructor type. *)
  | `ctor_pat_spine of (ctor_name * Type.t) * (Term.pattern list * Type.t)

  (* Unifying a case body type with the type of the match statement. *)
  | `case_body of (Scope.t * Term.t) * Type.t * Type.t

  (* Unifying a user-supplied annotation with the inferred type of a declared term. *)
  | `decl of tm_name * Type.t * Type.t

  (* Unifying the type variable for a recursive term with its inferred type. *)
  | `recursive of tm_name * Type.t
]

module Error = struct
  type t = [
    | `mismatch of unify_kind * Type.t * Type.t
    | `infinite_type of tmvar_name * Type.t
  ]

  type term = [
    | `term of Term.t
    | `head of Term.head
    | `spine of Term.spine
  ]

  type term_stack_entry = Scope.t * term
  type term_stack = term_stack_entry list

  type report = {
    (** The stack of (sub)terms that lead to the error. *)
    term_stack : term_stack;

    (** The actual error encountered. *)
    error : t;

    (** The location where the error occurred. *)
    loc : Loc.span;
  }

  let report loc (error : t) = { loc; error; term_stack = [] }

  let print_mismatch_kind ppf : unify_kind -> unit =
    let open Format in
    function
    | `scru_pat (scope, scru_and_tp, pat_and_tp) ->
      fprintf ppf "@[<v>@[<v 2>when unifying the match scrutinee@,@[%a@]@]@,@[<v 2>with the pattern@,@[%a@]@]@]"
        (P.print_tm_tp scope) scru_and_tp
        P.print_pat_tp pat_and_tp
    (* | `app (scope, e) -> fprintf ppf "when expecting @[%a@] to have a function type." (P.print_tm 0 scope) e *)
    | `head_spine (scope, (tH, a1), (tS, a2)) ->
      fprintf ppf "@[<v>@[<hv 2>when checking application@ %a@]@,@[<hv 2>inferred head type@ %a@]@,@[<hv 2>synthesized head type from spine@ %a@]@]"
        (P.print_app 0 scope) (tH, tS)
        (P.print_tp 0) a1
        (P.print_tp 0) a2
    | `ctor_pat_spine ((ctor, ctor_tp), (pat_sp, inf_ctor_tp)) ->
      fprintf ppf "@[<v>@[<hv 2>when matching constructor@ @[<hv 2>%s :@ %a@]@]@,@[<hv 2>with pattern spine@ %a@]@,@[hv 2>for which the inferred constructor type is@ %a@]@]"
        ctor
        (P.print_tp 0) ctor_tp
        (P.print_pat_spine 10) pat_sp
        (P.print_tp 0) inf_ctor_tp
    | `case_body ((scope, body), body_tp, body_tp') ->
      fprintf ppf "@[<v>@[<hv 2>when unifying the inferred type@ %a@]@,@[<hv 2>of the case body@ %a@]@,@[<hv 2>against the inferred type of the other branches@ %a@]@]"
        (P.print_tp 0) body_tp
        (P.print_tm 0 scope) body
        (P.print_tp 0) body_tp'
    | `decl (c, user_tp, inf_tp) ->
      fprintf ppf "@[<v>@[<hv 2>when unifying the given type@ %a@]@,of the declaration for `%s'@,@[<hv 2>against the inferred type@ %a@]@]"
        (P.print_tp 0) user_tp
        c
        (P.print_tp 0) inf_tp
    | `recursive (tm_name, tp) ->
      fprintf ppf "@[<v>@[<hv 2>in a recursive definition for@ %s@]@,@[<hv 2>with inferred type@ @[%a@]@]@]"
        tm_name
        (P.print_tp 0) tp

  let print ppf : t -> unit =
    let open Format in
    function
    | `mismatch (k, t1, t2) ->
      fprintf ppf "@[<v 2>mismatch.@,@[<2>Expected:%a%a@]@,@[<2>Inferred:%a%a@]@,%a@]"
        pp_print_space ()
        (P.print_tp 0) t1
        pp_print_space ()
        (P.print_tp 0) t2
        print_mismatch_kind k
    | `infinite_type (x, tp) ->
      fprintf ppf "@[<v 2>cannot construct infinite type.@,Type variable %s occurs in type @[%a@]@]"
        x
        (P.print_tp 0) tp

  (* Takes the last `n` elements of the given list.
  * If there are fewer than n elements in the list, the list is returned as is. *)
  let last_n (l : 'a list) (n : int) =
    snd @@ List.fold_right (fun x (n, l) -> if n > 0 then (n - 1, x :: l) else (0, l)) l (n, [])

  let print_term scope ppf : term -> unit = function
    | `term t -> P.print_tm 0 scope ppf t
    | `head tH -> P.print_app 0 scope ppf (tH, [])
    | `spine tS -> P.print_app 0 scope ppf (Sugar.r ".", tS)

  let print_term_stack ppf term_stack =
    let open Format in
    match last_n term_stack 3 with
    | [] -> ()
    | term_stack ->
      fprintf ppf "@,@[<v>Enclosing terms:@,%a@]"
        (pp_print_list ~pp_sep: pp_print_cut begin fun ppf (scope, e) ->
            fprintf ppf "- @[%a@]" (print_term scope) e
          end) term_stack

  let print_report ppf ({ error; term_stack; loc } : report): unit =
    Format.fprintf ppf "@[<v 2>%a: type error:@ %a%a@]"
      Loc.print loc.Loc.Span.start
      print error
      print_term_stack term_stack
end

type 'a result = (Error.report, 'a) Result.t

(* Pushes a term onto the error term stack in case the given Result is an Error. *)
let push e r = Result.map_error Error.(fun r -> { r with term_stack = e :: r.term_stack }) r

let push_scoped env e r = push (Ctx.to_scope env.ctx, e) r

(* Interprets a unification result as a typechecking result. *)
let unify loc (k : unify_kind) : 'a Unify.result -> 'a result =
  let f : Unify.unify_error -> Error.t = function
    | `occurs_check (x, tp) -> `infinite_type (x, tp)
    | `mismatch (t1, t2) -> `mismatch (k, t1, t2)
  in
  Result.map_error (fun err -> Error.report loc @@ f err)

let set_tmvars s (k : infer_state -> 'a result) : TMVar.sub -> 'a result = fun tmvars ->
  k { s with tmvars }

let dprintf env = Format.fprintf env.ppf

let infer_literal = function
  | IntLit _ -> Int
  | BoolLit _ -> Bool
  | CharLit _ -> Char
  | StringLit _ -> String

let infer_prim loc env s =
  let open Prim in
  let open Type in
  let builtin prim = Builtin (`fake, prim) in
  function
  | Eq ->
    let s, x = fresh_tmvar s "a" in
    let a = TMVar (`inferred loc, x) in
    s, arrows [a; a] (builtin Bool)
  | Plus -> s, arrows [builtin Int; builtin Int] (builtin Int)
  | Times -> s, arrows [builtin Int; builtin Int] (builtin Int)
  | Div -> s, arrows [builtin Int; builtin Int] (builtin Int)
  | Neg -> s, arrows [builtin Int] (builtin Int)
  | Not -> s, arrows [builtin Bool] (builtin Bool)
  | And -> s, arrows [builtin Bool; builtin Bool] (builtin Bool)
  | Or -> s, arrows [builtin Bool; builtin Bool] (builtin Bool)
  | CharAt -> s, arrows [builtin String; builtin Int] (builtin Char)
  | SubString -> s, arrows [builtin String; builtin Int; builtin Int] (builtin String)
  | Lt -> s, arrows [builtin Int; builtin Int] (builtin Bool)

let infer_head (env : infer_env) (s : infer_state) : Term.head -> (infer_state * Type.t) result =
  let open Term in let open Type in
  function
  | Const (_, c) -> Result.ok @@ instantiate_ctor_type env s c
  | Var (_, i) -> begin match lookup_var env.ctx i with
      | None -> Util.invariant "scopecheck: all variables are bound"
      | Some (_, tpsc) -> Result.ok @@ instantiate s tpsc
    end
  | Ref (_, f) -> begin match Signature.lookup_tm f env.sg with
      | None -> Util.invariant "scopecheck: all references are resolved"
      | Some ({ typ }) -> match typ with
        | None -> Util.invariant "every ref's type is known"
        | Some typ -> Result.ok (instantiate s typ)
    end
  | Prim (loc, prim) -> Result.ok @@ infer_prim loc env s prim


let rec infer_tm (env : infer_env) (s : infer_state) : Term.t -> (infer_state * Type.t) result =
  let open Term in let open Type in
  function
  | Lit (loc, lit) -> Result.ok (s, Builtin (`inferred loc, infer_literal lit))
                        (*
  | Const (loc, c, spine) ->
    let s, ctor_tp = instantiate_ctor_type env s c in
    Result.bind (infer_ctor_from_spine loc env s spine) @@ fun (s, inferred_ctor_tp, result_tp) ->
    dprintf env "Unifying constructor type@,";
    let ctor_tp' = TMVar.apply_sub s.tmvars ctor_tp in
    let inferred_ctor_tp' = TMVar.apply_sub s.tmvars inferred_ctor_tp in
    Result.bind begin
      unify loc
        (`ctor_spine (Ctx.to_scope env.ctx, (c, ctor_tp'), (spine, inferred_ctor_tp')))
        (Unify.types s.tmvars (ctor_tp, inferred_ctor_tp))
    end @@ fun tmvars ->
    Result.ok ({ s with tmvars }, result_tp)
                           *)
  | Fun (loc, (loc_x, x), e) ->
    let s, a = fresh_tmvar s "a" in
    let tp_a = TMVar (`inferred loc_x, a) in
    let env = extend_ctx env @@ (x, mono tp_a) in
    dprintf env "@[<hv 2>Entering function.@ ";
    Result.bind (push_scoped env (`term e) @@ infer_tm env s e) @@ fun (s, tp_b) ->
    let arr = Arrow (`inferred loc, tp_a, tp_b) in
    dprintf env "@]@[<v 2>Inferred function type@ %a@]@," (P.print_tp 0) (TMVar.apply_sub s.tmvars arr);
    Result.ok (s, arr)
  | App (loc, tH, tS) ->
    Result.bind (push_scoped env (`head tH) @@ infer_head env s tH) @@ fun (s, aH) ->
    Result.bind (push_scoped env (`spine tS) @@ infer_from_spine loc env s tS) @@ fun (s, aS, a_ret) ->
    Result.bind begin
      unify loc
        (`head_spine (Ctx.to_scope env.ctx, (tH, aH), (tS, aS)))
        (Unify.types s.tmvars (aH, aS))
    end @@ set_tmvars s @@ fun s ->
    Result.ok (s, a_ret)
  | Match (match_loc, t, cases) ->
    let open Result in
    bind (push_scoped env (`term t) @@ infer_tm env s t) @@ fun (s, a_scru) ->
    (* idea: synthesize a fresh tmvar whose type will be the type of all the case bodies
       then, when we infer the type of a case body, we unify its type with this TMVar.
       This will arrange that all case body types get unified together.
       This TMVar is the type of the whole match-expression. *)
    let s, x = fresh_tmvar s "b" in
    let rec go s = function
      | [] -> ok s
      | Case (loc, p, t_body) :: cases ->
        dprintf env "@[<hv 2>Infer type of pattern@ %a@]@," (P.print_pattern 0) p;
        bind (infer_pat env s p) @@ fun (env', s, aP) ->
        bind begin
          unify
            (loc_of_pattern p)
            (`scru_pat (Ctx.to_scope env.ctx, (t, a_scru), (p, aP)))
            (Unify.types s.tmvars (a_scru, aP))
        end @@ set_tmvars s @@ fun s ->
        dprintf env "Inferring body type.@,";
        bind (infer_tm env' s t_body) @@ fun (s, a_body) ->
        let a_body' = TMVar.apply_sub s.tmvars a_body in
        let a_other_body = TMVar.apply_sub s.tmvars (TMVar (`inferred match_loc, x)) in
        dprintf env "@[<hv 2>@[<hv 2>Unifying body types@ %a@]@ @[<hv 2>and@ %a@]@]@,"
          (P.print_tp 0) a_body'
          (P.print_tp 0) a_other_body;
        bind begin
          unify
            match_loc
            (`case_body ((Ctx.to_scope env.ctx, t_body), a_body', a_other_body))
            (Unify.types s.tmvars (a_other_body, a_body))
        end @@ set_tmvars s @@ fun s -> go s cases
    in
    dprintf env "Processing match cases@,";
    bind (go s cases) @@ fun s ->
    dprintf env "Done processing cases.@,";
    Result.ok (s, TMVar (`inferred match_loc, x))
  | Let (loc, Rec, (loc_x, x), e1, e2) ->
    let s, b = fresh_tmvar s "b" in
    (* in the env for inferring the type of x = e1, we introduce a binding x : T
    where T = a#n, that is a fresh TMVar.*)
    let env' = extend_ctx env @@ (x, mono (TMVar (`inferred loc_x, b))) in
    Result.bind (push_scoped env' (`term e1) @@ infer_tm env' s e1) @@ fun (s, scru_tp) ->
    (* Now let's go back to the original env and normalize the types. *)
    let env = apply_sub_to_ctx s.tmvars env in
    (* Collect all the tmvars that were around before we went to infer the type of e1. *)
    let outer_tmvars = TMVar.all_in_ctx env.ctx in
    (* Finally we can generalize the type of e1. *)
    let tp_sc = generalize outer_tmvars scru_tp in
    (* Form a new version of env', but this time using the generalized type of e1 for x. *)
    let env = extend_ctx env (x, tp_sc) in
    push_scoped env (`term e2) @@ infer_tm env s e2
  | Let (loc, NonRec, (loc_x, x), e1, e2) ->
    Result.bind (push_scoped env (`term e1) @@ infer_tm env s e1) @@ fun (s, scru_tp) ->
    let env = apply_sub_to_ctx s.tmvars env in
    let scru_tp = TMVar.apply_sub s.tmvars scru_tp in
    let outer_tmvars = TMVar.all_in_ctx env.ctx in
    let tp_sc = generalize outer_tmvars scru_tp in
    let env = extend_ctx env (x, tp_sc) in
    push_scoped env (`term e2) @@ infer_tm env s e2

(* Infers the type of a function this spine would be applicable to.
 * infer_ctor_from_spine E S sp = (S', T_f, T_r)
 * where T_f = T_1 -> ... -> T_n -> T_r
 * and each T_i is inferred from the corresponding sp_i
 * and T_r is a fresh TMVar
 *)
and infer_from_spine loc
    (env : infer_env) (s : infer_state) : Term.spine -> (infer_state * Type.t * Type.t) result =
  function
  | [] ->
    let s, x = fresh_tmvar s "s" in
    Result.ok @@ Type.(s, TMVar (`inferred loc, x), TMVar (`inferred loc, x))
  | e :: es ->
    Result.bind (push_scoped env (`term e) @@ infer_tm env s e) @@ fun (s, arg_tp) ->
    Result.bind (infer_from_spine loc env s es) @@ fun (s, f_tp, result_tp) ->
    Result.ok (s, Type.Arrow (`inferred (Loc.Span.join loc (Term.loc_of_tm e)), arg_tp, f_tp), result_tp)

(* Infers the type of a pattern. The pattern type must then be unified with the scrutinee type.
 * Extends the given context with bindings for the variables defined in the pattern.
 *)
and infer_pat (env : infer_env) (s : infer_state) : Term.pattern -> (infer_env * infer_state * Type.t) result =
  function
  | WildcardPattern loc ->
    let s, p = fresh_tmvar s "p" in
    Result.ok (env, s, Type.TMVar (`inferred loc, p))
  | VariablePattern (loc, x) ->
    let s, p = fresh_tmvar s "p" in
    Result.ok Type.(extend_ctx env (x, mono @@ TMVar (`inferred loc, p)), s, TMVar (`inferred loc, p))
  | LiteralPattern (loc, lit) ->
    Result.ok (env, s, Type.Builtin (`inferred loc, infer_literal lit))
  | ConstPattern (loc, c, pat_spine) ->
    let s, ctor_tp = instantiate_ctor_type env s c in
    Result.bind (infer_ctor_from_pat_spine loc env s pat_spine) @@ fun (env, s, inferred_ctor_tp, result_tp) ->
    let ctor_tp' = TMVar.apply_sub s.tmvars ctor_tp in
    let inferred_ctor_tp' = TMVar.apply_sub s.tmvars inferred_ctor_tp in
    let u = Unify.types s.tmvars (ctor_tp, inferred_ctor_tp) in
    Result.bind (unify loc (`ctor_pat_spine ((c, ctor_tp'), (pat_spine, inferred_ctor_tp'))) u) @@ fun tmvars ->
    Result.ok (env, { s with tmvars }, result_tp)

(* Given a spine t1, ..., tn, constructs the type of a constructor that would accept this spine.
 * Let T1, ..., Tn be the types of the spine's elements. Then the type T1 -> ... -> Tn -> X
 * would be the type of such a constructor, where X is an undetermined type.
 * That makes sense because it's the constructor that decides what the type being constructed in.
 * The same spine can be used on various different constructors to make different types.
 *)
and infer_ctor_from_pat_spine loc
    (env : infer_env) (s : infer_state) : Term.pattern list -> (infer_env * infer_state * Type.t * Type.t) result =
  function
  | [] ->
    let s, x = fresh_tmvar s "s" in
    Result.ok Type.(env, s, TMVar (`inferred loc, x), TMVar (`inferred loc, x))
  | pat :: pat_spine ->
    Result.bind (infer_pat env s pat) @@ fun (env, s, arg_tp) ->
    Result.bind (infer_ctor_from_pat_spine loc env s pat_spine) @@ fun (env, s, f_tp, result_tp) ->
    Result.ok (env, s, Type.Arrow (`inferred (Loc.Span.join loc (Term.loc_of_pattern pat)), arg_tp, f_tp), result_tp)

let make_env ppf (sg : Term.t Signature.t) : infer_env =
  { sg; ctx = Ctx.empty; ppf }

let check_decl ppf (sg : Term.t Signature.t) : Term.t Decl.t -> Term.t Signature.t result = function
  | TpDecl d ->
    Format.fprintf ppf "@[Define type %s@]@," d.name;
    Result.ok @@ Signature.declare_tp sg d
  | TmDecl ({ recursive; typ; name; body; loc } as d) ->
    Format.fprintf ppf "@[<v 2>Typechecking declaration for %s@," name;
    (* associate a fresh type variable to the definition, so that when we look
       up the type of the function for recursion, we end up unifying
       appropriately to figure out the type of the function.
       tp_synth is the type of the thing we're defining; that type is only
       associated in the signature to the thing we're defining for recursive
       definitions.
       This type needs to be unified with the type we infer for the term to
       detect certain infinite types.
       e.g. `def rec oops = fun x -> oops` should not typecheck.
    *)
    let tmvars, sg, tp_synth =
      let open Type in
      let tmvars, x = TMVar.fresh TMVar.empty_sub "a" in
      let tp = TMVar (`inferred loc, x) in
      if recursive then
        (tmvars, Signature.declare_tm sg { d with typ = Some (mono tp) }, tp)
      else
        (tmvars, sg, tp)
    in
    let sg' = match body with
      | None -> Result.ok @@ sg
      | Some body ->
        Format.fprintf ppf "Inferring body of declaration for %s@," name;
        Result.bind (infer_tm (make_env ppf sg) { tmvars } body) @@ fun (s, tp) ->
        Result.bind begin
          unify loc (`recursive (name, tp)) (Unify.types s.tmvars (tp_synth, tp))
        end @@ fun tmvars ->
        Result.bind begin match typ with
          | None -> (* no user-supplied type *)
            let tp = TMVar.apply_sub s.tmvars tp in
            Format.fprintf ppf "@[<hv>Inferred %s :@ @[%a@]@]@," name (P.print_tp 0) tp;
            let tpsc = generalize [] tp in
            Format.fprintf ppf "@[<hv 2>Generalized type is@ %a@]@," (P.print_tp_sc 0) tpsc;
            Result.ok tpsc
          | Some typ ->
            let s, user_tp = instantiate s typ in
            Format.fprintf ppf "@[<hv 2>@[<hv 2>Unifying user type@ %a@]@ @[<hv 2>with inferred type@ %a@]@]@,"
              (P.print_tp 0) user_tp
              (P.print_tp 0) (TMVar.apply_sub s.tmvars tp);
            Result.bind (unify loc (`decl (name, user_tp, tp)) (Unify.types s.tmvars (user_tp, tp))) @@ fun tmvars ->
            (* by unification, [tmvars]typ = [tmvars]tp *)
            Format.fprintf ppf "@[<v>@[<v 2>Applying substitution:@,%a@]@,@[<v 2>to user type:@,%a@]@]@,"
              TMVar.print_sub tmvars
              (P.print_tp 0) user_tp;
            let tp = TMVar.apply_sub tmvars user_tp in
            Format.fprintf ppf "Generalizing...@,";
            let tpsc = generalize [] tp in
            Format.fprintf ppf "@[<hv 2>Generalized type is@ %a@]@," (P.print_tp_sc 0) tpsc;
            Result.ok tpsc
        end @@ fun tpsc ->
        Result.ok @@ Signature.declare_tm sg { d with typ = Some tpsc }
    in
    Format.fprintf ppf "@]@,";
    sg'

let check_program ppf (sg : Term.t Signature.t) : Decl.program -> Term.t Signature.t result =
  Format.fprintf ppf "@[<v>";
  let x = List.fold_left (fun sg d -> Result.bind sg @@ fun sg -> check_decl ppf sg d) (Result.ok sg) in
  Format.fprintf ppf "@]";
  x
