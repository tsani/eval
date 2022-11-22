(* Scopechecking turns external syntax (the result of parsing) into internal
syntax, which can be typechecked and evaluated. *)

open Syntax
module I = Internal
module E = External

type env = {
  tms : tm_name list;
  ctors : ctor_name list;
  tps : tp_name list;
}

module Error = struct
  type t =
    | UnboundTypeVariable of tvar_name
    | UnknownNamedType of tp_name
    | BadArity of { expected : int; actual : int; tp_name : string }
    | BadConstructorArity of { expected : int; actual : int; ctor_name : string }
    | UnboundVariable of var_name
    | UnboundConstructor of ctor_name
end

type 'a result = (Error.t, 'a) Result.t

(* Scopechecks a type, possibly in a context of bound type variables.
   If the tvar context is present, then any TVar appearing in the type must appear in the context.
   Otherwise, TVars may appear wherever in the type.

   This is to allow using `check_tp` both for checking the types in type
   definitions as well as the types associated to terms, which may involve
   implicitly quantified variables.

   - lookup_tp a = None -> the type is not bound
   - lookup_tp a = Some n -> the type is known and has arity n

   lookup_tvar simply returns whether the type variable is in the context.
*)
let rec check_tp
    (lookup_tp : tp_name -> int option)
    (lookup_tvar : tvar_name -> bool) : E.Type.t -> I.Type.t result =
  function
  | E.Type.Int -> Result.ok I.Type.Int
  | E.Type.Arrow (t1, t2) ->
    Result.bind (check_tp lookup_tp lookup_tvar t1) @@ fun t1 ->
    Result.bind (check_tp lookup_tp lookup_tvar t2) @@ fun t2 ->
    Result.ok @@ I.Type.Arrow (t1, t2)

  | E.Type.TVar a when lookup_tvar a -> Result.ok (I.Type.TVar a)
  | E.Type.TVar a -> Result.error Error.(UnboundTypeVariable a)

  | E.Type.Named (a, ts) -> match lookup_tp a with
    | None -> Result.error Error.(UnknownNamedType a)
    | Some n ->
      let k = List.length ts in
      if k <> n then Result.error Error.(BadArity { expected = n; actual = k; tp_name = a }) else
      Result.(bind @@ traverse (check_tp lookup_tp lookup_tvar) ts) @@ fun ts ->
      Result.ok @@ I.Type.Named (a, ts)

let rec check_pattern lookup_ctor scope = function
  | E.Term.NumPattern n -> Result.ok @@ (scope, I.Term.NumPattern n)
  | E.Term.VariablePattern x -> Result.ok @@ (Scope.extend scope x, I.Term.VariablePattern x)
  | E.Term.WildcardPattern -> Result.ok @@ (scope, I.Term.WildcardPattern)
  | E.Term.ConstPattern (ctor_name, pat_spine) ->
    match lookup_ctor ctor_name with
    | None -> Result.error Error.(UnboundConstructor ctor_name)
    | Some n ->
      let k = List.length pat_spine in
      if n <> k then Result.error Error.(BadConstructorArity { ctor_name; actual = k; expected = n }) else
      Result.bind (check_pattern_spine lookup_ctor scope pat_spine) @@ fun (scope, pat_spine) ->
      Result.ok (scope, I.Term.ConstPattern (ctor_name, pat_spine))

and check_pattern_spine lookup_ctor scope = function
  | [] -> Result.ok (scope, [])
  | p :: ps ->
    Result.bind (check_pattern lookup_ctor scope p) @@ fun (scope, p) ->
    Result.bind (check_pattern_spine lookup_ctor scope ps) @@ fun (scope, ps) ->
    Result.ok (scope, p :: ps)


let rec check_tm
    (lookup_ctor : ctor_name -> int option)
    (lookup_tm : tm_name -> bool)
    (scope : Scope.t) : E.Term.t -> I.Term.t result =
  function
  | E.Term.Num n -> Result.ok @@ I.Term.Num n
  | E.Term.Var x -> begin match Scope.index_of x scope with
    | Some i -> Result.ok @@ I.Term.Var i
    | None when lookup_tm x -> Result.ok @@ I.Term.Ref x
    | _ -> Result.error Error.(UnboundVariable x)
  end
  | E.Term.Fun (x, e) ->
    Result.bind (check_tm lookup_ctor lookup_tm (Scope.extend scope x) e) @@ fun e ->
    Result.ok @@ I.Term.Fun (x, e)
  | E.Term.App (e1, e2) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e1) @@ fun e1 ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e2) @@ fun e2 ->
    Result.ok @@ I.Term.App (e1, e2)
  | E.Term.Let (rec_flag, x, e1, e2) ->
    let scope1 = match rec_flag with
      | NonRec -> scope
      | Rec -> Scope.extend scope x
    in
    Result.bind (check_tm lookup_ctor lookup_tm scope1 e1) @@ fun e1 ->
    Result.bind (check_tm lookup_ctor lookup_tm (Scope.extend scope x) e2) @@ fun e2 ->
    Result.ok @@ I.Term.Let (rec_flag, x, e1, e2)
  | E.Term.Const (ctor_name, _) when None = lookup_ctor ctor_name ->
    Result.error Error.(UnboundConstructor ctor_name)
  | E.Term.Const (ctor_name, es) ->
    Result.(bind @@ traverse (check_tm lookup_ctor lookup_tm scope) es) @@ fun es ->
    Result.ok @@ I.Term.Const (ctor_name, es)
  | E.Term.Match (e, cases) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e) @@ fun e ->
    Result.(bind @@ traverse (check_case lookup_ctor lookup_tm scope) cases) @@ fun cases ->
    Result.ok @@ I.Term.Match (e, cases)

and check_case lookup_ctor lookup_tm scope = function
  | Case (pat, body) ->
    Result.bind (check_pattern lookup_ctor scope pat) @@ fun (scope, pat) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope body) @@ fun body ->
    Result.ok @@ I.Term.Case (pat, body)

let rec quantify tvars = function
  | E.Type.Int -> tvars
  | E.Type.Arrow (t1, t2) -> List.fold_left quantify tvars [t1; t2]
  | E.Type.TVar a -> a :: tvars
  | E.Type.Named (_, ts) -> List.fold_left quantify tvars ts

let check_decl (tps : (string * int) list) (ctors : (string * int) list) (tms : string list) : E.Decl.t -> I.Term.t I.Decl.t result =
  let open E.Decl in
  let to_lookup m x = List.assoc_opt x m in
  let to_member s x = List.mem x s in
  function
  | TpDecl { name; tvar_binders; constructors } -> Util.not_implemented ()
  | TmDecl { name; typ; recursive; body } ->
    Result.bind (check_tp (to_lookup tps) (fun _ -> true) typ) @@
    let binders = quantify [] typ in fun typ ->
    let tms' = if recursive then name :: tms else tms in
    Result.bind (check_tm (to_lookup ctors) (to_member tms') Scope.empty body) @@ fun body ->
    Result.ok @@ I.Decl.(TmDecl { name; typ = (binders, typ); recursive; body = Some body })

let rec check_program (tps : (string * int) list) (ctors : (string * int) list) (tms : string list) : E.Decl.program -> I.Decl.program result =
  function
  | [] -> Result.ok []
  | d :: ds ->
    Result.bind (check_decl tps ctors tms d) @@ fun d -> match d with
    | I.Decl.(TpDecl { name; tvar_binders; constructors }) ->
      Result.bind begin
        check_program
          ((name, List.length tvar_binders) :: tps)
          (List.map (fun I.Decl.({ name; fields }) -> (name, List.length fields)) constructors @ ctors)
          tms
          ds
      end @@ fun ds -> Result.ok @@ d :: ds
      | I.Decl.(TmDecl { name }) ->
        Result.bind (check_program tps ctors (name :: tms) ds) @@ fun ds ->
        Result.ok @@ d :: ds
