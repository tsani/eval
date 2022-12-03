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
  type content =
    | UnboundTypeVariable of tvar_name
    | UnknownNamedType of tp_name
    | BadArity of { expected : int; actual : int; tp_name : string }
    | BadConstructorArity of { expected : int; actual : int; ctor_name : string }
    | UnboundVariable of var_name
    | UnboundConstructor of ctor_name
    | DuplicateTVarBinders of tvar_name list

  type t = Loc.span * content
  let make s c = (s, c)

  let print ppf (loc, content) =
    let open Format in
    let print_content ppf = function
      | UnboundTypeVariable a -> fprintf ppf "unbound type variable %s" a
      | UnknownNamedType a -> fprintf ppf "unknown named type %s" a
      | BadArity { expected; actual; tp_name } ->
        fprintf ppf "wrong number of arguments for type constructor %s; expected %d, but got %d"
          tp_name expected actual
      | BadConstructorArity { expected; actual; ctor_name } ->
        fprintf ppf "wrong number of arguments for constructor %s; expected %d, but got %d"
          ctor_name expected actual
      | UnboundVariable x ->
        fprintf ppf "unbound variable %s" x
      | UnboundConstructor c ->
        fprintf ppf "unbound constructor %s" c
      | DuplicateTVarBinders xs ->
        fprintf ppf "duplicate type variable binders in declaration: %a"
          (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf ", ") pp_print_string) xs
    in
    fprintf ppf "%a: scopecheck error: @[%a@]" Loc.print loc.Loc.Span.start print_content content
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
  (* Any type coming from external syntax was literally present in the source
     file, since no inference of any kind has happened yet. Therefore, any
     location in an external syntax type is given the `literal qualifier when
     translating to internal syntax. *)
  function
  | E.Type.Builtin (loc, bt) ->
    Result.ok (I.Type.Builtin (`literal loc, bt))
  | E.Type.Arrow (loc, t1, t2) ->
    Result.bind (check_tp lookup_tp lookup_tvar t1) @@ fun t1 ->
    Result.bind (check_tp lookup_tp lookup_tvar t2) @@ fun t2 ->
    Result.ok @@ I.Type.Arrow (`literal loc, t1, t2)

  | E.Type.TVar (loc, a) when lookup_tvar a -> Result.ok (I.Type.TVar (`literal loc, a))
  | E.Type.TVar (loc, a) -> Result.error @@ Error.(make loc @@ UnboundTypeVariable a)

  | E.Type.Named (loc, a, ts) -> match lookup_tp a with
    | None -> Result.error @@ Error.(make loc @@ UnknownNamedType a)
    | Some n ->
      let k = List.length ts in
      if k <> n then
        Result.error @@ Error.(make loc @@ BadArity { expected = n; actual = k; tp_name = a })
      else
        Result.(bind @@ traverse (check_tp lookup_tp lookup_tvar) ts) @@ fun ts ->
        Result.ok @@ I.Type.Named (`literal loc, a, ts)

let rec check_pattern lookup_ctor scope = function
  | E.Term.LiteralPattern (loc, lit) ->
    Result.ok @@ (scope, I.Term.LiteralPattern (loc, lit))
  | E.Term.VariablePattern (loc, x) -> Result.ok @@ (Scope.extend scope x, I.Term.VariablePattern (loc, x))
  | E.Term.WildcardPattern loc -> Result.ok @@ (scope, I.Term.WildcardPattern loc)
  | E.Term.ConstPattern (loc, ctor_name, pat_spine) ->
    match lookup_ctor ctor_name with
    | None -> Result.error @@ Error.(make loc @@ UnboundConstructor ctor_name)
    | Some n ->
      let k = List.length pat_spine in
      if n <> k then
        Result.error @@ Error.(make loc @@ BadConstructorArity { ctor_name; actual = k; expected = n })
      else
        Result.bind (check_pattern_spine lookup_ctor scope pat_spine) @@ fun (scope, pat_spine) ->
        Result.ok (scope, I.Term.ConstPattern (loc, ctor_name, pat_spine))

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
  | E.Term.Lit (loc, lit) ->
    Result.ok @@ I.Term.Lit (loc, lit)
  | E.Term.Var (loc, x) -> begin match Scope.index_of x scope with
    | Some i -> Result.ok @@ I.Term.Var (loc, i)
    | None when lookup_tm x -> Result.ok @@ I.Term.Ref (loc, x)
    | _ -> Result.error Error.(make loc @@ UnboundVariable x)
  end
  | E.Term.Fun (loc, (loc_x, x), e) ->
    Result.bind (check_tm lookup_ctor lookup_tm (Scope.extend scope x) e) @@ fun e ->
    Result.ok @@ I.Term.Fun (loc, (loc_x, x), e)
  | E.Term.App (loc, e1, e2) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e1) @@ fun e1 ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e2) @@ fun e2 ->
    Result.ok @@ I.Term.App (loc, e1, e2)
  | E.Term.Let (loc, rec_flag, (loc_x, x), e1, e2) ->
    let scope1 = match rec_flag with
      | NonRec -> scope
      | Rec -> Scope.extend scope x
    in
    Result.bind (check_tm lookup_ctor lookup_tm scope1 e1) @@ fun e1 ->
    Result.bind (check_tm lookup_ctor lookup_tm (Scope.extend scope x) e2) @@ fun e2 ->
    Result.ok @@ I.Term.Let (loc, rec_flag, (loc_x, x), e1, e2)
  | E.Term.Const (loc, ctor_name, _) when None = lookup_ctor ctor_name ->
    Result.error Error.(make loc @@ UnboundConstructor ctor_name)
  | E.Term.Const (loc, ctor_name, es) ->
    Result.(bind @@ traverse (check_tm lookup_ctor lookup_tm scope) es) @@ fun es ->
    Result.ok @@ I.Term.Const (loc, ctor_name, es)
  | E.Term.Match (loc, e, cases) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope e) @@ fun e ->
    Result.(bind @@ traverse (check_case lookup_ctor lookup_tm scope) cases) @@ fun cases ->
    Result.ok @@ I.Term.Match (loc, e, cases)

and check_case lookup_ctor lookup_tm scope = function
  | Case (loc, pat, body) ->
    Result.bind (check_pattern lookup_ctor scope pat) @@ fun (scope, pat) ->
    Result.bind (check_tm lookup_ctor lookup_tm scope body) @@ fun body ->
    Result.ok @@ I.Term.Case (loc, pat, body)

let rec quantify tvars = function
  | E.Type.Builtin _ -> tvars
  | E.Type.Arrow (_, t1, t2) -> List.fold_left quantify tvars [t1; t2]
  | E.Type.TVar (_, a) -> a :: tvars
  | E.Type.Named (_, _, ts) -> List.fold_left quantify tvars ts

(** Finds all elements of the given list that appear in it more than once. *)
let find_duplicates l = l |> List.filter begin fun x ->
    [x] <> List.filter (fun y -> x = y) l
  end

let check_ctor
    (owner_name : tp_name)
    (lookup_tp : tp_name -> int option)
    (lookup_tvar : tvar_name -> bool) : E.Decl.ctor -> I.Decl.ctor result =
  fun E.Decl.({ name; fields; loc }) ->
  Result.(bind @@ traverse (check_tp lookup_tp lookup_tvar) fields) @@ fun fields ->
  Result.ok @@ I.Decl.({
      name;
      fields;
      owner_name;
      loc;
    })

let check_decl
    (tps : (string * int) list)
    (ctors : (string * int) list)
    (tms : string list) : E.Decl.t -> I.Term.t I.Decl.t result =
  let open E.Decl in
  let to_lookup m x = List.assoc_opt x m in
  let to_member s x = List.mem x s in
  function
  | TpDecl { loc; name; tvar_binders; constructors } ->
    Result.bind begin match find_duplicates tvar_binders with
      | [] -> Result.ok ()
      (* not allowed to have duplicate tvar binders *)
      | dupes -> Result.error Error.(make loc @@ DuplicateTVarBinders dupes)
    end @@ fun () ->
    let tps = (name, List.length tvar_binders) :: tps in
    Result.(bind @@ traverse (check_ctor name (to_lookup tps) (to_member tvar_binders)) constructors) @@
    fun constructors ->
    Result.ok @@ I.Decl.(TpDecl { name; tvar_binders; constructors; loc })

  | TmDecl { loc; name; typ; recursive; body } ->
    Result.bind begin
      match typ with
      | Some typ ->
        let binders = quantify [] typ in
        check_tp (to_lookup tps) (fun _ -> true) typ |> Result.map (fun x -> Some (binders, x))
      | None -> Result.ok None
    end @@ fun typ ->
    let tms' = if recursive then name :: tms else tms in
    Result.bind (check_tm (to_lookup ctors) (to_member tms') Scope.empty body) @@ fun body ->
    Result.ok @@ I.Decl.(TmDecl { loc; name; typ; recursive; body = Some body })

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
