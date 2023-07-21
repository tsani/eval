open BasicSyntax
open Syntax
open Internal
open Type

type unify_error = [
  | `occurs_check of tmvar_name * Type.t
  | `mismatch of Type.t * Type.t (* expected, actual *)
]

type 'a result = (unify_error, 'a) Result.t

(* Extends the given substitution of tmvars to make the given types equal.
 * The interpretation of the given types is: expected, actual.
 *)
let rec types (tmvars : TMVar.sub) : Type.t * Type.t -> TMVar.sub result = function
  | Builtin (_, bt1), Builtin (_, bt2) when bt1 = bt2 -> Result.ok tmvars
  | Arrow (_, t1, t2), Arrow (_, t1', t2') ->
    Result.Syntax.(types tmvars (t1, t1') $ fun tmvars -> types tmvars (t2, t2'))
  | TMVar (_, x), t | t, TMVar (_, x) -> unify_tmvar tmvars x t
  | Named (l1, c1, ts1), Named (l2, c2, ts2) -> begin match () with
      | _ when c1 <> c2 -> Result.error @@ `mismatch (Named (l1, c1, ts1), Named (l2, c2, ts2))
      | _ when List.length ts1 <> List.length ts2 -> 
        raise (Util.Invariant "type family parameter list lengths must match")
      | _ -> unify_list tmvars @@ List.combine ts1 ts2
    end
  | TVar _, _ | _, TVar _ -> raise (Util.Invariant "no free TVars allowed")
  | expected, actual -> Result.error @@ `mismatch (expected, actual)

(* Sequentially unifies a list of type pairs. *)
and unify_list tmvars : (Type.t * Type.t) list -> TMVar.sub result = function
  | [] -> Result.ok tmvars
  | p :: ts -> Result.Syntax.(types tmvars p $ fun tmvars -> unify_list tmvars ts)

and unify_tmvar (tmvars : TMVar.sub) (x : tmvar_name) (tp : Type.t) : TMVar.sub result =
  match TMVar.lookup tmvars x with
  | `not_found -> raise (Util.Invariant "no free TMVars allowed")
  | `inst tp' -> types tmvars (tp', tp)
  | `uninst -> match TMVar.chase tmvars tp with
    | TMVar (_, y) when y = x ->
      Result.ok tmvars (* unifying a tmvar with itself does nothing *)
    | tp when TMVar.occurs tmvars x tp ->
      Result.error @@ `occurs_check (x, TMVar.apply_sub tmvars tp)
    | _ ->
      Result.ok (TMVar.extend_sub tmvars ~inst: (Some tp) x)
