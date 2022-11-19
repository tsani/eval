open Syntax
open Type

type unify_error = [
  | `occurs_check of tmvar_name * Type.t
  | `mismatch of Type.t * Type.t (* expected, actual *)
]

type 'a result = (unify_error, 'a) Result.t

let _ = Result.Syntax.(Result.Ok 5 $ fun x -> Result.Ok 5)

(* Extends the given substitution of tmvars to make the given types equal.
 * The interpretation of the given types is: expected, actual.
 *)
let rec types (tmvars : TMVar.sub) : Type.t * Type.t -> TMVar.sub result = function
  | Int, Int -> Result.ok tmvars
  | Arrow (t1, t2), Arrow (t1', t2') ->
    Result.Syntax.(types tmvars (t1, t1') $ fun tmvars -> types tmvars (t2, t2'))
  | TMVar x, t | t, TMVar x -> unify_tmvar tmvars x t
  | Named (c1, ts1), Named (c2, ts2) -> unify_family tmvars (c1, ts1) (c2, ts2)
  | TVar _, _ | _, TVar _ -> raise (Util.Invariant "no free TVars allowed")
  | expected, actual -> Result.error @@ `mismatch (expected, actual)

and unify_family (tmvars : TMVar.sub)
    (c1, ts1 : tp_name * Type.t list) (c2, ts2 : tp_name * Type.t list) : TMVar.sub result =
  match () with
  | _ when c1 <> c2 -> Result.error @@ `mismatch (Named (c1, ts1), Named (c2, ts2))
  | _ when List.length ts1 <> List.length ts2 -> 
    raise (Util.Invariant "type family parameter list lengths must match")
  | _ -> unify_list tmvars @@ List.combine ts1 ts2

(* Sequentially unifies a list of type pairs. *)
and unify_list tmvars : (Type.t * Type.t) list -> TMVar.sub result = function
  | [] -> Result.ok tmvars
  | p :: ts -> Result.Syntax.(types tmvars p $ fun tmvars -> unify_list tmvars ts)

and unify_tmvar (tmvars : TMVar.sub) (x : tmvar_name) (tp : Type.t) : TMVar.sub result =
  match TMVar.lookup tmvars x with
  | `not_found -> raise (Util.Invariant "no free TMVars allowed")
  | `inst tp' -> types tmvars (tp', tp)
  | `uninst when TMVar.chase tmvars tp = TMVar x -> Result.ok tmvars (* unifying a tmvar with itself is a no-op *)
  | `uninst when TMVar.occurs tmvars x tp -> Result.error @@ `occurs_check (x, TMVar.apply_sub tmvars tp)
  | `uninst -> Result.ok (TMVar.extend_sub tmvars ~inst: (Some tp) x)
