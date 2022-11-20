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
end

type 'a result = (Error.t, 'a) Result.t

(* Scopechecks a type, possibly in a context of bound type variables.
   If the tvar context is present, then any TVar appearing in the type must appear in the context.
   Otherwise, TVars may appear wherever in the type.

   This is to allow using `check_tp` both for checking the types in type
   definitions as well as the types associated to terms, which may involve
   implicitly quantified variables.
*)
let rec check_tp (tps : tp_name list) (tvars : tvar_name list option) : E.Type.t -> I.Type.t result =
  let check_tvar = match tvars with
    | None -> fun a -> Result.ok a
    | Some tvars -> fun a -> if List.mem a tvars then Result.ok a else Result.error Error.(UnboundTypeVariable a)
  in
  function
  | E.Type.Int -> Result.ok I.Type.Int
  | E.Type.Arrow (t1, t2) ->
    Result.bind (check_tp tps tvars t1) @@ fun t1 ->
    Result.bind (check_tp tps tvars t2) @@ fun t2 ->
    Result.ok @@ I.Type.Arrow (t1, t2)

  | E.Type.TVar a ->
    Result.bind (check_tvar a) @@ fun a ->
    Result.ok (I.Type.TVar a)

  | E.Type.Named (a, _) when not (List.mem a tps) -> Result.error Error.(UnknownNamedType a)
  | E.Type.Named (a, ts) ->
    Result.traverse (check_tp tps tvars) ts @@ fun ts ->
    Result.ok @@ I.Type.Named (a, ts)

