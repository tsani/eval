(** Closure conversion.

    Main operations:
        - Transform `Fun` nodes into `MkClo` nodes
        - Distinguish parameter variables from environment variables.
        - Hoist all nested functions into top-level functions

    The core entry point of this module is the function `term`, which closure-converts a term.

    See ../cloco.md
*)

open BasicSyntax
open Syntax

module I = Syntax.Internal
module C = Syntax.Closed
module RawER = I.EnvRen
module ER = C.EnvRen

(** Variables with indices beyond this value are free variables.
    Comparison of an internal syntax variable's index against the watermark determines whether the
    variable is a BVar or an EVar in the closed syntax. *)
type watermark = int

(* A description of a new, top-level function generated by closure conversion. *)
type fn_desc = {
    param_cnt : int;
    body : C.Term.t;
}

module FnMap = Util.StringMap

(* Closure conversion is stateful:
    - as we encounter variables, we update the current environment renaming to include them
    - as we encounter functions, we replace them with MkClo operations that refer to a synthetic
      name -- the _code_ of those functions is then stored in the state.
 *)
module State = struct
    type t = {
        fn_map : fn_desc FnMap.t;
        fn_name_counter : int;
        theta : RawER.t;
    }

    let initial = {
        fn_map = FnMap.empty;
        fn_name_counter = 0;
        theta = ER.empty;
    }
end

module Cloco = struct
    (* Cloco monad. *)
    type 'a t = watermark -> State.t -> State.t * 'a

    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t =
        fun w s -> let (s', x) = m w s in k x w s'

    let (>=>) (f : 'a -> 'b t) (g : 'b -> 'c t) : 'a -> 'c t =
        fun x -> bind (f x) g

    let (>>) (m1 : 'a t) (m2 : 'b t) : 'b t =
        bind m1 (fun _ -> m2)

    let pure x = fun _ s -> (s, x)

    let modify f = fun _ s -> (f s, ())

    let rec traverse (f : 'a -> 'b t) (l : 'a list) : 'b list t = match l with
    | [] -> pure []
    | x :: xs ->
        bind (f x) @@ fun y ->
        bind (traverse f xs) @@ fun ys ->
        pure (y :: ys)
end

(** Adds a new function to the current mapping, generating a new name for it. *)
let add_function (d : fn_desc) : tm_name Cloco.t = fun _ s ->
    let name = "%closure_" ^ string_of_int s.fn_name_counter in
    ( { s with
          fn_name_counter = s.fn_name_counter + 1;
          fn_map = FnMap.add name d s.fn_map;
      }
    , name
    )

(** Gets the current watermark. *)
let get_watermark : watermark Cloco.t = fun w s -> (s, w)

(** Performs the given action with the current watermark shadowed by the given value. *)
let with_watermark (w : watermark) (m : 'a Cloco.t) : 'a Cloco.t = fun _ s -> m w s

let get_env_ren : RawER.t Cloco.t = fun w s -> (s, s.theta)

let put_env_ren (theta : RawER.t) : unit Cloco.t = fun _ s -> { s with theta }, ()

(* Whenever we encounter a variable, we compare it to the current watermark.
   If it's less than the current watermark, the variable is a bound variable. Easy.
   If it's greater than the current watermark, the variable is free so we _subtract_ the current
   watermark from it to obtain an index that would make sense outside the current function.
   This adjusted index is then inserted into the current environment renaming.
   When we exit the current function, we have to examine the environment renaming that came out,
   since the indices stored inside it will then need to be reindexed. *)

(** Inserts an index into the current environment renaming.
    Returns the index _into the renaming_ of the given index. *)
let er_insert (i : index) : index Cloco.t =
    let open Cloco in
    bind get_env_ren @@ fun theta ->
    let (theta', j) = ER.insert i theta in
    bind (put_env_ren theta') @@ fun _ ->
    pure j

(* Closure-converts the index of a variable according to the active watermark, extending the
   current environment renaming in case the index refers to an environment variable. *)
let index (i : index) : C.var Cloco.t =
    let open Cloco in
    bind get_watermark @@ fun w ->
    if i < w then pure (`bound i) else
    bind (er_insert (i - w)) @@ fun j ->
    pure (`env j)

(** Closure-converts an environment renaming. Each index appearing in the ER is reindexed according
     to the current watermark, updating the current (raw) environment renaming. *)
let env_ren (theta : RawER.t) : ER.t Cloco.t = Cloco.traverse index theta

(** Runs the given action with an empty environment renaming, reindexing the resulting environment
    renaming in the presence of the outer one after.
    Returns the reindexed*)
let er_pushed (m : 'a Cloco.t) : (ER.t * 'a) Cloco.t =
    let open Cloco in
    bind get_env_ren @@ fun theta -> (* save outer ER *)
    bind (put_env_ren ER.empty) @@ fun _ ->
    bind m @@ fun x ->
    bind get_env_ren @@ fun theta' -> (* save inner ER *)
    bind (put_env_ren theta) @@ fun _ -> (* restore outer ER *)
    (* reindex the inner ER *)
    bind (env_ren theta') @@ fun theta' ->
    pure (theta', x)

(* Closure-converts the head of an application according to a watermark, extending the given
   environment renaming in the case for a variable. *)
let head : I.Term.head -> C.Term.head Cloco.t =
    let open Cloco in
    function
    | I.Term.Var (_, i) ->
        bind (index i) @@ fun x -> pure (C.Term.Var x)
    | I.Term.Const (_, c) -> pure (C.Term.Const c)
    | I.Term.Ref (_, r) -> pure (C.Term.Ref r)
    | I.Term.Prim (_, p) -> pure (C.Term.Prim p)

(* Closure-converts a term. *)
let rec term : I.Term.t -> C.Term.t Cloco.t =
    let open Cloco in
    function
    | I.Term.Fun _ as e ->
        let xs, e = I.Term.collapse_funs e in
        let w' = List.length xs in (* the watermark to use within the function body *)
        bind (er_pushed @@ with_watermark w' @@ term e) @@ fun (theta, e') ->
        bind (add_function { param_cnt = w'; body = e' }) @@ fun f ->
        pure @@ C.Term.MkClo (theta, w', f)

    | I.Term.Let (_, _, (_, x), e1, e2) -> failwith "todo"

    | I.Term.App (_, tH, tS) ->
            bind (head tH) @@ fun tH ->
            bind (spine tS) @@ fun tS ->
            pure (C.Term.App (tH, tS))

and spine (tS : I.Term.spine) : C.Term.spine Cloco.t = Cloco.traverse term tS


(* fun x -> let a = f _0 in ---- clo [] 1 @@ let a = f 0b in
   fun y -> let b = g _1 _0 in -- clo [0b] 1 @@ let b = g 0e 0b in
   fun z -> h _3 _2 _1 _0 ----------- clo [0b; 1b; 0e] @@ h 1e y 0e 0b *)

