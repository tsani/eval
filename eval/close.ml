(** Closure conversion.

    Main operations:
        - Transform `Fun` nodes into `MkClo` nodes
        - Distinguish parameter variables from environment variables.
        - Hoist all nested functions into top-level functions

    The core entry point of this module is the function `program`, which closure-converts the body
    of every term declaration in a signature. (And throws away all type declarations.)

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
    arity : arity;
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
        fns : fn_desc FnMap.t;
        fn_name_counter : int;
        theta : RawER.t;
    }

    let initial = {
        fns = FnMap.empty;
        fn_name_counter = 0;
        theta = ER.empty;
    }
end

module Ctx = struct
    type t = {
        watermark : watermark;
        ctors : (index * arity) CtorMap.t;
        refs : (fn_kind * arity) RefMap.t;
    }

    let initial = {
        watermark = 0;
        ctors = CtorMap.empty;
        refs = RefMap.empty;
    }
end

module ProgramInfo = struct
    type t = {
        fns : fn_desc FnMap.t;
        ctors : (index * arity) CtorMap.t;
        refs : (fn_kind * arity) RefMap.t;
    }

    let initial = {
        fns = FnMap.empty;
        ctors = CtorMap.empty;
        refs = RefMap.empty;
    }
end

let extend_refs_with_closures (fns : fn_desc FnMap.t) (refs : (fn_kind * arity) RefMap.t)
        : (fn_kind * arity) RefMap.t =
    RefMap.union (fun _ _ _ -> Util.invariant "[close] all ref names are unique")
        refs
        (FnMap.to_seq fns |> Seq.map (fun (f, d) -> (f, (`closure, d.arity))) |> RefMap.of_seq)

type arity_lookup = [ `ref of string | `ctor of string ]

module Cloco = struct
    (* Cloco monad. *)
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t =
        fun ctx s -> let (s', x) = m ctx s in k x ctx s'

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

    (** Adds a new function to the current mapping, generating a new name for it. *)
    let add_function (d : fn_desc) : tm_name t = fun _ s ->
        let name = "%closure_" ^ string_of_int s.fn_name_counter in
        ( { s with
              fn_name_counter = s.fn_name_counter + 1;
              fns = FnMap.add name d s.fns;
          }
        , name
        )

    (** Gets the current watermark. *)
    let get_watermark : watermark t = fun ctx s -> (s, ctx.watermark)

    (** Performs the given action with the current watermark shadowed by the given value. *)
    let with_watermark (w : watermark) (m : 'a t) : 'a t =
        fun ctx s -> m { ctx with watermark = w } s

    (** Performs the given action with the watermark increased by the given value. *)
    let bumped_watermark (w : watermark) (m : 'a t) : 'a t =
        fun ctx s -> m { ctx with watermark = ctx.watermark + w } s

    let lookup_ctor_arity c : arity t = fun ctx s ->
        (s, match CtorMap.find_opt c ctx.ctors with
            | None -> Util.invariant "[close] all constructors have known arities"
            | Some (_, n) -> n)

    let lookup_ref_arity f : arity t = fun ctx s ->
        (s, match RefMap.find_opt f ctx.refs with
            | None -> Util.invariant "[close] all refs have known arities"
            | Some (_, n) -> n)

    let get_env_ren : RawER.t t = fun w s -> (s, s.theta)

    let put_env_ren (theta : RawER.t) : unit t = fun _ s -> { s with theta }, ()
end

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

(** Closure-converts the index of a variable according to the active watermark, extending the
    current environment renaming in case the index refers to an environment variable. *)
let index (i : index) : C.var Cloco.t =
    let open Cloco in
    bind get_watermark @@ fun w ->
    if i < w then pure (`bound i) else
    bind (er_insert (i - w)) @@ fun j ->
    pure (`env j)

(** Closure-converts an environment renaming. Each index appearing in the given ER is reindexed
    according to the current watermark, updating the current (raw) environment renaming. *)
let env_ren (theta : RawER.t) : ER.t Cloco.t = Cloco.traverse index theta

(** Runs the given action with an empty environment renaming, reindexing the resulting environment
    renaming in the presence of the outer one after.
    Returns the reindexed environment renaming obtained from running the inner computation. *)
let er_pushed (m : 'a Cloco.t) : (ER.t * 'a) Cloco.t =
    let open Cloco in
    bind get_env_ren @@ fun theta -> (* save outer ER *)
    bind (put_env_ren ER.empty) @@ fun _ -> (* flush active ER *)
    bind m @@ fun x -> (* run inner computation *)
    bind get_env_ren @@ fun theta' -> (* save inner ER *)
    bind (put_env_ren theta) @@ fun _ -> (* restore outer ER *)
    bind (env_ren theta') @@ fun theta' -> (* reindex saved inner ER *)
    pure (theta', x)

(* Closure-converts the head of an application according to a watermark, extending the given
   environment renaming in the case for a variable. *)
let head : I.Term.head -> C.Term.head Cloco.t =
    let open Cloco in function
    | I.Term.Var (_, i) ->
        bind (index i) @@ fun x -> pure (C.Term.Var x)
    | I.Term.Const (_, c) -> pure (C.Term.Const c)
    | I.Term.Ref (_, r) -> pure (C.Term.Ref r)
    | I.Term.Prim (_, p) -> pure (C.Term.Prim p)

let bump_of_rec_flag = function
    | Rec -> Cloco.bumped_watermark 1
    | NonRec -> fun x -> x

let rec pattern : I.Term.pattern -> C.Term.pattern = function
    | I.Term.LiteralPattern (_, l) -> C.Term.LiteralPattern l
    | I.Term.WildcardPattern _ -> C.Term.WildcardPattern
    | I.Term.VariablePattern (_, _) -> C.Term.VariablePattern
    | I.Term.ConstPattern (_, c, ps) -> C.Term.ConstPattern (c, List.map pattern ps)

(** Eta-expands an application of a head to account for a partial constructor or ref application.
    expand tH n tS requires:
        - n is the arity of tH
    Then n - |tS| is the number of abstractions that are generated. *)
let eta_expand tH n tS =
    let var i = I.Term.(App (fake_loc, Var (fake_loc, i), [])) in
    let fn t = I.Term.(Fun (fake_loc, (fake_loc, "!"), t)) in
    (* idea: count down from n as we traverse tS
       At each step that we still have terms in the spine, move them to tS'.
       When we run out of terms in the spine but there is remaining arity, generate abstractions.
     *)
    let rec go n tS tS' return = match n, tS with
    | 0, [] -> return tS'
    | n, [] -> go (n-1) [] (var (n-1) :: tS') (fun t -> fn (return t))
    | 0, t :: tS -> go 0 tS (t :: tS') return
    | n, t :: tS -> go (n-1) tS (t :: tS') return
    in
    go n tS [] (fun tS' -> I.Term.(App (fake_loc, tH, List.rev tS')))

(* Example:
    expand_const c 3 [a]
    -> go 3 [a] [] done
    -> go 2 [] [a] done
    -> go 1 [] [v 1; a] (fn . done)
    -> go 0 [] [v 0; v 1; a] (fn . fn . done)
    -> (fn . fn . done) [v 0; v 1; a]
    -> `Fun ! ! -> c [a; v 1 ; v 0]` as required! *)

(* Closure-converts a term. *)
let rec term : I.Term.t -> C.Term.t Cloco.t =
    let open Cloco in
    (* Closure-convert a term that is KNOWN to be a function. *)
    let func e =
        let xs, e = I.Term.collapse_funs e in
        let w' = List.length xs in (* the watermark to use within the function body *)
        bind (er_pushed @@ with_watermark w' @@ term e) @@ fun (theta, e') ->
        bind (add_function { arity = w'; body = e' }) @@ fun f ->
        pure @@ C.Term.MkClo (theta, w', f)
    in
    (* Closure-convert an application. *)
    let app tH tS =
        bind (head tH) @@ fun tH ->
        bind (spine tS) @@ fun tS ->
        pure (C.Term.App (tH, tS))
    in
    let arity_of_head = function
        | I.Term.Var _ -> pure `unknown
        | I.Term.Const (_, c) -> bind (lookup_ctor_arity c) @@ fun n -> pure @@ `known n
        | I.Term.Ref (_, r) -> bind (lookup_ref_arity r) @@ fun n -> pure @@ `known n
        | I.Term.Prim (_, p) -> pure @@ `known (Prim.arity p)
    in
    function
    | I.Term.Fun _ as e -> func e
    | I.Term.Let (_, rec_flag, (_, x), e1, e2) ->
        bind (bump_of_rec_flag rec_flag @@ term e1) @@ fun e1' ->
        bind (bumped_watermark 1 @@ term e2) @@ fun e2' ->
        pure @@ C.Term.Let (rec_flag, e1', e2')
    | I.Term.Match (_, e, cases) ->
        bind (term e) @@ fun e' ->
        bind (traverse case cases) @@ fun cases' ->
        pure (C.Term.Match (e', cases'))
    | I.Term.App (_, tH, tS) ->
        bind (arity_of_head tH) @@ function
        | `unknown -> app tH tS
        | `known n ->
            match eta_expand tH n tS with
            | I.Term.Fun _ as e -> func e
            | I.Term.App (_, tH, tS) -> app tH tS

and case : I.Term.case -> C.Term.case Cloco.t =
    let open Cloco in function
    | I.Term.Case (_, p, e) ->
        let p' = pattern p in
        bind (bumped_watermark (I.Term.count_pattern_vars p) @@ term e) @@ fun e' ->
        pure (C.Term.Case (p', e'))

and spine (tS : I.Term.spine) : C.Term.spine Cloco.t = Cloco.traverse term tS

let tm_decl : I.Term.t I.Decl.tm -> (fn_kind * C.Decl.tm) Cloco.t =
    let var i = C.Term.(App (Var (`bound i), [])) in
    let rec gen_spine n = if n = 0 then [] else var (n-1) :: gen_spine (n-1) in
    function
    | I.Decl.({ body = None }) -> failwith "todo"
    | I.Decl.({ name; rec_flag; body = Some body }) ->
        Cloco.bind (bump_of_rec_flag rec_flag @@ term body) @@ function
        | C.Term.MkClo (theta, n, f) ->
            if ER.is_empty theta then
                (* When the closure has an empty environment renaming, then the closure is
                   degenerate: it doesn't actually capture any environment variables.
                    In this case, we can omit the MkClo operation and immediately call `f`. *)
                Cloco.pure @@ (
                    `pure,
                    C.Decl.({
                        name;
                        body = C.Term.(App (Ref f, gen_spine n));
                        arity = n;
                    })
                )
            else
                Cloco.pure @@ (
                    `closure,
                    C.Decl.({
                        name;
                        body = C.Term.MkClo (theta, n, f);
                        arity = 0;
                    })
                )

        | body ->
            (* Otherwise, the definition is considered to not (statically) define a
               function. *)
            Cloco.pure @@ (
                `pure,
                C.Decl.({
                    name;
                    body;
                    arity = 0;
                })
            )

(** Converts a list of functions emitted during closure conversion into a list of genuine function
    declarations. *)
let declare_fns (fns : fn_desc FnMap.t) : C.Decl.tm list =
    FnMap.to_seq fns
    |> Seq.map begin function
        | (f, d : tm_name * fn_desc) -> C.Decl.({ name = f; body = d.body; arity = d.arity })
    end
    |> List.of_seq

let rec program : ProgramInfo.t ->  I.Decl.program -> ProgramInfo.t * C.Decl.program =
    let open Cloco in fun pgmInfo -> function
    | [] -> (pgmInfo, [])
    | d :: ds -> match d with
        (* we don't need type declarations anymore, except for knowing the arities of constructors *)
        | I.Decl.(TpDecl { constructors }) ->
            let pgmInfo =
                { pgmInfo with ctors =
                    constructors
                    |> List.map (fun I.Decl.({ name; fields }) -> (name, List.length fields))
                    |> List.fold_left
                        (fun (i, ctors) (c, n) -> (i + 1, CtorMap.add c (i, n) ctors))
                        (0, pgmInfo.ctors)
                    (* we number all the constructors in each type because the compiler will use
                       these numbers to identify / represent the constructors later *)
                    |> snd
                }
            in
            program pgmInfo ds

        | I.Decl.TmDecl d' ->
            let (final_state, (fn_kind, d)) =
                tm_decl d' Ctx.({
                    initial with
                    (* closure conversion of a term needs to know the arity of each ref and
                       constructor *)
                    ctors = pgmInfo.ProgramInfo.ctors;
                    refs = pgmInfo.ProgramInfo.refs;
                }) State.initial
            in
            (* it emits a list of functions (closure bodies) to hoist to the top level
               thru its final state *)
            let closure_decls = declare_fns final_state.fns in
            let pgmInfo, ds =
                program {
                    pgmInfo with
                    refs = pgmInfo.refs
                        |> RefMap.add d.name (fn_kind, d.arity)
                        |> extend_refs_with_closures final_state.fns
                } ds
            in
            (pgmInfo, closure_decls @ d :: ds)
