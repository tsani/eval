(* Compiles closed syntax into bytecode. *)

open BasicSyntax
open Syntax.Closed
open Bytecode

type label = string

module State = struct
    type t = { label_counter : int; }
end

module Ctx = struct
    type t = {
        refs : (fn_kind * arity) RefMap.t;
        ctors : (index * arity) CtorMap.t;
    }
end

module Compiler = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure (x : 'a) : 'a t = fun _ s -> (s, x)

    (** Sequences compiler actions. *)
    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s -> let (s', x) = m ctx s in k x ctx s'

    (** Synthesizes a fresh label never before seen in the program. *)
    let new_label = fun _ s ->
        let open State in
        let n = s.label_counter in
        let s = { s with label_counter = n + 1 } in
        (s, n)

    let lookup_ctor c : (index * arity) t = fun ctx s ->
        match CtorMap.find_opt c ctx.ctors with
        | None -> Util.invariant "[compile] every ctor has a known arity"
        | Some x -> (s, x)

    let lookup_ref f : (fn_kind * arity) t = fun ctx s ->
        match RefMap.find_opt f ctx.refs with
        | None -> Util.invariant "[compile] every ref has a known arity"
        | Some x -> (s, x)

        (*
    (** Emits some bytecode instructions. *)
    let output b = fun _ s ->
        let open State in
        ({ s with program = Text.cat s.program (fun p -> b @ p)}, ())

    (** Flushes the program construction buffer, emptying it and returning the list of
        instructions. *)
    let flush_program = fun _ s ->
        let open State in
        let p = s.program [] in
        ({ s with program = fun x -> x }, p)
        *)
end

let call_mode_of_fn_kind : fn_kind -> int -> call_mode = function
    | `pure -> fun n -> `pure n
    | `closure -> fun n -> `closure n

let rec term (t : Term.t) : label Text.builder Compiler.t =
    let open Compiler in
    match t with
    | Term.Lit lit -> failwith "todo"
    | Term.App (tH, tS) ->
        bind (spine tS) @@ fun pS ->
        begin match tH with 
        | Term.Var v -> pure @@ Text.cats
            [ pS
            ; var v
            ; if tS = []
              then Text.empty
              else Text.single @@ Instruction.Call `dynamic
            ]
        | Term.Ref f -> 
            bind (lookup_ref f) @@ fun (kind, n) ->
            if List.length tS <> n then Util.invariant "[compile] ref call spine has n elements";
            pure @@ Text.single @@ Instruction.Call (call_mode_of_fn_kind kind n)
        | Term.Const c ->
            bind (lookup_ctor c) @@ fun (i, n) ->
            pure @@ Text.single @@ Instruction.Const { ctor = i; field_count = n }
        | Term.Prim p ->
            pure @@ Text.single @@ Instruction.Prim p
        end
    | Term.Let (rec_flag, t1, t2) ->
        failwith "todo"
    | Term.Match (t, cases) -> failwith "todo"
    | Term.MkClo (theta, n, f) -> failwith "todo"

and spine : Term.spine -> label Text.builder Compiler.t =
    let open Compiler in function
    | [] -> pure Text.empty
    | t :: tS ->
        bind (spine tS) @@ fun pS ->
        bind (term t) @@ fun p ->
        pure @@ Text.cat pS p

and var : var -> label Text.builder = function
    | `bound i -> Text.single @@ Instruction.Load (`param, i)
    | `env i -> Text.single @@ Instruction.Load (`env, i)

let decl (pgm : Bytecode.Program.t) : Closed.Decl.tm -> Bytecode.Program.t =
    let Bytecode.Program.({ well_knowns; functions; top }) = pgm in
    function
    | Closed.Decl.({ name; body; arity }) ->
        (* now this depends on... whether the term being defined is a *pure* function or not
           only pure functions have nonzero arity; IOW things with zero arity need to happen right
           away at program startup and are placed into `functions`. *)
        if arity = 0 then
            (* then the body of the declaration needs to happen right away, and its value is
               stored in the well-known name `name` -- that is, this declaration becomes for a
               so-called "well-known" value. *)
            let p = term body in
            Bytecode.Program.({ well_knowns = name :: well_knowns; functions; top
        else

let program (pgm : Closed.Decl.program) : Bytecode.program =
    List.fold_left decl Bytecode.Program.empty pgm
