(* Compiles closed syntax into bytecode. *)

open BasicSyntax
open Syntax.Closed
open Bytecode
open CompilerCommon
open RuntimeInfo

type label = string

module State = struct
    type t = { label_counter : int; }

    let initial = { label_counter = 0 }
end

module Ctx = ProgramInfo

module Compiler = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure (x : 'a) : 'a t = fun _ s -> (s, x)

    (** Sequences compiler actions. *)
    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s -> let (s', x) = m ctx s in k x ctx s'

    let map (f : 'a -> 'b) (m : 'a t) : 'b t = fun ctx s ->
        let (s', x) = m ctx s in (s', f x)

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

    let lookup_ref f : ProgramInfo.ref_spec t = fun ctx s ->
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

let call_mode_of_ref (r : ProgramInfo.ref_spec) : call_mode =
    match r.kind with
    | `func -> `func r.arity
    | `well_known -> `closure r.arity
    | `closure_body -> Util.invariant "[compile] calls to closure bodies are not possible"

let literal = function
    | IntLit n -> Text.single @@ Instruction.Push (`param, `integer n)
    | _ -> Util.not_implemented ()

let var : var -> label Text.builder = function
    | `bound i -> Text.single @@ Instruction.Load (`param i)
    | `env i -> Text.single @@ Instruction.Load (`env i)

let rec env_ren = let open Compiler in function
    | [] -> pure @@ Text.empty
    | v :: vs ->
        (* this happens 'backwards' because we need to arrange that the value to be stored in
            position 0 of the environment is at the top of the stack, but the variable whose value
            should go there is at index 0 in the environment renaming. *)
        bind (env_ren vs) @@ fun pS -> pure @@ Text.cat pS (var v)

let rec term (t : Term.t) : label Text.builder Compiler.t =
    let open Compiler in
    match t with
    | Term.Lit lit -> pure @@ literal lit
    | Term.App (tH, tS) ->
        bind (spine tS) @@ fun pS ->
        begin map (Text.cat pS) @@ match tH with
        | Term.Var v -> pure @@ Text.cats
            [ var v
            ; if tS = []
              then Text.empty
              else Text.single @@ Instruction.Call `dynamic
            ]
        | Term.Ref f -> 
            bind (lookup_ref f) @@ fun ref_spec ->
            if List.length tS <> ref_spec.arity then
                Util.invariant "[compile] ref call spine has n elements";
            pure @@ Text.cat
                (Text.single @@ Instruction.Push (`param, `address ref_spec.address))
                (Text.single @@ Instruction.Call (call_mode_of_ref ref_spec))
        | Term.Const c ->
            bind (lookup_ctor c) @@ fun (i, n) ->
            pure @@ Text.single @@ Instruction.Const { ctor = i; field_count = n }
        | Term.Prim p ->
            pure @@ Text.single @@ Instruction.Prim p
        end
    | Term.Let (Rec, t1, t2) -> failwith "recursive let bindings not implemented"
    | Term.Let (NonRec, t1, t2) ->
        bind (term t1) @@ fun p1 ->
        bind (term t2) @@ fun p2 ->
            pure @@ Text.cats [ p1; p2;
                Text.single @@ Instruction.Pop (`param, 1)
                (* drop the value of t1 from the stack, since function exit only knows to clean up
                   params *)
            ]
    | Term.Match (t, cases) -> failwith "todo match"
    | Term.MkClo (theta, n, f) ->
        bind (lookup_ref f) @@ fun ProgramInfo.({ address }) ->
        bind (env_ren theta) @@ fun p ->
            pure @@ Text.cats [
                p;
                Text.single @@ Instruction.Push (`param, `address address);
                Text.single @@ Instruction.(MkClo { env_size = n });
            ]

and spine : Term.spine -> label Text.builder Compiler.t =
    let open Compiler in function
    | [] -> pure Text.empty
    | t :: tS ->
        bind (spine tS) @@ fun pS ->
        bind (term t) @@ fun p ->
        pure @@ Text.cat pS p

let return_mode_of_ref r = match r.ProgramInfo.kind with
    | `well_known -> Util.invariant "[compile] well-known values do not define functions"
    | `func -> `func
    | `closure_body -> `closure

let decl (ctx : Ctx.t) (pgm : Bytecode.Program.t) : Decl.tm -> Bytecode.Program.t =
    let Bytecode.Program.({ well_knowns; functions; top }) = pgm in
    function
    | Decl.({ name; body; arity }) ->
        let ref_spec = match RefMap.find_opt name ctx.refs with
            | Some x -> x
            | None -> Util.invariant "[compile] ProgramInfo.t contains all functions"
        in
        if ref_spec.arity <> arity then Util.invariant "[compile] arity mismatch";
        (* now this depends on... whether the term being defined is a *pure* function or not
           Only pure functions have nonzero arity.
           *)
        let (s', p) = term body ctx State.initial in
        if arity = 0 then
            (* then the body of the declaration needs to happen right away, and its value is
               stored in the well-known name `name` -- that is, this declaration becomes for a
               so-called "well-known" value. *)
            Bytecode.Program.({
                well_knowns = name :: well_knowns;
                functions;
                top = Text.cat p (Text.single @@ Instruction.Store name)
            })
        else
            Bytecode.Program.({
                well_knowns;
                functions =
                    ( name
                    , Text.(
                          build @@ cat p (single @@ Instruction.Ret (return_mode_of_ref ref_spec))
                      )
                    ) :: functions;
                top;
            })

let program (ctx : Ctx.t) (pgm : Decl.program) : Bytecode.Program.t =
    List.fold_left (decl ctx) Bytecode.Program.empty pgm
