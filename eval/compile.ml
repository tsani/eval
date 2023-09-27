(* Compiles closed syntax into bytecode. *)

open BasicSyntax
open Syntax.Closed
open Bytecode

type label = string

module State = struct
    type t = {
        label_counter : int;
        program : label Program.builder;
    }
end

module Ctx = struct
    type t = unit
end

module Compiler = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    (** Sequences compiler actions. *)
    let bind m k = fun ctx s -> let (s', x) = m ctx s in k x s'

    (** Synthesizes a fresh label never before seen in the program. *)
    let new_label = fun _ s ->
        let open State in
        let n = s.label_counter in
        let s = { s with label_counter = n + 1 } in
        (s, n)

    (** Emits some bytecode instructions. *)
    let output b = fun _ s ->
        let open State in
        ({ s with program = Program.cat s.program (fun p -> b @ p)}, ())

    (** Flushes the program construction buffer, emptying it and returning the list of
        instructions. *)
    let flush_program = fun _ s ->
        let open State in
        let p = s.program [] in
        ({ s with program = fun x -> x }, p)
end

let rec term (t : Term.t) : label Program.builder Compiler.t = match e with
    | Term.Lit lit -> failwith "todo"
    | Term.App (tH, tS) -> failwith "todo"
    | Term.Let (rec_flag, t1, t2) -> failwith "todo"
    | Term.Match (t, cases) -> failwith "todo"
    | Term.MkClo (rho, n, f) -> failwith "todo"
