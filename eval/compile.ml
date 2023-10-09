(* Compiles closed syntax into bytecode. *)

open BasicSyntax
open Syntax.Closed
open Bytecode
open CompilerCommon
open RuntimeInfo

module State = struct
    type t = { label_counter : int; }

    let initial = { label_counter = 0 }
end

(* Maps variable indices to stack indices. *)
module Ren = struct
    type t = int list
    let empty = []
    let shifted k = List.map (fun x -> x + k)
    let extended rho = 0 :: shifted 1 rho

    let lookup rho i = match List.nth_opt i rho with
        | None -> Util.invariant "[compile] every variable is mapped in the renaming"
        | Some x -> x

    let rec extended_by n rho = match n with
        | 0 -> rho
        | n -> extended_by (n-1) (extended rho)
end

module Ctx = struct
    type t = {
        info : ProgramInfo.t;
        var_ren : Ren.t;
    }

    let initial info = { info; var_ren = Ren.empty }
end

module Compiler = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure (x : 'a) : 'a t = fun _ s -> (s, x)

    (** Sequences compiler actions. *)
    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s -> let (s', x) = m ctx s in k x ctx s'

    let with_ren f m = fun ctx s -> m Ctx.({ ctx with var_ren = f ctx.var_ren }) s

    let rec traverse (f : 'a -> 'b t) : 'a list -> 'b list t = function
        | [] -> pure []
        | x :: xs ->
            bind (f x) @@ fun y ->
            bind (traverse f xs) @@ fun ys ->
            pure (y :: ys)

    let traverse_rev (f : 'a -> 'b t) : 'a list -> 'b list t =
        let rec go acc = function
            | [] -> pure acc
            | x :: xs ->
                bind (f x) @@ fun y ->
                go (y :: acc) xs
        in
        go []

    let map (f : 'a -> 'b) (m : 'a t) : 'b t = fun ctx s ->
        let (s', x) = m ctx s in (s', f x)

    (** Synthesizes a fresh label never before seen in the program. *)
    let new_label = fun _ s ->
        let open State in
        let n = s.label_counter in
        let s = { label_counter = n + 1 } in
        (s, n)

    let lookup_ctor c : ProgramInfo.ctor_spec t = fun ctx s ->
        match CtorMap.find_opt c ctx.info.ctors with
        | None -> Util.invariant "[compile] every ctor has a known arity"
        | Some x -> (s, x)

    let lookup_ref f : ProgramInfo.ref_spec t = fun ctx s ->
        match RefMap.find_opt f ctx.info.refs with
        | None -> Util.invariant "[compile] every ref has a known arity"
        | Some x -> (s, x)
end

let call_mode_of_ref (r : ProgramInfo.ref_spec) =
    match !(r.kind) with
    | `func -> fun n -> `func n
    | `well_known -> fun n -> `closure n
    | `closure_body -> Util.invariant "[compile] calls to closure bodies are not possible"

let literal = function
    | IntLit n -> Text.single @@ Instruction.Push (`param, `integer n)
    | _ -> Util.not_implemented ()

let var (v : var) : 'l Text.builder Compiler.t = fun ctx s ->
    (s, match v with
        | `bound i -> Text.single @@ Instruction.Load (`param (Ren.lookup i ctx.Ctx.var_ren))
        | `env i -> Text.single @@ Instruction.Load (`env i))

let rec env_ren = let open Compiler in function
    | [] -> pure @@ Text.empty
    | v :: vs ->
        (* this happens 'backwards' because we need to arrange that the value to be stored in
            position 0 of the environment is at the top of the stack, but the variable whose value
            should go there is at index 0 in the environment renaming. *)
        bind (with_ren (Ren.shifted 1) @@ env_ren vs) @@ fun pS ->
        bind (var v) @@ fun pVar ->
        pure @@ Text.cat pS pVar

let rec pattern
        (failure : 'l)
        (pat : Term.pattern)
        : 'l Text.builder Compiler.t =
    let open Compiler in
    match pat with
    | WildcardPattern ->
        pure @@ Text.chunk Instruction.[
            Pop (`param, 0);
        ]
    | VariablePattern ->
        pure @@ Text.chunk Instruction.[
            Move `param_to_return;
        ]
    | LiteralPattern (IntLit n) ->
        pure @@ Text.chunk Instruction.([
            Push (`param, `integer (Int64.neg n));
            Prim Prim.Plus;
            Jump (`nonzero, failure);
        ])
    | LiteralPattern _ -> failwith "[compile] literal patterns other than int not supported"
    | ConstPattern (c, pats) ->
        bind (pats |> traverse (fun pat -> bind new_label @@ fun l -> pure (l, pat))) @@
        fun labelled_pats -> (* each pat here is equipped with a label referring to the code that
        cleans up the value that pattern matches on and everything after it *)
        bind new_label @@ fun cleanup_all ->
        let cleanup_code =
            Text.cat
                (List.fold_left
                    begin fun acc (l, pat) ->
                        Text.cat acc @@ Text.chunk Instruction.[
                            Pop (`param, 0);
                            Label l;
                        ]
                    end
                    (Text.single (Instruction.Label cleanup_all))
                    labelled_pats)
                (Text.single @@ Instruction.Jump (`unconditional, failure))
        in
        bind (labelled_pats |> traverse_rev (fun (failure, pat) -> pattern failure pat)) @@ fun pat_bodies ->
        bind new_label @@ fun success ->
        pure @@ Text.cats [
            Text.chunk @@ Instruction.([
                Load `constructor;
                Push (`param, `integer (Int64.neg (Int64.of_int c)));
                Prim Prim.Plus;
                Jump (`nonzero, cleanup_all);
            ]);
            Text.cats pat_bodies;
            Text.single (Jump (`unconditional, success));
            cleanup_code;
            Text.single (Label success);
        ]

let rec term (t : Term.t) : 'l Text.builder Compiler.t =
    let open Compiler in
    match t with
    | Term.Lit lit -> pure @@ literal lit
    | Term.App (tH, tS) ->
        app 0 (List.rev tS) tH
        (* Why in reverse? To uphold the calling convention, we need to emit the code to generate
           the arguments from right to left. However, `app` traverses the spine from left to right
           which is the simplest way to get the correct shifting of the variable renaming. *)
    | Term.Let (Rec, t1, t2) -> failwith "recursive let bindings not implemented"
    | Term.Let (NonRec, t1, t2) ->
        bind (term t1) @@ fun p1 ->
        bind (with_ren Ren.extended @@ term t2) @@ fun p2 ->
            pure @@ Text.cats [ p1; p2;
                Text.single @@ Instruction.Pop (`param, 1)
                (* drop the value of t1 from the stack, since function exit only knows to clean up
                   params *)
            ]
    | Term.Match (t, cases) ->
        bind (term t) @@ fun pV ->
        bind (new_label) @@ fun success ->
        let f (Term.Case (pat, n, t_branch)) =
            bind new_label @@ fun failed ->
            bind (pattern failed pat) @@ fun p_pat ->
            bind (with_ren Ren.(extended_by n) @@ term t_branch) @@ fun p_branch ->
            pure @@ Text.cats [
                Text.single @@ Instruction.Load (`param 0);
                p_pat;
                Text.single @@ Instruction.Pop (`param, 0);
                (* ^ remove the value we were matching on *)
                Text.chunk @@ List.init n @@ (fun _ -> Instruction.Move `return_to_param);
                (* ^ Move the matched values (which were stored on the call stack temporarily)
                   onto the parameter stack. *)
                p_branch;
                Text.chunk @@ List.init n @@ (fun _ -> Instruction.Pop (`param, 1));
                (* ^ remove the values brought in by matching
                   we use an offset of 1 to skip the result value of the matching *)
                Text.chunk Instruction.[
                    Jump (`unconditional, success);
                    Label failed;
                ];
            ]
        in
        bind (traverse f cases) @@ fun p_cases ->
        pure @@ Text.(cats [
            pV;
            cats p_cases;
            chunk Instruction.[
                Halt `inexhaustive_match;
                Label success;
            ];
        ])

    | Term.MkClo (theta, n, f) ->
        bind (lookup_ref f) @@ fun ProgramInfo.({ address }) ->
        let n = List.length theta in
        bind (env_ren theta) @@ fun p ->
            pure @@ Text.cats [
                p;
                Text.single @@ Instruction.Push (`param, `address address);
                Text.single @@ Instruction.(MkClo { env_size = n });
            ]

and app n (tS : Term.spine) (tH : Term.head) : 'l Text.builder Compiler.t =
    let open Compiler in
    match tS with
    | [] -> begin match tH with
        | Term.Var v ->
            bind (var v) @@ fun pVar ->
            pure @@ Text.cats
            [ pVar
            ; if n > 0
              then Text.single @@ Instruction.Call `dynamic
              else Text.empty
            ]
        | Term.Ref f ->
            bind (lookup_ref f) @@ fun ref_spec ->
            (* if List.length tS <> ref_spec.arity then
                Util.invariant "[compile] ref call spine has n elements"; *)
            pure @@ Text.cat
                (Text.single @@ match !(ref_spec.kind) with
                    | `func -> Instruction.Push (`param, `address ref_spec.address)
                    | `well_known -> Instruction.Load (`well_known f))
                (Text.single @@ Instruction.Call (call_mode_of_ref ref_spec n))
        | Term.Const c ->
            bind (lookup_ctor c) @@ fun ctor ->
            pure @@ Text.single @@ Instruction.Const { tag = ctor.tag; arity = ctor.arity }
        | Term.Prim p ->
            pure @@ Text.single @@ Instruction.Prim p
    end
    | t :: tS ->
        bind (term t) @@ fun p ->
        bind (with_ren (Ren.shifted 1) @@ app (n+1) tS tH) @@ fun pApp ->
        pure @@ Text.cat p pApp

let return_mode_of_ref r = match !ProgramInfo.(r.kind) with
    | `well_known -> Util.invariant "[compile] well-known values do not define functions"
    | `func -> `func r.arity
    | `closure_body -> `closure r.arity

let decl (ctx : Ctx.t) (pgm : 'l Bytecode.Program.t) : Decl.tm -> 'l Bytecode.Program.t =
    let Bytecode.Program.({ well_knowns; functions; top }) = pgm in
    function
    | Decl.({ name; body; arity }) ->
        let ref_spec = match RefMap.find_opt name ctx.Ctx.info.refs with
            | Some x -> x
            | None -> Util.invariant "[compile] ProgramInfo.t contains all functions"
        in
        if ref_spec.arity <> arity then Util.invariant "[compile] arity mismatch";
        (* now this depends on... whether the term being defined is a *pure* function or not
           Only pure functions have nonzero arity.
           *)
        let (s', p) = Compiler.with_ren Ren.(extended_by arity) (term body) ctx State.initial in
        if arity = 0 then
            (* then the body of the declaration needs to happen right away, and its value is
               stored in the well-known name `name` -- that is, this declaration becomes for a
               so-called "well-known" value. *)
            Bytecode.Program.({
                well_knowns = name :: well_knowns;
                functions;
                top = Text.cats [top; p; Text.single @@ Instruction.Store name];
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

let program (ctx : Ctx.t) (pgm : Decl.program) : 'l Bytecode.Program.t =
    let program = List.fold_left (decl ctx) Bytecode.Program.empty pgm in
    { program with
        functions = List.rev program.functions;
        top = Text.(cat program.top (single @@ Instruction.Halt `finished));
    }
