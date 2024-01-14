(* Compiles closed syntax into bytecode. *)

open BasicSyntax
open BasicInstruction
open Syntax.Low
open Lincode
open Instruction
open RuntimeInfo

let basic i = Basic i

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

    let rec id = function
        | 0 -> []
        | n -> extended @@ id (n-1)

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

    let lookup_ctor c = fun ctx s -> (s, ProgramInfo.lookup_ctor c ctx.Ctx.info)

    let lookup_ref f = fun ctx s -> (s, ProgramInfo.lookup_ref f ctx.Ctx.info)
end

let call_mode_of_ref (r : ProgramInfo.ref_spec) =
    match r.kind with
    | `func -> fun n -> `func n
    | `well_known -> fun n -> `closure n
    | `closure_body -> Util.invariant "[compile] calls to closure bodies are not possible"

let var (v : var) : builder Compiler.t = fun ctx s ->
    (s, match v with
        | `bound i -> Builder.single @@ basic (Load (`param (Ren.lookup i ctx.Ctx.var_ren)))
        | `env i -> Builder.single @@ basic @@ Load (`env i))

let rec env_ren = let open Compiler in function
    | [] -> pure @@ Builder.empty
    | v :: vs ->
        (* this happens 'backwards' because we need to arrange that the value to be stored in
            position 0 of the environment is at the top of the stack, but the variable whose value
            should go there is at index 0 in the environment renaming. *)
        bind (with_ren (Ren.shifted 1) @@ env_ren vs) @@ fun pS ->
        bind (var v) @@ fun pVar ->
        pure @@ Builder.cat pS pVar

(** Generates bytecode that checks whether the value on the top of the stack matches the given
    pattern. If the pattern does _not_ match, then a jump is made to the given failure label.
    If the pattern does match, then the pattern code falls through.
    Regardless, the top value of the stack is consumed. *)
let rec pattern
        (failure : 'l)
        (pat : Term.pattern)
        : builder Compiler.t =
    let open Compiler in
    match pat with
    | WildcardPattern ->
        pure @@ Builder.chunk Instruction.[
            basic @@ Pop (`param, 0);
        ]
    | VariablePattern ->
        pure @@ Builder.chunk Instruction.[
            basic @@ Move `param_to_return;
        ]
    | LiteralPattern (IntLit n) ->
        pure @@ Builder.chunk Instruction.([
            basic @@ Push (`param, `integer (Int64.neg n));
            basic @@ Prim Prim.Plus;
            basic @@ Jump (`nonzero, failure);
        ])
    | LiteralPattern _ -> failwith "[compile] literal patterns other than int not supported"
    | ConstPattern (c, pats) ->
        bind new_label @@ fun inner_failure ->
        bind new_label @@ fun success ->
        let field_count = List.length pats in
        bind (pats |> traverse_rev (fun pat -> pattern inner_failure pat)) @@ fun pat_bodies ->
        (* Why are the patterns processed in reverse?
           If we have a branch like `Cons x xs -> E`, then the indices are 0 -> x, 1 -> xs.
           So to arrange that the value to which x is bound ends up on the top of the stack, we
           process the patterns in reverse order. *)
        let open Builder in
        pure @@ cats Instruction.[
            chunk @@ List.map basic [
                Load (`param 0); (* duplicate the constructor address *)
                Load `constructor; (* replace the CON address with the constructor tag *)
                Push (`param, `integer (Int64.neg (Int64.of_int c)));
                Prim Prim.Plus;
                Jump (`nonzero, inner_failure);
            ];
            cats @@ List.mapi
                (fun i pat_body -> cats [
                    chunk [
                        basic @@ Load (`param 0); (* duplicate the constructor address *)
                        basic @@ Load (`field (field_count - i - 1)); (* replace with the nth field *)
                        (* Because we did the patterns in reverse, we have to 'flip' the index from
                           this mapi to load the correct field from the constructor. *)
                    ];
                    pat_body;
                ])
                pat_bodies;
            chunk @@ [
                basic @@ Jump (`unconditional, success);
                Label inner_failure;
                basic @@ Pop (`param, 0);
                basic @@ Jump (`unconditional, failure);
                Label success;
                basic @@ Pop (`param, 0);
            ];
        ]

let rec term (t : Term.t) : builder Compiler.t =
    let open Compiler in
    match t with
    | Term.Constant (`unboxed n) ->
        pure @@ Builder.single @@ basic @@ Push (`param, `integer n)
    | Term.Constant (`boxed r) ->
        pure @@ Builder.single @@ Instruction.LoadConstant r
    | Term.App (tH, tS) ->
        app 0 (List.rev tS) Builder.empty tH
        (* Why in reverse? To uphold the calling convention, we need to emit the code to generate
           the arguments from right to left. However, `app` traverses the spine from left to right
           which is the simplest way to get the correct shifting of the variable renaming. *)
    | Term.Let (Rec, t1, t2) -> failwith "recursive let bindings not implemented"
    | Term.Let (NonRec, t1, t2) ->
        bind (term t1) @@ fun p1 ->
        bind (with_ren Ren.extended @@ term t2) @@ fun p2 ->
            pure @@ Builder.cats [ p1; p2;
                Builder.single @@ basic @@ Pop (`param, 1)
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
            pure @@ Builder.cats [
                Builder.single @@ basic @@ Load (`param 0);
                p_pat;
                Builder.single @@ basic @@ Pop (`param, 0);
                (* ^ remove the value we were matching on *)
                Builder.chunk @@ List.init n @@ (fun _ -> basic @@ Move `return_to_param);
                (* ^ Move the matched values (which were stored on the call stack temporarily)
                   onto the parameter stack. *)
                p_branch;
                Builder.chunk @@ List.init n @@ (fun _ -> basic @@ Pop (`param, 1));
                (* ^ remove the values brought in by matching
                   we use an offset of 1 to skip the result value of the matching *)
                Builder.chunk Instruction.[
                    basic @@ Jump (`unconditional, success);
                    Label failed;
                ];
            ]
        in
        bind (traverse f cases) @@ fun p_cases ->
        pure @@ Builder.(cats [
            pV;
            cats p_cases;
            chunk Instruction.[
                basic @@ Halt `inexhaustive_match;
                Label success;
            ];
        ])

    | Term.MkClo (theta, arity, f) ->
        bind (lookup_ref f) @@ fun ProgramInfo.({ address }) ->
        let n = List.length theta in
        bind (env_ren theta) @@ fun p ->
            pure @@ Builder.cats [
                p;
                Builder.single @@ basic @@ Push (`param, `address address);
                Builder.single @@ basic @@ MkClo { env_size = n; arity };
            ]

and app n (tS : Term.spine) (acc : builder) (tH : Term.head) : builder Compiler.t =
    let open Compiler in
    match tS with
    | [] -> begin match tH with
        | Term.Var v ->
            bind (var v) @@ fun pVar ->
            let open Builder in
            pure @@ cats [
                acc;
                pVar;
                if n > 0 then
                    chunk Instruction.[
                        basic @@ Push (`return, `integer (Int64.of_int n));
                        basic @@ Call `dynamic;
                    ]
                else empty;
            ]
        | Term.Ref f ->
            bind (lookup_ref f) @@ fun ref_spec ->
            let open Builder in
            pure @@ cats [
                acc;
                (single @@ basic @@ match ref_spec.kind with
                    | `func -> Push (`param, `address ref_spec.address)
                    | `well_known -> Load (`well_known f));
                if ref_spec.ProgramInfo.arity > 0
                then single @@ basic @@ Call (
                    call_mode_of_ref ref_spec @@ ref_spec.ProgramInfo.arity
                )
                else empty;
                if n - ref_spec.ProgramInfo.arity > 0
                then chunk [
                    basic @@ Push (`return, `integer (Int64.of_int @@ n - ref_spec.ProgramInfo.arity));
                    basic @@ Call `dynamic;
                ]
                else empty;
            ]
        | Term.Const c ->
            bind (lookup_ctor c) @@ fun ctor ->
            pure @@ Builder.(cats [
                acc;
                single @@ basic @@ Const { tag = ctor.tag; arity = ctor.arity };
            ])
        | Term.Prim op ->
            pure @@ Builder.(cat acc (single @@ basic @@ Prim op))
    end
    | t :: tS ->
        bind (term t) @@ fun p ->
        with_ren (Ren.shifted 1) @@
        app (n+1) tS (Builder.cat acc p) tH

let return_mode_of_ref r = match ProgramInfo.(r.kind) with
    | `well_known -> Util.invariant "[compile] well-known values do not define functions"
    | `func -> `func r.arity
    | `closure_body -> `closure r.arity

let decl (ctx : Ctx.t) (pgm : Program.t) : Decl.tm -> Program.t =
    let Program.({ well_knowns; functions; top }) = pgm in
    function
    | Decl.({ name; body; arity }) ->
        let ref_spec = ProgramInfo.lookup_ref name ctx.Ctx.info in
        if ref_spec.arity <> arity then Util.invariant "[compile] arity mismatch";
        (* now this depends on... whether the term being defined is a *pure* function or not
           Only pure functions have nonzero arity.
           *)
        let (s', p) =
            term body { ctx with var_ren = List.rev @@ Ren.id arity } State.initial
            (* Why is the initial renaming reversed? It might not have been if I weren't so dumb.
               Consider that `fun x y z -> ...` has a body `...` that uses indices 0, 1, 2 to refer
               to the bound variables z y x respectively.
               Therefore, to get the de Bruijn indices to line up with the stack indices, we need
               to push the arguments to this function onto the stack _in order_.
               However, we crucially need to push them _in reverse_ order (from right to left)
               so that chained calls work properly.
               That is, consider `f a b c` where `f` takes 1 input to return a function of 2
               inputs. If a b c are pushed onto the stack in order, then f will use index `0` to
               refer to the value of `a`, but actually it will get `c` !
               So since the function's arguments are on the stack in the reverse order from what it
               expects, we uses a reversed identity renaming to correct this. *)
        in
        if arity = 0 then
            (* then the body of the declaration needs to happen right away, and its value is
               stored in the well-known name `name` -- that is, this declaration becomes for a
               so-called "well-known" value. *)
            Program.({
                well_knowns = name :: well_knowns;
                functions;
                top = Builder.cats [top; p; Builder.single @@ basic @@ Store name];
            })
        else
            Program.({
                well_knowns;
                functions =
                    ( name
                    , Builder.(
                          build @@ cat p (single @@ basic @@ Ret (return_mode_of_ref ref_spec))
                      )
                    ) :: functions;
                top;
            })

let program (ctx : Ctx.t) (pgm : Decl.program) : Program.t =
    let program = List.fold_left (decl ctx) Program.empty pgm in
    { program with
        functions = List.rev program.functions;
        top = Builder.(cat program.top (single @@ basic @@ Halt `finished));
    }
