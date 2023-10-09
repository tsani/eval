(* Bytecode interpreter *)

open BasicSyntax
open Bytecode
open RuntimeInfo

type offset = int
type stack = value list

let heap_size = 4096
type heap_addr = Int64.t

module WK = Util.StringMap

module State = struct
    type t = {
        pc : int; (* program counter; index into the code array *)
        ep : heap_addr; (* environment pointer, used to load env vars *)
        heap : value Array.t;
        next_free : int;
        param_stack : stack;
        return_stack : stack;
        well_knowns : heap_addr WK.t;
    }

    let initial = {
        ep = Int64.zero;
        pc = 0;
        heap = Array.make heap_size Int64.zero;
        next_free = 0;
        param_stack = [];
        return_stack = [];
        well_knowns = WK.empty;
    }
end

let well_knowns s = List.of_seq @@ WK.to_seq s.State.well_knowns

module Ctx = struct
    type t = {
        code : instr Array.t;
    }
end

(** Pops an item from a stack a given offset away from the top. *)
let rec stack_pop (offset : int) (l : stack) : stack * value = match offset, l with
    | _, [] -> Util.invariant "[interpret] stack is not empty for pop"
    | 0, x :: xs -> (xs, x)
    | n, x :: xs -> let (xs, v) = stack_pop (n-1) xs in (x :: xs, v)

let stack_push (v : value) (l : stack) : stack * unit = (v :: l, ())

let rec stack_peek (offset : int) (l : stack) : value = match offset, l with
    | _, [] -> Util.invariant "[interpret] stack is not empty for peek"
    | 0, x :: _ -> x
    | n, _ :: xs -> stack_peek (n-1) xs

let print_stack ppf stk = Format.(
    fprintf ppf "%a" (pp_print_list ~pp_sep: PrettyCommon.comma_space (
        fun ppf x -> fprintf ppf "%Ld" x)))
    stk

module Interpreter = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure x = fun _ s -> (s, x)

    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s ->
        let (s', x) = m ctx s in k x ctx s'

    let void m = bind m @@ fun _ -> pure ()

    (* Loads the instruction at the PC and increments the PC. *)
    let next_instruction : instr t = fun ctx s ->
        let i = ctx.code.(s.pc) in
        Debug.printf "PARAM:  @[%a@]@," print_stack s.param_stack;
        Debug.printf "RETURN: @[%a@]@," print_stack s.return_stack;
        Debug.printf "TRACE:  %d. %a@," s.pc Pretty.Bytecode.print_instruction i;
        ({ s with pc = s.pc + 1 }, i)

    let rec traverse (f : 'a -> 'b t) : 'a list -> 'b list t = function
        | [] -> pure []
        | x :: xs ->
            bind (f x) @@ fun y ->
            bind (traverse f xs) @@ fun ys ->
            pure (y :: ys)

    let rec iter (f : 'a -> unit t) : 'a list -> unit t = function
        | [] -> pure ()
        | x :: xs -> bind (f x) @@ fun _ -> iter f xs

    let get : State.t t = fun ctx s -> (s, s)

    (** Applies a transformation to the state. *)
    let modify (f : State.t -> State.t) : unit t = fun ctx s -> (f s, ())

    (** Applies a transformation to the state that computes something on the side. *)
    let modify_with (f : State.t -> State.t * 'a) : 'a t = fun ctx s ->
        let (s', x) = f s in (s', x)

    let modify_stack_with (stk : stack_mode) (f : stack -> stack * 'a) : 'a t =
        match stk with
        | `param -> modify_with begin fun s ->
            let param_stack, x = f s.param_stack in
            ({ s with param_stack }, x)
        end
        | `return -> modify_with begin fun s ->
            let return_stack, x = f s.return_stack in
            ({ s with return_stack }, x)
        end

    let pop (stk : stack_mode) (offset : int) : value t =
        modify_stack_with stk (stack_pop offset)

    let peek (stk : stack_mode) (offset :int) : value t =
        modify_stack_with stk (fun s -> (s, stack_peek offset s))

    let push (stk : stack_mode) (v : value) : unit t =
        modify_stack_with stk (stack_push v)

    (** Sets the PC to the given value. *)
    let jump_abs (pc : int) : unit t = modify (fun s -> { s with pc })

    (** Adds the given offset to the PC. *)
    let jump_rel (offset : int) : unit t = modify (fun s -> { s with pc = s.pc + offset })

    let move move_mode =
        let (src, dst) = match move_mode with
            | `param_to_return -> (`param, `return)
            | `return_to_param -> (`return, `param)
        in
        bind (pop src 0) @@ push dst

    (** Gets a value from the heap. *)
    let deref (addr : heap_addr) (offset : int) = fun ctx s ->
        (s, s.State.heap.(Int64.to_int addr + offset))
end

type exec = status Interpreter.t

open Interpreter

let exec_call : call_mode -> exec = function
    | `func n ->
        bind (pop `param 0) @@ fun code_addr ->
        bind get @@ fun s ->
        bind (push `return (Int64.of_int s.pc)) @@ fun _ ->
        bind (jump_abs @@ Int64.to_int code_addr) @@ fun _ ->
        pure `running

    | _ -> failwith "todo closure calls"
            (*
    | `closure n ->
        bind (pop `param) @@ fun heap_addr ->
        bind get @@ fun s ->
        bind (push `return (Int64.of_int s.pc)) @ fun _ ->
            *)

let exec_ret : return_mode -> exec = function
    | `func n ->
        (* remove the function's parameters from the stack *)
        bind (iter (fun () -> void @@ pop `param 1) (List.init n @@ fun _ -> ())) @@ fun () ->
        bind (pop `return 0) @@ fun addr ->
        bind (jump_abs @@ Int64.to_int addr) @@ fun _ ->
        pure `running

    | `closure n -> failwith "[interpret] todo closure return"

let exec_mkclo n : exec = failwith "todo mkclo"

let exec_const (tag, arity) : exec = failwith "todo const"

let exec_pop (stk, offset) : exec =
    bind (pop stk offset) @@ fun _ ->
    pure `running

let exec_push (stack_mode, push_mode) : exec =
    let v = match push_mode with
        | `integer n -> n
        | `address r -> !r
    in
    bind (push stack_mode v) @@ fun _ -> pure `running

let exec_move mode : exec = bind (move mode) @@ fun _ -> pure `running

let exec_load mode : exec =
    bind get @@ fun s ->
    match mode with
    | `well_known name -> begin match WK.find_opt name s.well_knowns with
        | Some x -> bind (push `param x) @@ fun _ -> pure `running
        | None -> pure `loop
    end
    | `param n ->
        bind (peek `param n) @@ fun v ->
        bind (push `param v) @@ fun _ ->
        pure `running
    | `env i ->
        bind get @@ fun s ->
        bind (deref s.ep i) @@ fun v ->
        bind (push `param v) @@ fun _ ->
        pure `running
    | `constructor -> failwith "load constructor"

let exec_store name : exec =
    bind (pop `param 0) @@ fun v ->
    bind (modify (fun s -> { s with well_knowns = WK.add name v s.well_knowns })) @@ fun _ ->
    pure `running

let exec_prim p : exec =
    let open Prim in
    match p with
    | Plus ->
        bind (pop `param 0) @@ fun a ->
        bind (pop `param 0) @@ fun b ->
        bind (push `param (Int64.add a b)) @@ fun _ ->
        pure `running
    | Neg ->
        bind (pop `param 0) @@ fun a ->
        bind (push `param (Int64.neg a)) @@ fun _ ->
        pure `running
    | _ -> failwith "todo prims"

let exec_jump (mode, offset) : exec =
    match mode with
    | `zero ->
        bind (pop `param 0) @@ fun v ->
        if Int64.zero = v then
            bind (jump_rel (offset - 1)) @@ fun _ -> pure `running
        else
            pure `running
    | `nonzero ->
        bind (pop `param 0) @@ fun v ->
        if Int64.zero <> v then
            bind (jump_rel (offset - 1)) @@ fun _ -> pure `running
        else
            pure `running
    | `unconditional ->
        bind (jump_rel (offset - 1)) @@ fun _ -> pure `running
    (* why -1? Consider `jump 1; .L1; prim plus`. This gets numbered as
           0. jump L1
           1. prim plus
       with the label map
           L1 -> index 1
       But when we call `next_instruction` and get `jump n`, the PC will already be
       incremented to point to the following instruction (the prim plus).
       So essentially we need to subtract 1 from the PC before adding the offset so the offset is
       correctly interpreted, relative to the _jump_ instruction rather than the instruction
       _after_ it. Therefore `jump unconditional 1` is equivalent to a no-op and
       `jump unconditional 0` is an infinite loop. *)

let exec : exec =
    bind (next_instruction) @@ function
    | Call call_mode -> exec_call call_mode
    | Ret ret_mode -> exec_ret ret_mode
    | MkClo { env_size } -> exec_mkclo env_size
    | Const { tag; arity } -> exec_const (tag, arity)
    | Pop (stack_mode, offset) -> exec_pop (stack_mode, offset)
    | Push (stack_mode, push_mode) -> exec_push (stack_mode, push_mode)
    | Move move_mode -> exec_move move_mode
    | Load load_mode -> exec_load load_mode
    | Store name -> exec_store name
    | Prim p -> exec_prim p
    | Jump (jump_mode, offset) -> exec_jump (jump_mode, offset)
    | Label _ -> Util.invariant "[interpret] labels are already interpreted"
    | Halt status -> pure status

let rec program ctx s =
    match exec ctx s with
    | (s', `running) -> program ctx s'
    | (s', status) -> (s', status)
