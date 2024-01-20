(* Bytecode interpreter *)

open BasicInstruction
open BasicSyntax
open Bytecode
open RuntimeInfo

type offset = int

let heap_size = 4096

module WK = Util.StringMap

module Stack = struct
    type t = value list

    let empty = []

    (** Pops an item from a stack a given offset away from the top. *)
    let rec pop (offset : int) (l : t) : t * value = match offset, l with
        | _, [] -> Util.invariant "[interpret] stack is not empty for pop"
        | 0, x :: xs -> (xs, x)
        | n, x :: xs -> let (xs, v) = pop (n-1) xs in (x :: xs, v)

    let push (v : value) (l : t) : t * unit = (v :: l, ())

    let rec peek (offset : int) (l : t) : value = match offset, l with
        | _, [] -> Util.invariant "[interpret] stack is not empty for peek"
        | 0, x :: _ -> x
        | n, _ :: xs -> peek (n-1) xs

    let print ppf stk = Format.(
        fprintf ppf "%a" (pp_print_list ~pp_sep: PrettyCommon.comma_space (
            fun ppf x -> fprintf ppf "%Ld" x)))
        stk
end

module State = struct
    type t = {
        pc : Int64.t; (* program counter; index into the code array *)
        ep : Heap.addr; (* environment pointer, used to load env vars *)
        heap : Heap.Runtime.t;
        param_stack : Stack.t;
        return_stack : Stack.t;
        well_knowns : Heap.addr WK.t;
    }

    let initial ?(heap = Heap.Runtime.make heap_size) () = {
        ep = Int64.zero;
        pc = Int64.zero;
        heap;
        param_stack = Stack.empty;
        return_stack = Stack.empty;
        well_knowns = WK.empty;
    }
end

let well_knowns s = List.of_seq @@ WK.to_seq s.State.well_knowns

module Ctx = struct
    type t = {
        code : Instruction.t Array.t;
    }
end

(** According to the encoding of heap objects, a CLO object is laid out as
    <header> <body code address> <env var 1> <env var 2> ... <env var N>
    So adding 2 to the address of a closure object gives a pointer to the environment! *)
let closure_env_offset : Int64.t = 2L


module Interpreter = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure x = fun _ s -> (s, x)

    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s ->
        let (s', x) = m ctx s in k x ctx s'

    let void m = bind m @@ fun _ -> pure ()

    (* Loads the instruction at the PC and increments the PC. *)
    let next_instruction : Instruction.t t = fun ctx s ->
        let i = ctx.code.(Int64.to_int s.pc) in
        Debug.printf "PARAM:  @[%a@]@," Stack.print s.param_stack;
        Debug.printf "RETURN: @[%a@]@," Stack.print s.return_stack;
        Debug.printf "TRACE:  %Ld. %a@," s.pc Pretty.BasicInstruction.print_instruction i;
        ({ s with pc = Int64.add s.pc 1L }, i)

    let rec traverse (f : 'a -> 'b t) : 'a list -> 'b list t = function
        | [] -> pure []
        | x :: xs ->
            bind (f x) @@ fun y ->
            bind (traverse f xs) @@ fun ys ->
            pure (y :: ys)

    let rec iter (f : 'a -> unit t) : 'a list -> unit t = function
        | [] -> pure ()
        | x :: xs -> bind (f x) @@ fun _ -> iter f xs

    let get : State.t t = fun _ctx s -> (s, s)

    (** Applies a transformation to the state. *)
    let modify (f : State.t -> State.t) : unit t = fun _ctx s -> (f s, ())

    let set_ep ep = modify (fun s -> { s with ep })

    (** Applies a transformation to the state that computes something on the side. *)
    let modify_with (f : State.t -> State.t * 'a) : 'a t = fun _ctx s ->
        let (s', x) = f s in (s', x)

    (** Applies a transformation to a chosen stack that computes something on the side. *)
    let modify_stack_with (stk : stack_mode) (f : Stack.t -> Stack.t * 'a) : 'a t =
        match stk with
        | `param -> modify_with begin fun s ->
            let param_stack, x = f s.param_stack in
            ({ s with param_stack }, x)
        end
        | `return -> modify_with begin fun s ->
            let return_stack, x = f s.return_stack in
            ({ s with return_stack }, x)
        end

    (** Removes an item from a chosen stack a given offset away from the top. *)
    let pop (stk : stack_mode) (offset : int) : value t =
        modify_stack_with stk (Stack.pop offset)

    (** Pop multiple values from the given stack at the given offset *)
    let rec pops n (stk : stack_mode) (offset : int) : value list t =
        if n = 0 then pure [] else
            bind (pop stk offset) @@ fun x ->
            bind (pops (n-1) stk offset) @@ fun xs ->
            pure (x :: xs)

    (** Look at an item from a chosen stack a given offset away from the top. *)
    let peek (stk : stack_mode) (offset :int) : value t =
        modify_stack_with stk (fun s -> (s, Stack.peek offset s))

    (** Adds an item to the top of a stack. *)
    let push (stk : stack_mode) (v : value) : unit t =
        modify_stack_with stk (Stack.push v)

    (** Pushes all the given values onto a stack. This happens in the order of the list's items,
        so the first item of the list will be bottom-most of all the pushed items. *)
    let rec pushes (stk : stack_mode) : value list -> unit t = function
        | [] -> pure ()
        | v :: vs -> bind (push stk v) @@ fun _ -> pushes stk vs

    (** Sets the PC to the given value. *)
    let jump_abs (pc : Int64.t) : unit t = modify (fun s -> { s with pc })

    (** Adds the given offset to the PC. *)
    let jump_rel (offset : int) : unit t = modify (fun s -> {
        s with pc = Int64.add s.pc @@ Int64.of_int offset
    })

    (** Move the top item of one stack to the top of another stack. *)
    let move move_mode =
        let (src, dst) = match move_mode with
            | `param_to_return -> (`param, `return)
            | `return_to_param -> (`return, `param)
        in
        bind (pop src 0) @@ push dst

    (** Gets a value from the heap. *)
    let deref (addr : Heap.addr) (offset : int) = fun _ctx s ->
        (s, s.State.heap.Heap.Runtime.body.(Int64.to_int addr + offset))

    let load_heap_object (pos : Heap.addr) : Heap.Object.spec t = fun _ctx s ->
        (s, Heap.Object.load_spec pos s.State.heap.Heap.Runtime.body)

    let load_associated_blob (pos : Heap.addr) (spec : Heap.Object.spec) : Heap.Object.blob t =
        fun _ctx s -> (s, Heap.Object.load_blob pos s.State.heap.Heap.Runtime.body spec)

    let load_full_heap_object (pos : Heap.addr) : Heap.Object.obj t = fun _ctx s ->
        let spec = Heap.Object.load_spec pos s.State.heap.Heap.Runtime.body in
        let blob = Heap.Object.load_blob pos s.State.heap.Heap.Runtime.body spec in
        (s, (spec, blob))

    let load_constructor_field (pos : Heap.addr) (n : int) : value t =
        deref pos (n + 1)

    (** Allocates space on the heap for the object, writes it to the heap, and returns the
        address of the object. *)
    let store_heap_object (obj : Heap.Object.obj) : Heap.addr t = fun _ctx s ->
        let open State in
        let (addr, heap) = Heap.Runtime.write_next_free (Heap.Object.serialize obj) s.heap in
        ({ s with heap }, addr)
end

module Exec = struct
    type exec = status Interpreter.t
    open Interpreter

    let call : call_mode -> exec = function
        | `func _n ->
            bind (pop `param 0) @@ fun code_addr ->
            bind get @@ fun s ->
            bind (push `return s.pc) @@ fun _ ->
            bind (jump_abs code_addr) @@ fun _ ->
            pure `running

        | `closure _n ->
            bind (pop `param 0) @@ fun clo_addr ->
            bind get @@ fun s ->
            bind (push `return s.ep) @@ fun _ ->
            bind (push `return s.pc) @@ fun _ ->
            bind (set_ep (Int64.add clo_addr 2L)) @@ fun _ ->
            bind (deref clo_addr 1) @@ fun clo_body_addr ->
            bind (jump_abs clo_body_addr) @@ fun _ ->
            pure `running

        | `pap _ -> failwith "[interpret] [call] `pap TODO"
        | `dynamic ->
            bind (pop `return 0) @@ function
            | k when k = Int64.zero ->
                (* a dynamic call with zero arguments is the base case and is a no-op *)
                pure `running
            | arg_count ->
                let arg_count = Int64.to_int arg_count in
                (* otherwise there are more arguments to apply *)
                bind (pop `param 0) @@ fun obj_addr ->
                bind (load_heap_object obj_addr) @@
                let open Heap.Object in function
                | Clo { arity; _ } when arg_count < arity ->
                    bind (pops arg_count `param 0) @@ fun args ->
                    bind (store_heap_object
                        ( Pap { held = arg_count; missing = arity - arg_count; clo = obj_addr; }
                        , Array.of_list args
                        )
                    ) @@ fun pap_addr ->
                    bind (push `param pap_addr) @@ fun _ ->
                    pure `running
                | Clo { arity; body; _ } -> (* then arg_count is >= arity *)
                    bind get @@ fun s ->
                    bind (push `return (Int64.of_int @@ arg_count - arity)) @@ fun _ ->
                    bind (push `return s.ep) @@ fun _ ->
                    bind (push `return @@ Int64.sub s.pc 1L) @@ fun _ ->
                    bind (set_ep (Int64.add obj_addr 2L)) @@ fun _ ->
                    bind (jump_abs body) @@ fun _ ->
                    pure `running
                | Pap { held; missing; clo } as spec when arg_count < missing ->
                    bind (pops arg_count `param 0) @@ fun args ->
                    bind (load_associated_blob obj_addr spec) @@ fun blob ->
                    bind (store_heap_object
                        ( Pap { held = held + arg_count; missing = missing - arg_count; clo }
                        , Array.(append blob (of_list args))
                        )
                    ) @@ fun pap_addr ->
                    bind (push `param pap_addr) @@ fun _ ->
                    pure `running
                | Pap { missing; clo; _ } as spec ->
                    (* there are enough values to call the function now, so we load its saved arguments
                       onto the stack. They were saved _in order_, so we have to load them in reverse
                       to arrange that the first argument ends up on the top of the stack. *)
                    bind (load_associated_blob obj_addr spec) @@ fun blob ->
                    bind (blob |> Array.to_list |> List.rev |> iter (fun v -> push `param v)) @@
                    fun _ ->
                    bind get @@ fun s ->
                    bind (push `return (Int64.of_int @@ missing - arg_count)) @@ fun _ ->
                    bind (push `return s.ep) @@ fun _ ->
                    bind (push `return @@ Int64.sub s.pc 1L) @@ fun _ ->
                    bind (set_ep (Int64.add clo 2L)) @@ fun _ ->
                    bind (deref clo 1) @@ fun clo_body_addr ->
                    bind (jump_abs clo_body_addr) @@ fun _ ->
                    pure `running

                (* The following cases are ruled out by typechecking. *)
                | Con _ -> Util.invariant "[interpret] [call] Con -- type error"
                | Arr _ -> Util.invariant "[interpret] [call] Arr -- type error"

    let ret : return_mode -> exec =
        (* removes the function's parameters from the stack *)
        let clean_params n = iter (fun () -> void @@ pop `param 1) (List.init n @@ fun _ -> ()) in
        function
        | `func n ->
            bind (clean_params n) @@ fun _ ->
            bind (pop `return 0) @@ fun addr ->
            bind (jump_abs addr) @@ fun _ ->
            pure `running

        | `closure n ->
            bind (clean_params n) @@ fun _ ->
            bind (pop `return 0) @@ fun ret_addr ->
            bind (pop `return 0) @@ fun ep ->
            bind (set_ep ep) @@ fun _ ->
            bind (jump_abs ret_addr) @@ fun _ ->
            pure `running

    let mkclo (env_size, arity) : exec =
        bind (pops (env_size + 1) `param 0) @@ function
        | [] -> Util.invariant "[interpret] [mkclo] pops at least 1 item"
        | (body :: env) ->
            let obj = (Heap.Object.(Clo { env_size; arity; body }), Array.of_list env) in
            bind (store_heap_object obj) @@ fun addr ->
            bind (push `param addr) @@ fun _ ->
            pure `running

    let const (tag, arity) : exec =
        bind (pops arity `param 0) @@ fun fields ->
        let obj = (Heap.Object.(Con { tag; arity }), Array.of_list fields) in
        bind (store_heap_object obj) @@ fun addr ->
        bind (push `param addr) @@ fun _ ->
        pure `running

    let load mode : exec =
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
        | `constructor ->
            bind (pop `param 0) @@ fun addr ->
            bind (load_heap_object addr) @@ fun obj ->
            let Heap.Object.({ tag; _ }) = Heap.Object.as_con obj in
            bind (push `param @@ Int64.of_int tag) @@ fun _ ->
            pure `running
        | `field n ->
            bind (pop `param 0) @@ fun addr ->
            bind (load_constructor_field addr n) @@ fun v ->
            bind (push `param v) @@ fun _ ->
            pure `running

    let store name : exec =
        bind (pop `param 0) @@ fun v ->
        bind (modify (fun s -> { s with well_knowns = WK.add name v s.well_knowns })) @@ fun _ ->
        pure `running

    let move mode : exec = bind (move mode) @@ fun _ -> pure `running

    let prim p : exec =
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

    let jump (mode, offset) : exec =
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

    let pop (stk, offset) : exec =
        bind (pop stk offset) @@ fun _ ->
        pure `running

    let push (stack_mode, push_mode) : exec =
        let v = match push_mode with
            | `integer n -> n
            | `address r -> !r
        in
        bind (push stack_mode v) @@ fun _ -> pure `running

    let dispatch = function
        | Call call_mode -> call call_mode
        | Ret ret_mode -> ret ret_mode
        | MkClo { env_size; arity } -> mkclo (env_size, arity)
        | Const { tag; arity } -> const (tag, arity)
        | Pop (stack_mode, offset) -> pop (stack_mode, offset)
        | Push (stack_mode, push_mode) -> push (stack_mode, push_mode)
        | Move move_mode -> move move_mode
        | Load load_mode -> load load_mode
        | Store name -> store name
        | Prim p -> prim p
        | Jump (jump_mode, offset) -> jump (jump_mode, offset)
        | Halt status -> pure status
        | MkPap _ -> Util.not_implemented ()

    (** Loads the next instruction, updating the PC, and dispatches it. *)
    let step = bind next_instruction dispatch
end

let rec program ctx s =
    match Exec.step ctx s with
    | (s', `running) -> program ctx s'
    | (s', status) -> (s', status)
