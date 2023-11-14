(* Bytecode interpreter *)

open BasicSyntax
open Bytecode
open RuntimeInfo

type offset = int

let heap_size = 4096
type heap_addr = Int64.t
type code_addr = Int64.t
type heap = value Array.t

type value_count = int
type byte_count = int

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
        ep : heap_addr; (* environment pointer, used to load env vars *)
        heap : heap;
        next_free : heap_addr;
        param_stack : Stack.t;
        return_stack : Stack.t;
        well_knowns : heap_addr WK.t;
    }

    let initial = {
        ep = Int64.zero;
        pc = Int64.zero;
        heap = Array.make heap_size Int64.zero;
        next_free = Int64.of_int 400; (* just to make heap addresses look different *)
        param_stack = Stack.empty;
        return_stack = Stack.empty;
        well_knowns = WK.empty;
    }
end

let well_knowns s = List.of_seq @@ WK.to_seq s.State.well_knowns

module Ctx = struct
    type t = {
        code : instr Array.t;
    }
end

module HeapObject = struct
    module Kind = struct
        type t =
            | CON
            | CLO
            | PAP
            | ARR

        let to_tag = function
            | CON -> '\x01'
            | CLO -> '\x02'
            | PAP -> '\x03'
            | ARR -> '\x04'

        let of_tag = function
            | '\x01' -> CON
            | '\x02' -> CLO
            | '\x03' -> PAP
            | '\x04' -> ARR
            | _ -> Util.invariant "[interpret] all tags are known"
    end

    (** Decomposes a value into 8 8-bit integers. *)
    let decompose_value (v : value) : char list =
        let b = Bytes.make 8 '\x00' in
        Bytes.set_int64_ne b 0 v;
        List.init 8 (fun i -> Bytes.get b i)

    module Header = struct
        type t = value

        let encode (k : Kind.t) (counts : int list) : t =
            if List.length counts > 7 then
                Util.invariant "[interpret] heap object header has at most 7 counts";
            let open Bytes in
            let b = make 8 '\x00' in
            set b 0 (Kind.to_tag k);
            List.iteri (fun i n -> set b (1 + i) (Char.chr n)) counts;
            get_int64_ne b 0

        let decode (hdr : t) : Kind.t * int list =
            let tag :: counts = decompose_value hdr in
            (Kind.of_tag tag, List.map Char.code counts)
    end

    type con_spec = {
        tag : int;
        arity : value_count;
        fields : value list;
    }

    type clo_spec = {
        env_size : value_count;
        arity : value_count;
        body : code_addr;
        env : value list;
    }

    type pap_spec = {
        held : value_count;
        missing : value_count;
        clo : heap_addr;
        fields : value list;
    }

    type arr_spec = {
        capacity : value_count;
        length: byte_count;
        data : char Array.t;
    }

    type t =
        | Con of con_spec
        | Clo of clo_spec
        | Pap of pap_spec
        | Arr of arr_spec

    (** Writes a heap object to a heap at the given address. *)
    let encode_at (pos : heap_addr) (heap : heap) (obj : t) : unit =
        (** Converts the heap object to a list of values. *)
        let to_value_list = function
            | Con { tag; arity; fields } ->
                Header.(encode Kind.CON [tag; arity]) :: fields
            | Clo { env_size; arity; body; env } ->
                Header.(encode Kind.CLO [env_size; arity]) :: body :: env
            | Pap { held; missing; clo; fields } ->
                Header.(encode Kind.PAP [held; missing]) :: clo :: fields
            | Arr { capacity; length; data } ->
                Header.(encode Kind.ARR [capacity; length]) :: (Util.not_implemented ())
        in

        let pos = Int64.to_int pos in
        List.iteri (fun i v -> heap.(pos + i) <- v) (to_value_list obj)

    (** Decodes a heap object from a heap at the given address. *)
    let decode_at (pos : heap_addr) (heap : heap) : t =
        let pos = Int64.to_int pos in
        match Header.decode heap.(pos) with
        | CON, tag :: arity :: _ ->
            Con {
                tag;
                arity;
                fields = List.init arity (fun i -> heap.(pos + i + 1));
            }
        | CLO, env_size :: arity :: _ ->
            Clo {
                env_size;
                arity;
                body = heap.(pos + 1);
                env = List.init env_size (fun i -> heap.(pos + i + 2));
            }
        | PAP, held :: missing :: _ ->
            Pap {
                held;
                missing;
                clo = heap.(pos + 1);
                fields = List.init held (fun i -> heap.(pos + i + 2));
            }

    (** Calculates the size (as a count of values) of the given heap object. *)
    let size : t -> int = function
        | Con { arity } -> 1 + arity
        | Clo { env_size } -> 2 + env_size
        | Pap { held; missing } -> 2 + held
        (* Everything gets a +1 for the header, then Clo and Pap get an extra +1 since they hold an
           address in addition to their fields. *)

    let as_clo = function
        | Clo spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a closure"

    let as_con = function
        | Con spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a constructor"

    let as_pap = function
        | Pap spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a partial application"
end

module Interpreter = struct
    type 'a t = Ctx.t -> State.t -> State.t * 'a

    let pure x = fun _ s -> (s, x)

    let bind (m : 'a t) (k : 'a -> 'b t) : 'b t = fun ctx s ->
        let (s', x) = m ctx s in k x ctx s'

    let void m = bind m @@ fun _ -> pure ()

    (* Loads the instruction at the PC and increments the PC. *)
    let next_instruction : instr t = fun ctx s ->
        let i = ctx.code.(Int64.to_int s.pc) in
        Debug.printf "PARAM:  @[%a@]@," Stack.print s.param_stack;
        Debug.printf "RETURN: @[%a@]@," Stack.print s.return_stack;
        Debug.printf "TRACE:  %Ld. %a@," s.pc Pretty.Bytecode.print_instruction i;
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

    let get : State.t t = fun ctx s -> (s, s)

    (** Applies a transformation to the state. *)
    let modify (f : State.t -> State.t) : unit t = fun ctx s -> (f s, ())

    let set_ep ep = modify (fun s -> { s with ep })

    (** Applies a transformation to the state that computes something on the side. *)
    let modify_with (f : State.t -> State.t * 'a) : 'a t = fun ctx s ->
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
    let deref (addr : heap_addr) (offset : int) = fun ctx s ->
        (s, s.State.heap.(Int64.to_int addr + offset))

    let load_heap_object (pos : heap_addr) : HeapObject.t t = fun ctx s ->
        (s, HeapObject.decode_at pos s.State.heap)

    (** Allocates space on the heap for the object, writes it to the heap, and returns the
        address of the object. *)
    let store_heap_object (obj : HeapObject.t) : heap_addr t = fun ctx s ->
        let open State in
        let addr = s.next_free in
        HeapObject.encode_at addr s.State.heap obj;
        ( { s with next_free = Int64.add addr (Int64.of_int @@ HeapObject.size obj) }
        , addr
        )
end

module Exec = struct
    type exec = status Interpreter.t
    open Interpreter

    let call : call_mode -> exec = function
        | `func n ->
            bind (pop `param 0) @@ fun code_addr ->
            bind get @@ fun s ->
            bind (push `return s.pc) @@ fun _ ->
            bind (jump_abs code_addr) @@ fun _ ->
            pure `running

        | `closure n ->
            bind (pop `param 0) @@ fun heap_addr ->
            bind get @@ fun s ->
            bind (push `return s.ep) @@ fun _ ->
            bind (push `return s.pc) @@ fun _ ->
            bind (set_ep (Int64.add heap_addr 2L)) @@ fun _ ->
            bind (deref heap_addr 1) @@ fun clo_body_addr ->
            bind (jump_abs clo_body_addr) @@ fun _ ->
            pure `running

        | `dynamic ->
            bind (pop `return 0) @@ function
            | k when k = Int64.zero ->
                (* a dynamic call with zero arguments is the base case and is a no-op *)
                pure `running
            | arg_count ->
                let arg_count = Int64.to_int arg_count in
                (* otherwise there are more arguments to apply *)
                bind (pop `param 0) @@ fun obj_addr ->
                bind (load_heap_object obj_addr) @@ let open HeapObject in function
                | Clo { arity } when arg_count < arity ->
                    bind (pops arg_count `param 0) @@ fun args ->
                    bind (store_heap_object @@ Pap {
                        held = arg_count;
                        missing = arity - arg_count;
                        clo = obj_addr;
                        fields = args;
                    }) @@ fun pap_addr ->
                    bind (push `param pap_addr) @@ fun _ ->
                    pure `running
                | Clo { arity; body } -> (* then arg_count is >= arity *)
                    bind get @@ fun s ->
                    bind (push `return (Int64.of_int @@ arg_count - arity)) @@ fun _ ->
                    bind (push `return s.ep) @@ fun _ ->
                    bind (push `return @@ Int64.sub s.pc 1L) @@ fun _ ->
                    bind (set_ep (Int64.add obj_addr 2L)) @@ fun _ ->
                    bind (jump_abs body) @@ fun _ ->
                    pure `running
                | Pap { held; missing; clo; fields } when arg_count < missing ->
                    bind (pops arg_count `param 0) @@ fun args ->
                    bind (store_heap_object @@ Pap {
                        held = held + arg_count;
                        missing = missing - arg_count;
                        clo;
                        fields = fields @ args;
                    }) @@ fun pap_addr ->
                    bind (push `param pap_addr) @@ fun _ ->
                    pure `running
                | Pap { held; missing; clo; fields } ->
                    (* there are enough values to call the function now, so we load its saved arguments
                       onto the stack. They were saved _in order_, so we have to load them in reverse
                       to arrange that the very first argument ends up on the top of the stack. *)
                    bind (List.rev fields |> iter (fun v -> push `param v)) @@ fun _ ->
                    bind get @@ fun s ->
                    bind (push `return (Int64.of_int @@ missing - arg_count)) @@ fun _ ->
                    bind (push `return s.ep) @@ fun _ ->
                    bind (push `return @@ Int64.sub s.pc 1L) @@ fun _ ->
                    bind (set_ep (Int64.add clo 2L)) @@ fun _ ->
                    bind (deref clo 1) @@ fun clo_body_addr ->
                    bind (jump_abs clo_body_addr) @@ fun _ ->
                    pure `running

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
        bind (pops (env_size + 1) `param 0) @@ fun (body :: env) ->
        let obj = HeapObject.(Clo { env_size; arity; body; env }) in
        bind (store_heap_object obj) @@ fun addr ->
        bind (push `param addr) @@ fun _ ->
        pure `running

    let const (tag, arity) : exec =
        bind (pops arity `param 0) @@ fun fields ->
        let obj = HeapObject.(Con { tag; arity; fields }) in
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
            let HeapObject.({ tag; fields }) = HeapObject.as_con obj in
            bind (push `param @@ Int64.of_int tag) @@ fun _ ->
            pure `running
        | `field n ->
            bind (pop `param 0) @@ fun addr ->
            bind (load_heap_object addr) @@ fun obj ->
            let HeapObject.({ tag; fields }) = HeapObject.as_con obj in
            bind (push `param @@ List.nth fields n) @@ fun _ ->
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
        | Instruction.Call call_mode -> call call_mode
        | Instruction.Ret ret_mode -> ret ret_mode
        | Instruction.MkClo { env_size; arity } -> mkclo (env_size, arity)
        | Instruction.Const { tag; arity } -> const (tag, arity)
        | Instruction.Pop (stack_mode, offset) -> pop (stack_mode, offset)
        | Instruction.Push (stack_mode, push_mode) -> push (stack_mode, push_mode)
        | Instruction.Move move_mode -> move move_mode
        | Instruction.Load load_mode -> load load_mode
        | Instruction.Store name -> store name
        | Instruction.Prim p -> prim p
        | Instruction.Jump (jump_mode, offset) -> jump (jump_mode, offset)
        | Instruction.Label _ -> Util.invariant "[interpret] labels are already interpreted"
        | Instruction.Halt status -> pure status

    let fetch_decode_execute = bind (next_instruction) dispatch
end

let rec program ctx s =
    match Exec.fetch_decode_execute ctx s with
    | (s', `running) -> program ctx s'
    | (s', status) -> (s', status)
