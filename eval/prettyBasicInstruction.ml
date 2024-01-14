open Format
open Bytecode

open PrettyCommon

let print_call_mode ppf = function
    | `func n -> fprintf ppf "func %d" n
    | `closure n -> fprintf ppf "clo %d" n
    | `pap n -> fprintf ppf "pap %d" n
    | `dynamic -> fprintf ppf "dyn"

let print_stack_mode ppf = function
    | `param -> fprintf ppf "param"
    | `return -> fprintf ppf "ret"

let print_load_mode ppf = function
    | `env n -> fprintf ppf "env %d" n
    | `param n -> fprintf ppf "param %d" n
    | `well_known s -> fprintf ppf "well-known %s" s
    | `constructor -> fprintf ppf "ctor"
    | `field n -> fprintf ppf "field %d" n

let print_jump_mode ppf = function
    | `unconditional -> ()
    | `zero -> fprintf ppf "zero "
    | `nonzero -> fprintf ppf "nonzero "

let print_ret_mode ppf = function
    | `closure n -> fprintf ppf "clo %d" n
    | `func n -> fprintf ppf "func %d" n

let print_push_mode ppf = function
    | `integer n -> fprintf ppf "int %Ld" n
    | `address a -> fprintf ppf "addr %Ld" !a

let print_move_mode ppf = function
    | `param_to_return -> fprintf ppf "->"
    | `return_to_param -> fprintf ppf "<-"

let print_status ppf = function
    | `inexhaustive_match -> fprintf ppf "inexhaustive_match"
    | `finished -> fprintf ppf "done"
    | `running -> fprintf ppf "running"
    | `loop -> fprintf ppf "loop"

let print_instruction ppf (i : Instruction.t) = match i with
    | Call mode ->
        fprintf ppf "call %a" print_call_mode mode
    | Ret mode ->
        fprintf ppf "ret %a" print_ret_mode mode
    | MkClo { env_size; arity } ->
        fprintf ppf "mkclo %d %d" env_size arity
    | MkPap { held_count; missing_count } ->
        fprintf ppf "mkpap %d %d" held_count missing_count
    | Const { tag; arity } ->
        fprintf ppf "const %d %d" tag arity
    | Pop (mode, i) ->
        fprintf ppf "pop %a %d" print_stack_mode mode i
    | Push (stack_mode, push_mode) ->
        fprintf ppf "push %a %a" print_stack_mode stack_mode print_push_mode push_mode
    | Load (mode) ->
        fprintf ppf "load %a" print_load_mode mode
    | Store wk ->
        fprintf ppf "store %s" wk
    | Prim p ->
        fprintf ppf "prim %a" print_prim_name p
    | Jump (mode, l) ->
        fprintf ppf "jump %a%d" print_jump_mode mode l
    | Move mode ->
        fprintf ppf "move %a" print_move_mode mode
    | Halt status ->
        fprintf ppf "trap %a" print_status status
