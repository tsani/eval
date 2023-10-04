open Format
open Bytecode

let print_call_mode ppf = function
    | `pure n -> fprintf ppf "pure %d" n
    | `closure n -> fprintf ppf "clo %d" n
    | `pap n -> fprintf ppf "pap %d" n
    | `dynamic -> fprintf ppf "dyn"

let print_stack_mode ppf = function
    | `arg -> fprintf ppf "val"
    | `return -> fprintf ppf "ret"

let print_load_mode ppf = function
    | `env -> fprintf ppf "env"
    | `param -> fprintf ppf "val"
    | `value -> fprintf ppf "well-known"
    | `field -> fprintf ppf "field"

let print_jump_mode ppf = function
    | `unconditional -> ()
    | `zero -> fprintf ppf "zero"
    | `nonzero -> fprintf ppf "nonzero"

let print_ret_mode ppf = function
    | `closure -> fprintf ppf "clo"
    | `direct -> fprintf ppf "pure"

let print_instruction ppf (i : string Instruction.t) = match i with
    | Call mode ->
        fprintf ppf "call %a" print_call_mode mode
    | Ret mode ->
        fprintf ppf "ret %a" print_ret_mode mode
    | MkClo { env_size } ->
        fprintf ppf "mkclo %d" env_size
    | MkPap { held_count; missing_count } ->
        fprintf ppf "mkpap %d %d" held_count missing_count
    | Const { ctor; field_count } ->
        fprintf ppf "const %d %d" ctor field_count
    | Match { ctor } -> failwith "todo"
        fprintf ppf "match %d" ctor
    | Pop mode ->
        fprintf ppf "pop %a" print_stack_mode mode
    | Push (mode, n) ->
        fprintf ppf "push %a %ld" print_stack_mode mode n
    | Load (mode, i) ->
        fprintf ppf "load %a %d" print_load_mode mode i
    | Prim p ->
        fprintf ppf "prim %d (wtf)" (Obj.magic p)
    | Jump (mode, l) ->
        fprintf ppf "jump %a %s" print_jump_mode mode l
