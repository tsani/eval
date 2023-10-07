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
    | `param n -> fprintf ppf "val %d" n
    | `field n -> fprintf ppf "field %d" n
    | `well_known s -> fprintf ppf "well-known %s" s
    | `func l -> fprintf ppf "func %Ld" (!l)

let print_jump_mode ppf = function
    | `unconditional -> ()
    | `zero -> fprintf ppf "zero"
    | `nonzero -> fprintf ppf "nonzero"

let print_ret_mode ppf = function
    | `closure -> fprintf ppf "clo"
    | `func -> fprintf ppf "func"

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
    | Match { ctor } ->
        fprintf ppf "match %d" ctor
    | Pop mode ->
        fprintf ppf "pop %a" print_stack_mode mode
    | Push (mode, n) ->
        fprintf ppf "push %a %ld" print_stack_mode mode n
    | Load (mode) ->
        fprintf ppf "load %a" print_load_mode mode
    | Store wk ->
        fprintf ppf "store %s" wk
    | Prim p ->
        fprintf ppf "prim %a" print_prim_name p
    | Jump (mode, l) ->
        fprintf ppf "jump %a %s" print_jump_mode mode l

let print_text ppf (p : string Text.t) =
    fprintf ppf "@[<v>%a@]" (pp_print_list ~pp_sep: pp_print_cut print_instruction) p

let print_program ppf Program.({ well_knowns; functions; top }) =
    fprintf ppf "@[<v 2>well_known:@,@[<v>%a@]@]@,"
        (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf ", ") pp_print_string) well_knowns;
    fprintf ppf "@[<v 2>functions:@,@[<v>%a@]@]@,"
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf (name, body) ->
            fprintf ppf "@[@[<v 2>%s:@,%a@]@,@]" name print_text body)) functions;
    fprintf ppf "@[<v 2>entrypoint:@,@[<v>%a@]@]"
        print_text (Text.build top) (* XXX *)
