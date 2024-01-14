open Format
open Lincode

open PrettyCommon

let print_instruction ppf : Instruction.t -> unit = function
    | Basic i -> PrettyBasicInstruction.print_instruction ppf i
    | Label l -> fprintf ppf ".%d:" l
    | LoadConstant i -> fprintf ppf "load constant %d" i

let print_text ppf p =
    fprintf ppf "@[<v>%a@]" (pp_print_list ~pp_sep: pp_print_cut print_instruction) p

let print_program ppf Program.({ well_knowns; functions; top }) =
    fprintf ppf "@[<v 2>well_known:@,@[<v>%a@]@]@,"
        (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf ", ") pp_print_string) well_knowns;
    fprintf ppf "@[<v 2>functions:@,@[<v>%a@]@]@,"
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf (name, body) ->
            fprintf ppf "@[@[<v 2>%s:@,%a@]@,@]" name print_text body)) functions;
    fprintf ppf "@[<v 2>entrypoint:@,@[<v>%a@]@]"
        print_text (Builder.build top) (* XXX *)

