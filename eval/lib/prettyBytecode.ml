open Format
open Bytecode

open PrettyBasicInstruction

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

let print_linked_program ppf instrs =
    fprintf ppf "@[<v>%a@]"
        (pp_print_list ~pp_sep: pp_print_cut (
            fun ppf (i, x) -> fprintf ppf "%d. %a" i print_instruction x))
        (Util.enumerate 0 instrs)
