open BasicSyntax
open Format

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"
let comma_space ppf () = fprintf ppf ",@ "

let print_rec_flag ppf = function
| Rec -> fprintf ppf "rec "
| NonRec -> ()

let print_literal ppf = function
  | BoolLit true -> fprintf ppf "true"
  | BoolLit false -> fprintf ppf "false"
  | CharLit c -> fprintf ppf "%c" c (* TODO handle escapes *)
  | StringLit s -> fprintf ppf "\"%s\"" s (* TODO handle escapes *)
  | IntLit n -> fprintf ppf "%ld" n

let print_prim_name ppf p =
    fprintf ppf "%s" (Prim.to_string p)
