open BasicSyntax
open Format

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"
let comma_space ppf () = fprintf ppf ",@ "

let print_rec_flag ppf = function
| Rec -> fprintf ppf "rec "
| NonRec -> ()
