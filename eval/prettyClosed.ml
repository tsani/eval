open Format
open BasicSyntax
open Syntax.Closed
open Term

open PrettyCommon

let print_prim ppf p = Util.not_implemented ()

let print_var ppf = function
    | `bound i -> fprintf ppf "#b_%d" i
    | `env i -> fprintf ppf "#e_%d" i

let print_head ppf = function
    | Var v -> print_var ppf v
    | Ref f -> fprintf ppf "%s" f
    | Const c -> fprintf ppf "%s" c
    | Prim p -> print_prim ppf p

let rec print_tm lvl ppf = function
    | MkClo (theta, n, f) -> fprintf ppf "mkclo(%a, %d, %s)" (print_env_ren ppf) theta n f
    | Lit l -> print_literal ppf l
    | App (tH, tS) -> print_app lvl ppf (tH, tS)
    | Let (rec_flag, e1, e2) ->
        fprintf ppf "%a@[<hv>@[<hv>@[<hv 2>let %a! =@ @[%a@]@]@ in@]@ @[%a@]@]%a"
            lparen (lvl > 8)
            print_rec_flag rec_flag
            (print_tm 0) e1
            (print_tm 0) e2
            rparen (lvl > 8)
    | Match (e, cases) ->
        fprintf ppf "%a@[<v>@[<v>match @[%a@] with @,%a@]@]%a"
            lparen (lvl > 0)
            (print_tm 0) e
            print_cases cases
            rparen (lvl > 0)

and print_case ppf : case -> unit = function
    | Case (pat, body) ->
        fprintf ppf "@[<hv 2>| %a ->@ %a@]"
            (print_pattern 0) pat
            (print_tm 1) body

and print_cases ppf : case list -> unit = function
    | [] -> ()
    | [case] -> fprintf ppf "%a" print_case case
    | case :: cases -> fprintf ppf "%a@,%a" print_case case print_cases cases

and print_pattern lvl ppf : pattern -> unit = function
    | ConstPattern (ctor_name, []) -> fprintf ppf "%s" ctor_name
    | ConstPattern (ctor_name, pat_spine) ->
        fprintf ppf "%a@[<hv 2>%s@ %a@]%a"
            lparen (lvl > 9)
            ctor_name
            (print_pat_spine 10) pat_spine
            rparen (lvl > 9)
    | LiteralPattern lit -> fprintf ppf "%a" print_literal lit
    | VariablePattern -> fprintf ppf "!"
    | WildcardPattern -> fprintf ppf "_"

and print_pat_spine lvl ppf : pattern list -> unit =
    pp_print_list ~pp_sep: pp_print_space (print_pattern lvl) ppf

and print_env_ren ppf theta = Util.not_implemented ()

and print_app lvl ppf : head * spine -> unit = function
    (* since Prims are usually operators, we handle printing them specially *)
    | (Prim prim, tS) -> print_prim_app lvl ppf (prim, tS)
    (* Variables and constructors work the same way. *)
    | (Var i, tS) ->
        print_simple_app lvl ppf ((fun ppf () -> print_var ppf i), tS)
    | (Const c, tS) ->
        print_simple_app lvl ppf ((fun ppf () -> fprintf ppf "%s" c), tS)
    | (Ref c, tS)->
        print_simple_app lvl ppf ((fun ppf () -> fprintf ppf "%s" c), tS)

and print_simple_app lvl ppf : 'u * spine -> unit = function
    | print_head, [] -> print_head ppf ()
    | print_head, tS ->
        fprintf ppf "%a@[<hv 2>%a@ %a@]%a"
            lparen (lvl > 10)
            print_head ()
            (print_spine 11) tS
            rparen (lvl > 10)

and print_spine ?(sep = pp_print_space) lvl ppf : Term.t list -> unit =
    pp_print_list ~pp_sep: sep (print_tm lvl) ppf

and print_prim_app lvl ppf =
    let bop op prec t1 t2 =
      fprintf ppf "@[%a%a@ %s@ %a%a@]"
        lparen (lvl > prec)
        (print_tm prec) t1
        op
        (print_tm prec) t2
        rparen (lvl > prec)
    in
    let uop op prec t =
      fprintf ppf "@[%a%s%a%a@]"
        lparen (lvl > prec)
        op
        (print_tm prec) t
        rparen (lvl > prec)
    in
    let open Prim in
    function
    | Or, [t1; t2] -> bop "||" 2 t1 t2
    | And, [t1; t2] -> bop "&&" 3 t1 t2
    | Eq, [t1; t2] -> bop "==" 4 t1 t2
    | Lt, [t1; t2] -> bop "<" 4 t1 t2
    | Div, [t1; t2] -> bop "/" 5 t1 t2
    | Plus, [t1; t2] -> bop "+" 6 t1 t2
    | Times, [t1; t2] -> bop "*" 7 t1 t2
    | CharAt, [t1; t2] -> bop "@" 8 t1 t2
    | Not, [t] -> uop "!" 9 t
    | Neg, [t] -> uop "-" 9 t
    | SubString, ts ->
      print_simple_app lvl ppf ((fun ppf _ -> fprintf ppf "substring"), ts)
    | _ -> Util.invariant "all internal syntax primops have correct number of arguments"


