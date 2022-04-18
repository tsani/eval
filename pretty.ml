open Format
open Syntax

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"

let rec print_tm lvl (ppf : formatter) : tm -> unit = function
  | Num n -> fprintf ppf "%s" (string_of_int n)
  | Var i -> fprintf ppf "!%s" (string_of_int i)
  | Ref f -> fprintf ppf "%s" f
  | Fun e ->
    fprintf ppf "%a@[<hv 2>fun -> @,%a@]%a"
      lparen (lvl > 0)
      (print_tm 0) e
      rparen (lvl > 0)
  | App (e1, e2) (* prec 9 *) ->
    fprintf ppf "%a@[<hv 2>%a @,%a@]%a"
      lparen (lvl > 9)
      (print_tm 9) e1
      (print_tm 10) e2
      rparen (lvl > 9)
  | Let (e1, e2) ->
    fprintf ppf "%a@[<v 2>let ! = @[%a@] in @,@[%a@]@]%a"
      lparen (lvl > 8)
      (print_tm 0) e1
      (print_tm 0) e2
      rparen (lvl > 8)
  | Match (e, cases) ->
    fprintf ppf "%a@[<v 2>match @[%a@] with @,%a@]end%a"
      lparen (lvl > 8)
      (print_tm 0) e
      print_cases cases
      rparen (lvl > 8)
  | Const (ctor_name, spine) ->
    fprintf ppf "%a@[<hv 2>%s @,%a@]%a"
      lparen (lvl > 8)
      ctor_name
      (print_spine 10) spine
      rparen (lvl > 8)
(*
  | Rec e ->
    fprintf ppf "%a@[<hv 2>rec. @,%a@]%a"
      lparen (lvl > 0)
      (print_tm 0) e
      rparen (lvl > 0)
*)
  | Clo (env, e) ->
    fprintf ppf "%a@[@[%a@](%a)@]%a"
        lparen (lvl > 0)
        print_env env
        (print_tm 0) e
        rparen (lvl > 0)

and print_env ppf : tm list -> unit =
  fprintf ppf "[@[<hov>%a@]]"
    (pp_print_list ~pp_sep: (fun ppf () -> fprintf ppf ",%a" pp_print_space ()) (print_tm 0))

and print_spine lvl ppf : tm list -> unit = function
  | [] -> ()
  | e :: spine -> fprintf ppf "%a @,%a" (print_tm lvl) e (print_spine lvl) spine

and print_case ppf : case -> unit = function
  | Case (pat, body) ->
    fprintf ppf "@[<hv 2>%a -> @,%a@]"
      (print_pattern 0) pat
      (print_tm 0) body

and print_cases ppf : case list -> unit = function
  | [] -> ()
  | [case] -> fprintf ppf "%a" print_case case
  | case :: cases -> fprintf ppf "%a@,%a" print_case case print_cases cases

and print_pattern lvl ppf : pattern -> unit = function
  | ConstPattern (ctor_name, pat_spine) ->
    fprintf ppf "%a@[<hv 2>%s @,%a@]%a"
      lparen (lvl > 9)
      ctor_name
      (print_pat_spine 10) pat_spine
      rparen (lvl > 9)
  | NumPattern n -> fprintf ppf "%d" n
  | VariablePattern -> fprintf ppf "!"
  | WildcardPattern -> fprintf ppf "_"

and print_pat_spine lvl ppf : pattern list -> unit = function
  | [] -> ()
  | pat :: pat_spine -> fprintf ppf "%a @,%a" (print_pattern lvl) pat (print_pat_spine lvl) pat_spine

let tm e = Format.(fprintf std_formatter "%a%a" (print_tm 0) e pp_print_newline ())
