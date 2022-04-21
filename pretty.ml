open Format
open Syntax

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"

let rec print_tp lvl (ppf : formatter) : tp -> unit = function
  | Int -> fprintf ppf "int"
  | Arrow (t1, t2) ->
    fprintf ppf "%a@[%a@] -> @[%a@]%a"
      lparen (lvl > 0)
      (print_tp 1) t1
      (print_tp 0) t2
      rparen (lvl > 0)
  | Named (c, []) -> fprintf ppf "%s" c
  | Named (c, tps) ->
    fprintf ppf "%a%s @[%a@]%a"
      lparen (lvl > 9)
      c
      (pp_print_list ~pp_sep: pp_print_space (print_tp 10)) tps
      rparen (lvl > 9)
  | TVar x -> fprintf ppf "%s" x
  | TMVar x -> fprintf ppf "%s" x

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
  | Const (c, []) -> fprintf ppf "%s" c
  | Const (c, spine) ->
    fprintf ppf "%a@[<hv 2>%s @,%a@]%a"
      lparen (lvl > 8)
      c
      (print_spine 10) spine
      rparen (lvl > 8)
  | Clo (env, e) ->
    fprintf ppf "%a@[@[%a@](%a)@]%a"
        lparen (lvl > 0)
        print_env env
        (print_tm 0) e
        rparen (lvl > 0)

and print_env ppf : tm list -> unit =
  fprintf ppf "[@[<hov>%a@]]"
    (pp_print_list ~pp_sep: (fun ppf () -> fprintf ppf ",%a" pp_print_space ()) (print_tm 0))

and print_spine lvl ppf : tm list -> unit =
  pp_print_list ~pp_sep: pp_print_space (print_tm lvl) ppf

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

(* Pretty-prints a term together with its type. *)
let print_tm_tp ppf (e, t : tm * tp) : unit =
  fprintf ppf "%a :%a%a" (print_tm 0) e pp_print_space () (print_tp 0) t

let print_pat_tp ppf (pat, t : pattern * tp) : unit =
  fprintf ppf "%a :%a%a" (print_pattern 0) pat pp_print_space () (print_tp 0) t

let tm e = Format.(fprintf std_formatter "%a%a" (print_tm 0) e pp_print_newline ())
