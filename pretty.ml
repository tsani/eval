open Format
open Syntax
open Internal
open Term
open Type

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"
let comma_space ppf () = fprintf ppf ",@ "

let rec print_tp lvl (ppf : formatter) : Type.t -> unit = function
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

let print_tp_sc lvl (ppf : formatter) (binders, tp : Type.sc) : unit =
  fprintf ppf "%a@[<hv 2>%a@,%a@]%a"
    lparen (lvl > 0)
    (pp_print_list @@ fun ppf x -> fprintf ppf "%s. " x) binders
    (print_tp 0) tp
    rparen (lvl > 0)

let rec print_ctx (ppf : formatter) (ctx : Ctx.t) : unit =
  pp_print_list ~pp_sep: comma_space begin fun ppf (i, t) ->
    fprintf ppf "@[<hv 2>v %d :@ %a@]" i begin fun ppf (x, tpsc) ->
      fprintf ppf "%s :@ %a" x (print_tp_sc 0) tpsc
    end t
  end ppf @@ Ctx.enumerate ctx

let print_rec_flag ppf = function
  | Rec -> fprintf ppf "rec "
  | NonRec -> ()

let rec collapse_funs : Term.t -> var_name list * Term.t = function
  | Fun (x, e) -> let (xs, e) = collapse_funs e in (x :: xs, e)
  | e -> ([], e)

let rec print_tm lvl scope (ppf : formatter) : Term.t -> unit = function
  | Num n -> fprintf ppf "%s" (string_of_int n)
  | Var i -> begin match lookup_var scope i with
    | Some x -> fprintf ppf "%s" x
    | None -> fprintf ppf "!%d" i
  end
  | Ref f -> fprintf ppf "%s" f
  | Fun (x, e) ->
    let (xs, e) = collapse_funs e in
    fprintf ppf "%a@[<hv 2>fun %a ->@ %a@]%a"
      lparen (lvl > 0)
      (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf " ") pp_print_string) (x :: xs)
      (print_tm 0 (Scope.extend_many scope @@ x :: xs)) e
      rparen (lvl > 0)
  | App (e1, e2) (* prec 9 *) ->
    fprintf ppf "%a@[<hv 2>%a @,%a@]%a"
      lparen (lvl > 9)
      (print_tm 9 scope) e1
      (print_tm 10 scope) e2
      rparen (lvl > 9)
  | Let (rec_flag, x, e1, e2) ->
    fprintf ppf "%a@[<hv>@[<hv>@[<hv 2>let %a%s =@ @[%a@]@]@ in@]@ @[%a@]@]%a"
      lparen (lvl > 8)
      print_rec_flag rec_flag
      x
      (print_tm 0 @@ Scope.extend_rec rec_flag scope x) e1
      (print_tm 0 @@ Scope.extend scope x) e2
      rparen (lvl > 8)
  | Match (e, cases) ->
    fprintf ppf "%a@[<v>@[<v 2>match @[%a@] with @,%a@]@,@]end%a"
      lparen (lvl > 8)
      (print_tm 0 scope) e
      (print_cases scope) cases
      rparen (lvl > 8)
  | Const (c, spine) as e -> match spine with
    | [] -> fprintf ppf "%s" c
    | spine ->
      fprintf ppf "%a@[<hv 2>%s@ %a@]%a"
        lparen (lvl > 8)
        c
        (print_spine 10 scope) spine
        rparen (lvl > 8)

and print_spine ?(sep = pp_print_space) lvl scope ppf : Term.t list -> unit =
  pp_print_list ~pp_sep: sep (print_tm lvl scope) ppf

and print_case scope ppf : case -> unit = function
  | Case (pat, body) ->
    fprintf ppf "@[<hv 2>%a ->@ %a@]"
      (print_pattern 0) pat
      (print_tm 0 (extend_with_pattern_vars scope pat)) body

and print_cases scope ppf : case list -> unit = function
  | [] -> ()
  | [case] -> fprintf ppf "%a" (print_case scope) case
  | case :: cases -> fprintf ppf "%a@,%a" (print_case scope) case (print_cases scope) cases

and print_pattern lvl ppf : pattern -> unit = function
  | ConstPattern (ctor_name, []) -> fprintf ppf "%s" ctor_name
  | ConstPattern (ctor_name, pat_spine) ->
    fprintf ppf "%a@[<hv 2>%s@ %a@]%a"
      lparen (lvl > 9)
      ctor_name
      (print_pat_spine 10) pat_spine
      rparen (lvl > 9)
  | NumPattern n -> fprintf ppf "%d" n
  | VariablePattern x -> fprintf ppf "%s" x
  | WildcardPattern -> fprintf ppf "_"

and print_pat_spine lvl ppf : pattern list -> unit =
  pp_print_list ~pp_sep: pp_print_space (print_pattern lvl) ppf

(* Pretty-prints a term together with its type. *)
let print_tm_tp scope ppf (e, t : Term.t * Type.t) : unit =
  fprintf ppf "%a :%a%a" (print_tm 0 scope) e pp_print_space () (print_tp 0) t

let print_pat_tp ppf (pat, t : pattern * tp) : unit =
  fprintf ppf "%a :%a%a" (print_pattern 0) pat pp_print_space () (print_tp 0) t

let rec print_value lvl ppf (v : Value.t) : unit = let open Value in match v with
  | Num n -> fprintf ppf "%d" n
  | Const (ctor_name, val_spine) -> begin match Sugar.decompose_list v with
    | Some l -> fprintf ppf "[@[%a@]]" (pp_print_list ~pp_sep: comma_space (print_value 0)) l
    | None -> match Sugar.decompose_nat v with
      | Some n -> fprintf ppf "%dN" n
      | None -> match val_spine with
        | [] -> fprintf ppf "%s" ctor_name
        | val_spine ->
          fprintf ppf "%a@[<hv 2>%s@ %a@]%a"
            lparen (lvl > 8)
            ctor_name
            (print_value_spine 10) val_spine
            rparen (lvl > 8)
  end
  | Clo (env, x, e) ->
    let e = Fun (x, e) in
    print_tm 0 (Env.to_scope env) ppf e

and print_value_spine lvl ppf : Value.spine -> unit =
  pp_print_list ~pp_sep: pp_print_space (print_value lvl) ppf

let rec print_env ppf (env : Env.t) : unit =
  fprintf ppf "[@[%a@]]"
    (pp_print_list ~pp_sep: comma_space print_env_entry) env

and print_env_entry ppf ((x, _, v) : Env.entry) : unit =
  let print_ref ppf v = match !v with
    | None -> fprintf ppf "<undef>"
    | Some v -> print_value 0 ppf v
  in
  fprintf ppf "@[%s =@ %a@]" x print_ref v
