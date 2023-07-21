open Format
open BasicSyntax
open Syntax

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"
let comma_space ppf () = fprintf ppf ",@ "

let print_rec_flag ppf = function
| Rec -> fprintf ppf "rec "
| NonRec -> ()

module Internal = struct
  open Internal
  open Term
  open Type

  let print_builtin_tp ppf = function
    | Int -> fprintf ppf "Int"
    | Bool -> fprintf ppf "Bool"
    | String -> fprintf ppf "String"
    | Char -> fprintf ppf "Char"

  let rec print_tp lvl (ppf : formatter) : Type.t -> unit = function
    | Builtin (_, bt) -> print_builtin_tp ppf bt
    | Arrow (_, t1, t2) ->
      fprintf ppf "%a@[%a@] -> @[%a@]%a"
        lparen (lvl > 0)
        (print_tp 1) t1
        (print_tp 0) t2
        rparen (lvl > 0)
    | Named (_, c, []) -> fprintf ppf "%s" c
    | Named (_, c, tps) ->
      fprintf ppf "%a%s @[%a@]%a"
        lparen (lvl > 9)
        c
        (pp_print_list ~pp_sep: pp_print_space (print_tp 10)) tps
        rparen (lvl > 9)
    | TVar (_, x) -> fprintf ppf "%s" x
    | TMVar (_, x) -> fprintf ppf "%s" x

  let print_tp_sc lvl (ppf : formatter) (binders, tp : Type.sc) : unit =
    fprintf ppf "%a@[<hv 2>%a@,%a@]%a"
      lparen (lvl > 0)
      (pp_print_list @@ fun ppf x -> fprintf ppf "%s. " x) binders
      (print_tp 0) tp
      rparen (lvl > 0)

  let print_var scope ppf i = match lookup_var scope i with
    | None -> fprintf ppf "!%d" i
    | Some x -> fprintf ppf "%s" x

  let rec print_ctx (ppf : formatter) (ctx : Ctx.t) : unit =
    pp_print_list ~pp_sep: comma_space begin fun ppf (i, t) ->
      fprintf ppf "@[<hv 2>v %d :@ %a@]" i begin fun ppf (x, tpsc) ->
        fprintf ppf "%s :@ %a" x (print_tp_sc 0) tpsc
      end t
    end ppf @@ Ctx.enumerate ctx

  let print_literal ppf = function
    | BoolLit true -> fprintf ppf "true"
    | BoolLit false -> fprintf ppf "false"
    | CharLit c -> fprintf ppf "%c" c (* TODO handle escapes *)
    | StringLit s -> fprintf ppf "\"%s\"" s (* TODO handle escapes *)
    | IntLit n -> fprintf ppf "%d" n

  let rec print_tm lvl scope (ppf : formatter) : Term.t -> unit = function
    | Lit (_, lit) -> fprintf ppf "%a" print_literal lit
    | Fun (_, (_, x), e) ->
      let (xs, e) = collapse_funs e in
      fprintf ppf "%a@[<hv 2>fun %a ->@ %a@]%a"
        lparen (lvl > 0)
        (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf " ") pp_print_string) (x :: xs)
        (print_tm 0 (Scope.extend_many scope @@ x :: xs)) e
        rparen (lvl > 0)
    | App (_, tH, tS) (* prec 9 *) ->
      print_app lvl scope ppf (tH, tS)
    | Let (_, rec_flag, (_, x), e1, e2) ->
      fprintf ppf "%a@[<hv>@[<hv>@[<hv 2>let %a%s =@ @[%a@]@]@ in@]@ @[%a@]@]%a"
        lparen (lvl > 8)
        print_rec_flag rec_flag
        x
        (print_tm 0 @@ Scope.extend_rec rec_flag scope x) e1
        (print_tm 0 @@ Scope.extend scope x) e2
        rparen (lvl > 8)
    | Match (_, e, cases) ->
      fprintf ppf "%a@[<v>@[<v>match @[%a@] with @,%a@]@]%a"
        lparen (lvl > 0)
        (print_tm 0 scope) e
        (print_cases scope) cases
        rparen (lvl > 0)

  and print_prim_app lvl scope ppf =
    let bop op prec t1 t2 =
      fprintf ppf "@[%a%a@ %s@ %a%a@]"
        lparen (lvl > prec)
        (print_tm prec scope) t1
        op
        (print_tm prec scope) t2
        rparen (lvl > prec)
    in
    let uop op prec t =
      fprintf ppf "@[%a%s%a%a@]"
        lparen (lvl > prec)
        op
        (print_tm prec scope) t
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
      print_simple_app lvl scope ppf ((fun ppf _ -> fprintf ppf "substring"), ts)
    | _ -> Util.invariant "all internal syntax primops have correct number of arguments"

  and print_app lvl scope ppf : Term.head * Term.spine -> unit = function
    (* since Prims are usually operators, we handle printing them specially *)
    | (Prim (_, prim), tS) -> print_prim_app lvl scope ppf (prim, tS)
    (* Variables and constructors work the same way. *)
    | (Var (_, i), tS) ->
      print_simple_app lvl scope ppf ((fun ppf () -> print_var scope ppf i), tS)
    | (Const (_, c), tS) | (Ref (_, c), tS)->
      print_simple_app lvl scope ppf ((fun ppf () -> fprintf ppf "%s" c), tS)

  and print_simple_app lvl scope ppf : 'u * Term.spine -> unit = function
    | print_head, [] -> print_head ppf ()
    | print_head, tS ->
      fprintf ppf "%a@[<hv 2>%a@ %a@]%a"
        lparen (lvl > 10)
        print_head ()
        (print_spine 11 scope) tS
        rparen (lvl > 10)

  and print_spine ?(sep = pp_print_space) lvl scope ppf : Term.t list -> unit =
    pp_print_list ~pp_sep: sep (print_tm lvl scope) ppf

  and print_case scope ppf : case -> unit = function
    | Case (_, pat, body) ->
      fprintf ppf "@[<hv 2>| %a ->@ %a@]"
        (print_pattern 0) pat
        (print_tm 1 (extend_with_pattern_vars scope pat)) body

  and print_cases scope ppf : case list -> unit = function
    | [] -> ()
    | [case] -> fprintf ppf "%a" (print_case scope) case
    | case :: cases -> fprintf ppf "%a@,%a" (print_case scope) case (print_cases scope) cases

  and print_pattern lvl ppf : pattern -> unit = function
    | ConstPattern (_, ctor_name, []) -> fprintf ppf "%s" ctor_name
    | ConstPattern (_, ctor_name, pat_spine) ->
      fprintf ppf "%a@[<hv 2>%s@ %a@]%a"
        lparen (lvl > 9)
        ctor_name
        (print_pat_spine 10) pat_spine
        rparen (lvl > 9)
    | LiteralPattern (_, lit) -> fprintf ppf "%a" print_literal lit
    | VariablePattern (_, x) -> fprintf ppf "%s" x
    | WildcardPattern _ -> fprintf ppf "_"

  and print_pat_spine lvl ppf : pattern list -> unit =
    pp_print_list ~pp_sep: pp_print_space (print_pattern lvl) ppf

  (* Pretty-prints a term together with its type. *)
  let print_tm_tp scope ppf (e, t : Term.t * Type.t) : unit =
    fprintf ppf "%a :%a%a" (print_tm 0 scope) e pp_print_space () (print_tp 0) t

  let print_pat_tp ppf (pat, t : pattern * tp) : unit =
    fprintf ppf "%a :%a%a" (print_pattern 0) pat pp_print_space () (print_tp 0) t

  let rec print_value lvl ppf (v : Value.t) : unit = let open Value in match v with
    | Lit lit -> print_literal ppf lit
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
    | Clo (env, xS, e) ->
      let e = expand_funs xS e in
      print_tm 0 (Env.to_scope env) ppf e
    | Prim _ -> Util.invariant "prim is not actually a value"

  and print_value_spine lvl ppf : Value.spine -> unit =
    pp_print_list ~pp_sep: pp_print_space (print_value lvl) ppf

  let rec print_env ppf (env : Env.t) : unit =
    fprintf ppf "[@[%a@]]"
      (pp_print_list ~pp_sep: comma_space print_env_entry) env

  and print_env_entry ppf ((x, v) : Env.entry) : unit =
    let print_ref ppf v = match !v with
      | None -> fprintf ppf "<undef>"
      | Some v -> print_value 0 ppf v
    in
    fprintf ppf "@[%s =@ %a@]" x print_ref v

  let print_evaluated_program ppf (sg_t, sg_e, program) =
    let open Format in
    let open Syntax.Internal in
    let print_tvar_binders =
      pp_print_list ~pp_sep: (fun ppf _ -> ()) (fun ppf x -> fprintf ppf " %s" x)
    in
    let print_ctor ppf Decl.({ name; fields }) =
      fprintf ppf "@ | @[<hv 2>%s@ @[%a@]@]"
        name
        (pp_print_list ~pp_sep: pp_print_space (print_tp 10)) fields
    in
    let print_decl ppf = function
      | Decl.(TpDecl { tvar_binders; name; constructors }) ->
        fprintf ppf "@[<hv 2>type %s%a =%a@]"
          name
          print_tvar_binders tvar_binders
          (pp_print_list ~pp_sep: pp_print_cut print_ctor) constructors
      | Decl.(TmDecl { name; recursive }) ->
        begin match Signature.lookup_tm' name sg_t, Signature.lookup_tm' name sg_e with
        | Decl.({ typ = Some (_, typ); }, { body = Some body }) ->
          fprintf ppf "@[<hv 2>val %s : @[%a@] =@ @[%a@]@]"
            name
            (print_tp 0) typ
            (print_value 0) body
        | _ ->
          Util.invariant "in printing an eval'd program we have both the type and value of each term"
        end
    in
    fprintf ppf "@[<v>%a@]" (pp_print_list ~pp_sep: pp_print_cut print_decl) program
end

module Closed = struct
    open Closed
    open Term

    let print_prim ppf p = Util.not_implemented ()

    let print_literal ppf = function
        | BoolLit true -> fprintf ppf "true"
        | BoolLit false -> fprintf ppf "false"
        | CharLit c -> fprintf ppf "%c" c (* TODO handle escapes *)
        | StringLit s -> fprintf ppf "\"%s\"" s (* TODO handle escapes *)
        | IntLit n -> fprintf ppf "%d" n

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


end
