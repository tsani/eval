open Format
open Syntax

let lparen ppf cond = if cond then fprintf ppf "("
let rparen ppf cond = if cond then fprintf ppf ")"
let comma_space ppf () = fprintf ppf ",@ "

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

  let print_rec_flag ppf = function
    | Rec -> fprintf ppf "rec "
    | NonRec -> ()

  let print_literal ppf = function
    | BoolLit true -> fprintf ppf "true"
    | BoolLit false -> fprintf ppf "false"
    | CharLit c -> fprintf ppf "%c" c (* TODO handle escapes *)
    | StringLit s -> fprintf ppf "\"%s\"" s (* TODO handle escapes *)
    | IntLit n -> fprintf ppf "%d" n

  let rec collapse_funs : Term.t -> var_name list * Term.t = function
    | Fun (_, (_, x), e) -> let (xs, e) = collapse_funs e in (x :: xs, e)
    | e -> ([], e)

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

  and print_prim lvl scope ppf = function
    | (prim, tS) -> Util.not_implemented ()

  and print_app lvl scope ppf : Term.head * Term.spine -> unit = function
    (* since Prims are usually operators, we handle printing them specially *)
    | (Prim (_, prim), tS) -> print_prim lvl scope ppf (prim, tS)
    (* Variables and constructors work the same way. *)
    | (Var (_, i), tS) ->
      print_simple_app lvl scope ppf ((fun ppf () -> print_var scope ppf i), tS)
    | (Const (_, c), tS) | (Ref (_, c), tS)->
      print_simple_app lvl scope ppf ((fun ppf () -> fprintf ppf "%s" c), tS)

  and print_simple_app lvl scope ppf : 'u * Term.spine -> unit = function
    | print_head, [] -> print_head ppf ()
    | print_head, tS ->
      fprintf ppf "%a@[<hv 2>%a@ %a@]%a"
        lparen (lvl > 8)
        print_head ()
        (print_spine 10 scope) tS
        rparen (lvl > 8)


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
      fprintf ppf "| @[<hv 2>%s@ @[%a@]@]"
        name
        (pp_print_list ~pp_sep: pp_print_space (print_tp 10)) fields
    in
    let print_decl ppf = function
      | Decl.(TpDecl { tvar_binders; name; constructors }) ->
        fprintf ppf "@[<hv 2>type %s%a =@ %a@]"
          name
          print_tvar_binders tvar_binders
          (pp_print_list ~pp_sep: pp_print_cut print_ctor) constructors
      | Decl.(TmDecl { name; recursive }) ->
        let Decl.({ typ = Some (_, typ); }) = Signature.lookup_tm' name sg_t in
        let Decl.({ body = Some body }) = Signature.lookup_tm' name sg_e in
        fprintf ppf "@[<hv 2>val %s : @[%a@] =@ @[%a@]@]"
          name
          (print_tp 0) typ
          (print_value 0) body
    in
    fprintf ppf "@[<v>%a@]" (pp_print_list ~pp_sep: pp_print_cut print_decl) program
end
