open Syntax
open Eval

let program = [
  TpDecl {
    name = "List";
    tvar_binders = ["a"];
    constructors = [{
      owner_name = "List";
      name = "Nil";
      fields = [];
    }; {
      owner_name = "List";
      name = "Cons";
      fields = Sugar.[TVar "a"; ty_list (TVar "a")];
    }];
  };
  TpDecl {
    name = "Nat";
    tvar_binders = [];
    constructors = [{
      owner_name = "Nat";
      name = "Z";
      fields = [];
    }; {
      owner_name = "Nat";
      name = "S";
      fields = Sugar.[ty_nat];
    }]
  };
  TmDecl {
    name = "double";
    typ = Sugar.(mono @@ Arrow (ty_nat, ty_nat));
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        case (v 0) [
          pconst "Z" [] --> begin const "Z" [] end;
          pconst "S" [pv] --> begin
            const "S" [const "S" [r "double" @@@ v 0]]
          end
        ]
      end
    end;
  };
  TmDecl {
    name = "two";
    typ = Sugar.(mono @@ ty_nat);
    recursive = false;
    body = Some Sugar.(const "S" [const "S" [const "Z" []]]);
  };
  TmDecl {
    name = "four";
    typ = Sugar.(mono @@ ty_nat);
    recursive = false;
    body = Some Sugar.(r "double" @@@ r "two");
  };
  TmDecl {
    name = "halve";
    typ = Sugar.(mono @@ Arrow (ty_nat, ty_nat));
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        case (v 0) [
          pconst "Z" [] --> const "Z" [];
          pconst "S" [pconst "Z" []] --> const "Z" [];
          pconst "S" [pconst "S" [pv]] --> const "S" [r "halve" @@@ v 0];
        ]
      end
    end;
  };
  TmDecl {
    name = "half_of_four";
    typ = Sugar.(mono @@ ty_nat);
    recursive = false;
    body = Some Sugar.(r "halve" @@@ r "four");
  };
  TmDecl {
    name = "length";
    typ = Sugar.(["a"], Arrow (ty_list @@ TVar "a", ty_nat));
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        case (v 0) [
          pconst "Nil" [] --> const "Z" [];
          pconst "Cons" [ignored; pv] --> const "S" [r "length" @@@ v 0];
        ]
      end
    end
  };
  TmDecl {
    name = "sample_list";
    typ = Sugar.(mono @@ ty_list ty_nat);
    recursive = false;
    body = Some Sugar.(list [nat 0; nat 1; nat 2; nat 3; nat 4]);
  };
  TmDecl {
    name = "sample_list_length";
    typ = mono @@ Sugar.ty_nat;
    recursive = false;
    body = Some Sugar.(r "length" @@@ r "sample_list")
  };
  TmDecl {
    name = "replicate";
    typ = Sugar.(["a"], arrows [TVar "a"; ty_nat] @@ ty_list (TVar "a"));
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        lam begin
          case (v 0) [
            pzero --> nil;
            psucc pv --> cons (v 2) (apps (r "replicate") [v 2; v 0]);
          ]
        end
      end;
    end
  };
  TmDecl {
    name = "list_of_lists";
    typ = mono @@ Sugar.(ty_list (ty_list ty_nat));
    recursive = false;
    body = Some Sugar.(apps (r "replicate") [r "sample_list"; nat 5])
  };
  TmDecl {
    name = "map";
    typ = Sugar.(["a"; "b"], arrows [arrow (TVar "a") (TVar "b"); ty_list (TVar "a")] @@ ty_list (TVar "b"));
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        lam begin
          case (v 0) [
            pnil --> nil;
            pcons pv pv --> cons (v 3 @@@ v 1) (apps (r "map") [v 3; v 0]);
          ]
        end
      end
    end;
  };
  TmDecl {
    name = "list_of_nats";
    typ = mono @@ Sugar.(ty_list ty_nat);
    recursive = false;
    body = Some Sugar.(apps (r "map") [r "length"; r "list_of_lists"]);
  };
]

open Format

let print_mismatch_kind ppf : Typecheck.unify_kind -> unit = function
  | `scru_pat (scru_and_tp, pat_and_tp) ->
    fprintf ppf "@[<v>@[<v 2>when unifying the match scrutinee@,@[%a@]@]@,@[<v 2>with the pattern@,@[%a@]@]@]"
      Pretty.print_tm_tp scru_and_tp
      Pretty.print_pat_tp pat_and_tp
  | `app e -> fprintf ppf "when expecting @[%a@] to have a function type." (Pretty.print_tm 0) e
  | `ctor_spine ((ctor, ctor_tp), (sp, inf_ctor_tp)) ->
    fprintf ppf "@[<v>@[<hv 2>when matching constructor@ @[<hv 2>%s :@ %a@]@]@,@[<hv 2>with spine@ %a@]@,@[hv 2>for which the inferred constructor type is@ %a@]@]"
      ctor
      (Pretty.print_tp 0) ctor_tp
      (Pretty.print_spine 10) sp
      (Pretty.print_tp 0) inf_ctor_tp
  | `ctor_pat_spine ((ctor, ctor_tp), (pat_sp, inf_ctor_tp)) ->
    fprintf ppf "@[<v>@[<hv 2>when matching constructor@ @[<hv 2>%s :@ %a@]@]@,@[<hv 2>with pattern spine@ %a@]@,@[hv 2>for which the inferred constructor type is@ %a@]@]"
      ctor
      (Pretty.print_tp 0) ctor_tp
      (Pretty.print_pat_spine 10) pat_sp
      (Pretty.print_tp 0) inf_ctor_tp
  | `case_body (body, body_tp, body_tp') ->
    fprintf ppf "@[<v>@[<hv 2>when unifying the inferred type@ %a@]@,@[<hv 2>of the case body@ %a@]@,@[<hv 2>against the inferred type of the other branches@ %a@]@]"
      (Pretty.print_tp 0) body_tp
      (Pretty.print_tm 0) body
      (Pretty.print_tp 0) body_tp'
  | `decl (c, user_tp, inf_tp) ->
    fprintf ppf "@[<v>@[<hv 2>when unifying the given type@ %a@]@,of the declaration for `%s'@,@[<hv 2>against the inferred type@ %a@]@]"
      (Pretty.print_tp 0) user_tp
      c
      (Pretty.print_tp 0) inf_tp
      

let print_type_error ppf : Typecheck.TypeError.t -> unit = function
  | `mismatch (k, t1, t2) ->
    fprintf ppf "@[<v 2>Type mismatch.@,@[<2>Expected:%a%a@]@,@[<2>Inferred:%a%a@]@,%a@]"
      pp_print_space ()
      (Pretty.print_tp 0) t1
      pp_print_space ()
      (Pretty.print_tp 0) t2
      print_mismatch_kind k
  | `infinite_type (x, tp) ->
    fprintf ppf "@[<v 2>Cannot construct infinite type.@,Type variable %s occurs in type @[%a@]@]"
      x
      (Pretty.print_tp 0) tp

(* Takes the last `n` elements of the given list.
 * If there are fewer than n elements in the list, the list is returned as is. *)
let last_n (l : 'a list) (n : int) =
  snd @@ List.fold_right (fun x (n, l) -> if n > 0 then (n - 1, x :: l) else (0, l)) l (n, [])

let print_term_stack ppf term_stack =
  let term_stack = last_n term_stack 3 in 
  fprintf ppf "@[<v>Enclosing terms:@,%a@]"
    (pp_print_list ~pp_sep: pp_print_cut begin fun ppf e ->
      fprintf ppf "- @[%a@]" (Pretty.print_tm 0) e
    end) term_stack

let print_error_report ppf ({ error; term_stack } : Typecheck.TypeError.report): unit =
  fprintf ppf "@[<v>%a@,%a@]" print_type_error error print_term_stack term_stack

let sg =
  let ppf = Format.err_formatter in
  fprintf ppf "@[<v>";
  let open Result in match Typecheck.check_program ppf Signature.empty program with
  | Ok x -> fprintf ppf "Typechecking succeeded!@,@]"; x
  | Error report ->
    fprintf ppf "@[<v 2>Type error.@,%a@]@]" print_error_report report;
    raise Util.NotImplemented

let _ = eval_program (State.empty Format.err_formatter) program
