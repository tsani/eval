module P = Pretty.Internal

(*
let program =
  let open Type in let open Term in let open Decl in let open Sugar in
  let loc = Loc.Span.fake in [
    TpDecl {
      name = "Bool";
      tvar_binders = [];
      constructors = [{
          owner_name = "Bool";
          name = "True";
          fields = [];
          loc;
        }; {
           owner_name = "Bool";
           name = "False";
           fields = [];
           loc;
         }];
      loc;
    };
    TpDecl {
      name = "List";
      tvar_binders = ["a"];
      constructors = [{
          owner_name = "List";
          name = "Nil";
          fields = [];
          loc;
        }; {
           owner_name = "List";
           name = "Cons";
           fields = [tv "a"; ty_list (tv "a")];
           loc;
         }];
      loc;
    };
    TpDecl {
      name = "Nat";
      tvar_binders = [];
      constructors = [{
          owner_name = "Nat";
          name = "Z";
          fields = [];
          loc;
        }; {
           owner_name = "Nat";
           name = "S";
           fields = [ty_nat];
           loc;
         }];
      loc;
    };
    TmDecl {
      name = "pred";
      typ = (mono @@ arrows [ty_nat] ty_nat);
      recursive = false;
      body = Some (
          lam "n" @@ case (v 0) [
            pzero --> zero;
            psucc (pv "n'") --> v 0;
          ]
        );
      loc;
    };
    TmDecl {
      name = "plus";
      typ = (mono @@ arrows [ty_nat; ty_nat] ty_nat);
      recursive = true;
      body = Some begin
          lams ["n"; "m"] begin
            case (v 0) [
              pzero --> v 1;
              psucc (pv "m'") --> apps (r "plus") [succ (v 2); v 0];
            ]
          end
        end;
      loc;
    };
    TmDecl {
      loc;
      name = "times";
      typ = (mono @@ arrows [ty_nat; ty_nat] ty_nat);
      recursive = true;
      body = Some (
          lams ["n"; "m"] @@ case (v 0) [
            pzero --> zero;
            psucc (pv "m'") --> apps (r "plus") [v 2; apps (r "times") [v 2; v 0]];
          ]
        );
    };
    TmDecl {
      loc;
      name = "fold_list";
      typ = (["a"; "b"], arrows [arrows [tv "a"; tv "b"] (tv "b"); tv "b"; ty_list (tv "a")] (tv "b"));
      recursive = true;
      body = Some begin
          lams ["f"; "e"; "l"] begin (* v 0 : List a, v 1 : b, v 2 : a -> b -> b *)
            case (v 0) [
              pnil --> v 1;
              pcons (pv "x") (pv "xs") --> (* v 0 : List a, v 1 : a, v 2 onwards above *)
              apps (v 4) [v 1; apps (r "fold_list") [v 4; v 3; v 0]]
            ]
          end
        end
    };
    TmDecl {
      loc;
      name = "map";
      typ = (["a"; "b"], arrows [arrow (tv "a") (tv "b"); ty_list (tv "a")] @@ ty_list (tv "b"));
      recursive = true;
      body = Some begin
          lams ["f"; "l"] begin
            case (v 0) [
              pnil --> nil;
              pcons (pv "x") (pv "xs") --> cons (v 3 @@@ v 1) (apps (r "map") [v 3; v 0]);
            ]
          end
        end;
    };
    TmDecl {
      loc;
      name = "sum_list";
      typ = mono @@ arrows [ty_list ty_nat] ty_nat;
      recursive = false;
      body = Some (apps (r "fold_list") [r "plus"; zero])
    };
    TmDecl {
      loc;
      name = "double";
      typ = mono @@ arrows [ty_nat] ty_nat;
      recursive = true;
      body = Some begin
          lam "n" begin
            case (v 0) [
              pconst "Z" [] --> begin const "Z" [] end;
              pconst "S" [pv "n'"] --> begin
                const "S" [const "S" [r "double" @@@ v 0]]
              end
            ]
          end
        end;
    };
    TmDecl {
      loc;
      name = "two";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (const "S" [const "S" [const "Z" []]]);
    };
    TmDecl {
      loc;
      name = "four";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (r "double" @@@ r "two");
    };
    TmDecl {
      loc;
      name = "halve";
      typ = mono @@ arrows [ty_nat] ty_nat;
      recursive = true;
      body = Some begin
          lam "n" begin
            case (v 0) [
              pconst "Z" [] --> const "Z" [];
              pconst "S" [pconst "Z" []] --> const "Z" [];
              pconst "S" [pconst "S" [pv "n'"]] --> const "S" [r "halve" @@@ v 0];
            ]
          end
        end;
    };
    TmDecl {
      loc;
      name = "half_of_four";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (r "halve" @@@ r "four");
    };
    TmDecl {
      loc;
      name = "length";
      typ = (["a"], arrows [ty_list @@ tv "a"] ty_nat);
      recursive = true;
      body = Some begin
          lam "l" begin
            case (v 0) [
              pconst "Nil" [] --> const "Z" [];
              pconst "Cons" [ignored; pv "xs"] --> const "S" [r "length" @@@ v 0];
            ]
          end
        end
    };
    TmDecl {
      loc;
      name = "sample_list";
      typ = mono @@ ty_list ty_nat;
      recursive = false;
      body = Some (list [nat 0; nat 1; nat 2; nat 3; nat 4]);
    };
    TmDecl {
      loc;
      name = "sample_list_sum";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (r "sum_list" @@@ r "sample_list");
    };
    TmDecl {
      loc;
      name = "sample_list_length";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (r "length" @@@ r "sample_list")
    };
    TmDecl {
      loc;
      name = "replicate";
      typ = (["a"], arrows [tv "a"; ty_nat] @@ ty_list (tv "a"));
      recursive = true;
      body = Some begin
          lams ["x"; "n"] begin
            case (v 0) [
              pzero --> nil;
              psucc (pv "n'") --> cons (v 2) (apps (r "replicate") [v 2; v 0]);
            ]
          end;
        end
    };
    TmDecl {
      loc;
      name = "list_of_lists";
      typ = mono @@ (ty_list (ty_list ty_nat));
      recursive = false;
      body = Some (apps (r "replicate") [r "sample_list"; nat 5])
    };
    TmDecl {
      loc;
      name = "list_of_nats";
      typ = mono @@ (ty_list ty_nat);
      recursive = false;
      body = Some (apps (r "map") [r "length"; r "list_of_lists"]);
    };
    TpDecl {
      loc;
      name = "Tree";
      tvar_binders = ["a"];
      constructors = [{
          owner_name = "Tree";
          name = "Empty";
          fields = [];
          loc;
        }; {
           owner_name = "Tree";
           name = "Node";
           fields = ([tv "a"; ty_list (ty_tree (tv "a"))]);
           loc;
         }]
    };
    TmDecl {
      loc;
      name = "fold_tree";
      typ = ( ["a"; "b"],
              (* (a -> List b -> b) -> b -> Tree a -> b *)
              arrows [arrows [tv "a"; ty_list (tv "b")] (tv "b"); tv "b"; ty_tree (tv "a")] (tv "b")
            );
      recursive = true;
      body = Some begin
          lams ["f"; "e"; "t"] begin
            case (v 0) (* v 0 : Tree a, v 1 : b, v 2: a -> List b -> b *) [
              pconst "Empty" [] --> v 1;
              pconst "Node" [pv "x"; pv "ts"] -->
              (* v 0 : List (Tree a), v 1 : a, v 2 : Tree a; v 3 : b, v 4 : a -> List b -> b *)
              apps (v 4) [v 1; apps (r "map") [apps (r "fold_tree") [v 4; v 3]; v 0]];
            ]
          end
        end;
    };
    TmDecl {
      loc;
      name = "tree_size";
      typ = (["a"], arrows [ty_tree (tv "a")] ty_nat);
      recursive = false;
      body = Some begin
          apps (r "fold_tree") [
            lams ["x"; "r"] begin (* v 0 : List Nat, v 1 : a *)
              succ (r "sum_list" @@@ v 0)
            end;
            zero;
          ]
        end;
    };
    TmDecl {
      loc;
      name = "sample_tree";
      typ = mono @@ ty_tree ty_nat;
      recursive = false;
      body = Some begin
          node zero [
            node (nat 1) [empty_tree; node (nat 2) []; node (nat 3) []];
        (*
        node (nat 4) [node (nat 5) [node (nat 6) []]];
        empty_tree;
        node (nat 7) [
          node (nat 8) [];
          node (nat 9) [node (nat 10) []];
          node (nat 11) [node (nat 12) [node (nat 13) []]];
        ];
        *)
          ];
        end
    };
    TmDecl {
      loc;
      name = "sample_tree_size";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (r "tree_size" @@@ r "sample_tree");
    };
    TmDecl {
      loc;
      name = "fact_tr";
      typ = mono @@ (arrows [ty_nat] ty_nat);
      recursive = false;
      body = Some (
          lam "x" @@ (* fun x => *)
          recdef "fact" begin (* let rec fact = *)
            lams ["acc"; "n"] @@ (* fun acc => fun n => *)
            case (v 0) [ (* match n with *)
              pzero --> v 1; (* | 0 -> 1 *)
              psucc (pv "n'") --> apps (v 3) [apps (r "times") [v 2; v 1]; v 0]; (* | S n' -> fact (n * acc) n' *)
            ]
          end @@
          apps (v 0) [nat 1; v 1]
        );
    };
    TmDecl {
      loc;
      name = "fact5";
      typ = mono @@ ty_nat;
      recursive = false;
      body = Some (
          r "fact_tr" @@@ nat 5
        );
    };
  ]
   *)

open Format

let read_file filename =
  let h = open_in_bin filename in
  let s = really_input_string h (in_channel_length h) in
  close_in h;
  s

let print_evaluated_program ppf (sg_t, sg_e, program) =
  let open Format in
  let open Syntax.Internal in
  let print_tvar_binders =
    pp_print_list ~pp_sep: (fun ppf _ -> ()) (fun ppf x -> fprintf ppf " %s" x)
  in
  let print_ctor ppf Decl.({ name; fields }) =
    fprintf ppf "| @[<hv 2>%s@ @[%a@]@]"
      name
      (pp_print_list ~pp_sep: pp_print_space (P.print_tp 10)) fields
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
        (P.print_tp 0) typ
        (P.print_value 0) body
  in
  fprintf ppf "@[<v>%a@]" (pp_print_list ~pp_sep: pp_print_cut print_decl) program

let main () =
  let filename = Array.get Sys.argv 1 in
  let input = read_file filename in
  let epf = err_formatter in
  let ppf = std_formatter in
  match Parser.(parse_only program) filename input with
  | Result.Error e ->
    fprintf epf "%a@." Parser.ParseError.print e
  | Result.Ok program ->
    fprintf ppf "Parsing succeeded.@.";
    match Scopecheck.check_program [] [] [] program with
    | Result.Error e ->
      fprintf epf "%a@." Scopecheck.Error.print e
    | Result.Ok program ->
      fprintf ppf "Scopechecking succeeded.@.";
      match Typecheck.check_program epf Syntax.Internal.Signature.empty program with
      | Result.Error report -> Typecheck.Error.print_report epf report;
      | Result.Ok sg_t ->
        fprintf ppf "Typechecking succeeded.@.";
        match Eval.(program (State.empty epf)) program with
        | Result.Error e -> fprintf ppf "@[<v 2>Runtime error.@,%a@]@." Eval.RuntimeError.print e
        | Result.Ok Eval.State.({ sg = sg_e }) ->
          fprintf ppf "Evaluation finished.@.%a@." print_evaluated_program (sg_t, sg_e, program)

let _ = main ()
