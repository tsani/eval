open Eval

module P = Pretty

open Format

let read_file filename =
    let h = open_in_bin filename in
    let s = really_input_string h (in_channel_length h) in
    close_in h;
    s

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
            | Result.Ok _sg_t ->
                fprintf epf "@.";
                fprintf ppf "Typechecking succeeded.@.";
                (* match Eval.(program (State.empty epf)) program with
                | Result.Error (loc, e) ->
                    fprintf ppf "@[<hv 2>%a: runtime error:@ %a@]@."
                        Loc.print loc.Loc.Span.start
                        Eval.RuntimeError.print e
                | Result.Ok Eval.State.({ sg = sg_e }) ->
                    fprintf epf "@.";
                    fprintf ppf "Evaluation succeeded.@.%a@."
                        P.Internal.print_evaluated_program (sg_t, sg_e, program);
                        *)
                    Debug.printf "@[<v>";
                    let info = ProgramInfo.collect program in
                    let (info, low_program) =
                        Lower.program info program
                    in
                    fprintf ppf "Lowering succeeded.@.";
                    fprintf ppf "  @[<v>%a@]@." P.Low.print_program low_program;
                    let pgm = Compile.(program (Ctx.initial info) low_program) in
                    fprintf ppf "Compilation succeeded.@.";
                    fprintf ppf "@[<v>%a@]@." P.Lincode.print_program pgm;
                    let code = Link.program info pgm in
                    fprintf ppf "Linking succeeded.@.";
                    fprintf ppf "%a@." P.Bytecode.print_linked_program code;
                    let (final_state, _status) =
                        Interpret.(program Ctx.({ code = Array.of_list code }) (State.initial ()))
                    in
                    fprintf ppf "@[<v 2>Interpretation succeeded.@,@[<v>%a@]@]@."
                        (pp_print_list ~pp_sep: pp_print_cut (fun ppf (name, v) ->
                            fprintf ppf "%s = %Ld" name v))
                        (Interpret.well_knowns final_state)

let _ = main ()
