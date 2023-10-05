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
            | Result.Ok sg_t ->
                fprintf ppf "Typechecking succeeded.@.";
                match Eval.(program (State.empty epf)) program with
                | Result.Error (loc, e) ->
                    fprintf ppf "@[<hv 2>%a: runtime error:@ %a@]@."
                        Loc.print loc.Loc.Span.start
                        Eval.RuntimeError.print e
                | Result.Ok Eval.State.({ sg = sg_e }) ->
                    fprintf ppf "Evaluation finished.@.%a@."
                        P.Internal.print_evaluated_program (sg_t, sg_e, program);
                    let (pgmInfo, closed_program) =
                        Close.program CompilerCommon.ProgramInfo.empty program
                    in
                    fprintf ppf "Closure conversion succeeded.@.";
                    let pgm = Compile.program pgmInfo closed_program in
                    fprintf ppf "Compilation succeeded.@.";
                    fprintf ppf "@[<v>%a@]@." P.Bytecode.print_program pgm


let _ = main ()
