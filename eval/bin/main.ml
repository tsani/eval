open Eval

module P = Pretty

open Format

let read_file filename =
    let h = open_in_bin filename in
    let s = really_input_string h (in_channel_length h) in
    close_in h;
    s

type error =
    | ParseError of Parser.Error.t
    | ScopecheckError of Scopecheck.Error.t
    | TypecheckError of Typecheck.Error.report
let parse_error e = ParseError e
let scopecheck_error e = ScopecheckError e
let typecheck_error e = TypecheckError e

let result_main epf ppf =
    let (let*) = Result.bind in
    let filename = Array.get Sys.argv 1 in
    let input = read_file filename in
    let* program =
        Parser.(parse_only program) filename input
        |> Result.map_error parse_error
    in
    fprintf ppf "Parsing succeeded.@.";
    let* program =
        Scopecheck.check_program [] [] [] program
        |> Result.map_error scopecheck_error
    in
    fprintf ppf "Scopechecking succeeded.@.";
    let* _sg_t =
        Typecheck.check_program epf Syntax.Internal.Signature.empty program
        |> Result.map_error typecheck_error
    in
    fprintf epf "@.";
    fprintf ppf "Typechecking succeeded.@.";
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
    let heap = Heap.Runtime.make Interpret.heap_size in
    let heap, code = Link.program info heap pgm in
    fprintf ppf "Linking succeeded.@.";
    fprintf ppf "%a@." P.Bytecode.print_linked_program code;
    let (final_state, _status) =
        Interpret.(program Ctx.({ code = Array.of_list code }) (State.initial heap))
    in
    fprintf ppf "@[<v 2>Interpretation succeeded.@,@[<v>%a@]@]@."
        (pp_print_list ~pp_sep: pp_print_cut (fun ppf (name, v) ->
            fprintf ppf "%s = %Ld" name v))
        (Interpret.well_knowns final_state);
    Result.ok ()

let main () =
    let epf = err_formatter in
    let ppf = std_formatter in
    match result_main epf ppf with
    | Result.Ok () -> fprintf ppf "@.Have a nice day :)@."
    | Result.Error e -> match e with
        | ParseError e -> fprintf epf "%a@." Parser.Error.print e
        | ScopecheckError e -> fprintf epf "%a@." Scopecheck.Error.print e
        | TypecheckError e -> fprintf epf "%a@." Typecheck.Error.print_report e
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

let _ = main ()
