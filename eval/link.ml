(* "linking" is the process of combining all function code into a single code segment.
   This process needs to resolve all unknown addresses and labels. *)

module LabelMap = Util.IntMap (* maps labels (ints) to their position in this function *)

open CompilerCommon
open Bytecode
open Instruction

let resolve_labels (body : int Instruction.t list) : instr list =
    (** Removes all Label nodes from the given body while computing a map associating label numbers
        to indices in the body that the label refers to. *)
    let rec unlabel (map : offset LabelMap.t) (i : int) (body : int Instruction.t list)
            : offset LabelMap.t * int Instruction.t list =
        match body with
        | [] -> (map, [])
        | Label l :: rest -> unlabel (LabelMap.add l i map) i rest
        | instr :: rest ->
            let (map, rest) = unlabel map (i+1) rest in
            (map, instr :: rest)
    in
    let label_map, unlabelled_body = unlabel LabelMap.empty 0 body in
    let calculate_offset = function
        | (i, Jump (mode, l)) -> begin match LabelMap.find_opt l label_map with
            | Some label_index -> Jump (mode, label_index - i)
            | None -> Util.invariant "[interpret] all labels have known positions"
        end
        | (_, instr) -> instr
    in
    Util.enumerate 0 unlabelled_body |> List.map calculate_offset

(** Resolves the addresses of all these functions, assembling the code segment.
    Each function body also gets its labels resolved in the process. *)
let resolve_addresses
        (pgmInfo : ProgramInfo.t)
        (bodies : (string * int Instruction.t list) list)
        : instr list =
    let rec go i = function
        | [] -> []
        | ("_", body) :: bodies -> (* the top code gets a fake name "_" *)
            let body = resolve_labels body in
            body @ go (i + List.length body) bodies
        | (name, body) :: bodies ->
            let body = resolve_labels body in
            let r = match RefMap.find_opt name pgmInfo.ProgramInfo.refs with
                | None -> Util.invariant "[link] all refs are known"
                | Some r -> r
            in
            r.ProgramInfo.address := Int64.of_int i;
            body @ go (i + List.length body) bodies
    in
    go 0 bodies

let program (pgmInfo : ProgramInfo.t) (pgm : int Program.t) : instr list =
    resolve_addresses pgmInfo Program.(("_", Text.build pgm.top) :: pgm.functions)
