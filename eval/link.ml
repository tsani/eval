(* "linking" is the process of combining all function code into a single code segment.
   This process needs to resolve all unknown addresses and labels. *)

open RuntimeInfo

module LabelMap = Util.IntMap (* maps labels (ints) to their position in this function *)

module L = Lincode
module B = Bytecode
module LI = L.Instruction
module BI = B.Instruction
module I = BasicInstruction

let resolve_labels (body : LI.t list) : BI.t list =
    (** Removes all Label nodes from the given body while computing a map associating label numbers
        to indices in the body that the label refers to. *)
    let rec unlabel (map : offset LabelMap.t) (i : int) (body : LI.t list)
            : offset LabelMap.t * BI.t list =
        match body with
        | [] -> (map, [])
        | Label l :: rest -> unlabel (LabelMap.add l i map) i rest
        | Basic instr :: rest ->
            let (map, rest) = unlabel map (i+1) rest in
            (map, instr :: rest)
    in
    let label_map, unlabelled_body = unlabel LabelMap.empty 0 body in
    let calculate_offset = function
        | (i, I.Jump (mode, l)) -> begin match LabelMap.find_opt l label_map with
            | Some label_index -> I.Jump (mode, label_index - i)
            | None -> Util.invariant "[interpret] all labels have known positions"
        end
        | (_, instr) -> instr
    in
    Util.enumerate 0 unlabelled_body |> List.map calculate_offset

(** Resolves the addresses of all these functions, assembling the code segment.
    Each function body also gets its labels resolved in the process. *)
let resolve_addresses
        (info : ProgramInfo.t)
        (bodies : (string * LI.t list) list)
        : BI.t list =
    let rec go i = function
        | [] -> []
        | ("_", body) :: bodies -> (* the top code gets a fake name "_" *)
            let body = resolve_labels body in
            body @ go (i + List.length body) bodies
        | (name, body) :: bodies ->
            let body = resolve_labels body in
            let r = ProgramInfo.lookup_ref name info in
            r.ProgramInfo.address := Int64.of_int i;
            body @ go (i + List.length body) bodies
    in
    go 0 bodies

(** Populates a given runtime heap by encoding a heap object for each constant in the program info.
    Returns an updated runtime heap and a mapping from each constant tag to its heap address. *)
let populate_heap_with_constants
    (cts : Constant.spec Constant.Map.t) (heap : Heap.Runtime.t) :
        Heap.addr Constant.Map.t * Heap.Runtime.t =
    let value_of_ref addr_map : Constant.ref -> value = function
        | `unboxed i -> i
        | `boxed tag -> match Constant.Map.find_opt tag addr_map with
            | None -> Util.invariant "[link] later constant tags only refer to earlier tags"
            | Some x -> x
    in
    let go (addr_map, runtime) (tag, Constant.({ constant })) =
        match constant with
        | Constant.String s -> failwith "todo: populate heap with string constants"
        | Constant.Const (c, rs) ->
            let blob = Array.of_list (List.map (value_of_ref addr_map) rs) in
            let spec = Heap.Object.Con { tag = c; arity = Array.length blob } in
            let obj = (spec , blob) in
            let (addr, runtime) =
                Heap.Runtime.write_next_free (Heap.Object.serialize obj) runtime
            in
            (Constant.Map.add tag addr addr_map, runtime)
    in
    Constant.Map.to_seq cts
    |> Seq.fold_left go (Constant.Map.empty, heap)

let program (info : ProgramInfo.t) (pgm : L.Program.t) : BI.t list =
    resolve_addresses info B.Program.(("_", B.Builder.build pgm.top) :: pgm.functions)
