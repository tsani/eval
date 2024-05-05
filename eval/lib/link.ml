(* "linking" is the process of combining all function code into a single code segment.
   This process needs to resolve all unknown addresses and labels. *)

open RuntimeInfo

module LabelMap = Util.IntMap (* maps labels (ints) to their position in this function *)

module L = Lincode
module B = Bytecode
module LI = L.Instruction
module BI = B.Instruction
module I = BasicInstruction

type constant_addresses = Heap.addr Constant.Map.Internal.t

let load_constant cas (tag : Constant.tag) : BI.t =
    match Constant.Map.Internal.find_opt tag cas with
    | None -> Util.invariant "[load_constant] tag is defined"
    | Some a -> I.Push (`param, `address (ref a))

let resolve_labels (cas : constant_addresses) (body : LI.t list) : BI.t list =
    (* Removes all Label nodes from the given body while computing a map associating label numbers
        to indices in the body that the label refers to. *)
    let rec unlabel (map : offset LabelMap.t) (i : int) (body : LI.t list)
            : offset LabelMap.t * BI.t list =
        match body with
        | [] -> (map, [])
        | Label l :: rest -> unlabel (LabelMap.add l i map) i rest
        | Basic instr :: rest ->
            let (map, rest) = unlabel map (i+1) rest in
            (map, instr :: rest)
        | LoadConstant c :: rest ->
            let (map, rest) = unlabel map (i+1) rest in
            (map, load_constant cas c :: rest)
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
        (cas : constant_addresses)
        (info : ProgramInfo.t)
        (bodies : (string * LI.t list) list)
        : BI.t list =
    let rec go i = function
        | [] -> []
        | ("_", body) :: bodies -> (* the top code gets a fake name "_" *)
            let body = resolve_labels cas body in
            body @ go (i + List.length body) bodies
        | (name, body) :: bodies ->
            let body = resolve_labels cas body in
            let r = ProgramInfo.lookup_ref name info in
            r.ProgramInfo.address := Int64.of_int i;
            body @ go (i + List.length body) bodies
    in
    go 0 bodies

(** Populates a given runtime heap by encoding a heap object for each constant in the program info.
    Returns an updated runtime heap and a mapping from each constant tag to its heap address. *)
let populate_heap_with_constants
    (cts : Constant.Map.t) (heap : Heap.Runtime.t) :
        constant_addresses * Heap.Runtime.t =
    let value_of_ref addr_map : Constant.ref -> value = function
        | `unboxed i -> i
        | `boxed tag -> match Constant.Map.Internal.find_opt tag addr_map with
            | None -> Util.invariant "[link] later constant tags only refer to earlier tags"
            | Some x -> x
    in
    let go (addr_map, runtime) (tag, Constant.({ constant })) =
        match constant with
        | Constant.String _s -> failwith "todo: populate heap with string constants"
        | Constant.Const (c, rs) ->
            let blob = Array.of_list (List.map (value_of_ref addr_map) rs) in
            let spec = Heap.Object.Con { tag = c; arity = Array.length blob } in
            let obj = (spec, blob) in
            let (addr, runtime) =
                Heap.Runtime.write_next_free (Heap.Object.serialize obj) runtime
            in
            (Constant.Map.Internal.add tag addr addr_map, runtime)
    in
    Constant.Map.to_seq cts
    |> Seq.fold_left go (Constant.Map.Internal.empty, heap)

(** Resolves all unknown addresses and links the entire program with a particular runtime heap.
    - The runtime heap is populated with all constants from the program.
    - LoadConstant instructions are replaced with pushes of static heap addresses
    - Label instructions are eliminated
    - Jump(-to-label) instructions are replaced with relative jumps
    - addresses of functions in static calls are resolved
        (compile.ml just gives them dummy values of 0)
*)
let program (info : ProgramInfo.t) (heap : Heap.Runtime.t) (pgm : L.Program.t) : Heap.Runtime.t * BI.t list =
    let constant_addresses, heap = populate_heap_with_constants info.constants heap in
    (heap, resolve_addresses constant_addresses info @@ ("_", B.Builder.build pgm.top) :: pgm.functions)
