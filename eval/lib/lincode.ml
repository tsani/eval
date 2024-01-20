type label_name = int

module Builder = Dlist

module Instruction = struct
    type t =
        | Basic of label_name BasicInstruction.t

        (* The real point of lincode is that it has 'synthetic instructions' that are
           removed/replaced during linking when certain addresses are resolved. *)

        (* SYNTHETIC INSTRUCTION.
           Doesn't actually do anything, but identifies the code address of a label. *)
        | Label of label_name

        (* SYNTHETIC INSTRUCTION. Replaced with a push of the calculated address of a heap object
            constructed from a constant appearing in the code. *)
        | LoadConstant of int
end

type builder = Instruction.t Builder.t

module Program = struct
    type function_name = string
    type well_known_name = string
    type block = Instruction.t list

    type t = {
        well_knowns : well_known_name list;
        functions : (function_name * block) list;
        top : Instruction.t Builder.t;
    }

    let empty = { well_knowns = []; functions = []; top = Builder.empty }
end
