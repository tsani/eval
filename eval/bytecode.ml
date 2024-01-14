open RuntimeInfo
open BasicInstruction

module Instruction = struct
    type t = offset BasicInstruction.t
end

module Builder = Dlist

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
