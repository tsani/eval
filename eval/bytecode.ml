type call_mode =
    [ `pure of int
    | `closure of int
    | `pap of int
    | `dynamic
    ]

(** Identifies the stack to push to. *)
type stack_mode = [ `arg | `return ]

(** Identifies which kind of value to load. *)
type load_mode =
    [ `env (* loads from the environment *)
    | `param (* loads a function parameter *)
    | `value (* loads a well-known value *)
    | `from_top (* duplicates a value some distance from the top of the stack *)
    | `field (* loads a field from a construtor *)
    ]

type jump_mode =
    [ `unconditional
    (* The following two jump modes consume a stack value and jump depending on its value. *)
    | `zero
    | `nonzero
    ]

type return_mode =
    (* returning from a closure has a little more ceremony than returning from a pure function *)
    [ `closure
    | `direct
    ]

type offset = int

module type LABEL = sig
    type t
end

module type INSTR = sig
    type t

    val compile : unit -> 'a
end

module Instr (L : LABEL) : INSTR = struct
    type t =
        (* Enter a function. *)
        | Call of call_mode

        (* Exit a function. *)
        | Ret of return_mode

        (* Construct a closure with `env_size` values popped from the stack and stored in its
           environment. The top of the stack must be the function code address. The address of the CLO
           object is left on the stack. *)
        | MkClo of { env_size : int }

        (* Construct a partial application with `held_count` held arguments (popped from the stack)
           and `missing_count` missing arguments. The top of the stack must be the function code
           address. The address of the PAP object is left on the stack. *)
        | MkPap of { held_count : int ; missing_count : int }

        (* Construct a value with the given constructor tag and number of fields. That many values are
           removed from the stack. The address of the object is left on the stack. *)
        | Const of { ctor : int ; field_count : int }

        (* Compares the ctor tag of the top with the given tag. Doesn't consume the top.
           If the tag matches, then all the fields of the constructor are loaded onto the stack.
           Regardless, a boolean indicating the success of the match is loaded at the top after.
         *)
        | Match of { ctor : int }

        (* Drops the drop of the stack. *)
        | Pop of stack_mode

        (* Loads an immediate value onto the top of the stack. *)
        | Push of stack_mode * Int32.t

        (* Loads an indirect value onto the top of the stack. *)
        | Load of load_mode * int

        (* Performs a primitive operation. Consumes from the stack whatever the arity of the prim is *)
        | Prim of BasicSyntax.Prim.t

        (* Performs a jump. Conditional jumps consume the top of the stack. *)
        | Jump of jump_mode * L.t

    let compile () = failwith "todo"
end

module Program (I : INSTR) = struct
    type t = I.t list

    type builder = t -> t
end
