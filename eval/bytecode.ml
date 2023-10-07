open RuntimeInfo

type call_mode =
    (* In each, the int is the count of arguments *)
    [ `func of int
    | `closure of int
    | `pap of int
    | `dynamic
    ]

(** Identifies the stack to push to. *)
type stack_mode = [ `param | `return ]

(** Identifies which kind of value to load. *)
type load_mode =
    [ `env of int (* loads from the environment *)
    | `param of int (* loads a function parameter *)
    | `well_known of string (* loads a well-known value *)
    (* | `from_top (* duplicates a value some distance from the top of the stack *)
       (* redundant with `param tbh *)
     *)
    | `field of int (* loads a field from a construtor *)
    | `func of address ref
      (* when we are writing the instruction to load the statically-known address of a function, we
         actually don't know what that address is yet. That will depend on the precise positions of
         the instructions in the output byte stream.
         We use this ref (initialized with zero) to later update when we do figure out what the
         address is. *)
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
    | `func
    ]

type offset = int

module Instruction = struct
    type 'l t =
        (* Enter a function.
           The shape of the stack, from top to bottom, is <function>, <arg 1>, <arg 2>, etc. *)
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
        | Load of load_mode

        | Store of string

        (* Performs a primitive operation. Consumes from the stack whatever the arity of the prim is *)
        | Prim of BasicSyntax.Prim.t

        (* Performs a jump. Conditional jumps consume the top of the stack. *)
        | Jump of jump_mode * 'l
end

module Text = struct
    type 'l t = 'l Instruction.t list

    type 'l builder = 'l t -> 'l t

    let cat (b1 : 'l builder) (b2 : 'l builder) : 'l builder = fun p -> b1 (b2 p)

    let single (i : 'l Instruction.t) = fun p -> [i] @ p

    let chunk (l : 'l Instruction.t list) = fun p -> l @ p

    let empty : 'l builder = fun x -> x

    let cats (bs : 'l builder list) : 'l builder = List.fold_right cat bs empty

    let build b = b []
end

module Program = struct
    type t = {
        well_knowns : string list;
        functions : (string * string Text.t) list;
        top : string Text.builder;
    }

    let empty = { well_knowns = []; functions = []; top = Text.empty }
end
