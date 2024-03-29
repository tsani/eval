open RuntimeInfo

type call_mode =
    [ `func of count
    | `closure of count
    | `pap of count
    | `dynamic
    ]

(** Identifies the stack to push to. *)
type stack_mode = [ `param | `return ]

(** Identifies which kind of value to load. *)
type load_mode =
    [ `env of offset (* loads from the environment *)
    | `param of offset (* loads a function parameter *)
    | `well_known of string (* loads a well-known value *)
    | `constructor (* loads the tag of a constructor *)
    | `field of offset (* loads the value from a field of a constructor *)
    ]

type push_mode = [ `integer of value | `address of address ref ]

type jump_mode =
    [ `unconditional
    (* The following two jump modes consume a stack value and jump depending on its value. *)
    | `zero
    | `nonzero
    ]

type return_mode =
    (* returning from a closure has a little more ceremony than returning from a pure function *)
    [ `closure of int (* the count of parameters *)
    | `func of int (* the count of parameters *)
    ]

type move_mode =
    [ `param_to_return
    | `return_to_param
    ]

type status =
    [ `inexhaustive_match
    | `finished
    | `running
    | `loop
    ]

type 'label t =
    (* Enter a function.
       The shape of the stack, from top to bottom, is <function>, <arg 1>, <arg 2>, etc. *)
    | Call of call_mode

    (* Exit a function. *)
    | Ret of return_mode

    (* Construct a closure with `env_size` values popped from the stack and stored in its
       environment. The top of the stack must the address of a closure body.
       The address of the CLO object is left on the stack. *)
    | MkClo of { env_size : int; arity : int }

    (* Construct a partial application with `held_count` held arguments (popped from the stack)
       and `missing_count` missing arguments. The top of the stack must be the function code
       address. The address of the PAP object is left on the stack. *)
    | MkPap of { held_count : int ; missing_count : int }

    (* Construct a value with the given constructor tag and number of fields. That many values are
       removed from the stack. The address of the object is left on the stack. *)
    | Const of { tag : int; arity : int }

    (* Drops the value from the stack the given offset away from the top. *)
    | Pop of stack_mode * offset

    (* Loads an immediate value onto the top of the stack. *)
    | Push of stack_mode * push_mode

    (* Moves the top of one stack to the other. *)
    | Move of move_mode

    (* Loads an indirect value onto the top of the stack. *)
    | Load of load_mode

    | Store of string

    (* Performs a primitive operation. Consumes from the stack whatever the arity of the prim is *)
    | Prim of BasicSyntax.Prim.t

    (* Performs a jump. Conditional jumps consume the top of the stack. *)
    | Jump of jump_mode * 'label

    | Halt of status (* Halt `running is actually a no-op *)
