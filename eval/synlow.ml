open BasicSyntax

(* In the lowered syntax we distinguish between bound variables and environment variables. *)
type var = [ `bound of index | `env of index ]

type ctor_tag = int
type constant_tag = int

module EnvRen = struct
    (* A renaming for an environment. Used to compute the restricted environment for a closure. *)
    type t = var OSet.t
    let insert x s = OSet.insert_index x s
    let empty = OSet.empty
    let fold = OSet.fold

    let is_empty (r : t) : bool = r = OSet.empty
end

module Term = struct
    type pattern =
        | ConstPattern of ctor_tag * pattern list
        | LiteralPattern of literal
        | VariablePattern
        | WildcardPattern

    type head =
        | Var of var
        | Ref of tm_name
        | Const of ctor_name
        | Prim of Prim.t

    type t =
        | MkClo of EnvRen.t * int * tm_name
        (* MkClo(theta, n, f) - Constructs a closure.
         - f represents the code pointer for the closure.
         - n is the count of arguments necessary to jump to the code pointer
         - theta is an _environment renaming_ which maps the EVars in `f` to variables in the
           enclosing scope. It is used at runtime to initialize the environment that gets
           returned together with `f` by MkClo *)
        | Constant of Constant.ref
        (* All literals are represented as integers in the lowered syntax. We just distinguish
           between boxed literals and unboxed literals. *)
        | App of head * spine
        | Let of rec_flag * t * t
        | Match of t * case list

    and spine = t list
    and case = Case of pattern * int (* number of bound variables *) * t
end

module Decl = struct
    type tm = {
        name : tm_name;
        body : Term.t;
        arity : int;
    }

    let defines_function { arity; _ } = arity > 0

    type program = tm list
end
