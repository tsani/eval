open BasicSyntax

(* In the closed syntax we distinguish between bound variables and environment variables. *)
type var = [ `bound of index | `env of index ]

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
        | ConstPattern of ctor_name * pattern list
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
           returned together with `f` by MkClo:
               rho_e; rho_p |- MkClo(theta, n, f) !! Clo((rho_e, rho_p) . theta, n, f)
           where `(rho_e, rho_p) . theta` is a composition of the environment pair with the
           environment renaming. See note [env-comp] below.
        *)
        | Lit of literal
        | App of head * spine
        | Let of rec_flag * t * t
        | Match of t * case list

    and spine = t list
    and case = Case of pattern * t
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
