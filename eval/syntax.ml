(* All Eval syntax and intermediate representations. *)

open BasicSyntax

(** External syntax is essentially the representation stored in text files. *)
module External = struct
  module Type = struct
    type t =
      | Builtin of Loc.span * builtin_tp
      | Arrow of Loc.span * t * t
      | TVar of Loc.span * tvar_name
      | Named of Loc.span * tp_name * t list

    let loc_of_tp = function
      | Builtin (loc, _) -> loc
      | Arrow (loc, _, _) -> loc
      | TVar (loc, _) -> loc
      | Named (loc, _, _) -> loc
  end

  (** A term is something that we can evaluate. *)
  module Term = struct
    type loc = Loc.span

    (** The syntax of patterns, which appear on the left of arrows in match-expression cases. *)
    type pattern =
      | LiteralPattern of Loc.span * literal
      | ConstPattern of Loc.span * ctor_name * pattern list
      | VariablePattern of Loc.span * var_name
      | WildcardPattern of Loc.span

    let loc_of_pattern = function
      | ConstPattern (loc, _, _) -> loc
      | LiteralPattern (loc, _) -> loc
      | VariablePattern (loc, _) -> loc
      | WildcardPattern loc -> loc

    type head =
      (* in external syntax, we can't tell apart a local var ref from a ref to
         another definition, so there is no case for "ref" -- we simply have 'Var'
         and the kind of variable is disambiguated during scopechecking.
         However, the external syntax does distinguish already between variables and constructors,
         since variables use lowercase names, whereas constructors begin with an uppercase letter.
         *)
      | Var of loc * var_name
      | Const of loc * ctor_name
      | Prim of loc * Prim.t

    let loc_of_head = function
      | Var (loc, _) -> loc
      | Const (loc, _) -> loc
      | Prim (loc, _) -> loc

    type t =
      | Lit of loc * literal
      | Fun of loc * (loc * var_name) * t
      | App of loc * head * spine
      | Let of loc * rec_flag * (loc * var_name) * t * t
      | Match of loc * t * case list

     and spine = t list
     and case = Case of loc * pattern * t

     let loc_of_tm = function
       | Lit (loc, _) -> loc
       | App (loc, _, _) -> loc
       | Fun (loc, _, _) -> loc
       | Let (loc, _, _, _, _) -> loc
       | Match (loc, _, _) -> loc

     let case_body (Case (_, _, body)) = body
  end

  (** Declarations introduce new names. Processing a declaration typically causes a state change.
   *)
  module Decl = struct
    (** A declaration for a term. *)
    type tm = {
      name : tm_name;
      typ : Type.t option;
      recursive : bool;
      body : Term.t;
      loc : Loc.span;
    }

    (** A declaration for a constructor. *)
    type ctor = {
      name : ctor_name;
      fields : Type.t list;
      loc : Loc.span;
    }

    (** A declaration for a type. *)
    type tp = {
      name : tp_name;
      tvar_binders : tvar_name list;
      constructors : ctor list;
      loc : Loc.span;
    }

    (** A toplevel declaration either introduces a named term, or a named type. *)
    type t =
      | TpDecl of tp
      | TmDecl of tm

    let loc_of_decl = function
      | TpDecl { loc } -> loc
      | TmDecl { loc } -> loc

    (** A program is a sequence of declarations. *)
    type program = t list
  end
end

(** Internal syntax is the result of scopechecking, during which various disambiguations are
    performed.
    Internal syntax is the syntax that we typecheck. *)
module Internal = Synint

(** Syntax of terms after closure conversion.
    The point of this syntax is that the construction of anonymous functions capturing their
    definition environment is eliminated.
    The construction of a closure is made explicit via an MkClo node, which specifies the _name_ of
    a function together with an _environment renaming_.

    The operational semantics of an MkClo is to compose the environment renaming with the current
    environment to construct a minimal environment required to later apply the closure.

    The evaluation judgment for closed syntax is:
        rho_e; rho_p |- t !! v
    meaning that in environments `rho_e` and `rho_p`, we evaluate a term `t` to a value `v`.

    There are two environments because in closed syntax there are two kinds of variables:
        - an EVar is an index into the closure environment `rho_e`
        - a BVar is an index into the parameter environment `rho_p`

    A 'pure function' (in contrast with a proper closure) has an empty closure environment `rho_e`
    and the construction of a pure function can be detected when the environment renaming of an
    `MkClo` is also empty.
 *)
module Closed = struct
    type var = [ `bound of index | `env of index ]

    module EnvRen = struct
        (* A renaming for an environment. Used to compute the restricted environment for a closure. *)
        type t = var OSet.t
        let insert x s = OSet.insert_index x s
        let empty = OSet.empty
        let fold = OSet.fold
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
               The name is actually lazily calculated due to the implementation of closure conversion.
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
            typ : Internal.Type.t;
            body : Term.t;
            param_cnt : int;
        }

        let defines_function { param_cnt ; _ } = param_cnt > 0
    end

    (* NOTE [env-comp]
       The composition of an environment pair an environment renaming is the following.
       This function isn't ever actually used, but a realization of it appears when we compile a
       MkClo node.  *)
    let rec env_comp (rho_e, rho_p) theta = match theta with
        | [] -> []
        | `env i :: theta' -> Internal.Env.lookup' rho_e i :: env_comp (rho_e, rho_p) theta'
        | `bound i :: theta' -> Internal.Env.lookup' rho_p i :: env_comp (rho_e, rho_p) theta'
end
