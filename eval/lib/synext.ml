open BasicSyntax

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
    rec_flag : rec_flag;
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
      | TpDecl { loc; _ } -> loc
      | TmDecl { loc; _ } -> loc

  (** A program is a sequence of declarations. *)
  type program = t list
end
