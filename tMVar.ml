open Syntax
open Internal
open Type

module P = Pretty.Internal

(** A Type MetaVariable is essentially a free type variable, together with
    a possible instantiation
    A TMVar is written like a#n where n is a number. *)
type sub = Type.t option Util.StringMap.t

let empty_sub = Util.StringMap.empty

let extend_sub (tmvars : sub) ?(inst = None) (x : tmvar_name) = Util.StringMap.add x inst tmvars

let list_of_sub : sub -> (tmvar_name * tp option) list = Util.StringMap.bindings

let parse (s : tmvar_name) : string * int =
  match String.split_on_char '#' s with
  | [prefix; n] -> (prefix, int_of_string n)
  | _ -> raise (Util.Invariant "TMvar name is well-formed")

let make (prefix, n : string * int) : tmvar_name =
  prefix ^ "#" ^ string_of_int n

let fresh (tmvars : sub) (prefix : string) : sub * tmvar_name =
  (* Idea: find the biggest n already used for this prefix, then add one *)
  let go a _ n =
    let (prefix', n') = parse a in
    if prefix' = prefix && n' >= n then n' else n
  in
  let x = make (prefix, 1 + Util.StringMap.fold go tmvars 0) in
  let tmvars' = extend_sub tmvars x in
  (tmvars', x)

let lookup (sub : sub) x = match Util.StringMap.find_opt x sub with
  | None -> `not_found
  | Some None -> `uninst
  | Some (Some x) -> `inst x

(* Looks up an element of the TMVar substitution.
 * Throws an invariant exception if the element doesn't exist.
 *)
let lookup' (sub : sub) x : [ `uninst | `inst of tp ] = match lookup sub x with
  | `not_found -> raise @@ Util.Invariant "TMVar sub must have required element"
  | `inst x -> `inst x
  | `uninst -> `uninst

(* Computes the list of all tmvars appearing in a type, whether instantiated or not. *)
let rec all_in : tp -> (loc * tmvar_name) list = function
  | Int _ -> []
  | Arrow (_, t1, t2) -> all_in t1 @ all_in t2
  | TVar (_, _) -> []
  | TMVar (loc, x) -> [(loc, x)]
  | Named (_, _, ts) -> List.fold_right (fun tp l2 -> all_in tp @ l2) ts []

(* Computes all TMVar names that appear in the given context by lifting `all_in`.
 * There can be duplicate names. The names of all TMVars are returned, whether
 * instantiated or not.
 *)
let all_in_ctx (ctx : Ctx.t) : (loc * tmvar_name) list =
  (* We can just ignore the binders since bound tvars appear as TVar instead of TMVar in the tp
   *)
  List.fold_right (fun (_, (_, tp)) names -> all_in tp @ names) ctx []


(* Applies a TMVar substitution to a type.
 * Ensures that any TMVar remaining in the resulting type is uninstantiated. *)
let rec apply_sub (tmvars : sub) : tp -> tp = function
  | Int loc -> Int loc
  | Named (loc, c, ts) -> Named (loc, c, List.map (apply_sub tmvars) ts)
  | Arrow (loc, t1, t2) -> Arrow (loc, apply_sub tmvars t1, apply_sub tmvars t2)
  | TVar (loc, x) -> TVar (loc, x)
  | TMVar (loc, x) -> begin match lookup tmvars x with
    | `inst t ->
       (* Format.(fprintf err_formatter "going under var %s@," x); *)
       apply_sub tmvars t
    | `uninst -> TMVar (loc, x)
    | `not_found -> raise @@ Util.Invariant "no free TMVars allowed"
  end

(* Applies the given substitution to each type in a context. *)
let apply_sub_to_ctx (tmvars : sub) : Ctx.t -> Ctx.t =
  List.map (fun (x, (tbinders, tp)) -> (x, (tbinders, apply_sub tmvars tp)))

(* Removes all instantiated variables from a substitution *)
let prune_sub : sub -> sub = Util.StringMap.filter begin fun _ -> function
  | Some _ -> false
  | _ -> true
end

let print_sub ppf (tmvars : sub) : unit =
  let open Format in
  let print_inst ppf = function
    | None -> fprintf ppf "<uninst>"
    | Some tp -> P.print_tp 0 ppf tp
  in
  pp_print_list ~pp_sep: pp_print_cut
    (fun ppf (x, inst) -> fprintf ppf "- %s = @[%a@]" x print_inst inst)
    ppf
    (Util.StringMap.bindings tmvars)

(** Decides whether a given uninstantiated tmvar appears in a type *)
let rec occurs (tmvars : sub) (x : tmvar_name) : tp -> bool = function
  | Named (_, _, ts) -> List.exists (occurs tmvars x) ts
  | Int _ -> false
  | TVar (_, _) -> false
  | Arrow (_, t1, t2) -> occurs tmvars x t1 || occurs tmvars x t2
  | TMVar (_, y) -> match lookup' tmvars y with
    | `uninst -> x = y
    | `inst t -> occurs tmvars x t

(** Resolves a chain of TMVar-TMVar instantiations.
    Invariant: if chase tmvars t = TMVar a then lookup tmvars a = `uninst *)
let rec chase (tmvars : sub) (t : tp) : tp = match t with
  | TMVar (loc, x) -> begin match lookup' tmvars x with
    | `uninst -> TMVar (loc, x)
    | `inst t -> chase tmvars t
  end
  | _ -> t
