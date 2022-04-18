open Syntax

(* Maps tvar names to their possible instantiation *)
type sub = tp option Util.StringMap.t

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
let rec all_in : tp -> tmvar_name list = function
  | Int -> []
  | Arrow (t1, t2) -> all_in t1 @ all_in t2
  | TVar _ -> []
  | TMVar x -> [x]
  | Named (_, ts) -> List.fold_right (fun tp l2 -> all_in tp @ l2) ts []

(* Computes all TMVar names that appear in the given context by lifting `all_in`.
 * There can be duplicate names. The names of all TMVars are returned, whether
 * instantiated or not.
 *)
let all_in_ctx (ctx : Ctx.t) : tmvar_name list =
  (* We can just ignore the binders since bound tvars appear as TVar instead of TMVar in the tp
   *)
  List.fold_right (fun (_, tp) names -> all_in tp @ names) ctx []


(* Applies a TMVar substitution to a type.
 * Ensures that any TMVar remaining in the resulting type is uninstantiated.
 *)
let rec apply_sub (tmvars : sub) : tp -> tp = function
  | Int -> Int
  | Named (c, ts) -> Named (c, List.map (apply_sub tmvars) ts)
  | Arrow (t1, t2) -> Arrow (apply_sub tmvars t1, apply_sub tmvars t2)
  | TVar x -> TVar x
  | TMVar x -> begin match lookup tmvars x with
    | `inst t -> apply_sub tmvars t
    | `uninst -> TMVar x
    | `not_found -> raise @@ Util.Invariant "no free TMVars allowed"
  end

(* Applies the given substitution to each type in a context. *)
let apply_sub_to_ctx (tmvars : sub) : Ctx.t -> Ctx.t =
  List.map (fun (tbinders, tp) -> (tbinders, apply_sub tmvars tp))

(* Removes all instantiated variables from a substitution *)
let prune_sub : sub -> sub = Util.StringMap.filter begin fun _ -> function
  | Some _ -> false
  | _ -> true
end
