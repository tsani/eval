(** A scope is a weak form of context, in which we merely track the names of variables, without any
    associated information such as a type. Scopes are used during the scopechecking phase that
    transforms external syntax into internal syntax. *)

open BasicSyntax

type entry = var_name
type t = entry list

let empty : t = []
let single x : t = [x]

let extend sco x = x :: sco
(* Extends a scope with a binding only if it's recursive. *)
let extend_rec rec_flag = match rec_flag with
  | Rec -> extend
  | NonRec -> fun sco x -> sco
let lookup : t -> index -> entry option = lookup_var

let extend_many (s : t) (xs : entry list) : t = List.fold_left extend s xs

let index_of x : t -> index option =
  let rec go i = function
    | [] -> None
    | x' :: xs when x' = x -> Some i
    | _ :: xs -> go (i+1) xs
  in
  go 0
