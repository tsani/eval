(** An ordered set. *)
type 'a t = 'a list

let rec insert x = function
  | [] -> [x]
  | y :: ys when x = y -> y :: ys
  | y :: ys -> y :: insert x ys

let rec insert_index x = function
  | [] -> ([x], 1)
  | y :: ys when x = y -> (y :: ys, 0)
  | y :: ys -> let ys, i = insert_index x ys in (y :: ys, i + 1)

let empty = []
let singleton x = [x]

let of_list l = List.fold_right insert empty l

let to_list s = s

let rec union s1 s2 = match s1 with
  | [] -> s2
  | x :: s1' -> union s1' (insert x s2)

let unions ss = List.fold_right union ss []

(** delete s l removes all elements of l from s. *)
let delete s l = List.filter (fun x -> not @@ List.mem x l) s
