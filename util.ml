let rec sequence_options (l : 'a option list) : 'a list option = match l with
  | [] -> Some []
  | None :: _ -> None
  | Some x :: xs -> match sequence_options xs with
    | None -> None
    | Some xs -> Some (x :: xs)

let map_option (f : 'a -> 'b) (o : 'a option) : 'b option = match o with
  | Some x -> Some (f x)
  | None -> None

module StringMap = Map.Make(String)

exception Invariant of string
exception NotImplemented

