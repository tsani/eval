type ('e, 'a) t = Error of 'e | Ok of 'a

type ('e, 'a) result = ('e, 'a) t

let bind (r : ('e, 'a) result) (k : 'a -> ('e, 'b) result) : ('e, 'b) result = match r with
  | Ok x -> k x
  | Error e -> Error e

module Syntax = struct
  let ($) = bind
end

let map (f : 'a -> 'b) (r : ('e, 'a) result) : ('e, 'b) result = match r with
  | Ok x -> Ok (f x)
  | Error e -> Error e

let map_error (f : 'e -> 'g) (r : ('e, 'a) result) : ('g, 'a) result = match r with
  | Ok x -> Ok x
  | Error e -> Error (f e)

let ok x = Ok x
let error e = Error e

let rec traverse (f : 'a -> ('e, 'b) result) (l : 'a list) : ('e, 'b list) result =
  match l with
  | [] -> ok []
  | x :: xs ->
    bind (f x) @@ fun y ->
    bind (traverse f xs) @@ fun ys ->
    ok (y :: ys)
