type 'a t = 'a list -> 'a list

let cat (b1 : 'a t) (b2 : 'a t) : 'a t = fun p -> b1 (b2 p)

let single (i : 'a) : 'a t = fun p -> [i] @ p

let chunk (l : 'a list) : 'a t = fun p -> l @ p

let empty : 'a t = fun x -> x

let cats (bs : 'a t list) : 'a t = List.fold_right cat bs empty

let build (b : 'a t) : 'a list = b []
