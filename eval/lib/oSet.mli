(* The type of a set whose elements have an associated index, as in a list. *)
type 'a t = 'a list

(* An empty set. *)
val empty : 'a t

(* A singleton set. *)
val singleton : 'a -> 'a t

(* Inserts an element into the set. *)
val insert : 'a -> 'a t -> 'a t

(* Inserts an element into the set giving its index. *)
val insert_index : 'a -> 'a t -> 'a t * int

(* Computes the union of two sets. *)
val union : 'a t -> 'a t -> 'a t

(* Computes the union of a list of sets. *)
val unions : 'a t list -> 'a t

(* Set difference: `delete s1 s2` removes every item in s1 that appears in s2. *)
val delete : 'a t -> 'a t -> 'a t

(* Turns a set into a list. *)
val to_list : 'a t -> 'a list

(* Turns a list into a set. This will deduplicate the elements of the list. *)
val of_list : 'a list -> 'a t

(* Folds the set. *)
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
