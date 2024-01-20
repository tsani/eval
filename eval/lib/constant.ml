(** A representation of constants suitable for being later transformed into heap objects at compile
    time.
    The key data structure is the type `t` which is an 'indirect' recursive type.
    The recursion is expressed through the use of so-called 'references' to constants, which may be
    unboxed (a literal integer constant) or boxed.
    A boxed constant reference is simply a tag, which is a key in the second key data structure, a
    `spec Map.t`. The keys into this map are generated in ascending order, which gives a critical
    property of the map's values: the tag references of any constant spec stored in the map are
    less than that item's tag.
    Lowering, which generates this map, upholds this invariant.
*)

open BasicSyntax

type tag = int

type t =
    | Const of ctor_tag * ref list
    | String of string
and ref = [ `unboxed of Int64.t | `boxed of tag ]

type spec = {
    constant : t;
}

module Map = Util.IntMap

type map = {
    map : spec Map.t;
    next : tag;
}

let empty_map = {
    map = Map.empty;
    next = 0;
}

let add c m =
    let index = m.next in
    let new_map = { map = Map.add m.next c m.map; next = m.next + 1 } in
    (index, new_map)

let lookup tag { map; _ } = Map.find_opt tag map

let lookup' tag { map; _ } = match Map.find_opt tag map with
    | Some x -> x
    | None -> Util.invariant "[constant] the map contains all constants"
