open BasicSyntax
open RuntimeInfo

module CtorMap = Util.StringMap
module RefMap = Util.StringMap

module I = Syntax.Internal

type decl_kind =
    [ `well_known (* a definition for a value that needs to be computed *)
    | `func (* a definition for a function (a value that does not need to be computed) *)
    | `closure_body
        (* this kind of definition is not writable by the programmer, but rather these
           are the definitions for the bodies of closures synthesized during closure conversion *)
    ]

type ref_spec = {
    kind : decl_kind;
    arity : int;
    address : address ref;
}

type ref_map = ref_spec RefMap.t

let new_ref_spec kind arity = ({ kind; arity; address = ref 0L })

type ctor_spec = {
    arity : int;
    tag : ctor_tag;
}

type ctor_map = ctor_spec CtorMap.t

type t = {
    ctors : ctor_map;
    refs : ref_map;
}

let empty = {
    ctors = CtorMap.empty;
    refs = RefMap.empty;
}

let lookup_ref name info = match RefMap.find_opt name info.refs with
    | None -> Util.invariant "[programInfo] all refs are known"
    | Some x -> x

let lookup_ctor name info = match CtorMap.find_opt name info.ctors with
    | None -> Util.invariant "[programInfo] all ctors are known"
    | Some x -> x

let add_ref name spec info = { info with refs = RefMap.add name spec info.refs }
let add_new_ref name (kind, arity) info = add_ref name (new_ref_spec kind arity) info

(** Counts sequential Fun nodes at the root of the given term. *)
let rec arity : I.Term.t -> int = function
    | I.Term.Fun (_, _, t) -> 1 + arity t
    | _ -> 0

(** Extract relevant metadata from a program signature to be used in later compiler stages.
        * The arity of every constructor and top-level function.
        * Each constructor gets associated with an integer tag (its index +1) *)
let collect : I.Decl.program -> t =
    List.fold_left begin fun info -> function
    | I.Decl.(TpDecl { constructors; _ }) ->
        { info with ctors =
            constructors
            |> List.map (fun I.Decl.({ name; fields; _ }) -> (name, List.length fields))
            |> List.fold_left
                (fun (i, ctors) (c, n) ->
                    (i + 1, CtorMap.add c ({ tag = i; arity = n }) ctors))
                (0, info.ctors)
            |> snd
        }
    | I.Decl.(TmDecl { body = None; _ }) ->
        Util.invariant "[programInfo] all function bodies are defined"
    | I.Decl.(TmDecl { body = Some body; name; _ }) ->
        let n = arity body in
        let kind = if n = 0 then `well_known else `func in
        { info with refs = RefMap.add name (new_ref_spec kind n) info.refs }
    end
    empty
