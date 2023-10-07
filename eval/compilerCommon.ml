open RuntimeInfo

module CtorMap = Util.StringMap
module RefMap = Util.StringMap

type index = int
type arity = int

type decl_kind =
    [ `well_known (* a definition for a value that needs to be computed *)
    | `func (* a definition for a function (a value that does not need to be computed) *)
    | `closure_body
        (* this kind of definition is not writable by the programmer, but rather these
           are the definitions for the bodies of closures synthesized during closure conversion *)
    ]

module ProgramInfo = struct
    type ref_spec = {
        kind : decl_kind;
        arity : int;
        address : address ref;
    }

    type t = {
        ctors : (index * arity) CtorMap.t;
        refs : ref_spec RefMap.t;
    }

    let empty = {
        ctors = CtorMap.empty;
        refs = RefMap.empty;
    }
end
