(** Closure conversion.

    Main operations:
        - Transform `Fun` nodes into `MkClo` nodes
        - Distinguish parameter variables from environment variables.
        - Hoist all nested functions into top-level functions

    The core entry point of this module is the function `term`, which closure-converts a term.

    See ../cloco.md
*)

open Syntax

module I = Syntax.Internal
module C = Syntax.Closed
module ER = C.Term.EnvRen

(** Variables with indices beyond this value are free variables.
    Comparison of an internal syntax variable's index against the watermark determines whether the
    variable is a BVar or an EVar in the closed syntax. *)
type watermark = int

(** In order to generate (somewhat meaningful) names for the anonymous functions that we hoist,
    we track the stack of names we traverse. For example, consider the code fragment

        def foo = fun x -> match x with
            | Nil -> ...
            | Cons (x, xs) ->
                let bar = fun y ->
                    map (fun z -> ...) (g y)
                in ...

    Each time we go under a binder, we push its name onto this stack.
    When we arrive at the function argument of map in this example, the name stack might look like
    ["y"; "bar"; "cons:x&xs"; "x"; "foo"]
    and we use this to synthesize the name for that anonymous function:

        foo.x.cons:x&xs.bar.y.2        -- fun z -> ...

    The other functions that appear in this example would have the names:

        foo.1                        -- fun x -> ...
        foo.x.cons:x&xs.bar.1        -- fun y -> ...

    The name `foo.x.cons:x&xs.bar.y` generated from the stack is not guaranteed to be unique, so
    ultimately we associate each such name with a counter that we increment to disambiguate in case
    of collision. The generated name involves the symbols `.`, `&`, and `:` which are forbidden in
    user-defined names and is unused elsewhere by compilation.

    To implement the hoisting of functions, the closure conversion builds a tree that holds this
    stack of names in its recursive structure. Following the stack of names ultimately leads to a
    list of closed functions that share that name prefix.
 *)
module CloTree = struct
    type t = CloTree
        of (tm_name ref * int * C.Term.t) list
           (* ^ the closed functions with this prefix, together with their parameter counts
              The reference is used to set the finalized name for this function, which happens in a
              separate pass over the full CloTree.t after the full traversal of the syntax tree. *)
        * (tm_name * t) list
           (* ^ the subtrees, stored in a mapping of one more name stack element *)

    (* Splices together two trees, concatenating their lists of functions and of subtrees. *)
    let join (CloTree (fns1, sts1)) (CloTree (fns2, sts2)) = CloTree (fns1 @ fns2, sts1 @ sts2)

    let empty = CloTree ([], [])

    let add_subtree (subtree : tm_name * t) (CloTree (fns, sts)) =
        CloTree (fns, subtree :: sts)

    let add_function (fn : tm_name ref * int * C.Term.t) (CloTree (fns, sts)) =
        CloTree (fn :: fns, sts)
end

(* The structure of the CloTree.t roughly mirrors the structure of the code. *)

(* Closure-converts the index of a variable according to a watermark, extending the given
   environment renaming in case the index refers to an environment variable. *)
let index (w : watermark) (theta : ER.t) (i : index) : ER.t * C.Term.var =
    if i < w then (theta, `bound i) else
    let theta, j = ER.insert (`env (i - w)) theta in
    (theta, `env j)

(* Closure-converts the head of an application according to a watermark, extending the given
   environment renaming in the case for a variable. *)
let head (w : watermark) (theta : ER.t) : I.Term.head -> ER.t * C.Term.head = function
    | I.Term.Var (_, i) ->
        let theta, var = index w theta i in
        (theta, C.Term.Var var)
    | I.Term.Const (_, c) -> (theta, C.Term.Const c)
    | I.Term.Ref (_, r) -> (theta, C.Term.Ref r)
    | I.Term.Prim (_, p) -> (theta, C.Term.Prim p)

(** Hoists an environment renaming across a binder boundary while extending an outer environment
    renaming.

    Invariant:
        hoist_env_ren w theta_out theta = (theta_out', theta')
    such that
    * length theta' = length theta
    * length theta_out' > length theta_out
    *)
let rec hoist_env_ren w (theta_out, theta : ER.t * ER.t) : ER.t * ER.t =
    let f v (theta_out, theta') = match v with
        | `bound i -> Util.invariant "hoist env_ren contains no bvars" (* this shouldn't happen *)
        | `env i ->
            let (theta_out', v) = index w theta_out i in
            (theta_out', v :: theta') (* XXX this is suspicious *)
    in
    ER.fold f theta (theta_out, ER.empty)

(* Closure-converts a term. *)
let rec term (w : watermark) (theta : ER.t) : I.Term.t -> ER.t * CloTree.t * C.Term.t =
    function
    | I.Term.Fun _ as e ->
        let xs, e = I.Term.collapse_funs e in
        let w' = List.length xs in (* the watermark to use within the function body *)
        let theta_in, ct, e_closed = term w' ER.empty e in
        (* [theta_in]e_closed = e *)
        let name = ref "[no name yet]" in
        let (theta', theta_in') = hoist_env_ren w' (theta, theta_in) in
        let path_el = String.concat "&" xs in
        let ct' =
            CloTree.(empty |> add_subtree (path_el, ct) |> add_function (name, w', e_closed))
        in
        (theta', ct', MkClo (theta_in', w', fun () -> !name))

    | I.Term.Let (_, _, (_, x), e1, e2) -> failwith "todo"

    | I.Term.App (_, tH, tS) ->
            let theta, tH_closed = head w theta tH in
            let theta, ct, tS_closed = spine w theta tS in
            (theta, ct, C.Term.App (tH_closed, tS_closed))

and spine w theta : I.Term.spine -> ER.t * CloTree.t * C.Term.spine = function
    | [] -> (theta, CloTree.empty, [])
    | t :: tS ->
        let (theta, ct1, t_closed) = term w theta t in
        let (theta, ct, tS_closed) = spine w theta tS in
        (theta, CloTree.join ct1 ct, t_closed :: tS_closed)


(* fun x -> let a = f _0 in ---- clo [] 1 @@ let a = f 0b in
   fun y -> let b = g _1 _0 in -- clo [0b] 1 @@ let b = g 0e 0b in
   fun z -> h _3 _2 _1 _0 ----------- clo [0b; 1b; 0e] @@ h 1e y 0e 0b *)

