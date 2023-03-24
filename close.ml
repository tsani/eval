(** Closure conversion.

    Main operations:
        - Transform `Fun` nodes into `MkClo` nodes
        - Distinguish parameter variables from environment variables.
        - Hoist all nested functions into top-level functions

    The core entry point of this module is the function `term`, which closure-converts a term.

    Idea: recursively tranverse the syntax tree and pay special attention to
    when we go under a (sequence) of `Fun` nodes.
    Each time we go under a `Fun`, we might need to construct a (proper) closure.
    Count how many funs we go under; this becomes the active watermark w.
    When we encounter a variable with index i, if i < w, then the variable
    translates to a BVar with index i; else it translates to an EVar with a new
    index into the environment.

    As we encounter free variables in a function body, these are given sequential indices into the
    new environment. We construct an _environment renaming_ as output of closure conversion to map
    these new, sequential indices back to the original environment indices.
    The environment renaming ends up being used in the target program:
      [[fun x1 ... xN -> e]] = mk_clo (eta, N, [[e]])
    where `f` is a synthetic name for the function, i.e. just a code pointer, and `eta` is the
    environment renaming calculated by the closure conversion.
    The primitive `mk_clo` is compiled by a later stage into an allocation for the environment
    plus an initialization of that environment, i.e. copying the current environment's values into
    the newly allocated environment according to `eta`.
    Semantically, this is a realization of the application of `eta` to the current environment to
    compute the restricted environment needed for `f`
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
    See note [env-ren-hoist].

    Invariant:
        hoist_env_ren w theta_out theta = (theta_out', theta')
    such that
    * length theta' = length theta
    * length theta_out' > length theta_out
    *)
let rec hoist_env_ren w (theta_out, theta : ER.t * ER.t) : ER.t * ER.t =
    let f v (theta_out, theta') = match v with
        | `bound i -> failwith "hoist env_ren must not contain bvars" (* this shouldn't happen *)
        | `env i ->
            let (theta_out', v) = index w theta_out i in
            (theta_out', ER.insert v theta') (* XXX this is suspicious *)
    in
    ER.fold f theta (theta_out, ER.empty)

(* Closure-converts a term. *)
let rec term (w : watermark) (theta : ER.t) : I.Term.t -> ER.t * CloTree.t * C.Term.t =
    function
    | I.Term.Fun _ as e ->
        let xs, e = I.Term.collapse_funs e in
        let w' = List.length xs in (* the watermark to use within the function body *)
        let theta_in, ct, e_closed = term w' ER.empty e in
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

(** NOTE [env-ren-hoist]

    Consider this code fragment:

        let b = ... in
        let c = ... in
        fun x y ->          -- F1
            (* watermark becomes 2 *)
            let z = x y c in
            (* watermark becomes 3 *)
            fun a ->
                (* watermark becomes 1 *)
                a z y b  -- F2

    Now in de Bruijn form:

        fun ! ! ->
            let ! = #1 #0 #2 in
            fun ! -> #0 #1 #2 #5

    The body of the innermost function, F2, is translated first:

        closure code = `#0b #0e #1e #2e`
        n = 1
        theta = [#0e, #1e, #4e]

    But this theta doesn't make sense OUTSIDE of the function! It allegedly wants #0e but that
    refers to the first variable in the environment that was passed to F1! That's actually the
    variable `b`. We actually want to refer to the variable `z` here.

    So we need a special hoisting operation to transfer the environment renaming across function
    boundaries.

    The watermark after `let z = x y in` is 3. Every env var with index less than that is
    translated to a bound variable with the same index. Env vars with index no less than the
    watermark have their watermark subtracted. Those refer to the outer function's env.
        theta' = [#0b, #1b, #0e]

    This is the renaming that we store in the MkClo node. From the POV of the function constructing
    the closure, these variable indices make sense.

    We also need to construct a closure for the `fun x y -> ...`, since it captures the variables
    `b` and `c`. Note that `b` is indirectly captured since it appears in the inner function. The
    reference to `b` actually occurs in the outer function _in the renaming_ associated with the
    inner function.

    In order to implement this upwards propagation of variables, the hoisting operation also takes
    as input the current environment renaming and extends it when it encounters an environment
    variable.
*)


























