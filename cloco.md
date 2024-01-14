# Closure conversion

Idea: recursively tranverse the syntax tree and pay special attention to when we go under a
(sequence) of `Fun` nodes. Each time we go under a `Fun`, we might need to construct a (proper)
closure. Count how many funs we go under; this becomes the active watermark w. When we encounter a
variable with index i, if i < w, then the variable translates to a BVar with index i; else it
translates to an EVar with a new index into the environment.

As we encounter free variables in a function body, these are given sequential indices into the new
environment. We construct an _environment renaming_ as output of closure conversion to map these
new, sequential indices back to the original environment indices. The environment renaming ends up
being used in the target program:

  [[fun x1 ... xN -> e]] = mk_clo (f, eta, N)

  def f x1 ... xN = [[e]]

where
- `f` is a synthetic name for the function, i.e. just a code pointer
- `eta` is the environment renaming calculated by the closure conversion.

The primitive `mk_clo` is compiled by a later stage into an allocation for the environment plus an
initialization of that environment, i.e. copying the relevant parts of the current environment and
the current argument stack into the newly allocated environment according to `eta`.
Semantically, this is a realization of the application of `eta` to the current environment to
compute the restricted environment needed for `f`


Consider this code fragment:

```
let b = ... in
let c = ... in
fun x y ->          -- F1
    (* watermark becomes 2 *)
    let z = x y c in
    (* watermark becomes 3 *)
    fun a ->
        (* watermark becomes 1 *)
        a z y b  -- F2
```

Now in de Bruijn form:

```
let ! = ... in
let ! = ... in
fun ! ! ->
    let ! = #1 #0 #2 in
    fun ! -> #0 #1 #2 #5
```

The body of the innermost function, F2, is translated first, with a watermark of 1:

- closure code = `#0b #0e #1e #2e`
- n = 1
- theta = [#0e, #1e, #4e]

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
