# Constant elimination

This is a crucial transformation for supporting string (literals) as well as "constructor
literals".

- String literals:
    I would rather not represent the string directly in the program text since this would require
    jumps and other funny business destroying the nice property we currently have that each
    instruction occupies one Int64.t slot in the program text.
    Instead, the idea is to store all the string literals in a table during lowering and to replace
    the syntax `Term.Lit.String s` with something like `Term.Constant i` where `i` is an integer
    tag we synthesize during lowering.

- Constructor "literals":
    What happens when a user writes `Cons 3 (Cons 2 (Cons 1 Nil))`? It would be a little silly to
    actually go and generate code to construct this at runtime, involving heap allocations!
    Instead, we can generate the heap object representation of this during compile time and store
    it at a known address. In other words, we "seed" the heap with all the constants used in the
    program.

So during lowering, we need to replace (the nested chain of) constant operations with a single node
`L.Term.Constant tag`. Of course this is harder than the simple case for strings!

When we see `App (Const c, tS)` we have to transform each term in the spine and check that it's
constant before we can build the overall constant for the constructor.

The idea is that lowering should return the lowered syntax (non-constant) together with a so-called
"tentatively constant value". We'll call them "tentative" because they haven't been added to the
constant table yet.

After we make all the necessary recursive calls, we're in a position to decide whether the current
node should also be constant. If it is, then we continue building a tentative constant and return
that up the chain, deferring to our caller to decide when to actually materialize the constant in
the table; else, we materialize the constants resulting from rec calls, throwing away their lowered
syntax and instead generating `L.Term.Constant tag` for tags generated for each.

Ok, here's my new idea that reconciles strings and constructors. At the end of the day, we're going
to need to generate heap object representations at compile-time (probably during linking). So why
am I using a _direct_ form of recursion in the definition of `constant`? Instead, I can make it
indirect thru a 'tag' which is used as a key into a map.

```
    type t =
        | Const of ctor_name * ref list
        | String of string
    and ref = [ `unboxed of Int64.t | `boxed of tag ]
```

Then, in the lowered syntax, we have a constructor `Constant : ref -> term` which holds either an
unboxed integer constant or a 'boxed' Large Constant (string or constructor).

Compilation of such a `ref` is simply to emit a Push instruction to get either the literal integer
on the stack or the heap address of the Large Constant.

This means that those heap addresses have to be known statically. So here's what's gonna happen:
- lowering will generate a global table of constants associated with tags
- linking will receive this table, and will be able to generate an initial heap. All tags will have
  to be resolved to genuine heap addresses.
- linking only happens _after_ compilation! So compilation has to emit an address before the
  address is actually known.
- we already had that problem when compiling jumps!
    - For jumps, we introduced 'synthetic' bytecode instructions Label and SetLabel
    - Linking eliminated those instructions from the bytecode as it resolved the (code) addresses
      of the bytecode instructions.
- we can introduce a new synthetic instruction `Load_constant` to holds a tag
- linking generates the initial heap before eliminating synthetic instructions, so all constant
  tags become associated with a genuine heap address
- during linking, all Load_constant instructions become replaced with a Push of the known address
