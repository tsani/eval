# Eval bytecode

Consider this definition.

```eval
def foo = let x = 5 in fun y -> x + y
```

Eval programs can be compiled to a bytecode, to be executed on the Eval VM.
The Eval VM is a stack-based virtual machine.

# Registers

EBCI uses a fixed number of special registers. It does not have any general-purpose registers.

- `PC` the program counter is the offset into the code segment of the next instruction to execute.
- `BP` the base pointer is an offset into the argument stack that identifies a function call
  boundary. This is used for calculating the address of function arguments.
- `SP` the stack pointer is the offset into the argument stack of the next unused item.
    (Seen differently, it is the current size of the stack.)

# Memory segments

A bytecode program for the EVM consists of multiple memory segments.

1. Heap. Large, variably-sized objects have to be stored somewhere and referred to on the stack
   by addresses. These objects are constructors and closures.
   The heap is prepopulated with any large constants that appear directly in the program text.
2. Code. This is all the instructions of the program.
3. Argument stack. Holds temporary values, arguments to functions.
4. Call stack. Holds return addresses and environment addresses.
    Instructions affecting this stack generally have an `r` prefix (as in FORTH) for 'return'.

# Values

- Each item on the argument stack is called a _value_. Each value is a 64 bit integer.
- There are two kinds of values, and these are tagged by the LSB of the integer:
    - An unboxed integer ends in 1, so it's really only 63 bits wide.
    - A heap address ends in 0.

# (Heap) objects

Stack items are inherently temporary and scoped to function calls. Items that must outlive a
function or are too large to fit into a value are stored on the heap, and are referred to by an
address that can be moved around on the stack. These items are called _heap objects_ or just
_objects_.

There are a few kinds of objects:
- functions, of which there are two kinds:
    - CLO - closures:
        - header that contains:
            - a tag identifying this as a closure
            - the count of environment variables
            - the count of required function parameters
            - a code pointer
        - the environment variables' values come next
    - PAP - partial applications: (It's not clear how much we need these vs just using closures)
        - a header that contains:
            - a tag identifying this as a partial application
            - the count `N` of held argumnets
            - the count `K` of missing arguments
            - a heap object pointer to a closure
        - an array of arguments of size N
- constructors:
    - header that contains the constructor tag & count of fields
    - the field values come next

# The code segment

The code segment of a program contains all the bytecode instructions.
It is divided into two sections:

- function definitions
    - these correspond to definitions in the program of nonzero arity, e.g.
        `def foo = fun x -> x + 2` does not need to compute anything upfront, so we store the code
        for `x+2` into a subsection named `foo`.
- the program entrypoint
    - the entrypoint code contains all the code that runs "while the module is being loaded"
    - these correspond to definitions in the program "of arity 0", e.g.
        `def four = 2 + 2` needs to compute 2+2 and store it in a well-known location named `four`.

This code is stored in the code segment.

All the code of each function is stored sequentially in the code segment.
Functions (either pure ones or closure _bodies_) are referred to by addresses in the code segment.

# The heap

Constructors and closures cause heap allocations: constructors for their fields and closures for
their environments.

The example program earlier forms a closure, so its code would look like.

```evalbc
push param int 5
push param addr $foo      ; load the address of the function code, which is statically known
mkclo 1                   ; construct a closure capturing one value into the environment
                          ; this consumes the function address and the one value on the stack
                          ; now the stack holds just the address of the closure on the heap
store well-known $clo_foo ; move the closure heap address into the well-known location
```

Since the example program was a top level definition, it isn't anonymous! Other programs will want
to refer to `foo` and would like to object the address of the closure that was created.
The programs 'communicate' thru the `store_v` / `load_v` pair of instructions.
In the human-readable bytecode, we use the symbol `$clo_foo` to refer to the well-known name -- in
the actual bytecode this symbol is represented as an integer encoded into the `store_v`
instruction.

# Calling a known closure

Recall the example `def foo = let x = 5 in fun y -> x + y`.

This allocates a closure and stores the address of the closure in the well-known location `foo`.
The _body_ of the closure `x + y` will generate a function `foo_closure_1`, that is the body of
the closure. Closure bodies are special, in that user code can never call them directly.
Jumps into them happen from within the interpreter, once the environment has been loaded.
Likewise, closure bodies use a special return instruction that tells the interpreter to clean up
the environment.

Now later on, there is an application in the program that looks like `foo 2`. This is what we mean
by "calling a known closure".

This needs to be translated into:

```evalbc
push param int 2 (* the literal 2 *)
load well-known foo (* load the closure address from the well-known location `foo` *)
call closure 1 (* invoke the closure with 1 argument *)
```

The "call closure" instruction deferences the closure address to fetch the _environment address_
and the _closure body address_. The environment is copied into the _call stack_ (since we can't use
the argument stack for this) and the closure body address is jumped to.
Since the closure body knows how many environment variables there were, it contains the necessary
code to remove that many entries from the call stack before it returns.
In particular, it will use the `ret closure N K` instruction, where `N` is the size of the
environment and `K` is the number of function parameters. The interpreter will:
- pop `N` many values from the call stack, thus cleaning up the environment
- moves the top of the param stack (the return value of the function) onto the call stack
- pop `K` many values from the param stack, thus cleaning up the parameters.
- move the top of the call stack (the function return value) onto the param stack
    (as expected by the caller)
- pop the return address off of the call stack and jump there

## Remark on degenerate closures and unhoisting

Closure conversion will turn _every_ (sequence of) `Fun` abstraction(s) into an MkClo node, so
`def foo = fun x -> x + 2` will actually be turned into an MkClo node, and the code for `x+2`
hoisted to a definition for `foo_closure_1`. However, this closure does not capture _any_
environment variables. We call it a _degenerate closure._ Degenerate closures associated to
top-level definitions get _unhoisted_ to define a _pure function_ rather than a _closure body_.
(Static) calls to pure functions are optimized since we don't need to load/destroy an environment.
(We avoid one indirection.)

```evalbc
load_e 0 ; load captured env var 0 (x)
load_p 0 ; load parameter var 0 (y)
add
ret      ; pops the env and return addresses from the call stack, sets PC to return address
```

This gets complicated with closures. Recall the example


```eval
def foo = let x = 5 in fun y -> x + y
```

## Making an exact call

Then later, when we want to call `foo`, we have something that looks like this.

```evalbc
load_i 7          ; argument (y)
load_v $clo_foo   ; load the heap address of the closure
dcall_clo 1       ; push PC on call stack, pop closure from arg stack, enter it
```

Statically, we know that `$value_foo` will hold a closure that requires exactly one argument, which
is the amount provided.

## Forming a PAP

On the other hand, what if the function `foo` is known to require two arguments, but only one is
provided? Then we can jump straight to the construction of the PAP.

```evalbc
push_i 7          ; argument
push_a $clo_foo   ; closure address
mkpap 1 1         ; 1 held argument and 1 missing argument
```

What's left on the stack is the heap address of the PAP.

## What if there are too many arguments?

In this case, we're calling a known closure that is returning an _unknown_ function.

The code might look like `f a b c` and `f` refers to a statically-known function that requires one
argument. The generated bytecode is then:

```evalbc
<get c on the stack>
<get b on the stack>
<get a on the stack>
load_v $clo_f
dcall_clo 1
; the dcall_clo will remove `f` and `a` from the stack
; when it completes, the address of the unknown function will be on the stack instead
; so to continue, we just make an icall with the remaining number of arguments given
rpush_i 2
icall
```

# Calling a known pure function

Calling known pure functions is pretty much the same as calling known closures. The difference is
that when calling a pure function, we can avoid doing any work involving environments as an
optimization. The instruction `dcall` without the `_clo` modifier skips fiddling with the
environment.

# Calling an unknown function

When a function is passed as an argument to another function, then we don't know how many arguments
we really need to actually enter the function.

For example, in the expression `f x y`, the function `f` might only really take one argument, then
return another function that should be applied to `y`. Or maybe `f` needs three arguments, so we
need to construct a partial application holding `x` and `y` but waiting for one more argument.

The approach we use in EBCI is called eval/apply, in which the _caller_ examines (evaluates) the
function and determines whether to actually call it or to form a partial application or even to
continue applying more arguments to the result of the call. The bytecode looks like

```evalbc
<get the value of y onto the stack>
<get the value of x onto the stack>
<get the value of f onto the stack>
rpush_i 2
icall
```

The small integer `2` represents the statically-known number of arguments passed to the function.
All the hard stuff happens inside the implementation of `icall`.
The mnemonic is for "indirect call"

The basic logic is the same for calling a CLO or a PAP: examine the number of required arguments
and compare with the given number of arguments.

- Less arguments than required are given: form a PAP
- Exact arguments are given: make an exact call
- Too many arguments are given: then we need to make an exact call with the required number of
  arguments, then repeat until we run out of arguments

This last case seems really challenging to implement.

The pseudocode for icall will make clear why the argument count is stored _on the stack_ vs being a
part of the icall instruction itself.

```
icall():
    n <- rpop()
    if n == 0: jump out
    -- we consumed all arguments, so what's on the stack is only the last call's return value
    -- there are no more arguments on the stack, and the count `n` has just been removed from the
    -- call stack.

    hdr <- *(SP-1) -- dereference the top of stack to get the header of the function

    if is_closure(hdr):
        compare n with hdr.param_cnt:
            - LT: jump to implementation of mkpap_clo(n, hdr.param_cnt - n)
            - EQ: jump to implementation of dcall_clo(n)
            - GT:
                rpush(n - hdr.param_cnt) -- update count of remaining args to consume
                rpush(PC - 1) -- address of the currently executing instruction
                jump to implementation of dcall_clo(hdr.param_cnt) _after_ rpush

    if is_pap(hdr):
        compare n with hdr.missing_cnt:
            - LT: jump to implementation of mkpap_pap(n, hdr.missing_cnt - n)
            - EQ: jump to implementation of dcall_pap(n)
            - GT:
                rpush(n - hdr.missing_cnt) -- update count of reminaing args to consume
                rpush(PC - 1) -- address of the currently executing icall instruction
                jump to implementation of dcall_pap(hdr.missing_cnt) _after_ rpush
```

The LT and EQ cases are straightforward. The GT case is the tricky one, because we need to continue
by calling the returned function with the remaining number of arguments. The returned function is
itself an unknown function, so the trick is to push the address of the currently executing icall
onto the return stack, and then perform a 'half-call'. Normally, a call begins by pushing the
address of the next instruction on to the stack before entering the function body. Instead, we want
to _replace_ the part where we push the address of the _next_ instruction with a push of the
address of the _current_ instruction. This way when we return, we make another indirect call.

This is why we store the number of remaining arguments on the return stack: we have to keep
subtracting from it to chain all the calls.
The count of remaining arguments should not ever reach zero, even though there is a handler for
that case in the implementation of `icall`. Notice that we only ever push an updated count in the
GT cases, and the updated count that's pushed is the difference, which must be nonzero positive.

# Bytecode instruction reference

Argument legend:
- `I` small integer
- `A` full integer aka an address

Instruction list:
- `push_i I` - loads a small integer value onto the stack.
- `push_a A` - loads an address onto the stack.
  The next item on the code segment is the full-width integer to load.
- `load_e I` - loads the value at the given offset from the current environment
- `load_p I` - loads the function parameter at the given offset
- `load_v I` - loads the address of a heap object thru a well-known name represented by an integer
- `icall` - 'indirect call' applies an unknown function to given arguments whose count is on the
  rstack.
- `dcall_clo I`

# Pattern matching compilation

How the fuck are we going to compile patterns?

At the point that we arrive at `match t with p1 -> t1 | ... | pN -> tN`:
- we evaluated `t`, so its value is on the top of the stack
- then we need to arrange to compile p1 so that when matching succeeds, `t`'s value is gone from
  the stack and is replaced with the values corresponding to the variables in p1; but if matching
  fails, then the value of `t` needs to remain on the stack so that the next pattern can try.

These base cases are trivial because they can't fail:
- a wildcard pattern just drops the value from the stack and succeeds
- a variable pattern just does nothing, since the value to bind is already in position 0

There is a less obvious base case, because it can fail:
- a literal (let's concentrate only on integer literals for now)
    we check if the top of stack equals the literal
        if it does we succeed by doing nothing since the comparison would have popped the int off
        if it fails then we need to jump... to a failure continuation!

Yes, we need continuations. We have to build up in the failure continuation all the work required
to destroy the partially-matched value before jumping to the next case to try.
The initial continuation jumps to code to crash on failed matching.

The only step case is for a constructor pattern.
In this case, the value on the top of the stack is a heap address of a CLO object, so we perform a
special constructor load instruction to bring onto the stack the constructor tag (as an integer)
and all the constructor's `N` fields.

Matching the constructor tag performs a subtraction, removing the tag from the stack, and branching
on whether the result is zero.
    - If it is, then the constructor matches, so the first field is on top of the stack.
        - We
    - If it is not, then the constructor failed to match. The `N` fields of the constructor need to
      be removed from the stack, so we jump to label `remove_n`
      generate code from the first
pattern, which regardless of success or failure

# Recursive closures

```
def rec foo = 1 + foo
```

This one should rely on the idea that at some point, `load` is gonna have to happen for `foo`, but
that would have happened before the first store to `foo`, so the interpreter detects this and
crashes.

What about this:

```
def rec foo = let n = 5 in fun y -> foo n
```

During closure conversion of foo, we're going to have to convert the call `foo n`, but what's the
arity of `foo`? Also, what _kind_ of value is `foo`? This impacts how `foo` will be called.

We can calculate the static arity of a term.
Oh wait actually we can't. Look at this:

```
def foo = let f = fun x -> x in f
```

actually `f` would need to be eta-expanded when we have _type_ information.

Why does the compiler check arity anyway?

# We have a problem with variables

In running this code

```
def rec fib = fun n -> match n with
    | 0 -> 0
    | 1 -> 1
    | n -> fib (n + -1) + fib (n + -2)

def fib_5 = fib 2
```

I found a problem.

The bytecode generated for `fib (n + -2)` looks like

```
push param int -2
load param 0
push param addr <fib>
call func
```

This is wrong! The `load param 0` is supposed to load the value of the variable `n`, but we already
pushed -2 onto the stack at this point, so the load would need to be offset.

In general this seems to be the case with any kind of application, since those are the only
constructs that introduce stuff "temporarily in the way" like this on the stack.
I guess one approach to fix this during compilation is to track a stack offset for variables while
compiling a spine. After compiling each spine item (from right to left) we increase the offset by
one. The offset goes away after the `App` is compiled because it will consume all the values for
the spine.

So I implemented this offset approach and it works for fib, but I think that in general it doesn't.
Consider this:

```
(match l with Cons x xs -> x) + 2
```

The prim application spine gets compiled first, so `2` gets pushed to the stack before the code for
the match runs. The code for the match will then load the CON object that `l` refers to onto the
stack -- its fields will be on top when the branch body runs. We would want to emit a
`load param 1` (to skip over xs and get to x). However, because we're inside an application spine,
there will be an offset of 1. Therefore, the `load param 1` will actually be a `load param 2`,
which is incorrect.

An simple offset is insufficient. We actually need a full renaming. Remember that an offset is a
special case of a renaming! To see why the full renaming is necessary, and works, consider a
slightly more complex example.

```
let y = 5 in
(match l with Cons x xs -> V) + 2
```

When `V = x`, we need to make sure we get a `load param 0`.
When `V = y`, we need to make sure we get a `laod param 3` (and not `2`) because we need to skip
over the `2` that was added to the stack during the prim application spine construction.

So how does this renaming work? It maps _variable_ indices to _stack_ indices.
Every binding construct adds a new item to the renaming and shifts everything in the renaming up by
one.
Every time a _temporary_ value is added to the stack, the renaming simply gets shifted up by one.

Ok, so I think this approach _works_, but is it the best?

The issue ultimately arises due to some operations producing _anonymous results_. For example,
in `fib`, we have `fib (n + -1) + fib (n + -2)` which has a lot of anonymous results. If we
expressed this as

```
let m1 = -1 in
let n1 = n + m1 in
let f1 = fib n1 in
let m2 = -2 in
let n2 = n + m2 in
let f2 = fib n2 in
f1 + f2
```

Then we establish a one-to-one correspondence between stack indices and variable indices, which
makes the renaming unnecessary during compilation. In other words, the requirement is that spines
consist _only_ of variables.

This is practically a CPS conversion / SSA form since we introduce a name for every intermediate
result and make the order of operations completely explicit via the chain of lets.
