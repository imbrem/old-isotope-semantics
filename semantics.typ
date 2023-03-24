#import "isotope.typ": *
#show: doc => isotope-report(
    title: "Isotope IR Semantics",
    authors: (
        (
            name: "Jad Elkhaleq Ghalayini",
            affiliation: "University of Cambridge",
            email: "jeg74@cl.cam.ac.uk"
        ),
    ),
    doc
)

= Syntax

In this section, we present the core `isotope` calculus, followed by some sample programs and syntax sugar, with the aim of working towards a familiar, Rust-based human-readable syntax for the `isotope` intermediate representation.

== Core Calculus

The `isotope` grammar is divided into following syntactic categories:
#let isotope-grammar = (
    (
        name: "Type",
        symbol: ($A$, $B$, $C$),
        productions: (
            ($X$, $tobj$, $bools$, $A ⊗ B$),
        )
    ),
    (
        name: "Term",
        symbol: ($a$, $b$, $c$, $e$),
        productions: ((
            $x$, $f aq e$, $()$, $ltt$, $lff$, $(a, b)$, 
            $llet x = a; e$, $llet (x, y) = a; e$,
            ${t}$
        ),),
    ),
    (
        name: "Block",
        symbol: ("s", "t"),
        productions: (
            (
                $br(a)$, $br(lbl(ℓ), a)$, $lite(e, t, s)$,
                $llet x = a; t$, $llet (x, y) = a; t$
            ),
            (
                $llet [lbl(ℓ_i)(x_i: A) => { t_i }]_i; s$
            )
        ),
    )
);
#grammar(isotope-grammar)
Note that we implicitly quotient up to α-equivalence, and that our grammar does not include a notion of function.

The grammar given is parametrized over a set of _base types_ $X ∈ cal(V)$ and _instructions_ $f ∈ cal(I)$.

A _term_ is interpreted as a regular value which may be passed as an argument or returned as a result of a computation. A _block_ is a computation that can either tail-call into another _block_ or return a value. For the rest of this section, we will assume the existence of fixed-width bitvector types (e.g. `u64`), basic arithmetic (e.g. `+`, `>=`), and constant values (e.g. 63) of these types (which we may interpret as functions called on the single argument `()`).

Consider the following simple program for calculating the factorial of `n`:
```rust
let 'fact(p: (i64, i64)) => {
    let (i, a) = p;
    if i >= n {
        break a
    } else {
        break 'fact (i + 1, i * a)
    }
}; 
break 'fact (0, 0)
```
Note that the program as a whole lies in the syntactic category of _blocks_. We also use Rust's `break` keyword instead of $lbr$ for syntax highlighting purposes; this should be fixed in a later version of this document.
//TODO: actually fix this.

Terms and targets being interleaved makes it possible to encapsulate control flow, which facilitates reasoning about rewriting and control-flow as well as program transformations such as inlining. For example, in a function to compute the absolute value and branch on it
```rust
let s = sgn x;
let abs = s * x;
if abs > 5 { break 4 } else { break 3 }
```
we could inline a plausible definition of `sgn` as follows:
```rust
let s = { 
    if x < 0 { break -1 } else { 
        if x == 0 { break 0 } else { break 1 } 
    } 
};
let abs = s * x;
if abs > 5 { break 4 } else { break 3 }
```
This contrasts with the standard approach of encoding the control-flow graph without allowing nesting, which would require us to rewrite everything as a single block as follows
```rust
let 'c(s: i64) => {
    let abs = s * x;
    if abs > 5 { break 4 } else { break 3 }
};
if x < 0 { break 'c -1 } else { 
    if x == 0 { break 'c 0 } else { break 'c 1 } } 
}
```
As can be seen, this considerably complicates the definition of inlining, and, later, when we consider the graphical representation of `isotope` programs, causes expressibility issues for re-ordering.

The grammar also allows for multiple, mutually recursive label definitions in a single `let`-binding, as in the following program, which prints out `x`'s binary representation:
```rust
print "0b";
let 
    'zero(x: i64) => {
        print "0";
        break 'next x
    }
    'one(x: i64) => { 
        print "1";
        break 'next x
    }
    'next(x: i64) => { 
        if x % 2 == 0 {
            break 'zero (x >> 1)
        } else {
            break 'one (x >> 1)
        }
    };
br 'next x
```
Here, bare function calls "`print s`" are syntax sugar for unused bindings `let \_ = print s;` to allow us to write side-effectful expressions more easily. One gotcha is that label bindings cannot be used in a block nested in an expression in another block; for example,
```rust
let 'label(x: i64) => {
    print x;
    break (x + 5)
};
break {
    if b { break 'label 9 } else { break 7 }
}
```
is _invalid_ code, since the label `'label` is used in the nested expression given as an argument to the `br`-statement, while
```rust
let 'label(x: i64) => {
    print x;
    break (x + 5)
};
if b { break 'label 9 } else { break 7 }
```
is a perfectly valid program with the desired semantics. On the other hand, this restriction does _not_ apply to `let`-bindings of _terms_ (versus _labels_).

== Syntax Sugar

We provide a variety of syntax sugar to make reading and writing programs easier, with the goal of, for the most part, emulating Rust's syntax. 

=== Abbreviations

We will write `br 'label` as an abbreviation for `br 'label ()`; likewise, for a set of _constant_ instructions $c ∈ cal(V)_C ⊆ cal(V)$ we will write $c$ as an abbreviation for $c aq ()$.

=== Blocks and Expressions

Where it would be otherwise unambiguous, we permit omitting the braces surrounding a block; for example, if the block
```rust
if x == 0 {
    let e = 7; br e
} else {
    br 8
}
```
is encountered where an term is expected, it may be interpreted as the term
```rust
{
    if x == 0 {
        let e = 7; br e
    } else {
        br 8
    }
}
```
We similarly allow omitting the `br` keyword in blocks; for example,
```rust
{ let x = 5;  x }
```
desugars to
```rust
{ break (let x = 5; x) }
```
While this behaviour might be confusing, since the user might expect
```rust
{ let x = 5; break x }
```
we will later require all such desugarings to be semantically equivalent, making the distinction moot.
//TODO: when?

=== Control-Flow

We support Rust-like `match`-expressions, such as
```rust
match x {
    Some(0) => 5,
    Some(3) if y == 7 => 7,
    None => 8,
    _ => big_calculation
}
```
by desugaring as follows, assuming the existence of appropriate `enum`-like types:
```rust
let default => { big_calculation };
if is_some x {
    let x = get_some x;
    if x == 0 {
        break 5
    } else {
        if x == 3 {
            // Note nested control flow is incorporated into the same block
            // This is to allow desugaring more complex constructions, such 
            // as breaks and loops.
            if y == 7 {
                break 7
            } else {
                break 'default
            }
        } else {
            break 'default
        }
    }
} else {
    break 8
}
```
Similarly to `if`-statements, `match` statements may be interpreted as expressions as well as blocks. Other Rust-like matching constructs, like `let`-`else` statements or pattern destructures, are also supported.
Similarly, we support Rust-style control-flow constructs such as `for`, `while`, and `loop`; for example,
```rust
for x in collection {
    side_effect x;
}
```
desugars to
```rust
let body(c: _) => {
    let (x, c) = next c;
    if is_some x {
        let x = get_some x;
        let _ = side_effect x;
        break 'body c
    } else {
        break ()
    }
};
break 'body collection
```
For ease of reading SSA-like programs, we also provide postfix `where`-syntax, where we simply desugar
```rust
t where
    'a(x: A) => { ... }
    'b(y: B) => { ... }
    ...
```
to
```rust
let 
    'a(x: A) => { ... }
    'b(y: B) => { ... }
    ...
;
t
```

#pagebreak()
#bibliography("references.bib")