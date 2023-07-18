#import "../isotope.typ": *

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
            $x$, $f med e$, $()$, $tt$, $ff$, $(a, b)$, 
            $klet x = a; e$, $klet (x, y) = a; e$,
            $lbl(ℓ)(A) med {t}$
        ),),
    ),
    (
        name: "Block",
        symbol: ("s", "t"),
        productions: (
            (
                $lbr(lbl(ℓ), a)$, $ljmp(lbl(ℓ), a)$, $lite(e, s, t)$,
                $klet x = a; t$, $klet (x, y) = a; t$
            ),
            (
                $s kwhere [lbl(ℓ_i)(x_i: A_i) => { t_i }]_i$
            )
        ),
    )
);
#grammar(isotope-grammar)
The grammar given is parametrized over a set of _base types_ $X ∈ cal(T)$ and _instructions_ $f ∈ cal(I)$. 
We will denote the set of valid types with base types $cal(T)$ as $types(cal(T))$.
Note that we implicitly quotient up to α-equivalence, and that our grammar does not include a notion of function.

For the rest of this section, we will assume the existence of fixed-width bitvector types (e.g. `u64`), basic arithmetic (e.g. `+`, `>=`), and constant values (e.g. 63) of these types (which we may interpret as instructions taking a single argument `()`).

Consider the following simple program for calculating the factorial of `n`:
```isotope
'exit(i64) {
    br 'fact (0, 0) where 'fact(p: (i64, i64)) => {
        let (i, a) = p;
        if i >= n {
            // Branching to the exit label 'exit with argument a means the
            // term will evaluate to a, which is now equal to n!
            br 'exit a
        } else {
            // We jump back to 'fact with the updated values of i and a
            // We jump rather than branch since 'fact can potentially recurse
            jmp 'fact (i + 1, i * a)
        }
    }
}
```
Note that the program as a whole lies in the syntactic category of _terms_. If we introduce the syntax sugar `ret a` for branching to an anonymous exit label, we can instead write
```isotope
{
    br 'fact (0, 0) where 'fact(p: (i64, i64)) => {
        let (i, a) = p;
        if i >= n {
            ret a
        } else {
            jmp 'fact (i + 1, i * a)
        }
    }
}
```

Terms and targets being interleaved makes it possible to encapsulate control flow, which facilitates reasoning about rewriting and control-flow as well as program transformations such as inlining. For example, in a function to compute the absolute value and branch on it
```isotope
let x = y + 5;
let s = sgn x;
let abs = s * x;
if abs > 5 { ret 4 } else { ret 3 }
```
we could inline a plausible definition of `sgn` as follows:
```isotope
let x = y + 5;
let s = { 
    if x < 0 { ret -1 } 
    else if x == 0 { ret 0 } 
    else { ret 1 } 
};
let abs = s * x;
if abs > 5 { ret 4 } else { ret 3 }
```
Note the use of `else if` syntax sugar; in general,
```isotope
if p { P } else if q { Q } else { R }
```
desugars to
```isotope
if p { P } else { if q { Q } else { R } }
```
With the standard approach of encoding the control-flow graph without allowing nesting, we'd have to rewrite everything as a single block as follows
```isotope
let x = y + 5;
if x < 0 { br 'c -1 } 
else if x == 0 { br 'c 0 } 
else { br 'c 1 }
where 'c(s: i64) => {
    let abs = s * x;
    if abs > 5 { ret 4 } else { ret 3 }
}
```

The grammar also allows for multiple, mutually recursive label definitions in a single `where`-binding, as in the following program, which prints out the binary representation of `x`:
```isotope
print "0b";
br 'next x where
    'zero(x: i64) => {
        print "0";
        jmp 'next x
    }
    'one(x: i64) => { 
        print "1";
        jmp 'next x
    }
    'next(x: i64) => { 
        if x == 0 {
            ret
        } else if x % 2 == 0 {
            jmp 'zero (x >> 1)
        } else {
            jmp 'one (x >> 1)
        }
    };
```
Here, bare function calls `print s` are syntax sugar for unused bindings `let \_ = print s` to allow us to writing side-effectful expressions more easily; similarly, a bare `ret` is syntax sugar for `ret ()` (we will also shorten `br`s and `jmp`s likewise). One gotcha is that label bindings cannot be used in a block nested in an expression in another block; for example,
```isotope
ret {
    if b { br 'label 9 } else { br 7 }
} where 'label(x: i64) => {
    print x;
    br (x + 5)
};

```
is _invalid_ code, since the label `'label` is used in the nested expression given as an argument to the `br`-statement, while
```isotope
if b { br 'label 9 } else { br 7 } where 'label(x: i64) => {
    print x;
    br (x + 5)
};
```
is a perfectly valid program with the desired semantics. On the other hand, this restriction does _not_ apply to `let`-bindings of _terms_ (versus _labels_).

== Syntax Sugar

We provide a variety of syntax sugar to make reading and writing programs easier, with the goal of, for the most part, emulating Rust's syntax. 

=== Blocks and Expressions

Where it would be otherwise unambiguous, we permit omitting the braces surrounding a block; for example, if the block
```isotope
if x == 0 {
    let e = 7; ret e
} else {
    ret 8
}
```
is encountered where a term is expected, it may be interpreted as the term
```isotope
{
    if x == 0 {
        let e = 7; ret e
    } else {
        ret 8
    }
}
```
We similarly allow omitting the `ret` keyword in blocks; for example,
```isotope
{ let x = 5;  x }
```
desugars to
```isotope
{ ret (let x = 5; x) }
```
While this behaviour might be confusing, since the user might expect
```isotope
{ let x = 5; ret x }
```
we will later require all such desugarings to be semantically equivalent, making the distinction moot.

=== Control-Flow

We support Rust-like `match`-expressions, such as
```isotope
match x {
    Some(0) => 5,
    Some(3) if y == 7 => 7,
    None => 8,
    _ => big_calculation
}
```
by desugaring as follows, assuming the existence of appropriate `enum`-like types:
```isotope
if is_some x {
    let x = get_some x;
    if x == 0 {
        ret 5
    } else if x == 3 {
        // Note nested control flow is incorporated into the same block
        // This is to allow desugaring more complex constructions, such 
        // as breaks and loops.
        if y == 7 {
            ret 7
        } else {
            ret 'default
        }
    } else {
        ret 'default
    }
} else {
    ret 8
} where 'default => { big_calculation }
```
Similarly to `if`-statements, `match` statements may be interpreted as expressions as well as blocks. Other Rust-like matching constructs, like `let`-`else` statements or pattern destructures, are also supported.
Similarly, we support Rust-style control-flow constructs such as `for`, `while`, and `loop`; for example,
```isotope
while predicate {
    side_effect;
}
rest
```
desugars to
```isotope
br 'head where
    'head => if predicate {
        jmp 'body
    } else {
        br 'rest
    }
    'body => {
        side_effect;
        jmp 'head
    }
    'rest => rest
```