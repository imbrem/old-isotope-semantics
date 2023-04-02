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

#let table-dbg = none;

/*
= Introduction

//TODO: this
*/

= Background

In this section, we go over some background notions used in the semantics. For an overview of basic category theory and the notations in use, see @cats[Appendix].

== Monoidal and Premonoidal Categories

/*
TODO:
- binoidal text
*/

#definition(name: "Binoidal Category")[
    A *binoidal category* is a category $cal(C)$ equipped with
    - A *tensor product* map on objects $⊗: |cal(C)| times |cal(C)| -> |cal(C)|$
    - For each object $A in |cal(C)|$,
        - A *right product functor* $A ⊗ -$ which is $B ↦ A ⊗ B$ on objects
        - A *left product functor* $- ⊗ A$ which is $B ↦ B ⊗ A$ on objects
    We define, for morphisms $f: A -> B$, $g: X -> Y$, the *left product* $f ⋉ g = f ⊗ X; A ⊗ g$ and *right product* $f ⋊ g: A ⊗ g; f ⊗ X$ morphisms $A ⊗ X -> B ⊗ Y$
]
#definition(name: "Central Morphism")[
    A morphsm $f$ a binoidal category $cal(C)$ is *central* if, for all morphisms $g$, we have $f ⋉ g = f ⋊ g$; in this case, we write $f ltimes g = f rtimes g = f ⊗ g$.
    We define the *center* of a binoidal category $cal(C)$, denoted $cen(cal(C))$, to be the wide subcategory with $|cen(cal(C))| = |cal(C)|$ and morphisms
    $
        cen(cal(C))(A, B) = {f in cal(C)(A, B) | f "is central"}
    $
    A natural transformation is central if all its components are.
]

/*
TODO:
- premonoidal text
*/

#definition(name: "Premonoidal Category")[
    A *premonoidal category* is a binoidal category $cal(C)$ equipped with
    - An *identity object* $munit in |cal(C)|$
    - A family of central isomorphisms $α_(A, B, C): (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C)$ (the *associator*) natural in $A, B, C in cal(C)$
    - A central natural isomorphism $λ: - ⊗ munit => idm$  (the *left unitor*) 
    - A central natural isomorphism $ρ: munit ⊗ - -> idm$ (the *right unitor*)
    such that the *triangle identity*
    $
    ρ_A ⊗ B = α_(A, munit, B); A ⊗ λ_B: (A ⊗ munit) ⊗ B -> A ⊗ B
    $
    and *pentagon identity*
    $
    α_(A, B, C) ⊗ D; α_(A, B ⊗ C, D); A ⊗ α_(B, C, D) =
    α_(A ⊗ B, C, D); α_(A, B, C ⊗ D)
    $
    hold for all $A, B, C, D in |cal(C)|$.

    We say a premonoidal category is *strict* if $(A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)$, $A ⊗ I = I ⊗ A = A$, and $α, ρ, λ$ are the identity transformations.
]
#definition(name: "Symmetric Premonoidal Category")[
    We say a premonoidal category is *braided* if, in addition, it is equipped with a family of central isomorphisms $σ_(A, B): A ⊗ B -> B ⊗ A$ natural in $C in |cal(C)|$ and $D in |cal(D)|$ such that
    - $σ_(A, B) = σ_(B, A)^{-1}$
    - The following *hexagon identities* hold:
        - $α_(A, B, C);σ_(A, B ⊗ C);α_(B, C, A)
            = σ_(A, B) ⊗ C;α_(B, A, C);B ⊗ σ_(A, C)$
        - $α_(A, B, C)^(-1);σ_(A ⊗ B, C);α_(C, A, B)^(-1)
            = A ⊗ σ_(B, C);α_(A, C, B)^(-1);σ_(C, A) ⊗ B$
    We say a braided premonoidal category is *symmetric* if, in addition, we have $σ_(A, B) = σ_(B, A)^(-1)$; in this case, either hexagon identity implies the other.
]
/*
TODO: naming
*/
#theorem(name: "Coherence")[
    Let $cal(C)$ be a premonoidal category. Then the smallest wide subcategory of $cal(C)$ containing all components of $α$, $λ$, and $ρ$ is thin.
]
/*
TODO: due to this, α syntax sugar
*/

/*
TODO:
- monoidal text
*/

#definition(name: "(Symmetric) Monoidal Category")[
    A (symmetric) monoidal category $cal(C)$ is a (symmetric) premonoidal category in which, equivalently,
    - All morphisms are central, i.e. $cal(C) = cen(cal(C))$
    - $⋉ = ⋊$, in which case we write both as $⊗$
    - $⊗$ is a bifunctor
]
In particular, for every (symmetric) premonoidal category $cal(C)$, we have that $cen(cal(C))$ is (symmetric) monoidal.

/*
TODO:
- string diagrams
- strong monads ==> premonoidal
- commutative monads ==> monoidal
- monoidal functor text
*/

#definition(name: "(Pre)monoidal Functor")[
    A *lax (pre)monoidal functor* $F: cal(C) -> cal(D)$ between (pre)monoidal categories $cal(C), cal(D)$ is a functor equipped with
    - A morphism $ε: munit_(cal(D)) -> F(munit_(cal(C)))$ (where $munit_(cal(C)), munit_(cal(D))$ are the monoidal units of $cal(C), cal(D)$ resp.)
    - A family of morphisms $μ_(A, B): F A ⊗_(cal(D)) F B -> F(A ⊗_(cal(C)) B)$ natural in $A, B in |cal(C)|$ (where $⊗_(cal(C)), ⊗_(cal(D))$ are the tensor products of $cal(C), cal(D)$ resp.)
    satisfying the following conditions:
    - *associativity*: for all $A, B, C in |cal(C)|$, the following diagram commutes:
    #align(center)[#commutative_diagram(
        node((0, 0), [$(F A ⊗_(cal(D)) F B) ⊗_(cal(D)) F C$]),
        node((0, 2), [$F A ⊗_(cal(D) (F B ⊗_(cal(D)) F C)$]),
        arr((0, 0), (0, 2), [$α^(cal(D))_(F(A), F(B), F(C))$], label_pos: 0),
        node((1, 0), [$F(A ⊗_(cal(C)) B) ⊗_(cal(D)) F C$]),
        arr((0, 0), (1, 0), [$μ_(A, B) ⊗_(cal(D)) F C$], label_pos: 0),
        node((2, 0), [$F((A ⊗_(cal(C)) B) ⊗_(cal(C)) C)$]),
        arr((1, 0), (2, 0), 
            rect($μ_(A ⊗_(cal(C)) B, C)$, stroke: none), label_pos: 0),
        node((1, 2), [$F A ⊗_(cal(D)) F(B ⊗_(cal(C)) C)$]),
        arr((0, 2), (1, 2), [$F A ⊗_(cal(D)) μ_(C, D)$], label_pos: 0),
        node((2, 2), [$F(A ⊗_(cal(C)) (B ⊗_(cal(C)) D))$]),
        arr((2, 0), (2, 2), [$F(α^(cal(C))_(A, B, C))$], label_pos: 0),
        arr((1, 2), (2, 2), [$μ_(A, B ⊗_(cal(C)) C)$], label_pos: 0)
    )]
    (where $α^(cal(C)), α^(cal(D))$ are the associators of $cal(C), cal(D)$ resp.)
    - *unitality*: for all $A in cal(C)$, the following diagrams commute:
    #grid(
        columns: 2,
        align(center)[#commutative_diagram(
            node((0, 0), [$munit_(cal(D)) ⊗_(cal(D)) F A $]),
            node((0, 1), [$F munit_(cal(C)) ⊗_(cal(D)) F A$]),
            node((1, 1), [$F(munit_(cal(C)) ⊗_(cal(C)) A)$]),
            node((1, 0), [$F A$]),
            arr((0, 0), (0, 1), $ε ⊗_(cal(D)) F A$, label_pos: 0),
            arr((0, 1), (1, 1), rect($μ_(munit_(cal(C)), a)$, stroke: none), label_pos: 0),
            arr((1, 1), (1, 0), $F(λ^(cal(C))_A)$, label_pos: 0),
            arr((0, 0), (1, 0), rect($λ^(cal(D))_(F A)$, stroke: none), label_pos: 0)
        )],
        align(center)[#commutative_diagram(
            node((0, 0), [$F A ⊗_(cal(D)) munit_(cal(D))$]),
            node((0, 1), [$F A ⊗_(cal(D)) F munit_(cal(C))$]),
            node((1, 1), [$F(A ⊗_(cal(C)) munit_(cal(C)))$]),
            node((1, 0), [$F A$]),
            arr((0, 0), (0, 1), $ε ⊗_(cal(D)) F A$, label_pos: 0),
            arr((0, 1), (1, 1), rect($μ_(A, munit_(cal(C)))$, stroke: none), label_pos: 0),
            arr((1, 1), (1, 0), $F(ρ^(cal(C))_A)$, label_pos: 0),
            arr((0, 0), (1, 0), rect($ρ^(cal(D))_(F A)$, stroke: none), label_pos: 0)
        )],
    )
    A *(strong) (pre)monoidal functor* is a weak (pre)monoidal functor for which $ε$ and all $μ_(A, B)$ are isomorphisms. If they are all the identity morphism, then $F$ is called a *strict (pre)monoidal functor*. 

    A (lax) (pre)monoidal functor is said to be *symmetric* if, for all $A, B in |cal(C)|$, the following diagram commutes:
    #align(center)[#commutative_diagram(
        node((0, 0), [$F A ⊗_(cal(D)) F B$]),
        node((0, 1), [$F B ⊗_(cal(D)) F A$]),
        node((1, 0), [$F(A ⊗_(cal(C)) B)$]),
        node((1, 1), [$F(B ⊗_(cal(C)) A)$]),
        arr((0, 0), (0, 1), $σ^(cal(D))_(F A, F B)$, label_pos: 0),
        arr((0, 1), (1, 1), $μ_(B, A)$, label_pos: 0),
        arr((0, 0), (1, 0), $μ_(A, B)$, label_pos: 0),
        arr((1, 0), (1, 1), $F σ^(cal(C))_(A, B)$, label_pos: 0)
    )]
    where $σ^(cal(C)), σ^(cal(D))$ denote the symmetry of $cal(C), cal(D)$ resp.
]

/*
TODO: problems with the above definition in the premonoidal case, justification for effectful categories
*/


== Effectful Categories

/*
TODO: effectful category text
*/

#definition(name: "Effectful Category")[
    An *effectful category* is an identity-on-objects premonoidal functor $F: cal(V) -> cal(C)$ from a monoidal categorty $cal(V)$ (of "*values*") to a premonoidal category $cal(C)$ (of "*computations*") whose image is central. It is *symmetric* when $F$ is symmetric premonoidal.

    A *Freyd category* is an effectful category in which $cal(V)$ is cartesian monoidal.
]

/*
TODO:
- "effectful functors"; go figure out what these are supposed to be called again
- "effectful categories are monoidal categories w/ runtime"
- something something profunctors something something?
*/

/*

== Iterative and Elgot Monads

/*
TODO:
- iterative monads, Elgot monads
- pointer to guardedness (NOT USED HERE! But could be for "coproducts ain't guarded")
*/

== Traced Monoidal Categories

/*
TODO:
- trace, properties
- pointer to premonoidal trace (NOT USED HERE!)
- connection between iterative/Elgot and traced
*/

*/

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
                $br(a)$, $br(lbl(ℓ), a)$, $lite(e, s, t)$,
                $llet x = a; t$, $llet (x, y) = a; t$
            ),
            (
                $llet [lbl(ℓ_i)(x_i: A_i) => { t_i }]_i; s$
            )
        ),
    )
);
#grammar(isotope-grammar)
Note that we implicitly quotient up to α-equivalence, and that our grammar does not include a notion of function.

/*
TODO: change syntax for set of base types, instructions to avoid conflicting with effectful categories
*/

The grammar given is parametrized over a set of _base types_ $X ∈ cal(V)$ and _instructions_ $f ∈ cal(I)$. We will denote the set of valid types with base types $cal(V)$ as $types(cal(V))$.

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

//TODO: consider whether this is a good idea
We may sometimes write `br a`, whre `a` is an expression, as `ret a` to emphasize the fact that this is the return value of a function. Generally, however, we will only do so in blocks which are *not* nested in an expression. This is purely syntactic and has no semantic significance.

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
== Typing

/*
TODO: conditions on pure instructions, set of splittable/droppable types
*/
/*
TODO: copy types as split + drop?
*/
/*
TODO: rename split/drop to relevant/affine?
*/

In this section, we go over the rules defining well-typed `isotope` syntax. Our typing rules are parametrized by: 
- Predicates $sans("rel"), sans("aff") subset.eq cal(V)$
- For each $A, B in types(cal(V))$, 
    - A subset $cal(I)_0(A, B) subset.eq cal(I)$ of *instructions*.
    - A subset $cal(I)_1(A, B) subset.eq cal(I)_0(A, B)$ of *pure instructions* such that, if $cal(I)_I(A, B)$ is nonempty, then $rel(B) => rel(A)$ and $aff(B) => aff(A)$.

/*
TODO: grammar for typing contexts, label contexts
*/

=== Judgements

We introduce the following typing judgements:
#align(center,
    table(
        columns: 2,
        stroke: none,
        column-gutter: 2em,
        align: left,
        [*Syntax*],
        [*Meaning*],
        $istm(Γ, p, a, A)$,
        [$a$ is a term of type $A$ in context $Γ$ with purity $p in {0, 1}$],
        $isblk(Γ, sans(L), p, t, B)$,
        [$t$ is a block of type $B$ in control context $Γ;sans(L)$with purity $p in {0, 1}$],
        $splitctx(Γ, Δ, Ξ)$,
        [$Γ$ splits into contexts $Δ$, $Ξ$],
        $dropctx(Γ, Δ)$,
        [$Γ$ is a weakening of $Δ$],
        $joinctx(sans(K), sans(L))$,
        [$sans(K)$ is a subset of label-set $sans(L)$],
        $rel(A)$, [$A$ can be split],
        $aff(A)$, [$A$ can be dropped]
    )
)

=== Structural rules

#let typing-rules = (
    "fwd-aff": prft(name: "fwd-aff", $sans("aff")(X)$, $aff(X)$),
    "unit-aff" : prft(name: "1-aff", $aff(tobj)$),
    "bool-aff": prft(name: "2-aff", $aff(bools)$),
    "pair-aff": prft(name: "pair-aff", $aff(A)$, $aff(B)$, $aff(A ⊗ B)$),
    "fwd-rel": prft(name: "fwd-rel", $sans("rel")(X)$, $rel(X)$),
    "unit-rel" : prft(name: "1-rel", $rel(tobj)$),
    "bool-rel": prft(name: "2-rel", $rel(bools)$),
    "pair-rel": prft(name: "pair-rel", $rel(A)$, $rel(B)$, $rel(A ⊗ B)$),
    "ctx-nil": prft(name: "ctx-nil", $splitctx(cnil, cnil, cnil)$),
    "ctx-left": prft(name: "ctx-left", 
        $splitctx(Γ, Δ, Ξ)$, 
        $#splitctx($x: A, Γ$, $x: A, Δ$, $Ξ$)$),
    "ctx-right": prft(name: "ctx-right", 
        $splitctx(Γ, Δ, Ξ)$, 
        $#splitctx($x: A, Γ$, $Δ$, $x: A, Ξ$)$),
    "ctx-rel": prft(name: "ctx-rel", 
        $splitctx(Γ, Δ, Ξ)$,
        $rel(A)$, 
        $#splitctx($x: A, Γ$, $x: A, Δ$, $x: A, Ξ$)$),
    "wk-nil": prft(name: "wk-nil", 
        $dropctx(cnil, cnil)$,
        $aff(A)$, 
        $#splitctx($x: A, Γ$, $Δ$, $Ξ$)$),
    "wk-add": prft(name: "wk-add", 
        $dropctx(Γ, Δ)$,
        $#dropctx($x: A, Γ$, $x: A, Δ$)$),
    "wk-aff": prft(name: "wk-aff", 
        $dropctx(Γ, Δ)$,
        $aff(A)$, 
        $#dropctx($x: A, Γ$, $Δ$)$),
    "label-nil": prft(name: "label-nil", $joinctx(bcnil, bcnil)$),
    "label-join": prft(name: "label-join", 
        $joinctx(sans(K), sans(L))$,
        joinctx($sans(K)$, $lhyp(Γ, lbl(ell), p, A), sans(L)$)),
    "label-ext": prft(name: "label-ext", 
        $joinctx(sans(K), sans(L))$,
        joinctx($lhyp(Γ, lbl(ell), p, A), sans(K)$, $lhyp(Γ, lbl(ell), p, A), sans(L)$)),
    "var": prft(name: "var", 
        dropctx($Γ$, $x: A$), $istm(Γ, p, x, A)$),
    "app": prft(name: "app",
        $f in cal(I)_p(A, B)$, $istm(Γ, p, a, A)$, 
        $istm(Γ, p, f aq a, B)$),
    "nil": prft(name: "nil",
        dropctx($Γ$, $cnil$), $istm(Γ, p, (), tobj)$),
    "true": prft(name: "true",
        dropctx($Γ$, $cnil$), $istm(Γ, p, ltt, bools)$),
    "false": prft(name: "false",
        dropctx($Γ$, $cnil$), $istm(Γ, p, lff, bools)$),
    "pair": prft(name: "pair",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Δ, p, a, A)$,
        $istm(Ξ, p, b, B)$,
        istm($Γ$, $p$, $(a, b)$, $A ⊗ B$)
    ),
    "let": prft(name: "let",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Δ, p, a, A)$,
        istm($x: A, Ξ$, $p$, $e$, $B$),
        istm($Γ$, $p$, $llet x = a; e$, $B$)
    ),
    "blk": prft(name: "blk",
        $isblk(Γ, bcnil, p, t, B)$,
        $istm(Γ, p, {t}, B)$
    ),
    "let2": prft(name: "let2",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Δ, p, e, A ⊗ B)$,
        istm($x: A, y: B, Ξ$, $p$, $e'$, $C$),
        istm($Γ$, $p$, $llet (x, y) = e; e'$, $C$)
    ),
    "br": prft(name: "br", 
        $joinctx(bcnil, sans(L))$,
        $istm(Γ, p, a, A)$,
        $isblk(Γ, sans(L), p, br(a), A)$,
    ),
    "jmp": prft(name: "jmp",
        $splitctx(Γ, Δ, Ξ)$,
        $istm(Δ, p, a, A)$,
        $joinctx(lhyp(Ξ, lbl(ℓ), q, A), sans(L))$,
        $p ≤ q$,
        $isblk(Γ, sans(L), p, br(lbl(ell), a), B)$,
    ),
    "ite": prft(name: "ite",
        $splitctx(Γ, Δ, Ξ)$,
        $istm(Δ, p, e, bools)$,
        $isblk(Ξ, sans(L), p, s, B)$,
        $isblk(Ξ, sans(L), p, t, B)$,
        $isblk(Γ, sans(L), p, lite(e, s, t), B)$
    ),
    "let-blk": prft(name: "let-blk",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Δ, p, a, A)$,
        isblk($x: A, Ξ$, $sans(L)$, $p$, $t$, $B$),
        isblk($Γ$, $sans(L)$, $p$, $llet x = a; t$, $B$)
    ),
    "let2-blk": prft(name: "let2-blk",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Δ, p, e, A ⊗ B)$,
        isblk($x: A, y: B, Ξ$, $sans(L)$, $p$, $t$, $C$),
        isblk($Γ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)
    ),
    "tr": prft(name: "tr",
        $forall i, 
            #[
                #isblk(
                $x_i: A_i, Delta_i$, 
                $[lhyp(Delta_j, lbl(ell)_j, 0, A_j)]_j, sans(L)$,
                $p_i$,
                $t_i$,
                $B$
            )]$,
        isblk(
            $Γ$, 
            $[lhyp(Delta_j, lbl(ell)_j, p_j, A_j)]_j, sans(L)$,
            $p$,
            $s$,
            $B$),
        isblk(
            $Γ$,
            $sans(L)$,
            $p$,
            $llet [lbl(ell)_j(x_j: A_j) => {t_i}]_j; s$,
            $B$
        )
    )
)

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.fwd-aff),
        dprf(typing-rules.unit-aff),
        dprf(typing-rules.bool-aff),
        dprf(typing-rules.pair-aff),
    ),
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.fwd-rel),
        dprf(typing-rules.unit-rel),
        dprf(typing-rules.bool-rel),
        dprf(typing-rules.pair-rel),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.ctx-nil),
        dprf(typing-rules.ctx-left),
        dprf(typing-rules.ctx-right),
    ),
    dprf(typing-rules.ctx-rel),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.wk-nil),
        dprf(typing-rules.wk-add),
        dprf(typing-rules.wk-aff),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.label-nil),
        dprf(typing-rules.label-ext),
        dprf(typing-rules.label-join),
    ),
))

=== Term Typing

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.var),
        dprf(typing-rules.app),
        dprf(typing-rules.nil),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.true),
        dprf(typing-rules.false),
        dprf(typing-rules.pair),
    ),
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.let),
        dprf(typing-rules.blk),
    ),
    dprf(typing-rules.let2),
))

=== Block Typing

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.br),
        dprf(typing-rules.jmp),
    ),
    dprf(typing-rules.ite),
    dprf(typing-rules.let-blk),
    dprf(typing-rules.let2-blk),
    dprf(typing-rules.tr),
))

== Syntactic Metatheory

We begin by defining the notion of one context being a *subcontext* of another via the following rules:
#row-den(
    $prf(subctx(cnil, cnil), name: "sub-nil")$,
    $prf(subctx(Γ, Δ), #[#subctx($x: A, Γ$, $x: A, Δ$)], name: "sub-add")$,
    $prf(subctx(Γ, Δ), #[#subctx($x: A, Γ$, $Δ$)], name: "sub-ext")$
)
We state the following basic properties of this relation:
- $subctx(Γ, Δ)$ is a partial order on contexts (i.e. is reflexive, transitive, and antisymmetric)
- $splitctx(Γ, Δ, Ξ) ==> subctx(Δ, Γ) and subctx(Ξ, Γ)$
- $dropctx(Γ, Δ) ==> subctx(Δ, Γ)$
// We now define the notion of the *union* of two contexts, $Γ ∪ Δ$, to be the unique context, if it exists, given by the following rules:
// #row-den(
//     $prf(cnil ∪ Γ = Γ, name: "union-lnil")$,
//     $prf(Γ ∪ cnil = Γ, name: "union-rnil")$,
//     prf($Γ ∪ Δ = Ξ$, $rel(A)$, $x: A, Γ ∪ x: A, Δ = x: A, Ξ$, name: "union-rel")
// )
// $
// #[
//     #prf($Γ ∪ Δ = Ξ$, $x ∉ Δ$, $x: A, Γ ∪ Δ = x: A, Ξ$, name: "union-ext")
// ]
// $
// Some basic properties of the union include
// - $splitctx(Γ ∪ Δ, Γ, Δ)$; furthermore, if $∃Ξ, splitctx(Ξ, Γ, Δ)$, then $Γ ∪ Δ$ exists and $Ξ$ is a permutation of it.
// - $Γ ∪ Γ = Γ$ if the former exists
// - $Γ ∪ (Δ ∪ Ξ) = (Γ ∪ Δ) ∪ Ξ$, with one side defined if the other is
// This allows us to define the union $union.big_x Δ_x$ of an ordered, finite collection of contexts $Δ_x$.

We now state a few basic lemmas about splitting and weakening contexts:
- $dropctx(Γ, Δ) <=> ∃Ξ, splitctx(Γ, Δ, Ξ) and dropctx(Ξ, cnil)$; furthermore, if it exists, this $Ξ$ is unique.
- $splitctx(Γ, Δ, Ξ) <==> splitctx(Γ, Ξ, Δ)$
- $∃K, splitctx(Γ, Δ, K) ∧ splitctx(K, Ξ, Θ) <==> ∃K', splitctx(Γ, K', Ξ) and splitctx(K', Δ, Θ)$ //TODO: think about this one...

We may now state some basic theorems and definitions:
#let upgrade-stmt = lemma(name: "Upgrade")[
    If $istm(Γ, 1, a, A)$, then $istm(Γ, 0, a, A)$. Similarly, if $isblk(Γ, sans(L), 1, t, B)$, then $isblk(Γ, sans(L), 0, t, B)$.
]
#upgrade-stmt
#proof[
    See @syntactic-properties[Appendix]
]

#definition(name: "Substitution")[
    We define a *substitution* $γ: Δ -> Γ$ to be an assignment of a context $Δ_x$ and a pure term $istm(Δ_x, 1, a, A)$ to each variable $x: A ∈ Γ$ such that $splitctx(Δ, [Δ_x]_(x ∈ Γ))$.

    We define the capture-avoiding substitution $[γ]a$, $[γ]t$ of a term or block as usual. We define the substitution of a _context_ $Ξ$ to be given by $[γ]Ξ = ⋃_(x: A ∈ Ξ)Δ_x$ where, for $x: A ∉ Γ$, we have $Δ_x = {x: A}$.
]

#let syntactic-substitution-stmt = lemma(name: "Syntactic Substitution")[
    Given a substitution $γ: Δ -> Γ$, for all terms $istm(Γ, p, a, A)$ and blocks $isblk(Γ, sans(L), p, t, B)$, we have $istm(Δ, p, [γ]a, A)$ and $isblk(Δ, sans(L), p, [γ]t, B)$
    //TODO: proper statement for label contexts...
];
#syntactic-substitution-stmt
#proof[
    See @syntactic-properties[Appendix]
]

= Semantics

In this section, we give a denotational semantics to well-typed `isotope` programs in an effectful category $(cal(C)_1, cal(C)_0)$ equipped with some auxiliary structure. We then prove some basic properties of our semantics.

== Denotational Semantics

/*
TODO: category used
TODO: cal(C)_0 = cal(V), cal(C)_1 = cal(C) or smt like that?
*/

/*
TODO: note on coercion
*/

=== Types and Contexts

#let syntax-den(..args) = {
    align(left)[#table(
        columns: args.pos().len(),
        column-gutter: 2em,
        align: horizon,
        stroke: none,
        ..args
    )]
};

#syntax-den(
    rect($dnt(A): |cal(C)_1|$),
    $dnt(X) = sans("base")(X)$,
    $dnt(tobj) = munit$,
    $dnt(bools) = bools$,
    $dnt(A ⊗ B) = dnt(A) ⊗ dnt(B)$,
)
#syntax-den(
    rect([$dnt(Γ): |cal(C)_1|$]),
    $dnt(cnil) = munit$,
    $dnt(#[$x: A, Γ$]) = dnt(A) ⊗ dnt(Γ)$,
)
#syntax-den(
    rect([$dnt(sans(L)): |cal(C)_1|$]),
    $dnt(bcnil) = iobj$,
    $dnt(#[$lhyp(Γ, lbl(ell), p, A), sans(L)$]) = (dnt(Gamma) ⊗ dnt(A)) ⊕ dnt(sans(L))$,
)
//TODO: this

=== Structural Rules

$
#rect([$dnt(aff(A)): cal(C)_1(dnt(A), munit)$])
$
#row-den(
    $dnt(dprf(#typing-rules.fwd-aff)) = sans("aff")(X)$,
    $dnt(dprf(#typing-rules.unit-aff)) = idm$
)
#row-den(
    $dnt(#dprf(typing-rules.bool-aff)) = sans("aff")(bools)$,
    $dnt(#dprf(typing-rules.pair-aff)) = dnt(#typing-rules.pair-aff.premises.at(0)) ⊗ dnt(#typing-rules.pair-aff.premises.at(1)); α$)
$
#rect([$dnt(rel(A)): cal(C)_1(dnt(A), dnt(A) ⊗ dnt(A))$])
$
#row-den(
    $dnt(dprf(#typing-rules.fwd-rel)) = sans("rel")(X)$,
    $dnt(dprf(#typing-rules.unit-rel)) = α$,
    $dnt(dprf(#typing-rules.bool-rel)) = sans("rel")(bools)$,
)
$
    dnt(dprf(#typing-rules.pair-rel)) =
    dnt(#typing-rules.pair-rel.premises.at(0)) ⊗ dnt(#typing-rules.pair-rel.premises.at(1));α;
    idm_(dnt(A)) ⊗ σ_(dnt(A), dnt(B)) ⊗ idm_(dnt(B));
    α
$
$
#rect([$dnt(joinctx(sans(K), sans(L))): cal(C)_1(dnt(sans(K)), dnt(sans(L)))$])
$
#row-den(
    $dnt(dprf(#typing-rules.label-nil)) = idm$,
    $dnt(dprf(#typing-rules.label-join)) = dnt(#typing-rules.label-join.premises.at(0)); α^⊕;0_(dnt(A) ⊗ dnt(Γ)) ⊕ dnt(L)$
)
$
dnt(dprf(#typing-rules.label-ext)) 
= (dnt(A) ⊗ dnt(Γ)) ⊕ dnt(#typing-rules.label-ext.premises.at(0))
$
$
#rect([$dnt(splitctx(Γ, Δ, Ξ)): cal(C)_1(dnt(Γ), dnt(Δ) ⊗ dnt(Ξ))$])
$
#row-den(
    $dnt(dprf(#typing-rules.ctx-nil)) = α$,
    $dnt(dprf(#typing-rules.ctx-left)) = dnt(A) ⊗ dnt(#typing-rules.ctx-left.premises.at(0));α$
)
$
dnt(dprf(#typing-rules.ctx-right)) =
dnt(A) ⊗ dnt(#typing-rules.ctx-right.premises.at(0));
α;σ_(dnt(A), dnt(Δ)) ⊗ dnt(Ξ);α
$
$
dnt(dprf(#typing-rules.ctx-rel)) =
dnt(#typing-rules.ctx-rel.premises.at(1)) ⊗ dnt(#typing-rules.ctx-rel.premises.at(0));
α;dnt(A) ⊗ σ_(dnt(A), dnt(Δ)) ⊗ dnt(Ξ);α
$
$
#rect([$dnt(dropctx(Γ, Δ)): cal(C)_1(dnt(Γ), dnt(Δ))$])
$
#row-den(
    $dnt(dprf(#typing-rules.wk-nil)) = idm$,
    $dnt(dprf(#typing-rules.wk-add)) = dnt(A) ⊗ dnt(dropctx(Γ, Δ))$
)

//TODO: string diagrams, since all structrure is in cal(C)_1?

=== Term Typing

$
#rect([$dnt(istm(Γ, p, a, A)): cal(C)_p(dnt(Γ), dnt(A))$])
$
#row-den(
    $dnt(dprf(#typing-rules.var)) = upg(dnt(#typing-rules.var.premises.at(0)), purity: p)$,
    $dnt(dprf(#typing-rules.nil)) = upg(dnt(#typing-rules.nil.premises.at(0)), purity: p)$,
)
$
dnt(dprf(#typing-rules.app)) = sans("inst")_p(f) ∘ dnt(#typing-rules.var.premises.at(0))
$
#row-den(
    $dnt(dprf(#typing-rules.true)) = upg(dnt(#typing-rules.true.premises.at(0)), purity: p);sans("tt")$,
    $dnt(dprf(#typing-rules.false)) = upg(dnt(#typing-rules.false.premises.at(0)), purity: p);sans("ff")$,
)
$
dnt(dprf(#typing-rules.pair)) = upg(dnt(#typing-rules.pair.premises.at(0)), purity: p);dnt(#typing-rules.pair.premises.at(1)) ⋉_p dnt(#typing-rules.pair.premises.at(2))
$
$
dnt(dprf(#typing-rules.let)) 
\ #h(5em) = upg(dnt(#typing-rules.let.premises.at(0)), purity: p);
    dnt(#typing-rules.let.premises.at(1)) ⊗ dnt(Ξ);
    dnt(#typing-rules.let.premises.at(2))
$
$
dnt(dprf(#typing-rules.let2))
\ #h(5em) = upg(dnt(#typing-rules.let2.premises.at(0)), purity: p);
    dnt(#typing-rules.let2.premises.at(1)) ⊗ dnt(Ξ);α;
    dnt(#typing-rules.let2.premises.at(2))
$
$
dnt(dprf(#typing-rules.blk)) = dnt(#typing-rules.blk.premises.at(0));α^⊕
$
/*
TODO: effectful string diagrams?
*/

=== Block Typing

$
#rect([$dnt(isblk(Γ, sans(L), p, t, B)): cal(C)_p(dnt(Γ), dnt(B) ⊕ dnt(sans(L)))$])
$


$
dnt(dprf(#typing-rules.br)) = dnt(#typing-rules.br.premises.at(1));α^⊕;dnt(A) ⊕ upg(dnt(#typing-rules.br.premises.at(0)), purity: p)
$
$
dnt(dprf(#typing-rules.jmp)) 
\ #h(5em) =
upg(dnt(#typing-rules.jmp.premises.at(0)), purity: p);dnt(#typing-rules.jmp.premises.at(1)) ⊗ Ξ;α^⊕;0_B ⊕ upg(dnt(#typing-rules.jmp.premises.at(2)), purity: p)
$
$
dnt(dprf(#typing-rules.ite))
\ #h(5em) =
upg(dnt(#typing-rules.ite.premises.at(0)), purity: p);
dnt(#typing-rules.ite.premises.at(1)) ⊗ Ξ;
sans("ite");
dnt(#typing-rules.ite.premises.at(2)) ⊕ dnt(#typing-rules.ite.premises.at(3))
$
$
dnt(dprf(#typing-rules.let-blk))
\ #h(5em) =
upg(dnt(#typing-rules.let-blk.premises.at(0)), purity: p);
dnt(#typing-rules.let-blk.premises.at(1)) ⊗ Ξ;
dnt(#typing-rules.let-blk.premises.at(2))
$
$
dnt(dprf(#typing-rules.let2-blk))
\ #h(5em) =
upg(dnt(#typing-rules.let2-blk.premises.at(0)), purity: p);
dnt(#typing-rules.let2-blk.premises.at(1)) ⊗ Ξ;
α;
dnt(#typing-rules.let2-blk.premises.at(2))
$
$
dnt(dprf(#typing-rules.tr))
\ =
sans("Tr")_(dnt(Γ), dnt(B) ⊕ dnt(sans(L)))^(⊕_i dnt(A_j) ⊗ dnt(Δ_j))
[
    (dnt(#typing-rules.tr.premises.at(1));α^⊕) ⊕ D; j
]
$
where
$
D = j^i ∘ plus.circle.big_i dnt(isblk(Δ_i, #[$[lhyp(Δ_j, lbl(ℓ_j), 0, A_j)]_j, sans(L)$], p, t_i, B))
$
/*
TODO: notes on guardedness...
*/
/*
TODO: string diagrams for control flow?
*/

/*
== Properties

//TODO: semantic substitution
*/

/*

= Graphical Syntax

//TODO: this

= Threading Transformation

//TODO: this

= State-splitting

//TODO: this

= Optimization

//TODO: this

= Related Work

//TODO: this

*/

#pagebreak()
#bibliography("references.bib")
#pagebreak()

#show: isotope-appendix

= Category Theory

== Elementary Category Theory <cats>

/*
TODO: define thin categories, etc.
*/

In this section, we go over some core notions from category theory, with the aim of fixing notations and conventions.
#definition(name: "Category")[
    A *category* $cal(C)$ consists of
    - A set of *objects* $|cal(C)|$
    - For any two objects $A, B ∈ |cal(C)|$, a *hom-set* of *morphisms* $cal(C)(A, B)$ between them. When $cal(C)$ is clear from context, we may denote this set as $A → B$
    - For each $A ∈ |cal(C)|$, an *identity morphism* $idm_A ∈ cal(C)(A, A)$. We omit the subscript where $A$ is clear from context.
    //TODO: id should not be italicized in the bullet above.
    - A *composition operator* $∘: cal(C)(B, C) → cal(C)(A, B) → cal(C)(A, C)$ such that
        - $f ∘ (g ∘ h) = (f ∘ g) ∘ h$
        - $f ∘ idm = idm ∘ f = f$
    We define $f;g = g ∘ f$
]
Some basic examples of categories we will be using include (all with the standard notion of composition):
- The category of sets $Set$, with objects sets, morphisms functions
- The category of _partial functions_ $Pfn$, with objects sets and morphisms _partial_ functions
- The category of _relations_ $Rel$, with objects sets and morphisms _relations_
- The category of _pointed sets_, $SetP$, with objects _pointed sets_ $(A, •)$ (where $A$ is a set and $• ∈ A$ is the _basepoint_) and morphisms $SetP((A, •_A), (B, •_B))$ _basepoint preserving maps_, i.e. functions $f: A → B$ such that
$f •_A = •_B$
- The category of _partially ordered sets_, $Pos$, with objects partially ordered sets $(A, ≼)$ (where $A$ is a set and $≼$ a partial order on $A$) and morphisms monotonically increasing functions
- The category of _monoids_ $Mon$, with objects monoids $(M, *)$ (where $A$ is a set and $*: M → M → M$ a monoid operation) and morphisms monoid homomorphisms
Note that in all three cases the "set" of objects is not really a set (since there is no set of all sets/monoids), but rather a class. However, for the purposes of this document, we will ignore size issues.
#definition(name: "Isomorphism")[
    A morphism $f: cal(C)(A, B)$ is an *isomorphism* if there exists a morphism $g: cal(C)(B, A)$ such that $f;g = idm_A$, $g;f = idm_B$; in this case we say that $A$ and $B$ are *isomorphic*, written $A ≃ B$
]
For example,
- In $Set$, $Pfn$, and $Rel$, the isomorphisms are the bijections; in $SetP$ the isomorpisms are the basepoint-preserving bijections
- In $Pos$ and $Mon$, we recover the usual mathematical notion of isomorphism
/*
TODO: improve this segue + section?
*/
We would also like to generalize the notion of _inclusion_ to the categorical setting; to that end, we may introduce the notion of a _monomorphism_ as follows:
#definition(name: "Monomorphism")[
    A morphism $f: cal(C)(B, C)$ is a *monomorphism* if
    $forall g, g': cal(C)(A, B), g;f = g';f <==> g = g'$
]
For example,
- In $Set$, $Pfn$, and $Rel$, the monomorphisms are the injections; in $SetP$ the isomorpisms are the basepoint-preserving injections
- In $Pos$ and $Mon$, we recover the usual mathematical notion of inclusion
In particular, we note that all isomorphisms are monomorphisms.
/*
TODO: intro to universal products and commutative diagrams, terminal and initial objects, Cartesian products and coproducts
*/
Given any category $cal(C)$, we may define the *opposite category* $opp(cal(C))$ with objects $|opp(cal(C))| = |cal(C)|$, morphisms $opp(cal(C))(A, B) = cal(C)(B, A)$, and composition $opp(f) ∘ opp(g) = opp(g ∘ f)$, where $opp(f)$ denotes reinterpreting $f: cal(C)(X, Y)$ as a morphism in $opp(cal(C))(Y, X)$ 
/*
TODO: flipping stuff in the opposite categeory
*/
#definition(name: "Functor")[
    A *(covariant) functor* $F: cal(C) → cal(D)$ from a category $cal(C)$ to a category $cal(D)$ consists of
    - A mapping $|F|: |cal(C)| → |cal(D)|$. We define $F A = F|A|$ for $A ∈ |cal(C)|$
    - A mapping $fcomp(F, A, B): cal(C)(A, B) → cal(D)(F A, F B)$. We define $F f = fcomp(F, A, B) f$ for $f ∈ cal(C)(A, B)$ such that
        - $F idm_A = idm_(F A)$
        - $F (f; g) = F f ; F g$
    We say a functor is *full* if each $fcomp(F, A, B)$ is surjective ("$F$ is surjective on hom-sets") and *faithful* if each $fcomp(F, A, B)$ is injective ("$F$ is injective on hom-sets"). A functor is *identity on objects* if $|F| = idm$. Composition on functors is defined componentwise as
    $
        |F ∘ G| = |F| ∘ |G|, qq
        fcomp((F ∘ G), A, B) = fcomp(F, G A, G B) ∘ fcomp(G, A, B)
    $
    A functor $F: cal(C) -> cal(C)$ is called an *endofunctor*. A *cotravariant functor* from $cal(C)$ to $cal(D)$ is simply a covariant functor from $opp(cal(C)) → cal(D)$.
]
Some examples of important functors on our example categories include:
- The *identity functor* $idm$, which is simply the identity on objects and morphisms
- The #strong("inclusion functor")s $Set → Pfn$ (interpreting a function as a partial function), $Set → Rel$, $Pfn → Rel$ (mapping [partial] functions to their graphs). These functor are _faithful_, but not _full_.
- The *forgetful functors* $SetP → Set$, $Pos → Set$, $Mon → Set$ mapping pointed sets/monoids/functors $(A, b), (A, ≼)$, $(A, *)$ to their carrier sets $A$ (with morphisms reinterpreted as plain functions)
- The *Hom-functor* $cal(C)(A, -): cal(C) → Set$ mapping objects $X$ to $cal(C)(A, X)$ and morphisms $f: X → Y$ via $cal(C)(A, f) = (g ↦ g;f): cal(C)(A, X) → cal(C)(A, Y)$
- The *contravariant Hom-functor* $cal(C)(-, B): opp(cal(C)) → Set$ mapping objects $X$ to $cal(C)(X, B)$ and morphisms $h: opp(cal(C))(Y, X)$ (i.e. $cal(C)(X, Y)$) via $cal(C)(h, B) = (g ↦ h;g): cal(C)(Y, B) → cal(C)(X, B)$
The notion of functor allows us to define the *category of categories*, $Cat$, with objects categories $cal(C)$ and morphisms functors $F: cal(C) → cal(D)$. This immediately gives us a definition for isomorphism of categories; namely, that there exist two functors $F: cal(C) → cal(D)$, $G: cal(D) → cal(G)$ such that $F;G = idm_(cal(C))$, $G;F = idm_(cal(D))$. However, it turns out this is not the correct notion of "sameness" for categories; to define equivalence of categories, we must first introduce the concept of a *natural transformation*:
#definition(name: "Natural Transformation")[
    Given two functors $F, G: cal(C) → cal(D)$, a *natural transformation* $α: F => G$ is an assignment to every object $A ∈ |cal(C)|$ a morphism $α_A: cal(D)(F A, G A)$ (called the *component* of $α$ at $A$) such that, for any morphism $f: cal(C)(A, B)$, we have that
    $
    α_A;G f = F f;α_B
    $
    We say a family $α_A: cal(D)(F A, G A)$ is *natural* in the index $A$ if it induces a natural transformation $α: F A => G B$
]

Given natural transformations $α: F => G$ and $β: G => H$, we find that they compose to yield a natural transformation $(α; β): F => H$ with components $(α; β)_A = α_A;β_A$. This allows us to define the *functor category* $[cal(C), cal(D)]$ with objects functors from $cal(C) → cal(D)$ and morphisms natural transformations. Note that in this category the identity morphism is simply the identity natural transformation $idm: F => F$ with components $idm_(F A): cal(C)(F A, F A)$. 
/*
TODO: examples of natural transformations beyond the identity?
*/
A *natural isomorphism* is then simply an isomorphism in this category or, more concretely, a natural transformation $η: F => G$ (often written $η: F niso G$) such that there exists a natural isomorphism $η^(-1): G => F$ such that
$
∀A ∈ |cal(C)|, η_A;η^(-1)_A = idm_(F A), qq η^(-1)_A;η_A = idm_(G A)
$
/*
TODO: examples of natural isomorphisms?
*/
We may now define equivalence of categories as follows:
#definition(name: "Equivalence of Categories")[
        An *equivalence* between categories $cal(C), cal(D)$ is given by a pair of functors $F: cal(C) → cal(D)$, $G: cal(D) → cal(C)$ and a pair of natural isomorphisms $F;G niso idm_(cal(C))$, $G;F niso idm_(cal(D))$. If there exists an equivalence between $cal(C), cal(D)$, they are said to be *equivalent*.
]
Note that any two isomorphic categories are equivalent (by taking the functors to be the components of the isomorphism, and the natural transformations to be the identity), but not all equivalent categories are isomorphic.
/*
TODO: notation for equivalence of categories?
*/

/*
TODO: section for diagrams and (co)limits?
*/

=== Monads

#definition(name: "Monad")[
    A *monad* in a category $cal(C)$ is a tuple $(T, μ, η)$ where
    - $T: cal(C) -> cal(C)$ is an endofunctor
    //TODO: name μ and η?
    - $μ: T compose T => T$ is a natural transformation
    - $η: idm => T$ is a natural transformation
    A *Kliesli triple* in $cal(C)$ is a tuple $(T, η, -^*)$ where
    - $T: cal(C) -> cal(C)$ is an endofunctor
    - $forall A in |cal(C)|, η_A: A -> T A$
    - $forall f: cal(C)(A, T B), f^*: T A -> T B$ //TODO: name bind?
    such that $η_A^* = idm_(T A)$, $η_A;f^* = f$, and $f^*;g^* = (f;g^*)^*$

    Every monad $(T, μ, η)$ induces a Kliesli triple $(T, η, -^*)$ with $f^* = T f;μ$; likewise, every Kliesli triple $(T, η, -^*)$ induces a monad with $μ_A = idm_(T A)^*$; hence, we will use these names and notations interchangeably.
]
#definition(name: "Kliesli Category")[
    Given a category $cal(C)$ equipped with a monad $T$, we may define its *Kliesli category* $cal(C)_T$ to have
    - Objects $|cal(C)_T| = |cal(C)|$
    - Morphisms $cal(C)_T(A, B) = cal(C)(A, T B)$
    - Composition of $f: cal(C)_T(A, B)$ followed by $g: cal(C)_T(B, C)$ given by $f;g^*$ where $f, g$ are taken as morphisms in $cal(C)$
]
Monads can be viewed as capturing a "notion of computation" by considering $T A$ to represent "computations yielding $A$," which may also have some side-effects and dependencies on external input. For example, we may encode
- Partiality with $T A = A + 1$; in this case $Set_T ≃ Pfn$
- Total nondeterminism with $T A = pset^+ A$
- Partial nondeterminism with $T A = pset A$; in this case $Set_T ≃ Rel$
- Printing outputs of type $B$ with $T A = A × B^*$, where $B^*$ denotes the _Kleene star_
- Carrying around a mutable state of type $S$ with $T A = S -> A × S$
/*
TODO: pull these examples up? Also, might want to explicitly state what return/bind are (or join!)
*/
/*
TODO: mono condition
*/
/*
TODO: strong monads; or do we pull this down to the monoidal categories section?
*/
/*
TODO: commutative monads?
*/

=== Adjunctions

#definition(name: "Adjunction")[
    Let $cal(C), cal(D)$ be categories and let $L: cal(C) -> cal(D)$, $R: cal(D) -> cal(C)$ be a pair of functors. This is called a pair of *adjoint functors*, with $L$ the *left adjoint* and $R$ the *right adjoint*, written $adj(L, R)$, if, equivalently,
    - There exist a family of isomorphisms (bijections) $phi_(C, D): cal(D)(L(C), D) -> cal(C)(C, R(D))$ natural in $C in |cal(C)|$ and $D in |cal(D)|$
    - There exist two natural transformations $ε: L;R => idm_(cal(C))$ (the *counit*) and $η: idm_(cal(D)) => R;L$ (the *unit*) such that, for all $C in |cal(C)|, D in |cal(D)|$, we have
        - $L η_C; ε_(L C) = idm_(L C)$
        - $η_(R D); R(ε_D) = idm_(R D)$
    If there exists such a pair $(L, R)$, we say that $L$ *is a left adjoint* or *has a right adjoint*, and likewise, $R$ *is a right adjoint* or *has a left adjoint*.
]

#definition(name: "Adjoint Equivalence")[
    An *adjoint equivalence* between categories $cal(C), cal(D)$ is a pair of adjoint functors $adj(L, R)$ for which the unit $η$ and counit $ε$ are natural _isomorphisms_.
]
Note that the counit and unit of an adjoint equivalence trivially induce an equivalence of categories via the natural isomorphisms $ε: L;R => idm_(cal(C))$, $η^(-1): R;L => idm_(cal(D))$; similarly, any equivalence of categories with natural isomorphisms $ε: L;R => idm_(cal(C))$, $η^(-1): R;L => idm_(cal(D))$ is an adjoint equivalence if and only if, for all $C in |cal(C)|, D in |cal(D)|$, we have $L η_C; ε_(L C) = idm_(L C)$ and $η_(R D); R(ε_D) = idm_(R D)$
/*
TODO: express these in terms of whiskering? Would need to define whiskering...
*/

/*
TODO:
- what is an adjunction (text)
- examples, free functors
- adjoint equivalence
- adjoints and (co)continuity? Need the (co)limits section...
*/

/*
TODO:
- results on polygraphs, explicit runtime constructions?
*/

= Proofs

== Syntactic Properties <syntactic-properties>

#upgrade-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$ with $p = 1$. We generate one case for each possible rule:
    #let rstyle(rule) = [(#text(typing-rules.at(rule).name, maroon))];
    #let rname(rule) = [
        $#typing-rules.at(rule).conclusion$ #h(0.2em) (#text(typing-rules.at(rule).name, maroon))
    ];
    - #rname("var"): since by assumption #dropctx($Γ$, $x: A$), we may apply #rstyle("var") to derive $istm(Γ, 0, x, A)$ as desired.
    - #rname("app"): since by assumption $f ∈ cal(I)_1(A, B) ⊆ cal(I)_0(A, B)$, and by induction $istm(Γ, 0, a, A)$, we may apply #rstyle("app") to derive $istm(Γ, 0, f aq a, A)$ as desired.
    - #rname("jmp"): by induction, we have that $istm(Δ, 0, a, A)$, by assumption we have that $joinctx(lhyp(Ξ, q, lbl(ℓ), A), sans(L))$ for some $q ∈ {0, 1}$. Since $0 ≤ q$, we may apply #rstyle("jmp") to derive $isblk(Γ, sans(L), 0, br(lbl(l), a), B)$, as desired.
    - #rname("tr"): by assumption, we have that $∀i, #[#isblk($x_i: A_i, Δ_i$, $[lhyp(Δ_j, 0, lbl(ℓ_j), A_j)]_j, sans(L)$, $p_i$, $t_i$, $B$)]$. By induction, we have that #isblk($Γ$, $[lhyp(Δ_j, 0, lbl(ℓ_j), A_j)]_j, sans(L)$, $0$, $s$, $B$). Hence, we may apply #rstyle("tr") to yield the desired conclusion.
    The other cases are direct application of the respective typing rule to the inductive hypotheses.
    // - #rname("nil"), #rname("true"), #rname("false"): since by assumption $dropctx(Γ, cnil)$, we may apply the original rule to recover the desired conclusion.
    // - #rname("pair"): since by induction $istm(Δ, 0, a, A)$, $istm(Ξ, 0, b, B)$, we may apply #rstyle("pair") to derive #istm($Γ$, $0$, $(a, b)$, $A ⊗ B$) as desired.
    // - #rname("let"): since by induction $istm(Δ, 0, a, A)$, #istm($x: A, Ξ$, $0$, $e$, $B$), we may apply #rstyle("let") to derive #istm($Γ$, $0$, $llet x = a; e$, $B$) as desired.
    // - #rname("let2"): since by induction $istm(Δ, 0, e, A ⊗ B)$, #istm($x: A, y: B, Ξ$, $0$, $e'$, $C$), we may apply #rstyle("let2") to derive #istm($Γ$, $0$, $llet (x, y) = e; e'$, $C$) as desired.
    // - #rname("blk"): since by induction $isblk(Γ, sans(L), 0, t, B)$, we may apply #rstyle("blk") to derive $istm(Γ, 0, {t}, B)$ as desired.
    // - #rname("br"): since by induction $istm(Γ, 0, a, A)$, we may apply #rstyle("br") to derive $isblk(Γ, sans(L), 0, br(a), A)$ as desired.
    // - #rname("ite"): since by induction $istm(Δ, 0, e, bools)$, $isblk(Ξ, sans(L), 0, s, B)$, $isblk(Ξ, sans(L), 0, t, B)$, we may apply #rstyle("ite") to derive $isblk(Γ, sans(L), 0, lite(e, s, t), B)$ as desired
    // - #rname("let-blk"): since by induction $istm(Δ, 0, a, A)$, #isblk($x: A, Ξ$, $sans(L)$, $0$, $t$, $B$), we may apply #rstyle("let-blk") to derive #isblk($Γ$, $sans(L)$, $0$, $llet x = a; t$, $B$) as desired.
    // - #rname("let2-blk"): since by induction $istm(Δ, 0, e, A ⊗ B)$, #isblk($x: A, y: B, Ξ$, $sans(L)$, $0$, $t$, $C$), we may apply #rstyle("let2") to derive #isblk($Γ$, $sans(L)$, $0$, $llet (x, y) = e; t$, $C$) as desired.
]

#syntactic-substitution-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$. We generate one case for each possible rule:
    #let rname(rule) = [
        $#typing-rules.at(rule).conclusion$ #h(0.2em) (#text(typing-rules.at(rule).name, maroon))
    ];
    - #rname("var"): Since $γ: Γ -> Δ$ is a substitution, we by assumption have that $istm(Δ, 1, [γ]x, A)$; hence, by upgrade, we have that $istm(Δ_x, p, [γ]x, A)$, as desired.
    - #rname("app"): //TODO: this
    - #rname("nil"), #rname("true"), #rname("false"): //TODO: this
    - #rname("pair"): //TODO: this
    - #rname("let"): //TODO: this
    - #rname("let2"): //TODO: this
    - #rname("blk"): //TODO: this
    - #rname("br"): //TODO: this
    - #rname("jmp"): //TODO: this
    - #rname("ite"): //TODO: this
    - #rname("let-blk"): //TODO: this
    - #rname("let2-blk"): //TODO: this
    - #rname("tr"): //TODO: this
]