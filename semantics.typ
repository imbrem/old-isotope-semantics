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

#definition(name: "Binoidal Category", [
    A *binoidal category* is a category $cal(C)$ equipped with
    - A *tensor product* map on objects $⊗: |cal(C)| times |cal(C)| -> |cal(C)|$
    - For each object $A in |cal(C)|$,
        - A *right product functor* $A ⊗ -$ which is $B |-> A ⊗ B$ on objects
        - A *left product functor* $- ⊗ A$ which is $B |-> B ⊗ A$ on objects
    We define, for morphisms $f: A -> B$, $g: X -> Y$, the *left product* $f ltimes g = f ⊗ X; A ⊗ g$ and *right product* $f rtimes g: A ⊗ g; f ⊗ X$ morphisms $A ⊗ X -> B ⊗ Y$
])
#definition(name: "Central Morphism", [
    A morphsm $f$ a binoidal category $cal(C)$ is *central* if, for all morphisms $g$, we have $f ltimes g = f rtimes g$; in this case, we write $f ltimes g = f rtimes g = f ⊗ g$.
    We define the *center* of a binoidal category $cal(C)$, denoted $cen(cal(C))$, to be the wide subcategory with $|cen(cal(C))| = |cal(C)|$ and morphisms
    $
        cen(cal(C))(A, B) = {f in cal(C)(A, B) | f "is central"}
    $
    A natural transformation is central if all its components are.
])
#definition(name: "Premonoidal Category", [
    A *premonoidal category* is a binoidal category $cal(C)$ equipped with
    - An *identity object* $munit in |cal(C)|$
    - For all objects $A, B, C in cal(C)$, a central isomorphism $alpha_(A, B, C): (A ⊗ B) ⊗ C \to A ⊗ (B ⊗ C)$ (the *associator*) such that the following are natural isomorphisms
        - $alpha_(-, B, C): (- ⊗ B) ⊗ C => - ⊗ (B ⊗ C)$
        - $alpha_(A, -, C): (A ⊗ -) ⊗ C => A ⊗ (- ⊗ C)$
        - $alpha_(A, B, -): (A ⊗ B) ⊗ - => A ⊗ (B ⊗ -)$
    - A central natural isomorphism $lambda: - ⊗ munit => idm$  (the *left unitor*) 
    - A central natural isomorphism $rho: munit ⊗ - -> idm$ (the *right unitor*)
    such that the *triangle identity*
    $
    rho_A ⊗ B = alpha_(A, munit, B); A ⊗ lambda_B: (A ⊗ munit) ⊗ B -> A ⊗ B
    $
    and *pentagon identity*
    $
    alpha_(A, B, C) ⊗ D; alpha_(A, B ⊗ C, D); A ⊗ alpha_(B, C, D) =
    alpha_(A ⊗ B, C, D); alpha_(A, B, C ⊗ D)
    $
    hold for all $A, B, C, D in |cal(C)|$.

    We say a premonoidal category is *strict* if $(A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)$, $A ⊗ I = I ⊗ A = A$, and $alpha, rho, lambda$ are the identity transformations.
])
#definition(name: "Symmetric Premonoidal Category", [
    We say a premonoidal category is *braided* if, in addition, it is equipped with, for all objects $A, B in cal(C)$, a central isomorphism $sigma_(A, B): A ⊗ B -> B ⊗ A$ such that
    - $sigma_(-, B): (- ⊗ B) => (B ⊗ A)$ is a natural isomorphism
    - $sigma_(A, -): (A ⊗ -) => (A ⊗ -)$ is a natural isomorphism
    - $sigma_(A, B) = sigma_(B, A)^{-1}$
    - The following *hexagon identities* hold:
        - $alpha_(A, B, C);sigma_(A, B ⊗ C);alpha_(B, C, A)
            = sigma_(A, B) ⊗ C;alpha_(B, A, C);B ⊗ sigma_(A, C)$
        - $alpha_(A, B, C)^(-1);sigma_(A ⊗ B, C);alpha_(C, A, B)^(-1)
            = A ⊗ sigma_(B, C);alpha_(A, C, B)^(-1);sigma_(C, A) ⊗ B$
    We say a braided premonoidal category is *symmetric* if, in addition, we have $sigma_(A, B) = sigma_(B, A)^(-1)$; in this case, either hexagon identity implies the other.
])
#theorem(name: "Coherence", [
    Let $cal(C)$ be a premonoidal category. Then the smallest wide subcategory of $cal(C)$ containing all components of $alpha$, $lambda$, and $rho$ is thin.
])
#definition(name: "(Symmetric) Monoidal Category", [
    A (symmetric) monoidal category $cal(C)$ is a (symmetric) premonoidal category in which, equivalently,
    - All morphisms are central, i.e. $cal(C) = cen(cal(C))$
    - $ltimes = rtimes$, in which case we write both as $⊗$
    - $⊗$ is a bifunctor
])
In particular, for every (symmetric) premonoidal category $cal(C)$, we have that $cen(cal(C))$ is (symmetric) monoidal.

/*
TODO:
- binoidal text
- premonoidal text
- monoidal text
- string diagrams
- strong monads ==> premonoidal
- commutative monads ==> monoidal
- monoidal functors
*/

/*

== Effectful Categories

/*
TODO:
- "effectful functors"; go figure out what these are supposed to be called again
- "effectful categories are monoidal categories w/ runtime"
- something something profunctors something something?
*/

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

In this section, we go over the rules defining well-typed `isotope` syntax. Our typing rules are parametrized by: 
- Predicates $sans("splits"), sans("drops") subset.eq cal(V)$
- For each $A, B in types(cal(V))$, a subset $cal(I)(A, B) subset.eq cal(I)$. /* We say this is *fully specified* if each such subset is disjoint. */

=== Judgements

We introduce the following typing judgements:
#align(center,
    table(
        columns: 2,
        stroke: none,
        column-gutter: 2em,
        [*Syntax*],
        [*Meaning*],
        $istm(Gamma, a, A)$,
        [$a$ is a term of type $A$ in context $Gamma$],
        $isblk(Gamma, sans(L), t, B)$,
        [$t$ is a block of type $B$ in control context $Gamma;sans(L)$],
        $splitctx(Gamma, Delta, Xi)$,
        [$Gamma$ splits into contexts $Delta$, $Xi$],
        $joinctx(sans(K), sans(L))$,
        [$sans(K)$ is a subset of label-set $sans(L)$],
        $splits(A)$, [$A$ can be split],
        $drops(A)$, [$A$ can be dropped]
    )
)

=== Structural rules

#let typing-rules = (
    "fwd-drops": prft(name: "fwd-drops", $sans("drops")(X)$, $drops(X)$),
    "unit-drops" : prft(name: "unit-drops", $drops(tobj)$),
    "bool-drops": prft(name: "bool-drops", $drops(bools)$),
    "pair-drops": prft(name: "pair-drops", $drops(A)$, $drops(B)$, $drops(A ⊗ B)$),
    "fwd-splits": prft(name: "fwd-splits", $sans("splits")(X)$, $splits(X)$),
    "unit-splits" : prft(name: "unit-splits", $splits(tobj)$),
    "bool-splits": prft(name: "bool-splits", $splits(bools)$),
    "pair-splits": prft(name: "pair-splits", $splits(A)$, $splits(B)$, $splits(A ⊗ B)$),
    "ctx-nil": prft(name: "ctx-nil", $splitctx(cnil, cnil, cnil)$),
    "ctx-left": prft(name: "ctx-left", 
        $splitctx(Gamma, Delta, Xi)$, 
        $#splitctx($x: A, Gamma$, $x: A, Delta$, $Xi$)$),
    "ctx-right": prft(name: "ctx-right", 
        $splitctx(Gamma, Delta, Xi)$, 
        $#splitctx($x: A, Gamma$, $Delta$, $x: A, Xi$)$),
    "ctx-split": prft(name: "ctx-split", 
        $splitctx(Gamma, Delta, Xi)$,
        $splits(A)$, 
        $#splitctx($x: A, Gamma$, $x: A, Delta$, $x: A, Xi$)$),
    "ctx-drop": prft(name: "ctx-drop", 
        $splitctx(Gamma, Delta, Xi)$,
        $drops(A)$, 
        $#splitctx($x: A, Gamma$, $Delta$, $Xi$)$),
    "label-nil": prft(name: "label-nil", $joinctx(bcnil, bcnil)$),
    "label-join": prft(name: "label-join", 
        $joinctx(sans(K), sans(L))$,
        joinctx($sans(K)$, $lhyp(Gamma, lbl(ell), A), sans(L)$)),
    "label-ext": prft(name: "label-ext", 
        $joinctx(sans(K), sans(L))$,
        joinctx($lhyp(Gamma, lbl(ell), A), sans(K)$, $lhyp(Gamma, lbl(ell), A), sans(L)$)),
    "var": prft(name: "var", 
        splitctx($Gamma$, $x: A$), $istm(Gamma, x, A)$),
    "app": prft(name: "app",
        $f in cal(I)(A, B)$, $istm(Gamma, a, A)$, 
        $istm(Gamma, f aq a, B)$),
    "nil": prft(name: "nil",
        splitctx($Gamma$, $cnil$), $istm(Gamma, (), tobj)$),
    "true": prft(name: "true",
        splitctx($Gamma$, $cnil$), $istm(Gamma, ltt, bools)$),
    "false": prft(name: "false",
        splitctx($Gamma$, $cnil$), $istm(Gamma, lff, bools)$),
    "pair": prft(name: "pair",
        splitctx($Gamma$, $Delta$, $Xi$),
        $istm(Delta, a, A)$,
        $istm(Xi, b, B)$,
        istm($Gamma$, $(a, b)$, $A ⊗ B$)
    ),
    "let": prft(name: "let",
        splitctx($Gamma$, $Delta$, $Xi$),
        $istm(Delta, a, A)$,
        istm($x: A, Xi$, $e$, $B$),
        istm($Gamma$, $llet x = a; e$, $B$)
    ),
    "blk": prft(name: "blk",
        $isblk(Gamma, bcnil, t, B)$,
        $istm(Gamma, {t}, B)$
    ),
    "let2": prft(name: "let2",
        splitctx($Gamma$, $Delta$, $Xi$),
        $istm(Delta, e, A ⊗ B)$,
        istm($x: A, y: B, Xi$, $e'$, $C$),
        istm($Gamma$, $llet (x, y) = e; e'$, $C$)
    ),
    "br": prft(name: "br", 
        $istm(Gamma, a, A)$,
        $isblk(Gamma, sans(L), br(a), A)$,
    ),
    "jmp": prft(name: "jmp",
        $splitctx(Gamma, Delta, Xi)$,
        $istm(Delta, a, A)$,
        $joinctx(lhyp(Xi, lbl(l), A), sans(L))$,
        $isblk(Gamma, sans(L), br(lbl(ell), a), B)$,
    ),
    "ite": prft(name: "ite",
        $splitctx(Gamma, Delta, Xi)$,
        $istm(Delta, e, bools)$,
        $isblk(Xi, sans(L), s, B)$,
        $isblk(Xi, sans(L), t, B)$,
        $isblk(Gamma, sans(L), lite(e, s, t), B)$
    ),
    "let-blk": prft(name: "let-blk",
        splitctx($Gamma$, $Delta$, $Xi$),
        $istm(Delta, a, A)$,
        isblk($x: A, Xi$, $sans(L)$, $t$, $B$),
        isblk($Gamma$, $sans(L)$, $llet x = a; t$, $B$)
    ),
    "let2-blk": prft(name: "let2-blk",
        splitctx($Gamma$, $Delta$, $Xi$),
        $istm(Delta, e, A ⊗ B)$,
        isblk($x: A, y: B, Xi$, $sans(L)$, $t$, $B$),
        isblk($Gamma$, $sans(L)$, $llet (x, y) = e; t$, $B$)
    ),
    "tr": prft(name: "tr",
        $forall i, 
            #[
                #isblk(
                $x_i: A_i, Delta_i$, 
                $[lhyp(Delta_j, lbl(ell)_j, A_j)]_j, sans(L)$,
                $t_i$,
                $B$
            )]$,
        isblk(
            $Gamma$, 
            $[lhyp(Delta_j, lbl(ell)_j, A_j)]_j, sans(L)$,
            $s$,
            $B$),
        isblk(
            $Gamma$,
            $sans(L)$,
            $llet [lbl(ell)_j(x_j: A_j) => {t_i}]_j; s$,
            $B$
        )
    )
)

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.pair-drops),
        dprf(typing-rules.pair-splits),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.fwd-drops),
        dprf(typing-rules.unit-drops),
        dprf(typing-rules.bool-drops),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.fwd-splits),
        dprf(typing-rules.unit-splits),
        dprf(typing-rules.bool-splits),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.ctx-nil),
        dprf(typing-rules.ctx-left),
        dprf(typing-rules.ctx-right),
    ),
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.ctx-split),
        dprf(typing-rules.ctx-drop),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.label-nil),
        dprf(typing-rules.label-ext),
        dprf(typing-rules.label-join),
    ),
))
We write $splitctx(Gamma, Delta)$ as syntax sugar for $splitctx(Gamma, Delta, cnil)$.

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

/*

= Semantics

//TODO: this

= Graphical Syntax

//TODO: this

= Threading Transformation

//TODO: this

= State-splitting

//TODO: this

*/

#pagebreak()
#bibliography("references.bib")
#pagebreak()

#show: isotope-appendix

= Category Theory

== Elementary Category Theory <cats>

In this section, we go over some core notions from category theory, with the aim of fixing notations and conventions.
#definition(name: "Category", ([
    A *category* $cal(C)$ consists of
    - A set of *objects* $|cal(C)|$
    - For any two objects $A, B ∈ |cal(C)|$, a *hom-set* of *morphisms* $cal(C)(A, B)$ between them. When $cal(C)$ is clear from context, we may denote this set as $A → B$
    - For each $A ∈ |cal(C)|$, an *identity morphism* $idm_A ∈ cal(C)(A, A)$. We omit the subscript where $A$ is clear from context.
    //TODO: id should not be italicized in the bullet above.
    - A *composition operator* $∘: cal(C)(B, C) → cal(C)(A, B) → cal(C)(A, C)$ such that
        - $f ∘ (g ∘ h) = (f ∘ g) ∘ h$
        - $f ∘ idm = idm ∘ f = f$
    We define $f;g = g ∘ f$
]))
Some basic examples of categories we will be using include (all with the standard notion of composition):
- The category of sets $Set$, with objects sets, morphisms functions
- The category of _partial functions_ $Pfn$, with objects sets and morphisms _partial_ functions
- The category of _relations_ $Rel$, with objects sets and morphisms _relations_
- The category of _pointed sets_, $SetP$, with objects _pointed sets_ $(A, •)$ (where $A$ is a set and $• ∈ A$ is the _basepoint_) and morphisms $SetP((A, •_A), (B, •_B))$ _basepoint preserving maps_, i.e. functions $f: A → B$ such that
$f •_A = •_B$
- The category of _partially ordered sets_, $Pos$, with objects partially ordered sets $(A, ≼)$ (where $A$ is a set and $≼$ a partial order on $A$) and morphisms monotonically increasing functions
- The category of _monoids_ $Mon$, with objects monoids $(M, *)$ (where $A$ is a set and $*: M → M → M$ a monoid operation) and morphisms monoid homomorphisms
Note that in all three cases the "set" of objects is not really a set (since there is no set of all sets/monoids), but rather a class. However, for the purposes of this document, we will ignore size issues.
#definition(name: "Isomorphism", ([
    A morphism $f: cal(C)(A, B)$ is an *isomorphism* if there exists a morphism $g: cal(C)(B, A)$ such that $f;g = idm_A$, $g;f = idm_B$; in this case we say that $A$ and $B$ are *isomorphic*, written $A ≃ B$
]))
For example,
- In $Set$, $Pfn$, and $Rel$, the isomorphisms are the bijections; in $SetP$ the isomorpisms are the basepoint-preserving bijections
- In $Pos$ and $Mon$, we recover the usual mathematical notion of isomorphism
/*
TODO: improve this segue + section?
*/
We would also like to generalize the notion of _inclusion_ to the categorical setting; to that end, we may introduce the notion of a _monomorphism_ as follows:
#definition(name: "Monomorphism", ([
    A morphism $f: cal(C)(B, C)$ is a *monomorphism* if
    $forall g, g': cal(C)(A, B), g;f = g';f <==> g = g'$
]))
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
#definition(name: "Functor", ([
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
]))
Some examples of important functors on our example categories include:
- The *identity functor* $idm$, which is simply the identity on objects and morphisms
- The #strong("inclusion functor")s $Set → Pfn$ (interpreting a function as a partial function), $Set → Rel$, $Pfn → Rel$ (mapping [partial] functions to their graphs). These functor are _faithful_, but not _full_.
- The *forgetful functors* $SetP → Set$, $Pos → Set$, $Mon → Set$ mapping pointed sets/monoids/functors $(A, b), (A, ≼)$, $(A, *)$ to their carrier sets $A$ (with morphisms reinterpreted as plain functions)
- The *Hom-functor* $cal(C)(A, -): cal(C) → Set$ mapping objects $X$ to $cal(C)(A, X)$ and morphisms $f: X → Y$ via $cal(C)(A, f) = (g ↦ g;f): cal(C)(A, X) → cal(C)(A, Y)$
- The *contravariant Hom-functor* $cal(C)(-, B): opp(cal(C)) → Set$ mapping objects $X$ to $cal(C)(X, B)$ and morphisms $h: opp(cal(C))(Y, X)$ (i.e. $cal(C)(X, Y)$) via $cal(C)(h, B) = (g ↦ h;g): cal(C)(Y, B) → cal(C)(X, B)$
The notion of functor allows us to define the *category of categories*, $Cat$, with objects categories $cal(C)$ and morphisms functors $F: cal(C) → cal(D)$. This immediately gives us a definition for isomorphism of categories; namely, that there exist two functors $F: cal(C) → cal(D)$, $G: cal(D) → cal(G)$ such that $F;G = idm_(cal(C))$, $G;F = idm_(cal(D))$. However, it turns out this is not the correct notion of "sameness" for categories; to define equivalence of categories, we must first introduce the concept of a *natural transformation*:
#definition(name: "Natural Transformation", [
    Given two functors $F, G: cal(C) → cal(D)$, a *natural transformation* $α: F => G$ is an assignment to every object $A ∈ |cal(C)|$ a morphism $α_A: cal(D)(F A, G A)$ (called the *component* of $α$ at $A$) such that, for any morphism $f: cal(C)(A, B)$, we have that
    $
    α_A;G f = F f;α_B
    $
])
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
#definition(name: "Equivalence of Categories", [
        An *equivalence* between categories $cal(C), cal(D)$ is given by a pair of functors $F: cal(C) → cal(D)$, $G: cal(D) → cal(C)$ and a pair of natural isomorphisms $F;G niso idm_(cal(C))$, $G;F niso idm_(cal(D))$. If there exists an equivalence between $cal(C), cal(D)$, they are said to be *equivalent*.
])
Note that any two isomorphic categories are equivalent (by taking the functors to be the components of the isomorphism, and the natural transformations to be the identity), but not all equivalent categories are isomorphic.
/*
TODO: notation for equivalence of categories?
*/

/*
TODO: section for diagrams and (co)limits?
*/

=== Monads

#definition(name: "Monad", [
    A *monad* in a category $cal(C)$ is a tuple $(T, mu, eta)$ where
    - $T: cal(C) -> cal(C)$ is an endofunctor
    //TODO: name mu and eta?
    - $mu: T compose T => T$ is a natural transformation
    - $eta: idm => T$ is a natural transformation
    A *Kliesli triple* in $cal(C)$ is a tuple $(T, eta, -^*)$ where
    - $T: cal(C) -> cal(C)$ is an endofunctor
    - $forall A in |cal(C)|, eta_A: A -> T A$
    - $forall f: cal(C)(A, T B), f^*: T A -> T B$ //TODO: name bind?
    such that $eta_A^* = idm_(T A)$, $eta_A;f^* = f$, and $f^*;g^* = (f;g^*)^*$

    Every monad $(T, mu, eta)$ induces a Kliesli triple $(T, eta, -^*)$ with $f^* = T f;mu$; likewise, every Kliesli triple $(T, eta, -^*)$ induces a monad with $mu_A = idm_(T A)^*$; hence, we will use these names and notations interchangeably.
])
#definition(name: "Kliesli Category", [
    Given a category $cal(C)$ equipped with a monad $T$, we may define its *Kliesli category* $cal(C)_T$ to have
    - Objects $|cal(C)_T| = |cal(C)|$
    - Morphisms $cal(C)_T(A, B) = cal(C)(A, T B)$
    - Composition of $f: cal(C)_T(A, B)$ followed by $g: cal(C)_T(B, C)$ given by $f;g^*$ where $f, g$ are taken as morphisms in $cal(C)$
])
Monads can be viewed as capturing a "notion of computation" by considering $T A$ to represent "computations yielding $A$," which may also have some side-effects and dependencies on external input. For example, we may encode
- Partiality with $T A = A + 1$; in this case $Set_T tilde.eq Pfn$
- Total nondeterminism with $T A = pset^+ A$
- Partial nondeterminism with $T A = pset A$; in this case $Set_T tilde.eq Rel$
- Printing outputs of type $B$ with $T A = A times B^*$, where $B^*$ denotes the _Kleene star_
- Carrying around a mutable state of type $S$ with $T A = S -> A times S$
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

#definition(name: "Adjunction", [
    Let $cal(C), cal(D)$ be categories and let $L: cal(C) -> cal(D)$, $R: cal(D) -> cal(C)$ be a pair of functors. This is called a pair of *adjoint functors*, with $L$ the *left adjoint* and $R$ the *right adjoint*, written $adj(L, R)$, if, equivalently,
    - There exist, for all $C in |cal(C)|$, $D in |cal(D)|$, isomorphisms (bijections) $phi_(C, D): cal(D)(L(C), D) -> cal(C)(C, R(D))$ such that the following are natural isomorphisms
        - $phi_(-, D): cal(D)(L(-), D) => cal(C)(-, R(D))$
        - $phi_(C, -): cal(D)(L(C), -) => cal(C)(C, R(-))$
    - There exist two natural transformations $epsilon: L;R => idm_(cal(C))$ (the *counit*) and $eta: idm_(cal(D)) => R;L$ (the *unit*) such that, for all $C in |cal(C)|, D in |cal(D)|$, we have
        - $L eta_C; epsilon_(L C) = idm_(L C)$
        - $eta_(R D); R(epsilon_D) = idm_(R D)$
    If there exists such a pair $(L, R)$, we say that $L$ *is a left adjoint* or *has a right adjoint*, and likewise, $R$ *is a right adjoint* or *has a left adjoint*.
])

#definition(name: "Adjoint Equivalence", [
    An *adjoint equivalence* between categories $cal(C), cal(D)$ is a pair of adjoint functors $adj(L, R)$ for which the unit $eta$ and counit $epsilon$ are natural _isomorphisms_.
])
Note that the counit and unit of an adjoint equivalence trivially induce an equivalence of categories via the natural isomorphisms $epsilon: L;R => idm_(cal(C))$, $eta^(-1): R;L => idm_(cal(D))$; similarly, any equivalence of categories with natural isomorphisms $epsilon: L;R => idm_(cal(C))$, $eta^(-1): R;L => idm_(cal(D))$ is an adjoint equivalence if and only if, for all $C in |cal(C)|, D in |cal(D)|$, we have $L eta_C; epsilon_(L C) = idm_(L C)$ and $eta_(R D); R(epsilon_D) = idm_(R D)$
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