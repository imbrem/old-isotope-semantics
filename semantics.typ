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

/*
= Introduction

//TODO: this
*/

= Background

In this section, we go over some background notions used in the semantics. For an overview of basic category theory and the notations in use, see @cats[Appendix].

/*

== Monoidal Categories

/*
TODO:
- binoidal
- premonoidal
- monoidal
- string diagrams
- strong monads ==> premonoidal
- commutative monads ==> monoidal
- monoidal functors
*/

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

/*
= Typing

//TODO: this

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

= Category Theory <cats>

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

== Monads

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

/*

== Adjunctions

/*
TODO:
- what is an adjunction
- examples, free functors
- adjoint equivalence
- adjoints and (co)continuity? Need the (co)limits section...
*/

*/