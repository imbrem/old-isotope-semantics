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
Tasks:
0. Introduction
    a. Explain SSA
    b. Weaknesses of SSA
    c. RVSDGs and advantages
    d. Weaknesses of RVSDGs
    e. GRVSDGs
    f. Risks:
        i. Linear time SSA conversion, provability
        ii. SSA + RVSDGs embed in GRVSDGs
    g. Provably correct needs semantics; we have a modular semantics
1. Syntax
2. Semantics
    a. Axiomatic
    b. Concrete models
        i. Pfn
        ii. Printing
        iii. State
        iv. Concurrency
3. Metatheory
    a. Semantic
    b. Syntactic
4. GRVSDG-SSA translation
    a. Algorithm
    b. Semantic correctness
*/

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


== Iterative and Elgot Monads

Definitions taken from @coinductive-resumption

/*
NOTE: Removing guardedness for now

// #definition(name: "Guarded Category")[
//     A *guardedness predicate* on a cocartesian category $cal(K)$ provides, for all objects $A, B, C ∈ |cal(K)|$, a subset $cal(K)^•(A, B, C) ⊆ cal(K)(A, B + C)$. We write $f: A -> B ⟩ C$ for $f ∈ cal(K)^•(A, B, C)$, and require that:
//     #row-den(
//         prf(name: "trv", $f: A → B$, $sans("inl") ∘ f: A → B ⟩ C$),
//         prf(name: "par", $f: A → C ⟩ D$, $g: B → C ⟩ D$, $[f, g]: A + B → C ⟩ D$),
//     )
//     #row-den(
//         prf(name: "cmp",
//             $f: A →  B ⟩ C$,
//             $g: B →  D ⟩ E$,
//             $h: C →  D + E$, 
//             $f;[g, h]: A → D ⟩ E$
//         )
//     )
//     A category equipped with a guardedness predicate is called a *guarded category*. A monad $T$ on $cal(C)$ is a *guarded monad* if it's Kliesli category $cal(C)_T$ is a guarded category under the coproducts inherited from $cal(C)$. 
// ]

// #definition(name: "Greatest and Least Guardedness Predicates")[
//     - The *greatest guardedness predicate* on $cal(K)$ sets $cal(K)^⬝(A, B, C) = cal(K)(A, B + C)$
//     - The *least guardedness predicate* on $cal(K)$ says that
//     $
//     f ∈ cal(K)^⬝(A, B, C) <==> ∃g: A → B, f = g;sans("inl")
//     $
//     We say that $cal(K)$ is *totally guarded* when equipped with the largest guardedness predicate and *vacuously guarded* when equipped with the smallest.
// ]

#definition(name: "Guarded Iterative Category")[
    A category $cal(K)$ is *guarded iterative* if every $f: A → B ⟩ A$ has a _unique_ fixpoint $f^†: A → B$ of the map $f;[idm, -]: cal(K)(A, B) → cal(K)(A, B)$, i.e.,
    $
    f^† = f;[idm, f^†]
    $
]
*/

#definition(name: " Iterative Category")[
    A category $cal(K)$ is *iterative* if every $f: A → B + A$ has a _unique_ fixpoint $f^†: A → B$ of the map $f;[idm, -]: cal(K)(A, B) → cal(K)(A, B)$, i.e.,
    $
    f^† = f;[idm, f^†]
    $
]

#definition(name: "Conway Iteration")[
    A *Conway (iteration) operator* on $cal(K)$ associates, to each $f: A → B + A$, a fixpoint $f^†: A → B$ of the map $f;[idm, -]: cal(K)(A, B) → cal(K)(A, B)$ satisfying the following axioms:
    - *Naturality:* for $f: A → B + A$ and $g: B → C$, $(f;g + A)^† = f^†;g$

    In particular, for $f: A -> B + D$, $g: B -> C$ and $h: D -> A$, $(f;g + h)^† = (f;B + h)^†;g$
    - *Dinaturality:* for $g: A → B + C$, $h: C -> B + A$, $(g;[ι_0, h])^† = g;[idm, (h;[ι_0, g])^†]$.
      
      In particular, for $f: A -> B + C$, $g: C -> A$, we have
      $
      (f;B + g)^† = (f;[ι_0, g;ι_1])^† = f;[idm, (g;ι_1;[ι_0, f])^†] = f;[idm, (g;f)^†]
      $
    - *Codiagonal:* for $f: A -> (B + A) + A$, $(f;[idm, ι_1])^† = f^(††)$ 
]
Some useful properties of Conway iteration operators include:
- Given $f: cal(K)(A, B + A)$, 
    - $(f;[ι_0, f])^† = f;[idm, (f; [ι_0, f])^†]$ by dinaturality. 
    
      Hence, if $cal(K)$ is iterative, $(f;[ι_0, f])^† = f^†$ by uniqueness.
    - $ι_0;(f + C;[B + ι_0, ι_1;ι_1])^† = ι_0;([f;B + ι_0, ι_1;ι_1])^†$
- Given $f: cal(K)(A + B, C + (A + B))$, by the codiagonal,
    $
    (f;[ι_0;ι_0, ι_1 + B];C + ι_0 + ι_1)^(††)
    = (f;[ι_0;ι_0, ι_1 + B];C + ι_0 + ι_1;[idm, ι_1])^†
    = f^†
    $

#definition(name: "Uniformity")[
    Let $J: cal(C) -> cal(K)$ be a functor, where $cal(C), cal(K)$ are have the same objects, and $J$ is identity on objects and strictly preserves co-Cartesian structure.

    A Conway operator $(-)^†$ on $cal(K)$ is *uniform* (w.r.t. a functor $J: cal(C) -> cal(K)$) when for $cal(K)$ morphisms $f: X -> Y + X$ and $g: Z -> Y + Z$ and $cal(C)$ morphisms $h: Z → X$, we have that
    $
    g;Y + J h = J h; f ==> g^† = J h; f^†
    $
]

//TODO: state properly, cite properly
#theorem[
    If $cal(K)$ is iterative, $f ↦ f^†$ is a Conway operator and uniform w.r.t. the identity functor $idm_cal(K)$ @coinductive-resumption.
]

#definition(name: "Iterative Monad, Elgot Monad")[
    Let $T$ be a monad. Then
    - We say $T$ is an *iterative monad* if $cal(C)_T$ is iterative
    - We say $T$ is an *Elgot monad* if $cal(C)_T$ has a Conway operator $f ↦ f^†$ which is uniform w.r.t. the obvious functor $cal(C) → cal(C)_T$ //TODO: specify functor?
]

== Traced Monoidal Categories

#definition(name: "Traced Monoidal Category")[
    A traced monoidal category $cal(C)$ is a symmetric monoidal category equipped with a family of functions
    $
    sans("Tr")^X_(A, B): cal(C)(A ⊗ X, B ⊗ X) -> cal(C)(A, B)
    $
    satisfying the following conditions:
    - *Naturality in $A, B$:*
    $
    ∀f ∈ cal(C)(A ⊗ X, B ⊗ X), ∀g ∈ cal(C)(A', A), ∀h ∈ cal(C)(B, B')
        sans("Tr")^X_(A', B')(g ⊗ X;f;h ⊗ X) = g;sans("Tr")^X_(A, B)(f);h
    $
    - *Dinaturality in $X$:*
    $
    ∀ f ∈ cal(C)(A ⊗ X, B ⊗ X'), ∀ g ∈ cal(C)(X', X),
        sans("Tr")^X_(A, B)(f;B ⊗ g) = sans("Tr")^(X')_(A, B)(A ⊗ g;f)
    $
    - *Vanishing:*
    $
    ∀f ∈ cal(C)(A ⊗ munit, B ⊗ munit),
        sans("Tr")^munit_(A, B)(f) = ρ^(-1);f;ρ 
    $
    $
    ∀f ∈ cal(C)(A ⊗ X ⊗ Y, B ⊗ X ⊗ Y),
        sans("Tr")^(X ⊗ Y)_(A, B)(α;f;α) =
        sans("Tr")^X_(A, B)(sans("Tr")^Y_(A ⊗ X, B ⊗ X)(f))
    $
    - *Yanking:*
    $
    sans("Tr")^A_(A, A)(σ_(A, A)) = idm_A
    $
]

//TODO: graphical representation

#theorem[
    Let $cal(C)$ be equipped with a Conway iteration operator $f ↦ f^†$. Then $cal(C)$ is a traced monoidal category under the symmetric monoidal structure induced by the coproduct, with trace
    $
    ∀f ∈ cal(C)(A + X, B + X) 
    sans("Tr")^X_(A, B)(f) = ι_0;(f;B + ι_1)^† = ι_0;f;[idm, (ι_1;f)^†]
    $
]
//TODO: cite Models of Sharing Graphs (Hasegawa)
//TODO: reverse implication: do traces => fixpoints for +, as they do for ×?
//TODO: state more general theorem? state fixpoint over general monoidal product?

// #proof[
//     We prove each required property as follows:
//     - Naturality in $A, B$:
//     Fix $f ∈ cal(C)(A + X, B + X), g ∈ cal(C)(A', A), h ∈ cal(C)(B, B')$. We have that
//     $
//     & sans("Tr")^X_(A', B')(g + X;f;h + X) #h(15em) &
//     \ &= ι_0;(g + X;f;h + ι_1)^† & "by definition"
//     \ &= ι_0;(g + X;f;B + ι_1)^†;h & "by naturality"
//     \ &= ι_0;g + X;f;B + ι_1;[idm, (g + X;f;B + ι_1)^†];h & "by fixpoint"
//     \ &= g;ι_0;f;[idm, ι_1;(g + X;f;B + ι_1)^†];h & "by definition"
//     \ &= g;ι_0;f;[idm, ι_1;(f;B + ι_1)^†];h & "by definition"
//     \ &= g;ι_0;f;B + ι_1[idm, (f;B + ι_1)^†];h & "by definition"
//     \ &= g;ι_0;(f;B + ι_1)^†;h & "by fixpoint"
//     \ &= g;sans("Tr")^X_(A, B)(f);h & "by definition"
//     $
//     - Dinaturality in $X$:
//     Fix $f ∈ cal(C)(A + X, B + X')$, $g ∈ cal(C)(X', X)$
//     $
//     & sans("Tr")^X_(A, B)(f;B + g) #h(20em) &
//     \ &= ι_0;(f;B + g;B + ι_1)^† & "by definition"
//     \ &= ι_0;(f;B + ι_1;B + (A + g)))^† & "by absorption" 
//     \ &= ι_0;f;B + ι_1;[idm, (A + g;f;B + ι_1)^†] & "by dinaturality"
//     \ &= ι_0;A + g;B + ι_1;[idm, (A + g;f;B + ι_1)^†] & "by absorption"
//     \ &= ι_0;(A + g;f;B + ι_1)^† & "by fixpoint"
//     \ &= sans("Tr")^x_(A, B)(A + g; f) & "by definition"
//     $
//     - Vanishing:
//         - Fix $f ∈ cal(C)(A + 0, B + 0)$. Then
//           $
//           & sans("Tr")^0_(A, B)(f) #h(20em) & 
//           \ &= ι_0;(f;B + ι_1)^† & "by definition"
//           \ &= ι_0;(f;B + 0_(A + 0))^† & "by initiality"
//           \ &= ι_0;f;[idm, (0_(A + 0);f)^†] & "by dinaturality"
//           \ &= ι_0;f;[idm, 0_B] & "by initiality" 
//           \ &= (ρ^+)^(-1);f;ρ^+ & "by definition"
//           $
//         - Fix $f ∈ cal(C)(A + X + Y, B + X + Y)$. Then
//           $
//           & sans("Tr")^(X + Y)_(A, B)(α^+;f;α^+) #h(25em) & 
//           \ &= sans("Tr")^(X + Y)_(A, B)([ι_0;ι_0, ι_1 + Y];f;[B + ι_0, ι_1;ι_1]) & "by definition"
//           \ &= ι_0;([ι_0;ι_0, ι_1 + Y];f;[B + ι_0, ι_1;ι_1];B + ι_1)^† & "by definition"
//           \ &= ι_0;([ι_0;ι_0, ι_1 + Y];f;[B + (ι_0;ι_1), ι_1;ι_1;ι_1])^† & "simp."
//           \ &= ι_0;([ι_0;ι_0, ι_1 + Y];f;[B + (ι_0;ι_1), ι_1;ι_1;ι_1];[ι_0;ι_0, ι_1 + Y];B + ι_0 + ι_1) & "by codiagonal"
//           \ &= ι_0;([ι_0;ι_0, ι_1 + Y];f;A + ι_0 + ι_1) &
//           \ &= "TODO..."
//           \ &= ι_0;(ι_0;f;[idm, (ι_1;f)^†];B + ι_1)^† & "by definition"
//           \ &= ι_0;sans("Tr")^Y_(A + X, B + X)(f);[idm, (ι_1;sans("Tr")^Y_(A + X, B + X)(f))^†] & "by definition" 
//           \ &= sans("Tr")^X_(A, B)(sans("Tr")^Y_(A + X, B + X)(f)) 
//           $
//     - Yanking:
//     $
//     & sans("Tr")^A_(A, A)(σ_(A, A)^+) #h(15em) & 
//     \ &= ι_0;(σ_(A, A)^+;A + ι_1)^† & "by definition"
//     \ &= ι_0;σ_(A, A)^+;A + ι_1;[idm, (σ_(A, A);A + ι_1)^†] & "by fixpoint"
//     \ &= ι_1;A + ι_1;[idm, (σ_(A, A);A + ι_1)^†] = ι_1;(σ_(A, A);A + ι_1)^†
//     \ &= i_1;σ_(A, A)^+;A + ι_1;[idm, (σ_(A, A);A + ι_1)^†] & "by fixpoint"
//     \ &= ι_0;A + ι_1;[idm, (σ_(A, A);A + ι_1)^†]
//     \ &= idm_A
//     $
// ]

/*
TODO:
- pointer to premonoidal trace (NOT USED HERE!)
- guarded trace?
*/

== Poset Enriched Categories

#definition(name: "Poset-Enriched Category")[
    A *poset-enriched category* $cal(C)$ is a category such that each hom-set $cal(C)(A, B)$ is equipped with a partial order $->_(cal(C))$ which is compatible with composition; that is, for $f, f' ∈ cal(C)(A, B)$ and $g, g' ∈ cal(C)(B, C)$, if $f ->_(cal(C)) f'$ and $g ->_(cal(C)) g'$, then $f;g ->_(cal(C)) f';g'$. 

    If $cal(C)(A, B)$ has a bottom element, we will often write it as $⊥_(A, B)$, or simply $⊥$. More rarely, we may write the top element of $cal(C)(A, B)$ as $⊤_(A, B)$ or $⊤$.
    
    We will usually omit the subscript and simply write $f -> g$ (pronounced "$f$ *is refined by* $g$"); similarly, we will write $f <- g$ (pronounced "$f$ *refines* $g$") to mean $g -> f$.

    A *poset-enriched functor* $F: cal(C) -> cal(D)$ is a functor between the underlying categories such that for all $f ->_(cal(C)) f'$, $F f ->_(cal(D)) F f'$.
    
    A *poset enriched monad* $T$ is a monad whose underlying functor is poset-enriched.
]
For example:
- Every category $cal(C)$ can be taken as a poset-enriched category with the discrete order on hom-sets given by $f ->_(cal(C)) g <=> f = g$
- If $cal(C)$ is poset-enriched and $T$ is a poset-enriched monad, then the Kliesli category $cal(C)_T$ is also poset-enriched with $(->_(cal(C)_T)) = (->_(cal(C)))$, since, for $f ->_(cal(C)) f'$ and $g ->_(cal(C)) g'$, $f;T g;μ ->_(cal(C)) f';T g';μ$. In particular, we have that $f^* = T f;μ -> T f';μ = f'^*$
- The category $Pfn$ of partial functions is poset-enriched with the subset ordering, i.e., taking
  $
  f ->_(cal(C)) g <==> f ⊆ g <==> ∀x ∈ A, f(x) ⊆ g(x)
  $
- The categories $Rel$ of relations and $Rel^+$ of nonempty relations are poset-enriched with the superset ordering on relations, i.e., taking
  $
  f ->_(cal(C)) g <==> f ⊇ g <==> ∀x ∈ A, f(x) ⊇ g(x)
  $
Note that it is possible for the same underlying category to be poset-enriched by different families of relations; as a trivial example, if $->_(cal(C))$ endows $cal(C)$ with the structure of a poset-enriched category, then so does $<-_(cal(C))$. In particular, $Pfn$ is also enriched by the superset ordering, but this is not very intuitive, as we consider a function to be "more defined", i.e. a _refinement_, when it has _more_ values defined, not less; this allows us to define a _bottom element_ $⊥ = {}$ which is refined by everything. On the other hand, for $Rel^+$, the superset ordering is more natural than the subset ordering, since we consider a function $f$ to be a refinement of $g$ if it has _less_ allowable outputs; the bottom element $⊥$ is now the _full_ relation, corresponding to "all possible outputs." The situation for $Rel$ is more complicated, since now ${}$ is a top element, being a refinement for everything (rather than a bottom element, as in $Pfn$).

// Some useful properties of bottom elements include:
// $
// ⊥_(A, B) -> ⊥_(A, B);⊥_(B, B) -> ⊥_(A, B);idm = ⊥_(A, B) ==> ⊥_(A, B) = ⊥_(A, B);⊥_(B, B)
// $
// $
// ⊥_(A, B) -> ⊥_(A, A);⊥_(A, B) -> idm;⊥_(A, B) = ⊥_(A, B) ==> ⊥_(A, B) = ⊥_(A, A);⊥_(A, B)
// $

//TODO: Products and coproducts

#definition(name: "Poset-Enriched Premonoidal Category")[
    A *poset-enriched (symmetric) (pre)monoidal category* $cal(C)$ is a poset-enriched category such that the underlying category is equipped with a (symmetric) (pre)monoidal structure where $⊗$ is a poset-enriched functor in both arguments; that is, for $f -> f'$, we have that $A ⊗ f -> A ⊗ f'$ and $f ⊗ A -> f' ⊗ A$. 
    
    In particular, this implies that for $f -> f'$ and $g -> g'$, we have $f ⋉ g -> f' ⋉ g'$ and $f ⋊ g -> f' ⋊ g'$ (and hence, in the central case, $f ⊗ g -> f' ⊗ g'$).

    A poset-enriched category whose underlying category is (co)cartesian where the (co)cartesian product induces a poset-enriched symmetric monoidal structure is called a *poset-enriched (co)cartesian category*.
]


#definition(name: "Poset-Enriched Effectful Category")[
    A *poset-enriched (symmetric) effectful category* $F: cal(V) -> cal(C)$ is a poset-enriched premonoidal functor, where $cal(V)$ is a poset-enriched (symmetric) monoidal category and $cal(C)$ is a poset-enriched (symmetric) premonoidal category.
]

/*
NOTE: removing guardedness for now

// #definition(name: "Poset-Enriched Guarded Category")[
//     A poset-enriched category $cal(C)$ is said to be *guarded* if its guardedness relation is compatible with $->_(cal(C))$, i.e., for all $f -> f': A -> B + C$, if $f$ is guarded, then so is $f'$. A poset-enriched category $cal(C)$ is said to be *coguarded* if its guardedness relation is compatible with $<-_(cal(C))$, i.e., for all $f <- f': A -> B + C$, if $f$ is guarded, then so is $f'$.

//     A poset-enriched category is *totally (co)guarded* if all morphisms $A -> B + C$ are considered guarded. A poset-enriched category is *vacuously (co)guarded* if a morphism $f: A -> B + C$ is guarded if and only if there exists a morphism $g: A -> B$ such that $g;sans("inl") -> f$ or $g;sans("inl") <- f$ resp.

//     A (not necessarily (co)guarded) poset-enriched category is said to have a (guarded) *Conway (iteration) operator* if the underlying category has a Conway operator compatible with $->_(cal(C))$, i.e., for all $f -> f'$ where both $f, f'$ are guarded, $f^† -> f'^†$. If the underlying category is iterative, and it is a poset-enriched guarded category, then it is called a *poset-enriched guarded iterative category*.
// ]
*/

#definition(name: "Poset-Enriched Iterative Category")[
    A poset-enriched category is said to have a *Conway (iteration) operator* if the underlying category has a Conway operator compatible with $->_(cal(C))$, i.e., for all $f -> f'$, $f^† -> f'^†$. If the underlying category is iterative, then it is called a *poset-enriched iterative category*.
]

#definition(name: "Poset-Enriched Traced Category")[
    A poset-enriched symmetric monoidal category is said to be *traced* if the underlying category is traced and the trace is compatible with $->_(cal(C))$, i.e., for all $f -> f'$,
    $sans("Tr")(f) -> sans("Tr")(f')$
]

/*
TODO: check this
Note that if a poset-enriched cocartesian category is traced if and only if it has a Conway (iteration) operator.
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
```isotope
let 'fact(p: (i64, i64)) => {
    let (i, a) = p;
    if i >= n {
        br a
    } else {
        br 'fact (i + 1, i * a)
    }
}; 
br 'fact (0, 0)
```
Note that the program as a whole lies in the syntactic category of _blocks_.

Terms and targets being interleaved makes it possible to encapsulate control flow, which facilitates reasoning about rewriting and control-flow as well as program transformations such as inlining. For example, in a function to compute the absolute value and branch on it
```isotope
let s = sgn x;
let abs = s * x;
if abs > 5 { br 4 } else { br 3 }
```
we could inline a plausible definition of `sgn` as follows:
```isotope
let s = { 
    if x < 0 { br -1 } else { 
        if x == 0 { br 0 } else { br 1 } 
    } 
};
let abs = s * x;
if abs > 5 { br 4 } else { br 3 }
```
This contrasts with the standard approach of encoding the control-flow graph without allowing nesting, which would require us to rewrite everything as a single block as follows
```isotope
let 'c(s: i64) => {
    let abs = s * x;
    if abs > 5 { br 4 } else { br 3 }
};
if x < 0 { br 'c -1 } else { 
    if x == 0 { br 'c 0 } else { br 'c 1 }
}
```
As can be seen, this considerably complicates the definition of inlining, and, later, when we consider the graphical representation of `isotope` programs, causes expressibility issues for re-ordering.

The grammar also allows for multiple, mutually recursive label definitions in a single `let`-binding, as in the following program, which prints out `x`'s binary representation:
```isotope
print "0b";
let 
    'zero(x: i64) => {
        print "0";
        br 'next x
    }
    'one(x: i64) => { 
        print "1";
        br 'next x
    }
    'next(x: i64) => { 
        if x % 2 == 0 {
            br 'zero (x >> 1)
        } else {
            br 'one (x >> 1)
        }
    };
br 'next x
```
Here, bare function calls "`print s`" are syntax sugar for unused bindings `let \_ = print s;` to allow us to write side-effectful expressions more easily. One gotcha is that label bindings cannot be used in a block nested in an expression in another block; for example,
```isotope
let 'label(x: i64) => {
    print x;
    br (x + 5)
};
br {
    if b { br 'label 9 } else { br 7 }
}
```
is _invalid_ code, since the label `'label` is used in the nested expression given as an argument to the `br`-statement, while
```isotope
let 'label(x: i64) => {
    print x;
    br (x + 5)
};
if b { br 'label 9 } else { br 7 }
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
```isotope
if x == 0 {
    let e = 7; br e
} else {
    br 8
}
```
is encountered where an term is expected, it may be interpreted as the term
```isotope
{
    if x == 0 {
        let e = 7; br e
    } else {
        br 8
    }
}
```
We similarly allow omitting the `br` keyword in blocks; for example,
```isotope
{ let x = 5;  x }
```
desugars to
```isotope
{ br (let x = 5; x) }
```
While this behaviour might be confusing, since the user might expect
```isotope
{ let x = 5; br x }
```
we will later require all such desugarings to be semantically equivalent, making the distinction moot.
//TODO: when?

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
let default => { big_calculation };
if is_some x {
    let x = get_some x;
    if x == 0 {
        br 5
    } else {
        if x == 3 {
            // Note nested control flow is incorporated into the same block
            // This is to allow desugaring more complex constructions, such 
            // as breaks and loops.
            if y == 7 {
                br 7
            } else {
                br 'default
            }
        } else {
            br 'default
        }
    }
} else {
    br 8
}
```
Similarly to `if`-statements, `match` statements may be interpreted as expressions as well as blocks. Other Rust-like matching constructs, like `let`-`else` statements or pattern destructures, are also supported.
Similarly, we support Rust-style control-flow constructs such as `for`, `while`, and `loop`; for example,
```isotope
for x in collection {
    side_effect x;
}
```
desugars to
```isotope
let body(c: _) => {
    let (x, c) = next c;
    if is_some x {
        let x = get_some x;
        let _ = side_effect x;
        br 'body c
    } else {
        br ()
    }
};
br 'body collection
```
For ease of reading SSA-like programs, we also provide postfix `where`-syntax, where we simply desugar
```isotope
t where
    'a(x: A) => { ... }
    'b(y: B) => { ... }
    ...
```
to
```isotope
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
    - A subset $cal(I)_∅(A, B) subset.eq cal(I)$ of *instructions*.
    - A subset $cal(I)_lcen(A, B) subset.eq cal(I)_0(A, B)$ of *pure instructions* 
    /*such that, if $cal(I)_I(A, B)$ is nonempty, then*/ /*$rel(B) => rel(A)$ and $aff(B) => aff(A)$*/ /*$rel(B) or aff(B) => rel(A) and aff(A)$*/
Throughout this section, we assume variable names are _unique_, performing $α$-conversion as necessary to maintain this invariant

/*
TODO: grammar for typing contexts, label contexts
*/

=== Judgements

We begin by giving a grammar for *contexts* and *label contexts* as follows:
#let isotope-ctx-grammar = (
    (
        name: "Context",
        symbol: ($Γ$, $Δ$, $Ξ$, $Θ$, $Φ$),
        productions: (
            ($cnil$, $Γ, thyp(x, A, q)$),
        )
    ),
    (
        name: "Label Context",
        symbol: ($sans(J)$, $sans(K)$, $sans(L)$),
        productions: ((
            $bcnil$,
            $sans(L), lhyp(Γ, p, lbl(ℓ), A)$
        ),),
    ),
);
#grammar(isotope-ctx-grammar)
where $q ⊆ {lrel, laff}$ is a *quantity* and $p ⊆ {lcen}$ is a *purity*.
Where clear from context, we will coerce $lrel, laff$, and $lcen$ to ${lrel}, {laff}$, and ${lcen}$ respectively.

We will write 
- $thyp(x, A)$ as shorthand for $thyp(x, A, ∞)$
- $istm(Γ, #{none}, a, A)$ as shorthand for $istm(Γ, ∅, a, A)$
- $isblk(Γ, sans(L), #{none}, t, B)$ as shorthand for $isblk(Γ, sans(L), #{none}, t, B)$
- $lhyp(Γ, #{none}, lbl(ℓ), A)$ as shorthand for $lhyp(Γ, ∅, lbl(ℓ), A)$

We may now introduce the following typing judgements:
#align(center)[#table(
    columns: 2,
    stroke: none,
    column-gutter: 2em,
    align: left,
    [*Syntax*],
    [*Meaning*],
    $istm(Γ, p, a, A)$,
    [$a$ is a term of type $A$ in context $Γ$ with purity $p$],
    $isblk(Γ, sans(L), p, t, B)$,
    [$t$ is a block of type $B$ in control context $Γ;sans(L)$with purity $p$],
    $splitctx(Γ, Δ, Ξ)$,
    [$Γ$ splits into contexts $Δ$, $Ξ$],
    $dropctx(Γ, Δ)$,
    [$Γ$ is a weakening of $Δ$],
    $joinctx(sans(K), sans(L))$,
    [$sans(K)$ is a subset of label-set $sans(L)$],
    $rel(A)$, [$A$ is relevant (can be split)],
    $aff(A)$, [$A$ is affine (can be dropped)],
    $islin(q, A)$, [$A$ has linearity $q$]
)]
Given a quantity $q$, we write $aff(A, q), rel(A, q)$ as shorthand for $laff ∈ q and rel(A)$ and $lrel ∈ q and aff(A)$ respectively.

=== Structural rules

/*
TODO: text for typing rules
*/

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
        $q' ⊆ q$,
        $#splitctx($Γ, thyp(x, A, q)$, $Δ, thyp(x, A, q')$, $Ξ$)$),
    "ctx-right": prft(name: "ctx-right", 
        $splitctx(Γ, Δ, Ξ)$, 
        $q' ⊆ q$,
        $#splitctx($Γ, thyp(x, A, q)$, $Δ$, $Ξ, thyp(x, A, q')$)$),
    "ctx-rel": prft(name: "ctx-rel", 
        $splitctx(Γ, Δ, Ξ)$,
        $rel(A, q)$, 
        $q' ⊆ q$,
        splitctx($Γ, thyp(x, A, q)$, $Δ, thyp(x, A, q')$, $Ξ, thyp(x, A, q')$)),
    "ctx-aff": prft(name: "ctx-aff", 
        $splitctx(Γ, Δ, Ξ)$,
        $aff(A, q)$, 
        splitctx($Γ, thyp(x, A, q)$, $Δ$, $Ξ$)),
    "wk-def": prft(name: "wk-def", 
        $splitctx(Γ, Δ, cnil)$,
        $dropctx(Γ, Δ)$),
    "label-nil": prft(name: "label-nil", $joinctx(bcnil, bcnil)$),
    "label-join": prft(name: "label-join", 
        $joinctx(sans(K), sans(L))$,
        joinctx($sans(K)$, $sans(L), lhyp(Γ, p, lbl(ell), A)$)),
    "label-ext": prft(name: "label-ext", 
        $joinctx(sans(K), sans(L))$,
        $dropctx(Γ, Δ)$,
        $p' ⊆ p$,
        joinctx($sans(K), lhyp(Γ, p, lbl(ell), A)$, $sans(L), lhyp(Δ, p', lbl(ell), A)$)),
    "lin-nil": prft(name: "lin-nil",
        $islin(∅, A)$
    ),
    "lin-aff": prft(name: "lin-aff",
        $aff(A)$, $islin({laff}, A)$
    ),
    "lin-rel": prft(name: "lin-rel",
        $rel(A)$, $islin({lrel}, A)$
    ),
    "lin-inf": prft(name: "lin-inf",
        $aff(A)$, $rel(A)$, $islin(∞, A)$
    ),
    "var": prft(name: "var", 
        dropctx($Γ$, $thyp(x, A, ∅)$), $istm(Γ, p, x, A)$),
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
        $istm(Ξ, p, a, A)$,
        istm($Δ, thyp(x, A)$, $p$, $e$, $B$),
        istm($Γ$, $p$, $llet x = a; e$, $B$)
    ),
    "blk": prft(name: "blk",
        $isblk(Γ, bcnil, p, t, B)$,
        $istm(Γ, p, {t}, B)$
    ),
    "let2": prft(name: "let2",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Ξ, p, e, A ⊗ B)$,
        istm($Δ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$),
        istm($Γ$, $p$, $llet (x, y) = e; e'$, $C$)
    ),
    "br": prft(name: "br", 
        $istm(Γ, p, a, A)$,
        $isblk(Γ, sans(L), p, br(a), A)$,
    ),
    "jmp": prft(name: "jmp",
        $splitctx(Γ, Δ, Ξ)$,
        $istm(Ξ, p, a, A)$,
        $joinctx(lhyp(Δ, p, lbl(ℓ), A), sans(L))$,
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
        $istm(Ξ, p, a, A)$,
        isblk($Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$),
        isblk($Γ$, $sans(L)$, $p$, $llet x = a; t$, $B$)
    ),
    "let2-blk": prft(name: "let2-blk",
        splitctx($Γ$, $Δ$, $Ξ$),
        $istm(Ξ, p, e, A ⊗ B)$,
        isblk($Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$),
        isblk($Γ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)
    ),
    "tr": prft(name: "tr",
        $forall i, 
            #[
                #isblk(
                $Delta_i, thyp(x_i, A_i)$, 
                $sans(L), [lhyp(Delta_j, ∅, lbl(ell)_j, A_j)]_j$,
                $p_i$,
                $t_i$,
                $B$
            )]$,
        isblk(
            $Γ$, 
            $sans(L), [lhyp(Delta_j, p_j, lbl(ell)_j, A_j)]_j$,
            $p$,
            $s$,
            $B$),
        isblk(
            $Γ$,
            $sans(L)$,
            $p$,
            $llet [lbl(ell)_j(x_j: A_j) => {t_j}]_j; s$,
            $B$
        )
    )
)

#let rstyle(rule) = [(#text(rule, maroon))];
#let rname(rule) = [(#text(rule, maroon))];

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
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.ctx-rel),
        dprf(typing-rules.ctx-aff),
        dprf(typing-rules.wk-def)
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.label-nil),
        dprf(typing-rules.label-ext),
        dprf(typing-rules.label-join),
    ),
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.lin-nil),
        dprf(typing-rules.lin-aff),
        dprf(typing-rules.lin-rel),
        dprf(typing-rules.lin-inf),
    ),
))

//TODO: basic properties of structural rules, e.g. unique derivations

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

We begin by introducing a few auxiliary judgments regarding contexts:
#align(center)[#table(
    columns: 2,
    stroke: none,
    column-gutter: 2em,
    align: left,
    [*Syntax*],
    [*Meaning*],
    // $subctx(Γ, Δ)$,
    // [$Γ$ is a subcontext of $Δ$],
    $islin(q, Γ)$,
    [$Γ$ has linearity $q$ (i.e. has components with linearity $q$)],
    $aff(Γ)$,
    [$Γ$ is affine (i.e. has affine components)],
    $rel(Γ)$,
    [$Γ$ is relevant (i.e. has relevant components)],
    $thyp(x, A, q) ∈ Γ$,
    [$thyp(x, A, q)$ is contained in $Γ$],
    $x ∈ Γ$,
    [$x$ is contained in $Γ$]
)]
These have the following derivations:
#row-den(
    $prf(subctx(cnil, cnil), name: "sub-nil")$,
    $prf(
        subctx(Δ, Γ), 
        q ⊆ q',
        #subctx($Δ, thyp(x, A, q)$, $Γ, thyp(x, A, q')$
    ), name: "sub-add")$,
    $prf(subctx(Δ, Γ), #subctx($Δ$, $Γ, thyp(x, A, q)$), name: "sub-ext")$
)
#row-den(
    $prf(islin(q, cnil), name: "lin-nil")$,
    prf($islin(q, A)$, $islin(q, Γ)$, $q ⊆ q'$, rel($Γ, thyp(x, A, q')$), name: "lin-add"),
    prf($islin(laff, Γ)$, $aff(Γ)$, name: "aff-def"),
    prf($islin(lrel, Γ)$, $rel(Γ)$, name: "rel-def"),
)
#row-den(
    $x ∈ Γ <==> ∃A, q, thyp(x, A, q) ∈ Γ$,
    $thyp(x, A, q) ∈ Γ <==> subctx(thyp(x, A, q), Γ)$,
)
We may now define the following operations on contexts:
$
cnil^q = cnil, qq qq (Γ, thyp(x, A, q'))^q = Γ^q, thyp(x, A, q' ∩ q)
$
We now state some basic properties and definitions:
- There can be at most one derivation of $splitctx(Γ, Δ, Ξ)$ and hence of $dropctx(Γ, Δ)$
- *Splitting commutes:* $splitctx(Γ, Δ, Ξ) <==> splitctx(Γ, Ξ, Δ)$
- $dropctx(Γ, Δ)$ is a partial order on contexts
- If $splitctx(Γ, Δ, Ξ)$ and $dropctx(Ξ, Θ)$, then $splitctx(Γ, Δ, Θ)$; likewise, if $dropctx(Δ, Θ)$, then $splitctx(Γ, Θ, Ξ)$
- We say a context $splitctx(Γ, Δ, Ξ)$ is *minimal* if $splitctx(Γ^∅, Δ^∅, Ξ^∅)$, i.e. $∀x ∈ Γ, x ∈ Δ or x ∈ Ξ$.
- If $splitctx(Γ, Δ, Ξ)$, $splitctx(Ξ, Θ, Φ)$
    - If $splitctx(K, Δ, Θ)$ and $K$ is minimal, then $splitctx(Γ, K, Φ)$
    - If $splitctx(K, Δ, Θ)$, $splitctx(K', Δ, Φ)$, $K, K'$ are minimal, and $rel(Δ)$, then $splitctx(Γ, K, K')$
    - If $aff(Δ)$, then $splitctx(Γ, Θ, Φ)$
- $subctx(Γ, Δ)$ is a partial order on contexts
- $∃Ξ, splitctx(Γ, Δ, Ξ) <==> subctx(Δ, Γ)$; in particular, $dropctx(Γ, Δ) => subctx(Δ, Γ)$
- $splitctx(Γ, Δ, Ξ) ==> subctx(Δ, Γ) and subctx(Ξ, Γ)$
- If $dropctx(Γ, Δ)$, then $aff(Γ) => aff(Δ)$. If $dropctx(Γ, Δ)$, then $aff(Γ) <==> aff(Δ)$.
- If $dropctx(Γ, Δ)$, then $rel(Γ) => rel(Δ)$
- $aff(Γ) <==> dropctx(Γ, cnil)$ and $rel(Γ) <==> splitctx(Γ, Γ, Γ)$
- If $aff(Γ)$ then $dropctx(Γ, Δ) <==> subctx(Δ, Γ)$
- If $subctx(Δ, Γ)$ and $x: A ∈ Γ$, then $x ∈ Δ <==> x: A ∈ Δ$
Given a proposition $P$, we define the *comprehension* of a context as follows:
$
    [thyp(x, A, q) ∈ cnil | P] &= cnil \
    [thyp(x, A, q) ∈ Γ, thyp(y, B, q') | P] &= [thyp(x, A, q) ∈ Γ | P], thyp(y, B, q') & "where" P(thyp(y, B, q')) \
    [x: A ∈ Γ, thyp(y, B, q') | P] &= [thyp(y, B, q') ∈ Γ | P] & "otherwise"
$
This has the following basic properties:
- $subctx([thyp(x, A, q) ∈ Γ | P], Γ)$
- $[thyp(x, A, q) ∈ Γ | thyp(x, A, q) ∈ Ξ] = [thyp(x, A, q) ∈ Ξ | thyp(x, A, q) ∈ Γ]$
- If $P ==> Q$, then $subctx([thyp(x, A, q) ∈ Γ | P], [thyp(x, A, q) ∈ Γ | Q])$
- If $subctx(Γ, Δ)$, then $subctx([thyp(x, A, q) ∈ Γ | P], [thyp(x, A, q) ∈ Δ | P])$
- If $subctx(Θ_Δ, Δ)$, $subctx(Θ_Ξ, Ξ)$, and $splitctx(Γ, Δ, Ξ)$, then, for $Θ = [thyp(x, A, q) ∈ Γ | x ∈ Θ_Δ or x ∈ Θ_Ξ]$, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, with $Θ$ minimal.

We may now state some basic theorems and definitions:
#let downgrade-stmt = lemma(name: "Downgrade")[
    Given purities $p' ⊆ p$,
    - If $istm(Γ, p, a, A)$, then $istm(Γ, q, a, A)$.
    - If $isblk(Γ, sans(L), p, t, B)$, then $isblk(Γ, sans(L), p', t, B)$.
]
#downgrade-stmt
#proof[
    See @syntactic-properties[Appendix]
]

#let substitution-rules = (
    "subst-nil": prft(
        $dropctx(Θ_cnil, cnil)$, $issub(cnil, Θ_cnil, cnil, p)$, 
        name: "subst-nil"),
    "subst-cons": prft(
        $issub(γ, Θ_Γ, Γ, p)$, 
        $istm(Θ_x, p, a, A)$,
        $islin(q, Θ_x)$,
        $splitctx(Θ, Θ_x, Θ_Γ)$,
        issub($[x ↦ a]γ$, $Θ$, $Γ, thyp(x, A, q)$),
        name: "subst-cons")
)

#definition(name: "Substitution")[
    We define a *substitution* $issub(γ, Θ, Γ, p)$ with purity $p$ from $Θ$ to $Γ$, via the following rules
    #row-den(
    dprf(substitution-rules.subst-nil),
    dprf(substitution-rules.subst-cons)
    )
    If the purity $p$ is not specified, we assume $p = {lcen}$.
    We define the capture-avoiding substitution $[γ]a$, $[γ]t$ of a term or block as usual. 
    We define the substitution of a _context_ $Ξ$ by a well-typed substitution to be given by the list comprehension
    $
    [γ]Ξ = [y: B ∈ Θ | ∃x ∈ Ξ, y ∈ Θ_x]
    $
    This may be alternatively defined recursively as
    $
    [γ]cnil &= cnil \
    [γ](Ξ, thyp(x, A, q)) = [thyp(y, B, q') ∈ Θ | thyp(y, B, q') ∈ Θ_x or thyp(y, B, q') ∈ [γ]Ξ]
    $
    We will often write $[γ]Ξ$ as $Θ_Ξ$ where the substitution $γ$ is clear from context.
    We may then define the substitution of a _label context_ as follows:
    $
    [γ]bcnil = bcnil, qq  [γ](lhyp(Ξ, p, lbl(ℓ), A), sans(L)) = (lhyp([γ]Ξ, p, lbl(ℓ), A)), sans(L)
    $
    We define the *lifting* of a substitution to be given by #issub($slft(γ) = [x ↦ x]γ$, $(Θ, thyp(x, A, q))$, $(Γ, thyp(x, A, q))$).
    We say a substitution $γ'$ is a *submap of $γ$*, written $submap(γ', γ)$, if:
    - For all terms and blocks $a$, if $[γ']a$ is defined, then $[γ]a = [γ']a$
    - For all contexts $Ξ$, if $[γ']Ξ$ is defined, then $[γ]Ξ$ = $[γ']Ξ$
    //TODO: proper terminology for this
]
For example, given the substitution and context
$
#[#issub($γ = [x ↦ 2, y ↦ a, z ↦ b + c]$, $(x: ℕ, y: ℕ, z: ℕ)$, $(a: ℕ, b: ℕ, c: ℕ)$)], qq Ξ = x: ℕ, z: ℕ
$
we have $[γ]Ξ = b: ℕ, c ∈ ℕ$.

We note the following basic properties about substitutions:
- For all substitutions $γ$, $submap(γ, slft(γ))$
- The relation $submap(γ', γ)$ is a partial order on substitutions
- If $submap(γ', γ)$, then for all label-contexts $sans(L)$, if $[γ']sans(L)$ is defined, then $[γ]sans(L) = [γ']sans(L)$
- There is only one substitution $issub(cnil, Θ, cnil)$; in this case context-substitution is given by $[cnil]Ξ = Θ$.
- For all $x$, $subctx(Θ_x, Θ)$
- For all $Ξ$, $subctx(Θ_Ξ, Θ)$, $subctx(Ξ, Ξ') ==> subctx(Θ_Ξ, Θ_(Ξ'))$, and $x: A ∈ Ξ ==> subctx(Θ_x, Θ_Ξ)$
- For all #issub($γ$, $Θ$, $x: A, Γ$) with #subctx($Ξ$, $Γ$), we have $splitctx(Θ_(x: A, Ξ), Θ_x, Θ_Ξ)$ with $Θ_(x: A, Ξ)$ minimal (since $subctx(Θ_x, Θ_x)$, $subctx(Θ_Ξ, Θ_Γ)$, and $splitctx(Θ, Θ_x, Θ_Γ)$)
- By downgrade, if $p' ⊆ p$ and $issub(γ, Θ, Γ, p)$, then $issub(γ, Θ, Γ, p')$

//TODO: segue?

We may now state the following basic lemmas w.r.t substitution

//TODO: better name
#lemma(name: "Split Substitution")[
    If $splitctx(Γ, Δ, Ξ)$ and $issub(γ, Θ, Γ, p)$, then $splitctx(Θ, Θ_Δ, Θ_Ξ)$, and there exist substitutions $γ_Δ$, $γ_Ξ$ such that 
    - $issub(γ_Δ, Θ_Δ, Δ, p)$, $issub(γ_Ξ, Θ_Ξ, Ξ, p)$. 
    - $submap(γ_Δ, γ)$, $submap(γ_Ξ, γ)$
    //TODO: these substitutions should be unique?
]
#proof[
    We proceed by induction on derivations of $splitctx(Γ, Δ, Ξ)$:
    - #rname("ctx-nil"): take $γ_cnil = cnil$; the desired properties hold trivially.
    - #rname("ctx-left"): let $γ_(Δ, thyp(x, A, q)) = [x ↦ [γ]x]γ_Δ$, where $γ_Δ, γ_Ξ$ are given by induction. Then $γ_(Δ, thyp(x, A, q)), γ_Ξ$ have the desired properties, since:
        - $splitctx(Θ, Θ_x, Θ_Γ)$ by assumption
        - $splitctx(Θ_Γ, Θ_Δ, Θ_Ξ)$ and $issub(γ_Ξ, Θ_Ξ, Ξ, p)$ by induction; therefore $splitctx(Θ_(Δ, thyp(x, A, q)), Θ_x, Θ_Δ)$ is minimal; hence we have $splitctx(Θ, Θ_(Δ, thyp(x, A, q)), Θ_Ξ)$.
        - Hence, we may derive
        #prf(
            name: "subst-add", 
            $issub(γ_Δ, Θ_Δ, Δ) " by ind."$,
            $istm(Θ_x, p, γ[x], A) " since " issub(γ, Θ, Γ, p)$,
            $splitctx(Θ_(Δ, thyp(x, A, q)), Θ_x, Θ_Δ)$,
            issub($[x ↦ [γ]x]γ_Δ$, $Θ_(Δ, thyp(x, A, q))$, $(Δ, thyp(x, A, q))$, $p$)
        )
        as desired
    - #rname("ctx-right"): let $γ_(Ξ, thyp(x, A, q)) = [x ↦ [γ]x]γ_Ξ$, where $γ_Δ, γ_Ξ$ are given by induction. Then $γ_Δ, γ_(Ξ, thyp(x, A, q))$ have the desired properties, since:
        - $splitctx(Θ, Θ_x, Θ_Γ)$ by assumption
        - $splitctx(Θ_Γ, Θ_Δ, Θ_Ξ)$ and $issub(γ_Δ, Θ_Δ, Δ, p)$ by induction; therefore $splitctx(Θ_(Ξ, thyp(x, A, q)), Θ_x, Θ_Ξ)$ is minimal; hence we have $splitctx(Θ, Θ_Δ, Θ_(Ξ, thyp(x, A, q)))$
        - Hence, we may derive
        #prf(
            name: "subst-add", 
            $issub(γ_Ξ, Θ_Ξ, Ξ) " by ind."$,
            $istm(Θ_x, p, γ[x], A) " since " issub(γ, Θ, Γ, p)$,
            $splitctx(Θ_(Ξ, thyp(x, A, q)), Θ_x, Θ_Ξ)$,
            issub($[x ↦ [γ]x]γ_Ξ$, $Θ_(Ξ, thyp(x, A, q))$, $(Ξ, thyp(x, A, q))$, $p$)
        )
        as desired
    - #rname("ctx-rel"): let $γ_(Δ, thyp(x, A, q)) = [x ↦ [γ]x]γ_Δ$, $γ_(x: A, Ξ) = [x ↦ [γ]x]γ_Ξ$, where $γ_Δ, γ_Ξ$ are given by induction. Then $γ_(Δ, thyp(x, A, q)), γ_(Ξ, thyp(x, A, q))$ have the desired properties, since:
        - $splitctx(Θ, Θ_x, Θ_Γ)$ by assumption
        - $splitctx(Θ_Γ, Θ_Δ, Θ_Ξ)$ by induction
        - Since $lrel ∈ q$ and $issub(γ, Θ, (Γ, thyp(x, A, q)), p)$, $rel(Θ_x)$, we have $splitctx(Θ, Θ_(Δ, thyp(x, A, q)), Θ_(Ξ, thyp(x, A, q)))$
        - Therefore $splitctx(Θ_(Δ, thyp(x, A, q)), Θ_x, Θ_Δ)$ and $splitctx(Θ_(Ξ, thyp(x, A, q)), Θ_x, Θ_Ξ)$
        - Hence, we may derive
        #prf(
            name: "subst-add", 
            $issub(γ_Δ, Θ_Δ, Δ) " by ind."$,
            $istm(Θ_x, p, γ[x], A) " since " issub(γ, Θ, Γ, p)$,
            $splitctx(Θ_(Δ, thyp(x, A, q)), Θ_x, Θ_Δ)$,
            issub($[x ↦ [γ]x]γ_Δ$, $Θ_(Δ, thyp(x, A, q))$, $(Δ, thyp(x, A, q))$, $p$)
        )
        #prf(
            name: "subst-add", 
            $issub(γ_Ξ, Θ_Ξ, Ξ) " by ind."$,
            $istm(Θ_x, p, γ[x], A) " since " issub(γ, Θ, Γ, p)$,
            $splitctx(Θ_(Ξ, thyp(x, A, q)), Θ_x, Θ_Ξ)$,
            issub($[x ↦ [γ]x]γ_Ξ$, $Θ_(Ξ, thyp(x, A, q))$, $(Ξ, thyp(x, A, q))$, $p$)
        )
    - #rname("ctx-aff"): Let $γ_Δ, γ_Ξ$ be given by induction. Then $γ_Δ, γ_Ξ$ have the desired properties, since:
        - $splitctx(Θ, Θ_x, Θ_Γ)$ by assumption
        - $splitctx(Θ_Γ, Θ_Δ, Θ_Ξ)$ by induction
        - Since $laff ∈  q$ and $issub(γ, Θ, (Γ, thyp(x, A, q)), p)$, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$
]
We may immediately deduce the following corollaries:
//TODO: rename to corollary?
//TODO: better name
#lemma(name: "Weakening Substitution")[
    If $dropctx(Γ, Δ)$ and $issub(γ, Θ, Γ, p)$, then $dropctx(Γ, Θ_Δ)$ there exists a substitution $γ_Δ$ such that $issub(γ_Δ, Θ_Δ, Δ, p)$, and $submap(γ_Δ, γ)$.
    //TODO: this substitution should be unique?
]
//TODO: better name
#lemma(name: "Join Substitution")[
    If $joinctx(sans(K), sans(L))$ and $issub(γ, Θ, Γ, p)$, then $joinctx([γ]sans(K), [γ]sans(L))$
]
//TODO: proofs?

//TODO: text

#let syntactic-weakening-stmt = lemma(name: "Weakening")[
    Given $dropctx(Γ, Δ)$
    - If $istm(Δ, p, a, A)$, then $istm(Γ, p, a, A)$
    - If $isblk(Δ, sans(L), p, t, B)$ then $isblk(Γ, sans(L), p, t, B)$.
];
#syntactic-weakening-stmt
#proof[
    See @syntactic-properties[Appendix]
]

#let syntactic-join-weakening-stmt = lemma(name: "Join Weakening")[
    If $joinctx(sans(K), sans(L))$ and $isblk(Γ, sans(K), p, t, B)$, then $isblk(Γ, sans(L), p, t, B)$
];
#syntactic-join-weakening-stmt

#let syntactic-substitution-stmt = lemma(name: "Syntactic Substitution")[
    Given a substitution $issub(γ, Θ, Γ, p)$,
    - If $istm(Γ, p, a, A)$ , then $istm(Θ, p, [γ]a, A)$
    - If $isblk(Γ, sans(L), p, t, B)$, then $isblk(Θ, [γ]sans(L), p, [γ]t, B)$
];
#syntactic-substitution-stmt
#proof[
    See @syntactic-properties[Appendix]
]

= Semantics

In this section, we give a denotational semantics to well-typed `isotope` programs in an effectful category equipped with some auxiliary structure. We then prove some basic properties of our semantics.

== Isotope Models

#definition(name: "Isotope Model")[
    An *isotope model* is an effectful category $F: cal(C)_∅ -> cal(C)_{cen}$ (the latter simply written $cal(C)_cen$) such that
    - $cal(C)_∅$ and $cal(C)_cen$ have an additional symmetric monoidal product $⊕$, for which $F$ is a symmetric monoidal functor. We denote the identity object of $⊕$ to be $0$, which we take to be the initial object; we denote morphisms from the initial object as $0_A: 0 -> A$.
    - $cal(C)_cen$ has a trace over $⊕$
    - There exists an object $bools$
    - For each object $A$, there exists a morphism $smite(A): bools ⊗ A -> A ⊕ A$ such that, for all morphisms $f: A → B$,
    $
    bools ⊗ f;smite(B) = smite(A);f ⊕ f
    $
    - For each object $A$, there exists a morphism $j: A ⊕ A -> A$ such that $(A, j, 0)$ forms a commutative monoid

    We say an isotope model is *standard* if $⊕$ is the coproduct, $j = [idm, idm]$, and $bools = tobj + tobj$, and it has a uniform Conway iteration operator.

    We say an isotope model is *iterative* if $cal(C)_cen$ is iterative.

    We say an isotope model is *poset-enriched* if $F$, $⊗$, $⊕$, and $sans("Tr")$ are poset-enriched. 
]

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
    $#dnt($Γ, thyp(x, A, q)$) = dnt(Γ) ⊗ dnt(A) ⊗$,
)
#syntax-den(
    rect([$dnt(sans(L)): |cal(C)_1|$]),
    $dnt(bcnil) = iobj$,
    $#dnt($sans(L), lhyp(Γ, lbl(ell), p, A)$) = dnt(sans(L)) ⊕ (dnt(Gamma) ⊗ dnt(A))$,
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
    $dnt(#dprf(typing-rules.pair-aff)) = dnt(#typing-rules.pair-aff.premises.at(0)) ⊗ dnt(#typing-rules.pair-aff.premises.at(1)); α^⊗$)
$
#rect([$dnt(rel(A)): cal(C)_1(dnt(A), dnt(A) ⊗ dnt(A))$])
$
#row-den(
    $dnt(dprf(#typing-rules.fwd-rel)) = sans("rel")(X)$,
    $dnt(dprf(#typing-rules.unit-rel)) = α^⊗$,
    $dnt(dprf(#typing-rules.bool-rel)) = sans("rel")(bools)$,
)
$
    dnt(dprf(#typing-rules.pair-rel)) =
    dnt(#typing-rules.pair-rel.premises.at(0)) ⊗ dnt(#typing-rules.pair-rel.premises.at(1));α;
    idm_(dnt(A)) ⊗ σ_(dnt(A), dnt(B)) ⊗ idm_(dnt(B));
    α^⊗
$
$
#rect([$dnt(joinctx(sans(K), sans(L))): cal(C)_1(dnt(sans(K)), dnt(sans(L)))$])
$
#row-den(
    $dnt(dprf(#typing-rules.label-nil)) = idm$,
    $dnt(dprf(#typing-rules.label-join)) = dnt(#typing-rules.label-join.premises.at(0)); α^⊕; dnt(L) ⊕ 0_(dnt(A) ⊗ dnt(Γ))$
)
$
dnt(dprf(#typing-rules.label-ext)) 
= dnt(#typing-rules.label-ext.premises.at(0)) ⊕ dnt(#typing-rules.label-ext.premises.at(1))
$
$
#rect([$dnt(splitctx(Γ, Δ, Ξ)): cal(C)_1(dnt(Γ), dnt(Δ) ⊗ dnt(Ξ))$])
$
#row-den(
    $dnt(dprf(#typing-rules.ctx-nil)) = α^⊗$,
    $dnt(dprf(#typing-rules.ctx-right)) = dnt(#typing-rules.ctx-right.premises.at(0)) ⊗ dnt(A);α^⊗$
)
$
dnt(dprf(#typing-rules.ctx-left)) = dnt(#typing-rules.ctx-left.premises.at(0)) ⊗ dnt(A);α^⊗;dnt(Δ) ⊗ σ_(dnt(Ξ), dnt(A));α^⊗
$
$
dnt(dprf(#typing-rules.ctx-rel)) =
dnt(#typing-rules.ctx-rel.premises.at(0)) ⊗ dnt(rel(A));
α^⊗;dnt(Δ) ⊗ σ_(dnt(Ξ), dnt(A)) ⊗ dnt(A);α^⊗
$
$
dnt(dprf(#typing-rules.ctx-aff)) =
dnt(#typing-rules.ctx-rel.premises.at(0)) ⊗dnt(aff(A));α^⊗
$
$
#rect([$dnt(dropctx(Γ, Δ)): cal(C)_1(dnt(Γ), dnt(Δ))$])
$
// #row-den(
//     $dnt(dprf(#typing-rules.wk-nil)) = idm$,
//     $dnt(dprf(#typing-rules.wk-add)) = dnt(A) ⊗ dnt(dropctx(Γ, Δ))$
// )
#row-den($dnt(dprf(#typing-rules.wk-def)) = dnt(#typing-rules.wk-def.premises.at(0));α^⊗$)

//TODO: string diagrams, since all structrure is in cal(C)_1?

=== Term Typing

$
#rect([$dnt(istm(Γ, p, a, A)): cal(C)_p(dnt(Γ), dnt(A))$])
$
#row-den(
    $dnt(dprf(#typing-rules.var)) = dwng(dnt(#typing-rules.var.premises.at(0)), purity: p)$,
    $dnt(dprf(#typing-rules.nil)) = dwng(dnt(#typing-rules.nil.premises.at(0)), purity: p)$,
)
$
dnt(dprf(#typing-rules.app)) = instof(p, f) ∘ dnt(#typing-rules.var.premises.at(0))
$
#row-den(
    $dnt(dprf(#typing-rules.true)) = dwng(dnt(#typing-rules.true.premises.at(0)), purity: p);sans("tt")$,
    $dnt(dprf(#typing-rules.false)) = dwng(dnt(#typing-rules.false.premises.at(0)), purity: p);sans("ff")$,
)
$
dnt(dprf(#typing-rules.pair)) = dwng(dnt(#typing-rules.pair.premises.at(0)), purity: p);dnt(#typing-rules.pair.premises.at(1)) ⋉_p dnt(#typing-rules.pair.premises.at(2))
$
$
dnt(dprf(#typing-rules.let)) 
\ #h(5em) = dwng(dnt(#typing-rules.let.premises.at(0)), purity: p);
    dnt(Δ) ⊗ dnt(#typing-rules.let.premises.at(1));
    dnt(#typing-rules.let.premises.at(2))
$
$
dnt(dprf(#typing-rules.let2))
\ #h(5em) = dwng(dnt(#typing-rules.let2.premises.at(0)), purity: p);
    dnt(Δ) ⊗ dnt(#typing-rules.let2.premises.at(1));α^⊗;
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
dnt(dprf(#typing-rules.br)) = dnt(#typing-rules.br.premises.at(0));α^⊕; dnt(A) ⊕ 0_(dnt(sans(L)))
$
$
dnt(dprf(#typing-rules.jmp)) 
\ #h(5em) =
dwng(dnt(#typing-rules.jmp.premises.at(0)), purity: p);dnt(Δ) ⊗ dnt(#typing-rules.jmp.premises.at(1));α^⊕;0_(dnt(B)) ⊕ dwng(dnt(#typing-rules.jmp.premises.at(2)), purity: p)
$
$
dnt(dprf(#typing-rules.ite))
\ #h(5em) =
dwng(dnt(#typing-rules.ite.premises.at(0)), purity: p);
dnt(#typing-rules.ite.premises.at(1)) ⊗ dnt(Ξ);
smite(dnt(Ξ));
dnt(#typing-rules.ite.premises.at(2)) ⊕ dnt(#typing-rules.ite.premises.at(3))
$
$
dnt(dprf(#typing-rules.let-blk))
\ #h(5em) =
dwng(dnt(#typing-rules.let-blk.premises.at(0)), purity: p);
dnt(Δ) ⊗ dnt(#typing-rules.let-blk.premises.at(1));
dnt(#typing-rules.let-blk.premises.at(2))
$
$
dnt(dprf(#typing-rules.let2-blk))
\ #h(5em) =
dwng(dnt(#typing-rules.let2-blk.premises.at(0)), purity: p);
dnt(Δ) ⊗ dnt(#typing-rules.let2-blk.premises.at(1));
α;
dnt(#typing-rules.let2-blk.premises.at(2))
$
$
dnt(dprf(#typing-rules.tr))
\ #h(5em) = 
dnt(#isblk($Γ$, $sans(S), sans(L)$, $p$, $s$, $B$));α^⊕;sans(B) ⊕ sans(L) ⊕ sans("Tr")_(dnt(sans(S)), dnt(B) ⊕ dnt(sans(L)))^(dnt(sans(S)))(j;D);j
$
where
$
sans(S)_0 &= [lhyp(Δ_j, ∅, lbl(ℓ)_j, A_j)]_j \
sans(S) &= [lhyp(Δ_j, p_j, lbl(ℓ)_j, A_j)]_j \
D &= α^⊕ ∘ j^i ∘ plus.circle.big_i dnt(#isblk($Δ_i, thyp(x_i, A_i)$, $sans(L), sans(S)_0$, $p$, $t_i$, $B$))
    &: cal(C)_p(dnt(sans(S)_0), (dnt(B) ⊕ dnt(sans(L))) ⊕ dnt(sans(S)_0))
$
noting that $dnt(sans(S)) = dnt(sans(S)_0)$.
/*
TODO: notes on guardedness...
*/
/*
TODO: string diagrams for control flow?
*/

== Metatheory

//TODO: text, segue

#let semantic-downgrade-stmt = theorem(name: "Semantic Downgrade")[
    If $p' ⊆ p$, then
    - $dwng(purity: p', dnt(istm(Γ, p, a, A))) = istm(Γ, p', a, A)$
    - $dwng(purity: p', dnt(isblk(Γ, sans(L), p, t, B))) = isblk(Γ, sans(L), p', t, B)$
    where the right-hand side is defined whenever the left-hand side is by downgrade.
]
#semantic-downgrade-stmt
#proof[
    By mutual induction on derivations of $dnt(istm(Γ, p, a, A))$, $dnt(isblk(Γ, sans(L), p, t, B))$
]

We now state a few basic properties of weakenings:
- Since derivations $splitctx(Γ, Δ, Ξ)$, $dropctx(Γ, Δ)$, $joinctx(sans(L), sans(K))$ are unique, it follows their denotations are unique, if they exist, justifying the syntax $dnt(splitctx(Γ, Δ, Ξ))$, $dnt(dropctx(Γ, Δ))$, $dnt(joinctx(sans(L), sans(K)))$
- In particular, we have that $dnt(dropctx(Γ, Γ)) = idm$, and, if $dropctx(Γ, Δ), dropctx(Δ, Ξ)$, then 
$
dnt(dropctx(Γ, Ξ)) = dnt(dropctx(Γ, Δ));dnt(dropctx(Δ, Ξ))
$

#let weakening-stmt = theorem(name: "Semantic Weakening")[
    - If $D_Γ$ is a derivation of $istm(Γ, p, a, A)$, then for all $dropctx(Γ, Δ)$, for all derivations $D_Θ$ of $istm(Θ, p, a, A)$, $dnt(D_Γ) = dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(D_Θ)$
    - If $D_Γ$ is a derivation of $isblk(Γ, sans(L), p, t, B)$, then for all $dropctx(Γ, Θ)$, for all derivations $D_Θ$ of $isblk(Θ, sans(L), p, t, B)$, $dnt(D_Γ) = dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(D_Θ)$
    In particular, all derivations of $istm(Γ, p, a, A)$ and $isblk(Γ, sans(L), p, t, B)$ have equal denotations, justifying the syntax $dnt(istm(Γ, p, a, A))$, $dnt(isblk(Γ, sans(L), p, t, B))$
]
#weakening-stmt
#proof[
    See @semantic-properties[Appendix]
]

#let join-weakening-stmt = theorem(name: "Semantic Join Weakening")[
    If $joinctx(sans(K), sans(L))$, then
    $
    dnt(isblk(Γ, sans(L), p, t, A)) = dnt(isblk(Γ, sans(K), p, t, A));dnt(B) ⊕ dnt(joinctx(sans(K), sans(L)))
    $
]
#join-weakening-stmt

//TODO: text, segue

We now give a denotational semantics for substititons:
$
#rect([$dnt(#[$issub(γ, Θ, Γ, p)$]): cal(C)_p(dnt(Θ), dnt(Γ))$])
$
$
dnt(dprf(#substitution-rules.subst-nil)) = idm 
$
$
dnt(dprf(#substitution-rules.subst-cons)) \
= dnt(#substitution-rules.subst-cons.premises.at(3));
    dnt(#substitution-rules.subst-cons.premises.at(1)) ⋉
    dnt(#substitution-rules.subst-cons.premises.at(0))
$
Since the denotations of derivations $istm(Γ, 1, a, A)$ and $splitctx(Γ, Δ, Ξ)$ are unique, it follows by a trivial induction that the denotations of $issub(γ, Θ, Γ, p)$ are unique, justifying the syntax $dnt(issub(γ, Θ, Γ, p))$.

A substitution $issub(γ, Θ, Γ, p)$ also induces a map on label contexts as follows:
$
#rect([$labmap(sans(L), γ): cal(C)_p(dnt([γ]sans(L)), dnt(sans(L)))$])
$
$
labmap(bcnil, γ) & = idm \
labmap((sans(L), lhyp(Δ, p, lbl(ℓ), A)), γ) & = labmap(sans(L), γ) ⊗ (dnt(issub(γ_Δ, Θ_Δ, Δ, p)) ⊗ dnt(A))
$
with $sans("labmap")$ defined iff $γ_Δ$ is for all $Δ ∈ sans(L)$.

We state the following basic properties of substitutions:

- For $p' ⊆ p$,
    - $dwng(purity: p', issub(γ, Θ, Γ, p))) = issub(γ, Θ, Γ, p')$
    - $dwng(purity: p', labmap(sans(L), γ)) = labmap(sans(L), dwng(purity: p', γ))$

//TODO: text, segue

#let wk-split-stmt = lemma(name: "Semantic Splitting")[
    If $dropctx(Γ, Θ)$ and $splitctx(Γ, Δ, Ξ)$, then
    $
    dnt(splitctx(Γ, Δ, Ξ));(dnt(dropctx(Δ, Θ_Δ)) ⊗ dnt(dropctx(Ξ, Θ_Ξ))) =
    dnt(dropctx(Γ, Θ));dnt(splitctx(Θ, Θ_Δ, Θ_Ξ))
    $
    In particular,
    $
    dnt(dropctx(Γ, Δ));dnt(dropctx(Δ, Ξ)) = dnt(dropctx(Γ, Ξ))
    $
]
#wk-split-stmt

#let substitution-wk-stmt = lemma(name: "Semantic Substitution Splitting")[
    If $splitctx(Γ, Δ, Ξ)$ and $issub(γ, Θ, Γ)$ is a *pure* substitution, then
    $
    dnt(issub(γ, Θ, Γ));dnt(splitctx(Γ, Δ, Ξ)) = dnt(splitctx(Θ, Θ_Δ, Θ_Ξ));dnt(issub(γ, Θ, Δ)) ⊗ dnt(issub(γ, Θ, Ξ))
    $
    In particular, $dnt(issub(γ, Θ, cnil)) = dnt(dropctx(Θ, cnil))$ and therefore
    $
    dnt(issub(γ, Θ, Γ));dnt(dropctx(Γ, Δ)) = dnt(dropctx(Θ_Γ, Θ_Δ));dnt(issub(γ_Δ, Θ, Δ))
    $
    Note that this holds for _pure_ substitutions $issub(γ, Θ, Δ)$, *not* substitutions in general!
]
#substitution-wk-stmt

We may now state the semantic substitution theorem:
#let substitution-stmt = theorem(name: "Semantic Substitution")[
    If $issub(γ, Θ, Γ)$ is a *pure* substitution and $istm(Γ, p, a, A)$ or $isblk(Γ, sans(L), p, t, B)$, then
    $
        dnt(istm(Θ, p, [γ]a, A)) &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, [γ]a, A)) \
        dnt(isblk(Θ, [γ]sans(L), p, [γ]t, B));(dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))) &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(isblk(Γ, [γ]sans(L), p, [γ]t, A))
    $
]
#substitution-stmt
#proof[
    See @semantic-properties[Appendix]
]

//TODO: semantic equivalence of (potentially impure) substitutions

//TODO: rewriting theorem

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
/*
TODO: monad transformers
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

= Metatheory

//TODO: fix repeated theorem numbering...

== Syntactic Properties <syntactic-properties>

#downgrade-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$. We generate one case for each possible rule:
    - #rname("var"): since by assumption #dropctx($Γ$, $thyp(x, A, ∅)$), we may apply #rstyle("var") to derive $istm(Γ, p', x, A)$ as desired.
    - #rname("app"): since by assumption $f ∈ cal(I)_p(A, B) ⊆ cal(I)_p'(A, B)$, and by induction $istm(Γ, p', a, A)$, we may apply #rstyle("app") to derive $istm(Γ, p', f aq a, A)$ as desired.
    - #rname("jmp"): by induction, we have that $istm(Ξ, p', a, A)$, by assumption we have that $joinctx(lhyp(Δ, p, lbl(ℓ), A), sans(L))$ and therefore since $p' ⊆ p$ $joinctx(lhyp(Δ, p', lbl(ℓ), A), sans(L))$, hence we may apply #rstyle("jmp") to derive $isblk(Γ, sans(L), p', br(lbl(l), a), B)$, as desired.
    - #rname("tr"): by assumption, we have that $∀i, #[#isblk($Δ_i, thyp(x_i, A_i)$, $sans(L), [lhyp(Δ_j, ∅, lbl(ℓ_j), A_j)]_j$, $p_i$, $t_i$, $B$)]$. By induction, we have that #isblk($Γ$, $sans(L), [lhyp(Δ_j, 0, lbl(ℓ_j), A_j)]_j$, $p'$, $s$, $B$). Hence, we may apply #rstyle("tr") to yield the desired conclusion.
    The other cases are direct application of the respective typing rule to the inductive hypotheses.
    //NOTE: these case are *no longer valid*, as the statement of the theorem has changed
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

#syntactic-weakening-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$ given a weakening $dropctx(Θ, Γ)$:
    - #rname("var"): 
        - By transitivity of weakening, $#subctx($Γ$, $thyp(x, A, ∅)$) ==> #subctx($Θ$, $thyp(x, A, ∅)$)$ 
        - Hence, by #rstyle("var"), $istm(Θ, p, x, A)$, as desired.
    - #rname("app"):
        - By induction, $istm(Θ, p, a, A)$
        - Hence, by #rstyle("app"), $istm(Θ, p, f aq a, B)$, as desired.
    - #rname("nil"), #rname("true"), #rname("false"): 
        - By transitivity of weakening, $#subctx($Γ$, $x: A$) ==> #subctx($Θ$, $cnil$)$ 
        - Hence, by #rstyle("nil")/#rstyle("true")/#rstyle("false"), we may derive the desired conclusion
    //NOTE: these case are *no longer valid*, as the typing rules have changed
    // - #rname("pair"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("pair"), $istm(Θ, p, (a, b), A ⊗ B)$
    // - #rname("let"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("let"), #istm($Θ$, $p$, $llet x = a; b$, $B$)
    // - #rname("let2"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("let2"), #istm($Θ$, $p$, $llet (x, y) = e; e'$, $C$)
    - #rname("blk"):
        - By induction, $isblk(Θ, bcnil, p, t, B)$
        - Hence, by #rstyle("blk"), #istm($Θ$, $p$, ${t}$, $B$)
    - #rname("br"): 
        - By induction, $istm(Θ, p, a, A)$
        - Hence, by #rstyle("br"), $isblk(Θ, sans(L), p, br(a), A)$, as desired.
    //NOTE: these case are *no longer valid*, as the typing rules have changed
    // - #rname("jmp"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("jmp"), #isblk($Θ$, $sans(L)$, $p$, $br(lbl(ℓ), a)$, $B$)
    // - #rname("ite"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("ite"), #isblk($Θ$, $sans(L)$, $p$, $lite(e, s, t)$, $B$)
    // - #rname("let-blk"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("let-blk"), #isblk($Θ$, $sans(L)$, $p$, $llet x = a; t$, $B$)
    // - #rname("let2-blk"): 
    //     - By assumption, $splitctx(Γ, Δ, Ξ)$; hence, by composition, $splitctx(Θ, Δ, Ξ)$
    //     - Hence, by #rstyle("let2-blk"), #isblk($Θ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)
    - #rname("tr"): 
        - By induction, #isblk($Θ$, $sans(L), [lhyp(Δ_j, p_j, lbl(ℓ)_j, A_j)]_j, sans(L)$, $p$, $s$, $B$)
        - Hence, by #rstyle("tr"), #isblk($Θ$, $sans(L)$, $p$, $llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; s$, $B$)
    - The remainder of the cases may be discharged by noting that, as by assumption, $splitctx(Γ, Δ, Ξ)$; and hence, by composition, $splitctx(Θ, Δ, Ξ)$, the appropriate typing rule may simply be applied directly.
]


#syntactic-substitution-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$ given a substitution $issub(γ, Θ, Γ, p)$:
    - #rname("var"): 
        - By assumption, we have that $istm(Θ_x, p, [γ]x, A)$ (since $issub(γ, Θ, Γ, p)$ is a substitution)
        - Hence, since $dropctx(Θ, Θ_x)$ by weakening substitution (since $dropctx(Γ, #[$x: A$])$ by assumption), $istm(Θ, p, [γ]x, A)$ by weakening, as desired.
    - #rname("app"): 
        - $istm(Θ, p, a, A)$ by induction
        - $f ∈ cal(I)_p(A, B)$ by assumption
        - Hence, $istm(Θ, p, [γ](f aq a), B)$ by #rstyle("app"), as desired.
    - #rname("nil"), #rname("true"), #rname("false"): 
        By weakening substitution, we have $dropctx(Δ, cnil)$ by weakening substitution (since $dropctx(Γ, cnil)$ by assumption) and therefore applying #rstyle("nil")/#rstyle("true")/#rstyle("false") gives the desired result.
    - #rname("pair"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - Therefore, by induction $istm(Θ_Δ, p, [γ_Δ]a, A)$ and $istm(Θ_Ξ, p, [γ_Ξ]b, B)$. 
        - Hence, #istm($Θ$, $p$, $[γ](a, b)$, $A ⊗ B$) by #rstyle("pair"), as desired, since $[γ_Δ]a = [γ]a$ and $[γ_Ξ]b = [γ]b$
    - #rname("let"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - By definition, #issub($slft(γ_Δ)$, $(Θ_Δ, thyp(x, A))$, $(Δ, thyp(x, A))$) (since $issub(γ_Δ, Θ_Δ, Δ)$) 
        - By induction, we have that $istm(Θ_Ξ, p, [γ_Ξ]a, A)$ and #istm($Θ_Δ, thyp(x, A)$, $p$, $[slft(γ_Δ)]e$, $B$). 
        - Hence, by #rstyle("let"), since $[γ_Ξ]a = [γ]a$ and $[slft(γ_Δ)]e = [slft(γ_Δ)]e$, #istm($Θ$, $p$, $[γ](llet x = a; e)$, $B$), as desired.
    - #rname("let2"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - By definition, #issub($slft(slft(γ_Δ))$, $(Θ_Δ, thyp(x, A), thyp(y, B))$, $(Δ, thyp(x, A), thyp(y, B))$) (since $issub(γ_Δ, Θ_Δ, Δ)$). 
        - By induction, we have that $istm(Θ_Ξ, p, [γ_Ξ]e, A)$ and #istm($Θ_Δ, thyp(x, A), thyp(y, B)$, $p$, $[slft(slft(γ_Ξ))]e'$, $C$). 
        - Hence, by #rstyle("let2"), since $[γ_Ξ]e = [γ]e$ and $[slft(slft(γ_Δ))]e' = [slft(slft(γ))]e'$, #istm($Θ$, $p$, $[γ](llet (x, y) = e; e')$, $C$), as desired.
    - #rname("blk"): by induction, we have that $isblk(Θ, bcnil, p, t, B)$, and hence, by #rstyle("blk"), $istm(Θ, p, [γ]{t}, B)$
    - #rname("br"): by induction, we have that $istm(Θ, p, a, A)$, and hence, by #rstyle("br"), we have that $isblk(Θ, [γ]sans(L), p, [γ](br(a)), A)$
    - #rname("jmp"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - By join substitution, $joinctx(lhyp(Θ_Δ, q, lbl(ℓ), A), [γ]sans(L))$ (since $joinctx(lhyp(Δ, q, lbl(ℓ), A), sans(L))$). 
        - By induction, $istm(Θ_Ξ, p, a, A)$. 
        - Therefore, since $[γ_Ξ]a = [γ]a$, by #rstyle("jmp"), we have $isblk(Θ, [γ]sans(L), p, [γ](br(lbl(ℓ), a)), B)$, as desired
    - #rname("ite"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - By induction, we have $istm(Θ_Δ, p, e, bools)$, $isblk(Θ_Ξ, [γ]sans(L), p, s, B)$, $isblk(Θ_Ξ, [γ]sans(L), p, t, B)$
        - Hence, applying #rstyle("ite"), since $[γ_Δ]e = [γ]e$, $[γ_Ξ]s = [γ]s$, and $[γ_Ξ]t = [γ]t$, we obtain $isblk(Θ, [γ]sans(L), p, [γ](lite(e, s, t)), B)$, as desired.
    - #rname("let-blk"): 
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption).
        - Therefore, in particular, #issub($slft(γ_Δ)$, $(Θ_Δ, thyp(x, A))$, $(Δ, thyp(x, A))$)
        - By induction, we have that $istm(Θ_Ξ, p, [γ_Ξ]a, A)$ and #isblk($Θ_Δ, thyp(x, A)$, $[slft(γ_Δ)]sans(L)$, $p$, $[slft(γ_Δ)]t$, $B$). 
        - Hence, since $[γ_Ξ]a = [γ]a$, $[slft(γ_Δ)]t = [slft(γ)]t$, and  $[slft(γ_Δ)]sans(L) = [γ]sans(L)$, applying #rstyle("let-blk"), we obtain #isblk($Θ$, $[γ]sans(L)$, $p$, $[γ](llet x = a; e)$, $B$), as desired.
    - #rname("let2-blk"):  
        - By split substitution, we have $splitctx(Θ, Θ_Δ, Θ_Ξ)$, $issub(γ_Δ, Θ_Δ, Δ)$, and $issub(γ_Ξ, Θ_Ξ, Ξ)$ (since $splitctx(Γ, Δ, Ξ)$ by assumption). 
        - Therefore, #issub($slft(slft(γ_Δ))$, $(Θ_Δ, thyp(x, A), thyp(y, B))$, $Δ, thyp(x, A), thyp(y, B)$) since $issub(γ_Δ, Θ_Δ, Δ)$. 
        - By induction, we have that $istm(Θ_Ξ, p, [γ_Ξ]e, A)$ and #isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $[slft(slft(γ_Δ))]sans(L)$, $p$, $[slft(slft(γ_Δ))]t$, $C$). 
        - Hence, since $[γ_Ξ]e = [γ]e$, $[slft(slft(γ_Δ))]t = [slft(slft(γ))]t$, and $[slft(slft(γ_Δ))]sans(L) = [γ]sans(L)$, we may apply #rstyle("let2-blk"), yielding #isblk($Θ$, $p$, $[γ]sans(L)$, $[γ](llet (x, y) = e; t)$, $C$) as desired.
    - #rname("tr"):
        - By induction, $∀i, #isblk($Θ_(Δ_i), thyp(x_i, A_i)$, $[γ]sans(L), [lhyp(Θ_(Δ_j), 0, lbl(ℓ)_j, A_j)]_j$, $p_i$, $[γ_(Δ_i)]t_i$, $B$)$
        - By induction, #isblk($Θ$, $[γ]sans(L), [lhyp(Θ_(Δ_j), p_j, lbl(ℓ)_j, A_j)]_j$, $p$, $s$, $B$)
        - Hence, by #rstyle("tr"), #isblk($Θ$, $[γ]sans(L)$, $p$, $llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; [γ]s$, $B$), as desired.
]

== Semantic Properties <semantic-properties>

#weakening-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$ given a weakening $dropctx(Γ, Θ)$ and a corresponding derivation $istm(Θ, p, a, A)$ or $isblk(Θ, sans(L), p, t, B)$.
    - #rname("var"): we have that
    $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(istm(Θ, p, x, A)) #h(12em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(#dropctx($Θ$, $thyp(x, A, ∅)$))) & "by definition"
        \ &= dwng(purity: p, dnt(#dropctx($Γ$, $thyp(x, A, ∅)$))) & "weakening composes"
        \ &= dnt(istm(Γ, p, x, A)) & "by definition"
    $
    - #rname("app"): 
        We have that
        $
            & dwng(purity: p, dnt(dropctx(Γ, Θ))); dnt(istm(Θ, p, f aq a, B)) #h(12em) &
            \ &= dwng(purity: p, dnt(dropctx(Γ, Θ))); dnt(istm(Θ, p, a, A)); instof(p, f) & "by definition"
            \ &= dnt(istm(Γ, p, a, A));  instof(p, f) & "by induction"
            \ &= dnt(istm(Γ, p, f aq a, B)) & "by definition"
        $
    - #rname("nil"), #rname("true"), #rname("false"): 
        in each case, the desired result follows trivially from the fact that weakening composes.
    - #rname("pair"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));
            dnt(istm(Θ, p, (a, b), A ⊗ B)) #h(20em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));
            dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(istm(Θ_Δ, p, a, A)) ⋉
            dnt(istm(Θ_Ξ, p, b, B))
            & "by definition"
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));
            dnt(istm(Θ_Δ, p, a, A)) ⋉
            dnt(istm(Θ_Ξ, p, b, B))
            & "weakening splits"
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            (dwng(purity: p, dnt(dropctx(Δ, Θ_Δ)));dnt(istm(Θ_Δ, p, a, A))) ⋉
            (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, b, B)))
            & "by centrality"
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(istm(Δ, p, a, A)) ⋉ dnt(istm(Ξ, p, b, A)) 
            & "by induction"
        \ &= dnt(istm(Γ, p, (a, b), A ⊗ B)) & "by definition"
        $
    - #rname("let"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#istm($Θ$, $p$, $llet x = a; e$, $B$)) #h(20em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Ξ) ⊗ dnt(istm(Θ_Ξ, p, a, A));
            dnt(#istm($Θ_Δ, thyp(x, A)$, $p$, $e$, $B$))
        & "by definition"
        \ #h(4em) 
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(#dropctx($Ξ$, $Θ_Ξ$)));
        & "by splitting"
        \ #h(4em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, a, A));
            dnt(#istm($Θ_Δ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, a, A)));
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Δ$, $Θ_Δ$)) ⊗ dnt(A);
            dnt(#istm($Θ_Ξ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Δ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, a, A)));
        & "by definition"
        \ #h(4em) dnt(#dropctx($Δ, thyp(x, A)$, $Θ_Δ, thyp(x, A)$));
            dnt(#istm($Θ_Δ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));
            dnt(#istm($Δ, thyp(x, A)$, $p$, $e$, $B$))
        & "by induction"
        \ &= dnt(#istm($Γ$, $p$, $llet x = a; e$, $B$)) & "by definition"
        $
    - #rname("let2"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#istm($Θ$, $p$, $llet (x, y) = e; e'$, $C$)) #h(15em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, e, A ⊗ B));α^⊗;
        & "by definition"
        \ #h(4em) 
            dnt(#istm($Θ_Ξ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dnt(#dropctx($Ξ$, $Θ_Ξ$));
        & "by splitting"
        \ #h(4em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, e, A ⊗ B));α^⊗;
            dnt(#istm($Θ_Ξ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, e, A ⊗ B)));α^⊗;
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Ξ$, $Θ_Ξ$)) ⊗ dnt(A) ⊗ dnt(B);
            dnt(#istm($Θ_Δ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, e, A ⊗ B)));α^⊗;
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Δ, thyp(x, A), thyp(y, B)$, $Θ_Δ, thyp(x, A), thyp(y, B)$));
            dnt(#istm($Θ_Δ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α^⊗;
            dnt(#istm($Δ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        & "by induction"
        \ &= dnt(#istm($Γ$, $p$, $llet (x, y) = e; e'$, $C$))
        & "by definition"
        $ 
    - #rname("blk"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(istm(Θ, p, {t}, B)) #h(12em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(isblk(Θ, bcnil, p, t, B));α^⊕ & "by definition"
        \ &= dnt(isblk(Γ, bcnil, p, t, B));α^⊕ & "by induction"
        \ &= dnt(istm(Γ, p, {t}, B)) & "by definition"
        $
    - #rname("br"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(isblk(Θ, sans(L), p, br(a), A)) #h(12em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(istm(Θ, p, a, A));α^⊕;dnt(A) ⊕ 0_(dnt(sans(L))) & "by definition"
        \ &= dnt(istm(Γ, p, a, A));α^⊕;dnt(A) ⊕ 0_(dnt(sans(L))) & "by induction"
        \ &= dnt(isblk(Γ, sans(L), p, br(a), A)) & "by definition"
        $
    - #rname("jmp"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(isblk(Θ, sans(L), p, br(lbl(ℓ), a), B)) #h(17em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ))); & "by definition"
        \ #h(5em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, a, A));α^⊕;0_(dnt(B)) ⊕ dwng(purity: p, dnt(joinctx(lhyp(Θ_Δ, lbl(ℓ), p, A), sans(L))))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ))); & "by splitting"
        \ #h(5em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, a, A));α^⊕;0_(dnt(B)) ⊕ dnt(joinctx(lhyp(Θ_Δ, lbl(ℓ), p, A), sans(L)))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dnt(istm(Ξ, p, a, A));α^⊕;0_(dnt(B)) ⊕ dwng(purity: p, dnt(joinctx(lhyp(Θ_Δ, lbl(ℓ), p, A), sans(L)))) & "by induction"
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));α^⊕;0_(dnt(B)) ⊕ dwng(purity: p, dnt(joinctx(lhyp(Δ, lbl(ℓ), p, A), sans(L)))) & "by composition"
        \ &= dnt(isblk(Γ, sans(L), p, br(lbl(ℓ), a), A)) & "by definition"
        $
    - #rname("ite"):
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(isblk(Θ, sans(L), p, lite(e, s, t), B)) #h(15em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(istm(Θ_Δ, p, e, bools)) ⊗ dnt(Θ_Ξ);
            smite(dnt(Θ_Ξ)); & "by definition"
        \ &#h(5em)    dnt(isblk(Θ_Ξ, sans(L), p, s, B)) ⊕ dnt(isblk(Θ_Ξ, sans(L), p, t, B))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Δ, p, e, bools)) ⊗ dnt(Θ_Ξ);smite(dnt(Θ_Ξ)); & "by splitting"
        \ &#h(5em) dnt(isblk(Θ_Ξ, sans(L), p, s, B)) ⊕ dnt(isblk(Θ_Ξ, sans(L), p, t, B))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));(dwng(purity: p, dnt(dropctx(Δ, Θ_Δ)));dnt(istm(Θ_Δ, p, e, bools))) ⊗ dnt(Ξ);smite(dnt(Ξ))
        & "by centrality"
        \ &#h(5em) (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(isblk(Θ_Ξ, sans(L), p, s, B))) ⊕ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(isblk(Θ_Ξ, sans(L), p, t, B)))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(istm(Δ, p, e, bools));smite(dnt(Ξ));dnt(isblk(Ξ, sans(L), p, s, B)) ⊕ dnt(isblk(Ξ, sans(L), p, t, B)) 
        & "by induction"
        \ &= dnt(isblk(Γ, sans(L), p, lite(e, s, t), B)) & "by definition"
        $
    - #rname("let-blk"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#isblk($Θ$, $sans(L)$, $p$, $llet x = a; t$, $B$)) #h(20em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, a, A));
            dnt(#isblk($Θ_Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        & "by definition"
        \ #h(4em) 
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(#dropctx($Ξ$, $Θ_Ξ$)));
        & "by splitting"
        \ #h(4em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, a, A));
            dnt(#isblk($Θ_Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, a, A)));
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Δ$, $Θ_Δ$)) ⊗ dnt(A);
            dnt(#isblk($Θ_Ξ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
            dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, a, A)));
        & "by definition"
        \ #h(4em) dnt(#dropctx($Δ, thyp(x, A)$, $Θ_Δ, thyp(x, A)$));
            dnt(#isblk($Θ_Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));
            dnt(#isblk($x: A, Δ$, $sans(L)$, $p$, $t$, $B$))
        & "by induction"
        \ &= dnt(#isblk($Γ$, $sans(L)$, $p$, $llet x = a; t$, $B$)) & "by definition"
        $
    - #rname("let2-blk"): 
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#isblk($Θ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)) #h(15em) &
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, e, A ⊗ B));α^⊗;
        & "by definition"
        \ #h(4em) 
            dnt(#isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dwng(purity: p, dnt(dropctx(Δ, Θ_Δ))) ⊗ dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));
        & "by splitting"
        \ #h(4em) dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, e, A ⊗ B));α^⊗;
            dnt(#isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
             dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, e, A ⊗ B)));α^⊗;
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Δ$, $Θ_Δ$)) ⊗ dnt(A) ⊗ dnt(B);
            dnt(#isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ))); 
             dnt(Δ) ⊗ (dwng(purity: p, dnt(dropctx(Ξ, Θ_Ξ)));dnt(istm(Θ_Ξ, p, e, A ⊗ B)));α^⊗;
        & "by centrality"
        \ #h(4em) dnt(#dropctx($Δ, thyp(x, A), thyp(y, B)$, $Θ_Δ, thyp(x, A), thyp(y, B)$));
            dnt(#isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α^⊗;
            dnt(#isblk($Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        & "by induction"
        \ &= dnt(#isblk($Γ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)) 
        & "by definition"
        $ 
    - #rname("tr"):
        We have that
        $
        & dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#isblk($Θ$, $sans(L)$, $p$, $llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; s$, $B$))
        #h(12em) & 
        \ &= dwng(purity: p, dnt(dropctx(Γ, Θ)));dnt(#isblk($Θ$, $sans(L), sans(S)$, $p$, $s$, $B$));α^⊕;dnt(B) ⊕ dnt(sans(L)) ⊕ sans("Tr")_(dnt(sans(S)), dnt(B) ⊕ dnt(sans(L)))^(dnt(sans(S)))(j;D);j
        & "by definition" \
        \ &= dnt(#isblk($Γ$, $sans(S), sans(L)$, $p$, $s$, $B$));α^⊕;dnt(B) ⊕ dnt(sans(L)) ⊕ sans("Tr")_(dnt(sans(S)), dnt(B) ⊕ dnt(sans(L)))^(dnt(sans(S)))(j;D);j
        & "by induction"
        \ &= dnt(#isblk($Γ$, $sans(L)$, $p$, $llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; s$, $B$))
        & "by definition"
        $
        where 
        $
        sans(S) &= [lhyp(Δ_j, p_j, lbl(ℓ)_j, A_j)]_j \
        sans(S)_0 &= [lhyp(Δ_j, ∅, lbl(ℓ)_j, A_j)]_j \
        D &= α^⊕ ∘ j^i ∘ plus.circle.big_i dnt(#isblk($Δ_i, thyp(x_i, A_i)$, $sans(L), sans(S)_0$, $p$, $t_i$, $B$))
            &: cal(C)_p(dnt(sans(S)_0), sans(B) ⊕ sans(L) ⊕ dnt(sans(S)_0))
        $
]

#substitution-stmt
#proof[
    We proceed by mutual induction on derivations $istm(Γ, p, a, A)$, $isblk(Γ, sans(L), p, t, B)$ given a substitution $issub(γ, Θ, Γ)$
    - #rname("var"): By semantic substitution weakening, we have
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, x, A)) #h(5em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dwng(purity: p, dnt(#dropctx($Γ$, $thyp(x, A, ∅)$)))
        & "by definition"
        \ &= dnt(dropctx(Θ, Θ_x));dwng(purity: p, dnt(#issub($γ_x$, $Θ_x$, $thyp(x, A, ∅)$)))
        & "by semantic substitution weakening"
        \ &= dnt(dropctx(Θ, Θ_x));dnt(istm(Θ_x, p, [γ]x, A))
        & "by definition"
        \ &= dnt(istm(Θ, p, [γ]x, A))
        & "by semantic weakening"
        $
    - #rname("app"): We have that
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, f aq a, B)) #h(5em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, a, A));instof(p, f)
        & "by definition"
        \ &= dnt(istm(Θ, p, [γ]a, A));instof(p, f)
        & "by induction"
        \ &= dnt(istm(Θ, p, [γ]f aq a, B))
        & "by definition" 
        $
    - #rname("nil"), #rname("true"), #rname("false"): each of these cases holds trivially by virtue of the fact that, by semantic substitution weakening,
    $
        dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(dropctx(Γ, cnil)) = dnt(dropctx(Θ, cnil))
    $  
    - #rname("pair"): We have that
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, (a, b), A ⊗ B)) #h(15em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(istm(Δ, p, a, A)) ⋉ dnt(istm(Ξ, p, b, B))
        & "by definition"
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting" 
        \ & #h(4em) dnt(istm(Δ, p, a, A)) ⋉ dnt(istm(Ξ, p, b, B))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
        & "by centrality"
        \ & #h(4em) (dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ)));dnt(istm(Δ, p, a, A))) ⋉ (dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));dnt(istm(Ξ, p, b, B))) 
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(istm(Θ_Δ, p, [γ]a, A)) ⋉ dnt(istm(Θ_Ξ, p, [γ]b, B))
        & "by induction"
        \ &= dnt(istm(Θ, p, [γ](a, b), A ⊗ B))
        & "by definition"
        $
    - #rname("let"): 
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(#istm($Γ$, $p$, $llet x = a; e$, $B$)) #h(15em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));dnt(#istm($Δ, thyp(x, A)$, $p$, $e$, $B$))
        & "by definition"
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)))
        & "by splitting" 
        \ #h(5em) dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));dnt(#istm($Ξ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ))); dnt(Δ) ⊗ (dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        dnt(istm(Ξ, p, a, A)));
        & "by centrality"
        \ #h(5em) dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dnt(A); dnt(#istm($Δ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ))); dnt(Δ) ⊗ (dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        dnt(istm(Ξ, p, a, A)));
        & "by definition"
        \ #h(5em) dwng(purity: p, dnt(issub(slft(γ_Δ), (Θ_Δ, thyp(x, A)), (Δ, thyp(x, A))))); dnt(#istm($Δ, thyp(x, A)$, $p$, $e$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Δ) ⊗ dnt(istm(Θ_Ξ, p, [γ]a, A));dnt(#istm($Θ_Δ, thyp(x, A)$, $p$, $[γ]e$, $B$))
        & "by induction"
        \ &= dnt(#istm($Θ$, $p$, $[γ](llet x = a; e)$, $B$))
        & "by definition"
        $
    - #rname("let2"): 
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(#istm($Γ$, $p$, $llet (x, y) = e; e'$, $C$)) #h(15em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α;
        & "by definition"
        \ & #h(4em) dnt(#istm($Ξ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting" 
        \ #h(5em) dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α;dnt(#istm($Ξ, thyp(x, A), thyp(y, B)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Δ) ⊗ (dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ)));
        dnt(istm(Ξ, p, e, A ⊗ B)));α;
        & "by centrality"
        \ #h(5em) dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dnt(A) ⊗ dnt(B);α; dnt(#istm($Δ, thyp(x, A), thyp(y, A)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Δ) ⊗ (dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ)));
        dnt(istm(Ξ, p, e, A ⊗ B)));α;
        & "by definition"
        \ #h(5em) dwng(purity: p, dnt(issub(slft(slft(γ_Δ)), (Θ_Δ, thyp(x, A), thyp(y, B)), (Δ, thyp(x, A), thyp(y, B)))));α^⊗; dnt(#istm($Δ, thyp(x, A), thyp(y, A)$, $p$, $e'$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, [γ]e, A ⊗ B));α^⊗;dnt(#istm($Θ_Δ, thyp(x, A), thyp(y, A)$, $p$, $[γ]e'$, $C$))
        & "by induction"
        \ &= dnt(#istm($Θ$, $p$, $[γ](llet (x, y) = e; e')$, $C$))
        & "by definition"
        $
    - #rname("blk"): We have that
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, {t}, B)) #h(10em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(isblk(Γ, bcnil, p, t, B));α^⊕
        & "by definition"
        \ &= dnt(isblk(Θ, bcnil, p, [γ]t, B));B ⊕ dwng(purity: p, labmap(bcnil, γ));α^⊕
        & "by induction"
        \ &= dnt(isblk(Θ, bcnil, p, [γ]t, B));α^⊕
        & "by definition"
        \ &= dnt(istm(Θ, p, [γ]{t}, B))
        & "by definition, as desired"
        $
    - #rname("br"): We have that
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(isblk(Γ, sans(L), p, br(a), A)) #h(10em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(istm(Γ, p, a, A));α^⊕;dnt(A) ⊕ 0_(dnt(sans(L)))
        & "by definition"
        \ &= dnt(istm(Θ, p, [γ]a, A));α^⊕;dnt(A) ⊕ 0_(dnt(sans(L)))
        & "by induction"
        \ &= dnt(istm(Θ, p, [γ]a, A));α^⊕;dnt(A) ⊕ 0_(dnt([γ]sans(L)));dnt(A) ⊕ dwng(purity: p, labmap(sans(L), γ))
        & "by absorption"
        \ &= dnt(isblk(Θ, [γ]sans(L), p, [γ]br(a), A));dnt(A) ⊕ dwng(purity: p, labmap(sans(L), γ))
        & "by definition"
        $
    - #rname("jmp"): We have that
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));
            dnt(isblk(Γ, sans(L), p, br(lbl(ℓ), a), B)) #h(16em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));
            dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p , a, A));
        & "by definition"
        \ &   #h(5em)
            α^⊕;
            0_(dnt(B)) ⊕ dwng(purity: p,dnt(joinctx(lhyp(Δ, lbl(ℓ), p, A), sans(L))))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(issub(y_Δ, Θ_Δ, Δ)) ⊗
            dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting"
        \ &   #h(5em)
            dnt(Δ) ⊗ dnt(istm(Ξ, p , a, A));
            α^⊕;
            0_(dnt(B)) ⊕ dwng(purity: p,dnt(joinctx(lhyp(Δ, lbl(ℓ), p, A), sans(L))))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dnt(istm(Θ_Ξ, p, [γ]a, A));
        & "by induction"
        \ & #h(5em)
            α^⊕;
            0_(dnt(B)) ⊕ dwng(purity: p,dnt(joinctx(lhyp(Δ, lbl(ℓ), p, A), sans(L))))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p , [γ]a, A));
        & "by definition"
        \ & #h(5em)
            α^⊕;
             0_(dnt(B)) ⊕ dwng(purity: p, dnt(joinctx(lhyp(Θ_Δ, lbl(ℓ), p, A), [γ]sans(L))));dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
        \ &= dnt(isblk(Θ, [γ]sans(L), p, br(lbl(ℓ), a), B));dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
        & "by definition"
        $
    - #rname("ite"): 
        $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(isblk(Γ, sans(L), p, lite(e, s, t), B)) #h(14em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));dnt(istm(Δ, p, e, bools)) ⊗ dnt(Ξ);
        & "by definition"
        \ & #h(5em) smite(dnt(Ξ));
        dnt(isblk(Ξ, sans(L), p, s, B)) ⊕
        dnt(isblk(Ξ, sans(L), p, t, B))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ))); 
            dwng(purity: p, dnt(issub(y_Δ, Θ_Δ, Δ))) ⊗
            dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting"
        \ & #h(5em) 
        dnt(istm(Δ, p, e, bools)) ⊗ dnt(Ξ); smite(dnt(Ξ));
        dnt(isblk(Ξ, sans(L), p, s, B)) ⊕
        dnt(isblk(Ξ, sans(L), p, t, B))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(istm(Θ_Δ, p, [γ]e, bools)) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by induction"
        \ & #h(5em) smite(dnt(Ξ));
        dnt(isblk(Ξ, sans(L), p, s, B)) ⊕
        dnt(isblk(Ξ, sans(L), p, t, B))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(istm(Θ_Δ, p, [γ]e, bools)) ⊗ dnt(Θ_Ξ);
        & "by distribution"
        \ & #h(5em) smite(dnt(Θ_Ξ));
        (dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));dnt(isblk(Ξ, sans(L), p, s, B))) ⊕
        (dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));dnt(isblk(Ξ, sans(L), p, t, B)))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
             dnt(istm(Θ_Δ, p, [γ]e, bools)) ⊗ dnt(Θ_Ξ);
        & "by induction"
        \ & #h(5em) smite(dnt(Ξ));
        (dnt(isblk(Θ_Ξ, [γ]sans(L), p, [γ]s, B)); dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))) 
        \ & #h(7em) ⊕
        (dnt(isblk(Θ_Ξ, [γ]sans(L), p, [γ]t, B)); dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ)))        
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
             dnt(istm(Θ_Δ, p, [γ]e, bools)) ⊗ dnt(Θ_Ξ);
        & "by distribution"
        \ & #h(5em) smite(dnt(Ξ));
        dnt(isblk(Θ_Ξ, [γ]sans(L), p, [γ]s, B)) ⊕
        dnt(isblk(Θ_Ξ, [γ]sans(L), p, [γ]t, B));
        dwng(purity: p, labmap(sans(L), γ)) ⊕ dnt(B)
        \ &= dnt(isblk(Θ, [γ]sans(L), p, [γ](lite(e, s, t)), B));
        dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
        & "by definition"
        $
    - #rname("let-blk"): We have
    $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));
        dnt(#isblk($Γ$, $sans(L)$, $p$, $llet x = a; t$, $B$)) #h(17em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));
            dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));
            dnt(#isblk($Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        & "by definition"
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting"
        \ #h(5em)
            dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));
            dnt(#isblk($Δ, thyp(x, A)$, $sans(L)$, $p$, $t$, $B$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, [γ]a, A));
        & "by induction"
        \ #h(5em)
            dnt(#isblk($Θ_Δ, thyp(x, A)$, $[γ]sans(L)$, $p$, $t[γ]$, $B$)); 
            dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
        \ &= dnt(#isblk($Θ$, $[γ]sans(L)$, $p$, $[γ](llet x = a; t)$, $B$)); dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
        & "by definition"
    $
    - #rname("let2-blk"): We have
    $
        & dwng(purity: p, dnt(issub(γ, Θ, Γ)));
        dnt(#isblk($Γ$, $sans(L)$, $p$, $llet (x, y) = e; t$, $C$)) #h(16em) &
        \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));
            dwng(purity: p, dnt(splitctx(Γ, Δ, Ξ)));
            dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α;
        & "by definition"
        \ & #h(4em) dnt(#isblk($Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dwng(purity: p, dnt(issub(γ_Δ, Θ_Δ, Δ))) ⊗ dwng(purity: p, dnt(issub(γ_Ξ, Θ_Ξ, Ξ)));
        & "by splitting"
        \ #h(5em)
            dnt(Δ) ⊗ dnt(istm(Ξ, p, e, A ⊗ B));α^⊗;dnt(#isblk($Δ, thyp(x, A), thyp(y, B)$, $sans(L)$, $p$, $t$, $C$))
        \ &= dwng(purity: p, dnt(splitctx(Θ, Θ_Δ, Θ_Ξ)));
            dnt(Θ_Δ) ⊗ dnt(istm(Θ_Ξ, p, [γ]e, A ⊗ B));α^⊗;
        & "by induction"
        \ #h(5em)
            dnt(#isblk($Θ_Δ, thyp(x, A), thyp(y, B)$, $[γ]sans(L)$, $p$, $t[γ]$, $C$)); 
            dnt(B) ⊗ dwng(purity: p, labmap(sans(L), γ))
        \ &= dnt(#isblk($Θ$, $[γ]sans(L)$, $p$, $[γ](llet (x, y) = e; t)$, $C$)); 
            dnt(B) ⊗ dwng(purity: p, labmap(sans(L), γ))
        & "by definition"
    $ 
    - #rname("tr"): Let
    $
    sans(S)_0 &= [lhyp(Δ_j, ∅, lbl(ℓ)_j, A_j)]_j \
    sans(S) &= [lhyp(Δ_j, p_j, lbl(ℓ)_j, A_j)]_j \
    D &= α^⊕ ∘ j^i ∘ plus.circle.big_i dnt(#isblk($Δ_i, thyp(x_i, A_i)$, $sans(S)_0, sans(L)$, $p$, $t_i$, $B$))
        &: cal(C)_p(dnt(sans(S)_0), dnt(B) ⊕ dnt(sans(L)) ⊕ dnt(sans(S)_0)) \
    D_γ &= α^⊕ ∘ j^n ∘ plus.circle.big_i dnt(#isblk($Θ_(Δ_i), thyp(x_i, A_i)$, $[γ]sans(S)_0, [γ]sans(L)$, $p$, $[γ]t_i$, $B$)): cal(C)_p(dnt([γ]B) ⊕ dnt([γ]sans(L)) ⊕ dnt([γ]sans(S)_0))
    $
    We note that $dnt(sans(S)) = dnt(sans(S)_0)$, and that
    $
    & dwng(purity: p, labmap(sans(S)_0, γ));D #h(27em) &
    \ &= α^⊕ ∘ j^n ∘ (dwng(purity: p, labmap(sans(S)_0, γ)); plus.circle.big_i [dnt(#isblk($x: A_i, Δ_i$, $sans(S)_0, sans(L)$, $p$, $t_i$, $B$))])
    & "by definition"
    \ &= α^⊕ ∘ j^n ∘ plus.circle.big_i [dnt(A_i) ⊗ dwng(purity: p, dnt(issub(γ_(Δ_i), Θ_(Δ_i), Δ_i))); dnt(#isblk($x: A_i, Δ_i$, $sans(S)_0, sans(L)$, $p$, $t_i$, $B$))]
    & "by definition"
    \ &= α^⊕ ∘ j^n ∘ plus.circle.big_i  [dnt(#isblk($x: A_i, Θ_(Δ_i)$, $[γ]sans(S)_0, [γ]sans(L)$, $p$, $[γ]t_i$, $B$)); 
    & "by induction"
    \ & #h(8em) dwng(purity: p, labmap(sans(S)_0, γ)) ⊕ dwng(purity: p, labmap(sans(L), γ)) ⊕ dnt(B)]
    \ &= (α^⊕ ∘ j^n ∘ plus.circle.big_i  [dnt(#isblk($x: A_i, Θ_(Δ_i)$, $[γ]sans(S)_0, [γ]sans(L)$, $p$, $[γ]t_i$, $B$))]); 
    & "by distribution"
    \ & #h(4em) dwng(purity: p, labmap(sans(L), γ)) ⊕ dnt(B) ⊕ dwng(purity: p, labmap(sans(S)_0, γ))
    \ &= D_γ;dwng(purity: p, labmap(sans(L), γ)) ⊕ dnt(B) ⊕ dwng(purity: p, labmap(sans(S)_0, γ))
    & "by definition"
    $
    It follows that
    $
    & dwng(purity: p, labmap(sans(S)_0, γ));sans("Tr")_(dnt(sans(S)), dnt(B) ⊕ dnt(sans(L)))^(dnt(sans(S)))(j;D)
    \ &= sans("Tr")_(dnt([γ]sans(S)), dnt(B) ⊕ dnt(sans(L)))^(dnt([γ]sans(S)))(j;D_γ;dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ)) ⊕ dnt(sans(S)))
    \ &= sans("Tr")_(dnt([γ]sans(S)), dnt(B) ⊕ dnt([γ]sans(L)))^(dnt([γ]sans(S)))(j;D_γ);dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
    $
    Therefore, we have that
    $
    & dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(#isblk($Γ$, $sans(L)$, $p$, $llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; s$, $B$))
    #h(10em) & 
    \ &= dwng(purity: p, dnt(issub(γ, Θ, Γ)));dnt(#isblk($Γ$, $sans(S), sans(L)$, $p$, $s$, $B$));α^⊕;sans(L) ⊕ sans(B) ⊕ sans("Tr")_(dnt(sans(S)), dnt(sans(B)) ⊕ dnt(L))^(dnt(sans(S)))(j;D);j
    & "by definition" \
    \ &= dnt(#isblk($Θ$, $[γ]sans(S), [γ]sans(L)$, $p$, $[γ]s$, $B$));
        dnt(B) ⊕ dwng(purity: p, labmap((sans(S), sans(L)), γ));α^⊕;
    & "by induction"
    \ & #h(4em) 
        dnt(B) ⊕ dnt(sans(L)) ⊕ sans("Tr")_(dnt(sans(S)), dnt(sans(B)) ⊕ dnt(L))^(dnt(sans(S)))(j;D);j
    \ &= dnt(#isblk($Θ$, $[γ]sans(S), [γ]sans(L)$, $p$, $[γ]s$, $B$));α^⊕;
    & "by association"
    \ & #h(4em) 
        dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ)); ⊕ (dwng(purity: p, labmap(sans(S)_0, γ));sans("Tr")_(dnt(sans(S)), dnt(sans(B)) ⊕ dnt(L))^(dnt(sans(S)))(j;D);j)
    \ &= dnt(#isblk($Θ$, $[γ]sans(S), [γ]sans(L)$, $p$, $[γ]s$, $B$));α^⊕;σ^⊕;
    \ #h(5em) dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ)) ⊕ (sans("Tr")_(dnt([γ]sans(S)), dnt([γ]sans(L)) ⊕ dnt(B))^(dnt([γ]sans(S)))(j;D_γ);dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ)));j
    \ &= dnt(#isblk($Θ$, $[γ]sans(S), [γ]sans(L)$, $p$, $[γ]s$, $B$));α^⊕;dnt(B) ⊕ dnt(sans(L)) ⊕ sans("Tr")_(dnt([γ]sans(S)), dnt(B) ⊕ dnt([γ]sans(L)))^(dnt([γ]sans(S)))(j;D_γ);j;
    & "by distribution"
    \ & #h(4em) dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
    \ &= dnt(#isblk($Θ$, $[γ]sans(L)$, $p$, $[γ](llet [lbl(ℓ)_j(x_j: A_j) => {t_j}]_j; s)$, $B$));dnt(B) ⊕ dwng(purity: p, labmap(sans(L), γ))
    & "by definition"
    $
]