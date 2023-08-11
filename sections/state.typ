#import "../isotope.typ": *

= State-Passing

== Syntactic State-Passing Category

Let $ι: cal(C)_0 -> cal(C)_1$ be a symmetric effectful category enriched over posets. We define a category $cal(R)$ as follows:
#let state-passing-grammar = (
    (
        name: "Objects",
        symbol: ($A$, $B$, $C$),
        productions: (
            ($ul(X) quad (∀X ∈ |cal(C)|)$,),
            ($A ⊗ B$, $I$, $S$)
        )
    ),
    (
        name: "Morphisms",
        symbol: ($f$, $g$, $h$),
        productions: (
            ($idm_A: cal(R)(A, A)$),
            ($f;g: cal(R)(A, C) quad (∀f ∈ cal(R)(A, B), g ∈ cal(R)(B, C))$,),
            ($f ⊗ C: cal(R)(A ⊗ C, B ⊗ C) quad (∀f ∈ cal(R)(A, B))$),
            ($C ⊗ f: cal(R)(C ⊗ A, C ⊗ B) quad (∀f ∈ cal(R)(A, B))$),
            ($α_(A, B, C): cal(R)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C))$),
            ($α_(A, B, C)^(-1): cal(R)(A ⊗ (B ⊗ C), (A ⊗ B) ⊗ C)$),
            ($λ_A: cal(R)(I ⊗ A, A)$, $λ_A^(-1): cal(R)(A, I ⊗ A)$),
            ($ρ_A: cal(R)(A ⊗ I, A)$, $ρ_A^(-1): cal(R)(A, A ⊗ I)$),
            ($σ_(A, B): cal(R)(A ⊗ B, B ⊗ A)$),
            ($j: cal(R)(S ⊗ S, S)$, $s: cal(R)(S, S ⊗ S)$),
            ($ul(f): cal(R)(ul(A), ul(B)) quad (∀f ∈ cal(C)_0(A, B))$,),
            ($[f]: cal(R)(ul(A) ⊗ S, ul(B) ⊗ S) quad (∀f ∈ cal(C)_1(A, B))$,),
        )
    )
);
#grammar(state-passing-grammar)
This is quotiented as follows:
- Category: $idm;f = f;idm = f, quad f;(g;h) = (f;g);h$
- Symmetric monoidal category: 
    - Functoriality of $⊗$: 
        - $idm ⊗ A = idm, quad A ⊗idm = idm$
        - $(f;g) ⊗ A = f ⊗ A;g ⊗ A, quad A ⊗ (f;g) = A ⊗ f;A ⊗ g$
    - Sliding: $f ⊗ B;A' ⊗ g = A ⊗ g;f ⊗ B'$; we write this morphism as $f ⊗ g$
    - Natural isomorphisms:
        - $α;α^(-1) = idm$, $α^(-1);α = idm$, $ρ;ρ^(-1) = idm$, $ρ^(-1);ρ = idm$, $λ;λ^(-1) = idm$, $λ^(-1);λ = idm$, $σ;σ = idm$
        - $(f ⊗ g) ⊗ h;α = α;f ⊗ (g ⊗ h)$, or, equivalently,
            - $(f ⊗ B) ⊗ C;α = α;f ⊗ (B ⊗ C)$
            - $(A ⊗ f) ⊗ C;α = α;A ⊗ (f ⊗ C)$
            - $(A ⊗ B) ⊗ f;α = α;A ⊗ (B ⊗ f)$
        - $λ;f = I ⊗ f;λ$, $ρ;f = f ⊗ I;ρ$
        - $f ⊗ g;σ = σ;g ⊗ f$, or, equivalently, $A ⊗ f;σ = σ;f ⊗ A$, $f ⊗ B;σ = σ;B ⊗ f$
    - Triangle: $α_(A, I, B);A ⊗ λ = ρ ⊗ B$
    - Pentagon: $α_(A ⊗ B, C, D);α_(A, B, C ⊗ D) = α_(A, B, C) ⊗ D;α_(A, B ⊗ C, D);A ⊗α_(B, C, D)$
    - Hexagon: $α_(A, B, C);σ_(A, B ⊗ C);α_(B, C, A) = σ_(A, B) ⊗ C;α_(B, A, C);B ⊗ σ_(A, C)$
- Compatibility with $cal(C_0)$: 
    - $ul(dot)$ is a functor: $ul(idm) = idm, quad ul(f);ul(g) = ul(#$f;g$)$
    - $ul(dot)$ is an enriched functor: $f refines g ==> ul(f) refines ul(g)$
    - $ul(dot)$ is a strict monoidal functor: 
        - $ul(I) = I, quad ul(A ⊗ B) = ul(A) ⊗ ul(B)$
        - $ul(f ⊗ g) = ul(f) ⊗ ul(g), quad ul(α) = α, quad ul(λ) = λ, quad ul(ρ) = ρ, quad ul(σ) = σ$
- Compatibility with $cal(C_1)$: $[idm] = idm, quad [f; g] refines [f];[g], quad f refines g ==> [f] refines [g]$
- Compatibility with $ι: cal(C_0) -> cal(C_1)$: $[ι f] = ul(f) ⊗ S$
- Join/split:
    - $s;σ = s, quad σ;j = j, quad s;j = idm, quad idm refines j;s$
    - $s;S ⊗ s = s;s ⊗ S;α, quad j ⊗ S;j = α;S ⊗ j;j$

Let $cal(R)_0$ denote the full subcategory of $cal(R)$ with objects of the form $ul(A)$, and let $cal(R)_S$ denote the full subcategory on $|cal(R)| ∖ |cal(R)_0|$. It is easy to see by induction that, for all nonempty $cal(R)(A, B)$, $A ∈ |cal(R)_0| <==> B ∈ |cal(R)_0|$ and $A ∈ |cal(R)_S| <==> B ∈ |cal(R)_S|$.

#lemma[
    $ul(dot)$ is an isomorphism $cal(C)_0 ≃ cal(R)_0$
]
#proof[
    By our quotients, we have that $ul(dot): cal(C)_0 -> cal(R)_0$ is an enriched functor, and by definition, $ul(dot)$ is surjective on the objects of $cal(R)_0$. Hence, it suffices to show that
    - $ul(dot)$ is surjective on morphisms:
    - $∀f, g, ul(f) refines ul(g) ==> f refines g$:
]

== The Isotopy Category

Given a premonoidal category $cal(C)$, we define _formal string diagrams_ on $cal(C)$ to be expressions with the following grammar and typing rules
#let fin-diagram-grammar = (
    (
        name: "Contexts",
        symbol: ($Γ, Δ$),
        productions: (
            ($cnil$, $Γ, x: A -> B quad ∀A, B ∈ |cal(C)|$),
        )
    ),
    (
        name: "Morphisms",
        symbol: ($f$, $g$, $h$),
        productions: (
            ($x$, idm, $f;g$, $f ⊗ C$, $C ⊗ f$, $α$, $α^(-1)$, $ρ$, $ρ^(-1)$, $λ$, $λ^(-1)$, $σ$,),
        )
    )
);
#grammar(fin-diagram-grammar)
#let fin-diagram-rules = (
    "var": prft(name: "var", $x: A -> B ∈ Γ$, $Γ ⊢ x: A -> B$),
    "id": prft(name: "id", $Γ ⊢ idm: A -> A$),
    "comp": prft(name: "comp", $Γ ⊢ f: A -> B$, $Γ ⊢ g: B -> C$, $Γ ⊢ f;g: A -> C$),
    "left": prft(name: "left", $Γ ⊢ f: A -> B$, $Γ ⊢ f ⊗ C: A ⊗ C -> B ⊗ C$),
    "right": prft(name: "right", $Γ ⊢ f: A -> B$, $Γ ⊢ C ⊗ f: C ⊗ A -> C ⊗ B$),
    "α": prft(name: $α$, $Γ ⊢ α: (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C)$),
    "α-inv": prft(name: $α^(-1)$, $Γ ⊢ α^(-1): A ⊗ (B ⊗ C) -> (A ⊗ B) ⊗ C$),
    "ρ": prft(name: $ρ$, $Γ ⊢ ρ: A ⊗ I -> A$),
    "ρ-inv": prft(name: $ρ^(-1)$, $Γ ⊢ ρ^(-1): A -> A ⊗ I$),
    "λ": prft(name: $λ$, $Γ ⊢ λ: I ⊗ A -> A$),
    "λ-inv": prft(name: $λ^(-1)$, $Γ ⊢ λ^(-1): A -> I ⊗ A$),
    "σ": prft(name: $σ$, $Γ ⊢ σ: A ⊗ B -> B ⊗ A$),
)
quotiented as follows:
- Category: $idm;f = f;idm = f, quad f;(g;h) = (f;g);h$
- Symmetric premonoidal category: 
    - Functoriality of $⊗$: 
        - $idm ⊗ A = idm, quad A ⊗idm = idm$
        - $(f;g) ⊗ A = f ⊗ A;g ⊗ A, quad A ⊗ (f;g) = A ⊗ f;A ⊗ g$
    - Natural isomorphisms:
        - $α;α^(-1) = idm$, $α^(-1);α = idm$, $ρ;ρ^(-1) = idm$, $ρ^(-1);ρ = idm$, $λ;λ^(-1) = idm$, $λ^(-1);λ = idm$, $σ;σ = idm$
        - $(f ⊗ B) ⊗ C;α = α;f ⊗ (B ⊗ C)$
        - $(A ⊗ f) ⊗ C;α = α;A ⊗ (f ⊗ C)$
        - $(A ⊗ B) ⊗ f;α = α;A ⊗ (B ⊗ f)$
        - $λ;f = I ⊗ f;λ$, $ρ;f = f ⊗ I;ρ$
        - $A ⊗ f;σ = σ;f ⊗ A$, $f ⊗ B;σ = σ;B ⊗ f$
    - Centrality: $∀c ∈ {α, α^(-1), ρ, ρ^(-1), λ, λ^(-1), σ}$, $c ⊗ B;A' ⊗ f = A ⊗ f;c ⊗ B$
    - Triangle: $α_(A, I, B);A ⊗ λ = ρ ⊗ B$
    - Pentagon: $α_(A ⊗ B, C, D);α_(A, B, C ⊗ D) = α_(A, B, C) ⊗ D;α_(A, B ⊗ C, D);A ⊗α_(B, C, D)$
    - Hexagon: $α_(A, B, C);σ_(A, B ⊗ C);α_(B, C, A) = σ_(A, B) ⊗ C;α_(B, A, C);B ⊗ σ_(A, C)$

Given a context $Γ$, we define the set of valid interpretations of $Γ$, $dnt(Γ)$, to be the set of functions mapping each $x: A -> B ∈ Γ$ to a morphism $cal(C)(A, B)$.
We now give typing rules and semantics for formal string diagrams as follows:
#align(center, table(
    align: center + horizon, stroke: table-dbg, gutter: 1em,
    rect($dnt(Γ ⊢ f: A -> B): dnt(Γ) -> cal(C)(A, B)$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#fin-diagram-rules.var)) = λ G. G(x)$,
        $dnt(dprf(#fin-diagram-rules.id)) = λ . idm$,
    ),
    $dnt(dprf(#fin-diagram-rules.comp)) = λ G. dnt(Γ ⊢ f: A -> B)(G);dnt(Γ ⊢ g: B -> C)(G)$,
    $dnt(dprf(#fin-diagram-rules.left)) = λ G. dnt(Γ ⊢ f: A -> B)(G) ⊗ C$,
    $dnt(dprf(#fin-diagram-rules.right)) = λ G. C ⊗ dnt(Γ ⊢ f: A -> B)(G)$,
    $dnt(dprf(#fin-diagram-rules.α)) = λ.α$,
    $dnt(dprf(#fin-diagram-rules.α-inv)) = λ.α^(-1)$,
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#fin-diagram-rules.ρ)) = λ.ρ$,
        $dnt(dprf(#fin-diagram-rules.ρ-inv)) = λ.ρ^(-1)$,
    ),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#fin-diagram-rules.λ)) = λ.λ$,
        $dnt(dprf(#fin-diagram-rules.λ-inv)) = λ.λ^(-1)$,
    ),
    $dnt(dprf(#fin-diagram-rules.σ)) = λ.σ$,
))
Let $sans("String")_cal(C)[Γ](A, B)$ denote the set of formal string diagrams $f$ such that $Γ ⊢ f: A -> B$.

We define the _isotopy relation_ between two formal string diagrams $f, g ∈ sans("String")_cal(C)[Γ](A, B)$, written $f ≃ g$ and pronounced "$f$ is _isotopic_ to $g$", to be the smallest equivalence relation containing the following:
- Congruence: $f ≃ g ∧ f' ≃ g' ==> f;g ≃ f';g', quad f ⊗ C ≃ f' ⊗ C, quad C ⊗ f ≃ C ⊗ f'$
- Sliding: $f ⊗ B;A' ⊗ g ≃ A ⊗ g;f ⊗ B'$

//TODO: check premonoidal stuff 

We say two elements $f, g ∈ cal(C)(A, B)$ are _isotopic_, written $f ≃_sans("iso") g$, if 
$
∃Γ, ∃s_f, s_g ∈ sans("String")_cal(C)[Γ](A, B), ∃G, s_f ≃ s_g ∧ s_f (G) = f ∧ s_g (G) = g
$
We say a set $F ⊆ cal(C)(A, B)$ is _isotopic_ if
$∀f, g ∈ F, f ≃_sans("iso") g$.
// We say a set $F ⊆ cal(C)(A, B)$ is _strongly isotopic_ if there exists a context $Γ$ and a nonempty set $S_F ⊆ sans("String")_cal(C)[Γ](A, B)$ such that:
// - $∀f, g ∈ S_F, f ≃ g$
// - $∃G ∈ dnt(Γ), F = {f(G) | f ∈ S_F}$
We note in particular that 
- $∀f ∈ cal(C)(A, B)$, ${f}$ is isotopic (take $S_F = {x}$, $Γ = x: A -> B$, and $G = {x ↦ f}$).
- If $F ⊆ cal(C)(A, B)$, $G ⊆ cal(C)(B, C)$ are isotopic, then their pointwise composition is isotopic since
    $
    & ∀ (f;g), (f';g') ∈ F;G, f ≃_sans("iso") f' ∧ g ≃_sans("iso") g' \
    & ==> ∃Δ,Ξ,
        Δ ∩ Ξ = ∅ ∧ 
        ∃s_f, s_f' ∈ sans("String")_cal(C)[Δ](A, B), 
        ∃s_g, s_g' ∈ sans("String")_cal(C)[Ξ](A, B),
        ∃D, E, \
    & #h(4em) s_f ≃ s_f' ∧ s_g ≃ s_g' ∧ s_f (D) = f ∧ s_f' (D) = f' ∧ s_g (E) = g ∧ s_g' (E) = g' \
    & ==> s_f;s_g ≃ s_f';s_g' ∧ (s_f;s_g)(D, E) = f;g ∧ (s_f';s_g')(D, E) = f';g' \
    & ==> f;g ≃_sans("iso") f';g'
    $
- If $cal(C)$ is symmetric monoidal, then $F$ is isotopic if and only if it is empty or a singleton, since
    $
    ∀f, g ∈ sans("String")[Γ](A, B), f ≃ g ==> ∀G ∈ dnt(Γ), f(G) = g(G)   
    $
We may hence define the _category of isotopic sets over $cal(C)$_, $isoc(cal(C))$, to be the category with objects $|isoc(cal(C))| = |cal(C)|$ and morphisms $isoc(cal(C))(A, B) = {F ⊆ cal(C)(A, B) | F ≠ ∅ "is isotopic"}$, with composition defined pointwise and identity ${idm}$.

// This category is a:
// - Symmetric premonoidal category: //TODO: this 
// //TODO: other stuff?

// If $cal(C)$ is enriched over posets, we may enrich the category of isotopy classes in the following manners:

// - Pointwise enrichment: //TODO: this and name
// - Full enrichment: //TODO: this and name

// There exists a functor $cal(R)_S -> cal(C)^sans("iso")$...

// //TODO: relationship to $[dot]$

// There exists an identity-on-objects enriched functor ${dot}: cal(C) -> cal(C)^sans("iso")$...

// //TODO: ...

// Let $Σ: cal(C)^sans("iso") -> cal(C)$ be an enrichsed functor such that ${dot};Σ = idm$ and $idm refines Σ;{dot}$...

// //TODO: ...

// Then there exists an isomorphism $cal(R)_S ≃ cal(C)$...

// //TODO: ...