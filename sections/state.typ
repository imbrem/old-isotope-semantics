#import "../isotope.typ": *

= State-Passing

== Syntactic State-Passing Category

Let $cal(C)_0 -> cal(C)_1$ be a symmetric effectful category enriched over posets. We define an _ordered string diagram_ from $A$ to $B$ over $cal(C)$ to be given by the following grammar
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
            ($idm_A: cal(D)(A, A)$),
            ($f;g: cal(D)(A, C) quad (∀f ∈ cal(D)(A, B), g ∈ cal(D)(B, C))$,),
            ($f ⊗ C: cal(D)(A ⊗ C, B ⊗ C) quad (∀f ∈ cal(D)(A, B))$),
            ($C ⊗ f: cal(D)(C ⊗ A, C ⊗ B) quad (∀f ∈ cal(D)(A, B))$),
            ($α_(A, B, C): cal(D)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C))$),
            ($α_(A, B, C)^(-1): cal(D)(A ⊗ (B ⊗ C), (A ⊗ B) ⊗ C)$),
            ($λ_A: cal(D)(I ⊗ A, A)$, $λ_A^(-1): cal(D)(A, I ⊗ A)$),
            ($ρ_A: cal(D)(A ⊗ I, A)$, $ρ_A^(-1): cal(D)(A, A ⊗ I)$),
            ($σ_(A, B): cal(D)(A ⊗ B, B ⊗ A)$),
            ($j: cal(D)(S ⊗ S, S)$, $s: cal(D)(S, S ⊗ S)$),
            ($ul(f): cal(D)(ul(A), ul(B)) quad (∀f ∈ cal(C)_0(A, B))$,),
            ($[f]: cal(D)(ul(A) ⊗ S, ul(B) ⊗ S) quad (∀f ∈ cal(C)_1(A, B))$,),
        )
    )
);
#grammar(state-passing-grammar)
quotiented such that $ul(A ⊗ B) = ul(A) ⊗ ul(B)$ and $ul(I) = I$.

We may now define a preorder on ordered string diagrams to be the smallest preorder containing the following, where $≃$ denotes equivalence:
- Category: $idm;f ≃ f;idm ≃ f, quad f;(g;h) ≃ (f;g);h$
- Symmetric monoidal category: 
    - Functoriality of $⊗$: 
        - $idm ⊗ A ≃ idm, quad A ⊗idm ≃ idm$
        - $(f;g) ⊗ A ≃ f ⊗ A;g ⊗ A, quad A ⊗ (f;g) ≃ A ⊗ f;A ⊗ g$
    - Sliding: $f ⊗ B;A' ⊗ g ≃ A ⊗ g;f ⊗ B'$; we write this morphism as $f ⊗ g$
    - Natural isomorphisms:
        - $α;α^(-1) ≃ idm$, $α^(-1);α ≃ idm$, $ρ;ρ^(-1) ≃ idm$, $ρ^(-1);ρ ≃ idm$, $λ;λ^(-1) ≃ idm$, $λ^(-1);λ ≃ idm$, $σ;σ ≃ idm$
        - $(f ⊗ g) ⊗ h;α ≃ α;f ⊗ (g ⊗ h)$, or, equivalently,
            - $(f ⊗ B) ⊗ C;α ≃ α;f ⊗ (B ⊗ C)$
            - $(A ⊗ f) ⊗ C;α ≃ α;A ⊗ (f ⊗ C)$
            - $(A ⊗ B) ⊗ f;α ≃ α;A ⊗ (B ⊗ f)$
        - $λ;f ≃ I ⊗ f;λ$, $ρ;f ≃ f ⊗ I;ρ$
        - $f ⊗ g;σ ≃ σ;g ⊗ f$, or, equivalently, $A ⊗ f;σ ≃ σ;f ⊗ A$, $f ⊗ B;σ ≃ σ;B ⊗ f$
    - Triangle: $α_(A, I, B);A ⊗ λ ≃ ρ ⊗ B$
    - Pentagon: $α_(A ⊗ B, C, D);α_(A, B, C ⊗ D) ≃ α_(A, B, C) ⊗ D;α_(A, B ⊗ C, D);A ⊗α_(B, C, D)$
    - Hexagon: $α_(A, B, C);σ_(A, B ⊗ C);α_(B, C, A) ≃ σ_(A, B) ⊗ C;α_(B, A, C);B ⊗ σ_(A, C)$
- Compatibility with $cal(C_0)$: 
    - $ul(dot)$ is a functor: $ul(idm) ≃ idm, quad ul(f);ul(g) ≃ ul(#$f;g$)$
    - $ul(dot)$ is an enriched functor: $f refines g ==> ul(f) refines ul(g)$
    - $ul(dot)$ is a strict monoidal functor: $ul(f ⊗ g) ≃ ul(f) ⊗ ul(g), quad ul(α) = α, quad ul(λ) = λ, quad ul(ρ) = ρ, quad ul(σ) = σ$
- Compatibility with $cal(C_1)$: $[idm] = idm, quad [f; g] refines [f];[g], quad f refines g ==> [f] refines [g]$
- Compatibility with $ι: cal(C_0) -> cal(C_1)$: $[ι f] = ul(f) ⊗ S$
- Join/split:
    - $s;σ ≃ s, quad σ;j ≃ j, quad s;j ≃ idm, quad idm refines j;s$
    - $s;S ⊗ s ≃ s;s ⊗ S;α, quad j ⊗ S;j ≃ α;S ⊗ j;j$
We note that _equivalence classes_ of morphisms $cal(D)(A, B)$, which we will write $cal(R)(A, B)$, trivially form a symmetric monoidal category with composition $;$ and tensor product $⊗$.

We define the _interpretation_ $dnt(A): |cal(C)|$ of objects $A ∈ |cal(D)|$ and morphisms $dnt(f): cal(C)(dnt(A), dnt(B))$ of morphisms $f: cal(D)(A, B)$ as follows:
$
dnt(ul(A)) = A, quad dnt(A ⊗ B) = dnt(A) ⊗ dnt(B), quad dnt(S) = dnt(I) = I
$
$
dnt(idm_A) = idm_dnt(A), quad
dnt(#$f;g$) = dnt(f);dnt(g), quad
dnt(f ⊗ C) = dnt(f) ⊗ dnt(C), quad
dnt(C ⊗ f) = dnt(C) ⊗ dnt(f)
$
$
dnt(α_(A, B, C)) = α_(dnt(A), dnt(B), dnt(C)), quad
dnt(α_(A, B, C))^(-1) = α_(dnt(A), dnt(B), dnt(C))^(-1)
$
$
dnt(λ_A) = λ_dnt(A), quad
dnt(λ_A)^(-1) = λ_dnt(A)^(-1), quad
dnt(ρ_A) = ρ_dnt(A), quad
dnt(ρ_A)^(-1) = ρ_dnt(A)^(-1), quad
dnt(σ_(A, B)) = σ_(dnt(A), dnt(B))
$
$
$
dnt(j) = λ_I, quad dnt(s) = λ_I^(-1), quad dnt(ul(f)) = f, quad dnt([f]) = f ⊗ I