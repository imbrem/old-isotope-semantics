#import "../isotope.typ": *
#import "syntax.typ": rel-rules, aff-rules, typing-rules, subst-rules

= Semantics

== Isotope Models

An *`isotope` model* is given by:
- Categories $cal(C)_{cen}, cal(C)_∅$ with coproducts enriched over posets, the *control category*, such that: 
    - $cal(C)_{cen}$ has a trace
    - $cal(C)_∅$ has a guarded trace (this can be vacuous)
    - $cal(C)_∅$ is a wide subcategory of $cal(C)_{cen}$
    //TODO: list out all ite properties; or generalize over control structures?
    - For each $A$, there exist morphisms $sans("ite"): cal(C)_∅(E(K(bools ⊗ A)), E(K(A)) ⊕ E(K(A)))$ such that $sans("ite");E(f) ⊕ E(f) = E(bools ⊗ f);sans("ite")$
    //TODO: structure on clamp so this stops being a problem?
    - Full subcategories $cal(C)_p'$ of $cal(C)_p$ such that $r ⊆ p ==> cal(C)_r' ⊆ cal(C)_r$
- An symmetric effectful category $cal(V) -> cal(R)$ enriched over posets, the *expression category*, equipped with
    - For every droppable base type $A$, a pure morphism $sans("drop")(A): cal(V)(sans("base")(A), I)$
    - For every splittable base type $A$, a pure morphism $sans("split")(A): cal(V)(sans("base")(A), sans("base")(A) ⊗ sans("base")(A))$, such that:
        - Commutativity: $sans("split")(A);σ = sans("split")(A)$
        - Associativity: 
        $
        sans("split")(A);dnt(A) ⊗ sans("split")(A)
        = sans("split")(A);sans("split")(A) ⊗ dnt(A);α
        $
        - Unit: if $A$ is droppable, $sans("split")(A);(sans("drop")(A) ⊗ dnt(A)) = idm$
    - Full subcategories $cal(V)_cal(C), cal(R)_cal(C)$ such that $cal(V)_cal(C)$ and $cal(R)_cal(C)$ share objects, with $iobj, bools ∈ |cal(R)_cal(C)|$ //TODO: need this be full? only allow clamped and nil?
    - A mapping $K: |cal(R)| -> |cal(R)_cal(C)|$ satisfying: 
        - $K_|cal(R)_cal(C)| = idm$
        - $K(A ⊗ B) = K(A) ⊗ K(B)$ //TODO: generalize to just requiring a natural isomorphism?
    - For all $A ∈ |cal(R)|$, central morphisms *clamp* $k_(A, K(A))$ and *unclamp* $u_(K(A), A)$ such that:
        - $k;u;k = k, u;k;u = u$
        - For all pure morphisms $f ∈ cal(V)(A, B)$, $underline(f);k;u = k;u;underline(f)$
        - For all morphisms $f, g$, $f;g ≥ f;k;u;g$ // "SSA condition"
    - An enriched isomorphism of categories $E_{cen}: cal(R)_cal(C) ≃ cal(C)_{cen}'$
    - An enriched isomorphism of categories $E_∅: cal(V)_cal(C) ≃ cal(C)_∅'$
We define, for purities $p ⊆ {cen}$,
$
cal(C)_∅ = cal(R)_∅ = cal(V)
$
We let $upg(dot, p)$ be the functor sending $cal(R)_r$ to $cal(R)_p$ or $cal(C)_r$ to $cal(C)_p$.

An `isotope` model is *graphical* if $cal(R)$ is monoidal. An `isotope` model is *simple* if $cal(R) = cal(C)$ and $K, k, u$ are the identity. An `isotope` model is *flat* if $k_(K(A), K(K(A))), u_(K(K(A)), K(A))$ are the identity. An `isotope` model is *straight* if $K$ is the identity.

Given a symmetric effectful category $cal(V) -> cal(C)$ with coproducts and an Elgot operator, we can construct a simple `isotope` model by taking $cal(R) = cal(C)$ and $K, k, u$ the identity (with the discrete order on each hom-set).

// If $cal(V) -> cal(C)$ is enriched over posets and equipped with an operation $Σ$ which takes sets of permutations $f ⋉ g, f ⋊ g$ to morphisms such that
// $∀h ∈ P, Σ P ≥ h $
// then we may construct, for each $Σ$, the *$Σ$-graphical `isotope` model*.

== Denotational Semantics

#let table-dbg = none

=== Types and Contexts

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    rect($dnt(A): |cal(V)|$),
    table(
        columns: 4, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(X) = sans("base")(X)$,
        $dnt(tobj) = tobj$,
        $dnt(bools) = bools$,
        $dnt(A ⊗ B) = dnt(A) ⊗ dnt(B)$,
    ),
    rect($dnt(Γ): |cal(V)|$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(cnil) = munit$,
        $#dnt(tctx($Γ$, ($x$, $A$, $q$))) = dnt(Γ) ⊗ dnt(A)$,
    ),
    rect($dnt(sans(L)): |cal(C)|$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(bcnil) = iobj$,
        $#dnt(lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))) = dnt(sans(L)) ⊕ E(K(dnt(Γ) ⊗ dnt(A)))$,
    ),
))

=== Structural Rules

#align(center, table(
    align: center + horizon, stroke: table-dbg, gutter: 1em,
    rect($dnt(rel(A)): cal(V)(A, A ⊗ A)$),
    $dnt(dprf(#rel-rules.base)) = sans("split")(dnt(X))$,
    $dnt(dprf(#rel-rules.pair)) = dnt(rel(A)) ⊗ dnt(rel(B));α;dnt(A) ⊗ σ ⊗ dnt(B);α$,
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#rel-rules.unit)) = λ_munit^(-1)$,
        $dnt(dprf(#rel-rules.bool)) = sans("split")(bools)$,
    ),
    rect($dnt(aff(A)): cal(V)(A, munit)$),
    $dnt(dprf(#aff-rules.base)) = sans("drop")(dnt(X))$,
    $dnt(dprf(#aff-rules.pair)) = dnt(aff(A)) ⊗ dnt(aff(B));λ_munit$,
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#aff-rules.unit)) = idm$,
        $dnt(dprf(#aff-rules.bool)) = sans("drop")(bools)$,
    ),
    rect($dnt(splitctx(Γ, Δ, Ξ)): cal(V)(dnt(Γ), dnt(Δ) ⊗ dnt(Ξ))$),
    $dnt(dprf(#typing-rules.split-nil)) = λ_munit^(-1)$,
    $dnt(dprf(#typing-rules.split-left)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(A);α;dnt(Γ) ⊗ σ;α$,
    $dnt(dprf(#typing-rules.split-right)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(A);α$,
    $dnt(dprf(#typing-rules.split-dup)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(rel(A));α;dnt(Γ) ⊗ σ ⊗ dnt(A);α$,
    $dnt(dprf(#typing-rules.split-drop)) = dnt(Γ) ⊗ dnt(aff(A));ρ;dnt(splitctx(Γ, Δ, Ξ))$,
    rect($dnt(dropctx(Γ, Δ)): cal(V)(dnt(Γ), dnt(Δ))$),
    $dnt(dropctx(Γ, Δ)) = dnt(splitctx(Γ, cnil, Δ));λ$,
    rect($dnt(joinctx(sans(L), sans(K))): cal(V)(dnt(sans(L)), dnt(sans(K)))$),
    $dnt(dprf(#typing-rules.join-nil)) = idm$,
    $dnt(dprf(#typing-rules.join-id)) = dnt(joinctx(sans(L), sans(K)) ⊕ (dnt(Γ) ⊗ dnt(A)))$,
    $dnt(dprf(#typing-rules.join-ext)) = dnt(joinctx(sans(L), sans(K)));α^⊕$,
))

=== Terms

#align(center, [
    #rect($dnt(istm(Γ, p, a, A)): cal(R)_p (dnt(Γ), A)$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#typing-rules.var)) = dnt(dropctx(Γ, thyp(x, A, q)))$,
        $dnt(dprf(#typing-rules.app)) = dnt(istm(Γ, p, a, A));dnt(f)$,
        $dnt(dprf(#typing-rules.unit)) = dnt(dropctx(Γ, cnil))$,
        table(
            columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
            $dnt(dprf(#typing-rules.true)) = dnt(dropctx(Γ, cnil));sans("tt")$,
            $dnt(dprf(#typing-rules.false)) = dnt(dropctx(Γ, cnil));sans("ff")$,
        ),
        $dnt(dprf(#typing-rules.pair)) = dnt(splitctx(Γ, Δ, Ξ));dnt(istm(Δ, p, a, A)) ⋉ dnt(istm(Ξ, p, b, B))$,
        $dnt(dprf(#typing-rules.let))
        \ #h(4em) = dnt(splitctx(Γ, Δ, Ξ)); dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));dnt(istm(#tctx($Δ$, ($x$, $A$, $q$)), p, e, B))
        $,
        $dnt(dprf(#typing-rules.let2)) 
        \ #h(4em) = dnt(splitctx(Γ, Δ, Ξ)); dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A ⊗ B));dnt(istm(#tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), p, e, C))$,
        $dnt(dprf(#typing-rules.blk)) = k;E^(-1)(dnt(#typing-rules.blk.premises.at(0));α^⊕);u;α$,)
])

=== Blocks

#align(center, [
    #rect($dnt(isblk(Γ, p, t, sans(L))): cal(C)_p (E(K(dnt(Γ))), dnt(sans(L)))$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#typing-rules.br)) 
        \ #h(4em) = E(u;dnt(splitctx(Γ, Δ, Ξ)); dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));k);dnt(joinctx(lhyp(lbl(ℓ), p, Δ, A), sans(L)))$,
        $dnt(dprf(#typing-rules.ite)) = 
        \ #h(4em) = E(u;dnt(splitctx(Γ, Δ, Ξ)); dnt(istm(Δ, p, e, bools)) ⊗ dnt(Ξ);k);sans("ite");dnt(isblk(Ξ, p, s, sans(L))) ⊕ dnt(isblk(Ξ, p, t, sans(L)));sans(J)$,
        $dnt(dprf(#typing-rules.let-blk)) 
        \ #h(4em) = E(u;dnt(splitctx(Γ, Δ, Ξ)); dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));k);dnt(isblk(#tctx($Δ$, ($x$, $A$, $q$)), p, t, sans(L)))$,
        $dnt(dprf(#typing-rules.let2-blk)) 
        \ #h(4em) = E(u;dnt(splitctx(Γ, Δ, Ξ));dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A ⊗ B));k);dnt(isblk(#tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), p, e, sans(L)))$,
        $dnt(dprf(#typing-rules.where))
        \ #h(4em) = sans("Tr")_(dnt(Γ), sans(L))^sans(K)(
            (
                (⊕_i dnt(istm(Δ_i, p_i, t_i, lctx(sans(L), sans(K)'))))
                ⊕ dnt(isblk(Γ, p, s, lctx(sans(L), sans(K))))
            );sans(J))
        \ "where" sans(K) = [lhyp(lbl(ℓ)_i, p_i, Δ_i, A_i)]_i, sans(K') = [lhyp(lbl(ℓ)_i, p_i ∩ pure_ℓ, Δ_i, A_i)]_i
        $,)
])

== Metatheory

=== Weakening

#lemma(name: "Semantic Weakening")[
    Given $dropctx(Θ, Γ)$, $joinctx(sans(L), sans(K))$, and $p ⊆ r$, we have
    - $upg(dnt(dropctx(Θ, Γ)), r);upg(dnt(istm(Γ, p, a, A)), r) = dnt(istm(Γ, r, a, A))$
    - $upg(dnt(dropctx(Θ, Γ)), r);upg(dnt(isblk(Γ, p, t, sans(L))), r);upg(dnt(joinctx(sans(L), sans(K))), r) = dnt(isblk(Γ, r, t, sans(K)))$
]

=== Substitution

We begin by giving a semantics for substitutions and rewriting as follows:
#align(center, [
    #rect($dnt(issub(γ, Θ, Γ, p)): cal(R)_p (dnt(Θ), dnt(Γ))$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#subst-rules.subst-nil)) = dnt(dropctx(Θ, cnil))$,
        $dnt(dprf(#subst-rules.subst-cons))
        \ #h(4em) = upg(dnt(splitctx(Θ, Θ_Γ, Θ_x)), p);dnt(issub(γ, Θ_Γ, Γ, p)) ⋊ dnt(istm(Θ_x, p, a, A))
        $
    )
    // #rect($dnt(lbrn(cal(K), sans(L), sans(K), p)): cal(C)_p (dnt(E(K(sans(L)))), dnt(E(K(sans(K)))))$),
    // #table(
    //     align: left + horizon, stroke: table-dbg, gutter: 1em,
    //     $dnt(dprf(#subst-rules.rn-nil)) = 0_sans(K)$,
    //     $dnt(dprf(#subst-rules.rn-cons)) 
    //     \ #h(4em) = 
    //     dnt(lbrn(cal(K), sans(L), sans(K), p)) 
    //     ⊕ dnt(isblk(tctx(Δ, thyp(x, A, q)), p, t, sans(K)));
    //     j
    //     $
    // )
])

#lemma(name: "Substitution Splitting")[
    Given a _pure_ substitution $issub(γ, Θ, Γ, ∅)$, we have
    $
    dnt(issub(γ, Θ, Γ, ∅));dnt(splitctx(Γ, Δ, Ξ))
    = dnt(splitctx(Θ, [γ]Δ, [γ]Ξ));dnt(issub(γ_Δ, [γ]Δ, Δ, ∅)) ⊗ dnt(issub(γ_Ξ, [γ]Ξ, Ξ, ∅))
    $
]

#theorem(name: "Semantic Substitution")[
    Given a _pure_ substitution $issub(γ, Θ, Γ, ∅)$ and an arbitrary renaming $lbrn(cal(K), sans(L), sans(K), p)$, we have
    - $upg(dnt(issub(γ, Θ, Γ, ∅)), p);dnt(istm(Γ, p, a, A)) = dnt(istm(Θ, p, [γ]a, A))$
    - $upg(dnt(issub(γ, Θ, Γ, ∅)), p);dnt(isblk(Γ, p, t, sans(L)));dnt(lbrn([γ]cal(K), sans(L), [γ]sans(K), p)) = dnt(isblk(Θ, p, [γ][cal(K)]t, [γ]sans(K)))$
]

#theorem(name: "Congruence")[
    Given substitutions $issub(γ ≃ γ', Θ, Γ, p)$ and renamings $lbrn(cal(K) ≃ cal(K)', sans(L), sans(K), p)$, we have
    - $dnt(istm(Θ, p, [γ]a, A)) = dnt(istm(Θ, p, [γ']a, A))$
    - $dnt(isblk(Θ, p, [γ][cal(K)]t, [γ]sans(K))) = dnt(isblk(Θ, p, [γ'][cal(K)']t, [γ']sans(K)))$
    - $[γ]cal(K) ≃ [γ]cal(K)' ≃ [γ']cal(K) ≃ [γ']cal(K)'$
]