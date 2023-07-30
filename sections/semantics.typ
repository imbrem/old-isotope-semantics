#import "../isotope.typ": *
#import "syntax.typ": rel-rules, aff-rules, typing-rules, subst-rules

= Semantics

== Isotope Models

An *`isotope` model* is given by:
- Categories $cal(C)_∅, cal(C)_{cen}$ with coproducts enriched over posets, the *control category*, such that: 
    - $underline(dot): cal(C)_∅ -> cal(C)_{cen}$ is an identity-on-objects monoidal functor
    - $cal(C)_∅$ has a guarded trace (this can be vacuous)
    - $cal(C)_{cen}$ has a trace
    //TODO: list out all ite properties; or generalize over control structures?
    - For each $A$, there exist morphisms $sans("ite"): cal(C)_∅(E(K(bools ⊗ A)), E(K(A)) ⊕ E(K(A)))$ such that $sans("ite");E(f) ⊕ E(f) = E(u;f;k);sans("ite")$
    //TODO: structure on clamp so this stops being a problem?
    - Full subcategories $cal(C)_p'$ of $cal(C)_p$ such that $r ⊆ p ==> cal(C)_r' ⊆ cal(C)_r$
- An symmetric effectful category $cal(R)_∅ -> cal(R)_{cen}$ enriched over posets, the *expression category*, equipped with
    - For every droppable base type $A$, a pure morphism $sans("drop")(A): cal(R)_∅(sans("base")(A), I)$
    - For every splittable base type $A$, a pure morphism $sans("split")(A): cal(R)_∅(sans("base")(A), sans("base")(A) ⊗ sans("base")(A))$, such that:
        - Commutativity: $sans("split")(A);σ = sans("split")(A)$
        - Associativity: 
        $
        sans("split")(A);dnt(A) ⊗ sans("split")(A)
        = sans("split")(A);sans("split")(A) ⊗ dnt(A);α
        $
        - Unit: if $A$ is droppable, $sans("split")(A);(sans("drop")(A) ⊗ dnt(A)) = idm$
    - A set of distinguised "clamped" objects $K(|cal(R)|)$, inducing full subcategories $cal(R)_p'$
    - A mapping $K: |cal(R)| -> K(|cal(R)|)$ satisfying: 
        - $K_|cal(R)_cal(C)| = idm$
    - For all $A ∈ |cal(R)|$, central morphisms *clamp* $k_A: cal(R)_∅(A, K(A))$ and *unclamp* $u_A: cal(R)_∅(K(A), A)$ such that:
        - $k;u;k = k;k = k, quad u;k;u = u_(K(A));u = u$
        // - $k;u;A ⊗ f;k = A ⊗ (k;u;f);k, quad k;u;f ⊗ B;k = (k;u;f) ⊗ B;k$
        - For all pure morphisms $f ∈ cal(R)_∅(A, B)$, $f;k;u = k;u;f$
        - For all morphisms $f, g ∈ cal(R)_p(A, B)$, $f;upg((k;u), p);g refines f;g$ // "SSA condition"
    - Enriched isomorphisms $E_p: cal(R)_p' ≃ cal(C)_p'$ such that $∀r, E_p;(upg(dot, r)) = (upg(dot, r));E_r$ and $E_p^(-1);(upg(dot, r)) = (upg(dot, r));E_r^(-1)$ //TODO: generalize to just requiring an equivalence?
Note $upg(dot, p)$ denotes the functor sending $cal(R)_r$ to $cal(R)_p$ or $cal(C)_r$ to $cal(C)_p$.

We write $|cal(R)|, |cal(C)|$ to denote the shared set of objects of $|cal(R)_p|, |cal(C)_p|$ respectively.

An `isotope` model is *graphical* if $cal(R)_cen$ is monoidal. An `isotope` model is *simple* if $cal(R)_p = cal(C)_p$ and $K, k, u$ are the identity. An `isotope` model is *flat* if $k_(K(A)), u_(K(A))$ are the identity.

Given a symmetric effectful category $cal(R)_∅ -> cal(R)_{cen}$ enriched over posets with coproducts and an Elgot operator, we can construct a simple `isotope` model by taking $cal(R)_p = cal(C)_p$ and $E, K, k, u$ the identity.

// If $cal(V) -> cal(C)$ is enriched over posets and equipped with an operation $Σ$ which takes sets of permutations $f ⋉ g, f ⋊ g$ to morphisms such that
// $∀h ∈ P, h refines Σ P $
// then we may construct, for each $Σ$, the *$Σ$-graphical `isotope` model*.

== Denotational Semantics

#let table-dbg = none

=== Types and Contexts

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    rect($dnt(A): |cal(R)|$),
    table(
        columns: 4, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(X) = sans("base")(X)$,
        $dnt(tobj) = tobj$,
        $dnt(bools) = bools$,
        $dnt(A ⊗ B) = dnt(A) ⊗ dnt(B)$,
    ),
    rect($dnt(Γ): |cal(R)|$),
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
    rect($dnt(rel(A)): cal(R)_∅(A, A ⊗ A)$),
    $dnt(dprf(#rel-rules.base)) = sans("split")(dnt(X))$,
    $dnt(dprf(#rel-rules.pair)) = dnt(rel(A)) ⊗ dnt(rel(B));α;dnt(A) ⊗ σ ⊗ dnt(B);α$,
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#rel-rules.unit)) = λ_munit^(-1)$,
        $dnt(dprf(#rel-rules.bool)) = sans("split")(bools)$,
    ),
    rect($dnt(aff(A)): cal(R)_∅(A, munit)$),
    $dnt(dprf(#aff-rules.base)) = sans("drop")(dnt(X))$,
    $dnt(dprf(#aff-rules.pair)) = dnt(aff(A)) ⊗ dnt(aff(B));λ_munit$,
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(dprf(#aff-rules.unit)) = idm$,
        $dnt(dprf(#aff-rules.bool)) = sans("drop")(bools)$,
    ),
    rect($dnt(splitctx(Γ, Δ, Ξ)): cal(R)_∅(dnt(Γ), dnt(Δ) ⊗ dnt(Ξ))$),
    $dnt(dprf(#typing-rules.split-nil)) = λ_munit^(-1)$,
    $dnt(dprf(#typing-rules.split-left)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(A);α;dnt(Γ) ⊗ σ;α$,
    $dnt(dprf(#typing-rules.split-right)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(A);α$,
    $dnt(dprf(#typing-rules.split-dup)) = dnt(splitctx(Γ, Δ, Ξ)) ⊗ dnt(rel(A));α;dnt(Γ) ⊗ σ ⊗ dnt(A);α$,
    $dnt(dprf(#typing-rules.split-drop)) = dnt(Γ) ⊗ dnt(aff(A));ρ;dnt(splitctx(Γ, Δ, Ξ))$,
    rect($dnt(dropctx(Γ, Δ)): cal(R)_∅(dnt(Γ), dnt(Δ))$),
    $dnt(dropctx(Γ, Δ)) = dnt(splitctx(Γ, cnil, Δ));λ$,
    rect($dnt(joinctx(sans(L), sans(K))): cal(C)_∅(dnt(sans(L)), dnt(sans(K)))$),
    $dnt(dprf(#typing-rules.join-nil)) = idm$,
    $dnt(dprf(#typing-rules.join-id)) = dnt(joinctx(sans(L), sans(K))) ⊕ E(K(dnt(Γ) ⊗ dnt(A)))$,
    $dnt(dprf(#typing-rules.join-ext)) = dnt(joinctx(sans(L), sans(K)));α^⊕;dnt(sans(K)) ⊕ 0_(E(K(dnt(Γ) ⊗ dnt(A))))$,
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
        \ #h(4em) = E(u;dnt(splitctx(Γ, Δ, Ξ));dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A ⊗ B));α;k);dnt(isblk(#tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), p, e, sans(L)))$,
        $dnt(dprf(#typing-rules.where))
        \ #h(4em) = sans("Tr")_(E(K(dnt(Γ))), dnt(sans(L)))^dnt(sans(K))(
            (
                (⊕_i dnt(istm(Δ_i, p_i, t_i, lctx(sans(L), sans(K)'))))
                ⊕ dnt(isblk(Γ, p, s, lctx(sans(L), sans(K))))
            );sans(J)^(n + 1);α^⊕)
        \ "where" sans(K) = [lhyp(lbl(ℓ)_i, p_i, Δ_i, A_i)]_i, sans(K') = [lhyp(lbl(ℓ)_i, p_i ∩ pure_ℓ, Δ_i, A_i)]_i
        $,)
])

== Metatheory

=== Weakening

#lemma(name: "Semantic Weakening")[
    Given $dropctx(Θ, Γ)$, $joinctx(sans(L), sans(K))$, and $p ⊆ r$, we have
    - $upg(dnt(dropctx(Θ, Γ)), r);upg(dnt(istm(Γ, p, a, A)), r) = dnt(istm(Θ, r, a, A))$
    - $upg(E(u;dnt(dropctx(Θ, Γ));k), r);upg(dnt(isblk(Γ, p, t, sans(L))), r);upg(dnt(joinctx(sans(L), sans(K))), r) = dnt(isblk(Γ, r, t, sans(K)))$
]

=== Substitution

We begin by giving a semantics for substitutions and rewriting as follows:
#align(center, [
    #rect($dnt(issub(γ, Θ, Γ, p)): cal(R)_p (dnt(Θ), dnt(Γ))$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#subst-rules.subst-nil)) = dnt(dropctx(Θ, cnil))$,
        $dnt(dprf(#subst-rules.subst-cons))
        \ #h(12em) = upg(dnt(splitctx(Θ, Θ_Γ, Θ_x)), p);dnt(issub(γ, Θ_Γ, Γ, p)) ⋊ dnt(istm(Θ_x, p, a, A))
        $
    )
    #rect($dnt(lbrn(cal(K), sans(L), sans(K), p)): cal(C)_p (dnt(sans(L)), dnt(sans(K)))$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#subst-rules.rn-nil)) = 0_sans(K)$,
        $dnt(dprf(#subst-rules.rn-cons))  = 
        dnt(lbrn(cal(K), sans(L), sans(K), p)) 
        ⊕ dnt(isblk(tctx(Δ, thyp(x, A, q)), p, t, sans(K)));
        sans(J)
        $
    )
])

#lemma(name: "Substitution Splitting")[
    Given a _pure_ substitution $issub(γ, Θ, Γ, ∅)$, we have
    $
    dnt(issub(γ, Θ, Γ, ∅));dnt(splitctx(Γ, Δ, Ξ))
    = dnt(splitctx(Θ, [γ]Δ, [γ]Ξ));dnt(issub(γ_Δ, [γ]Δ, Δ, ∅)) ⊗ dnt(issub(γ_Ξ, [γ]Ξ, Ξ, ∅))
    $
]

#theorem(name: "Semantic Substitution")[
    Given a _pure_ substitution $issub(γ, Θ, Γ, ∅)$, we have
    - $upg(dnt(issub(γ, Θ, Γ, ∅)), p);dnt(istm(Γ, p, a, A)) = dnt(istm(Θ, p, [γ]a, A))$
    - $upg(E(u;dnt(issub(γ, Θ, Γ, ∅));k), p);dnt(isblk(Γ, p, t, sans(L)));dnt(lbrn(γ^sans(L), sans(L), [γ]sans(L), p)) = dnt(isblk(Θ, p, [γ]t, [γ]sans(L)))$
    Similarly, for _arbitrary_ renamings $lbrn(cal(K), sans(L), sans(K), p)$, we have that $dnt(isblk(Γ, p, t, sans(L)));dnt(lbrn(cal(K), sans(L), sans(K), p)) = dnt(isblk(Γ, p, [cal(K)]t, sans(K)))$
]

#theorem(name: "Congruence")[
    Given substitutions $issub(γ refines γ', Θ, Γ, p)$, we have
    - $dnt(istm(Θ, p, [γ]a, A)) refines dnt(istm(Θ, p, [γ']a, A))$
    - $dnt(isblk(Θ, p, [γ]t, [γ]sans(L))) refines dnt(isblk(Θ, p, [γ']t, [γ']sans(L)))$
    Similarly, for renamings $lbrn(cal(K) → cal(K)', sans(L), sans(K), p)$, we have that
    $dnt(isblk(Γ, p, [cal(K)]t, sans(K))) refines dnt(isblk(Γ, p, [cal(K)']t, sans(K)))$
]