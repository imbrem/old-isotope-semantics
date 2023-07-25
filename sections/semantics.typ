#import "../isotope.typ": *
#import "syntax.typ": rel-rules, aff-rules, typing-rules

= Semantics

== Isotope Models

An *`isotope` model* is given by:
- A symmetric monoidal *base category* $cal(V)$ equipped with a coproduct distributing over the tensor product
- An symmetric effectful category $cal(V) -> cal(C)$, the *control category* equipped with a coproduct distributing over the tensor product and an Elgot structure
- An symmetric effectful category $cal(V) -> cal(R)$ enriched over posets, the *expression category*, equipped with
    - A subcategory $cal(R)_cal(C) ⊇ cal(V)$
    - A mapping $K: |cal(R)| -> |cal(R)_cal(C)|$ which is the identity on $|cal(R)_cal(C)|$
    - For all $A ∈ |cal(R)|$, morphisms *clamp* $k_(A, K(A))$ and *unclamp* $u_(K(A), A)$ such that:
        - $k;u;k = k, u;k;u = u$
        - For all pure morphisms $f ∈ cal(V)(A, B)$, $underline(f);k;u = k;u;underline(f)$
        - For all morphisms $f, g$, $f;g ≥ f;k;u;g$ // "SSA condition"
    - An isomorphism of categories $E: cal(R)_cal(C) ≃ cal(C)$ such that $E$ is the identity on $|cal(V)|$ and on pure morphisms $f ∈ cal(V)(A, B)$
    // - An equivalence of categories $(C, R, η, ε): cal(R)_cal(C) ≃ cal(C)$ such that:
    //     - For all objects in $A ∈ |cal(V)|$, $C, R, η_A, ε_A$ are the identity
    //     - For pure morphisms $f ∈ cal(V)(A, B)$, $C(underline(f)) = underline(f)$, $R(underline(f)) = underline(f)$
An `isotope` model is *graphical* if $cal(R)$ is monoidal. An `isotope` model is *simple* if $cal(R) = cal(C)$ and $K, k, u$ are the identity. An `isotope` model is *flat* if $k_(K(A), K(K(A))), u_(K(K(A)), K(A))$ are the identity (note all simple `isotope` models are flat).

Given a control category $cal(V) -> cal(C)$, we can construct a simple `isotope` model by taking $cal(R) = cal(C)$ and $K, k, u$ the identity (with the discrete order on each hom-set).

If $cal(V) -> cal(C)$ is enriched over posets and equipped with an operation $Σ$ which takes sets of permutations $f ⋉ g, f ⋊ g$ to morphisms such that
$∀h ∈ P, Σ P ≥ h $
then we may construct, for each $Σ$, the *$Σ$-graphical `isotope` model*.

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
    rect($dnt(sans(L)): |cal(V)|$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(bcnil) = iobj$,
        $#dnt(lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))) = dnt(sans(L)) ⊕ (dnt(Γ) ⊗ dnt(A))$,
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
    #rect($dnt(isblk(Γ, p, t, sans(L))): cal(C)_p (E(K(dnt(Γ))), E(K(sans(L))))$)
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