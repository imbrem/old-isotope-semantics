#import "../isotope.typ": *
#import "syntax.typ": rel-rules, aff-rules, typing-rules

= Semantics

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
    #rect($dnt(istm(Γ, p, a, A)): cal(C)_p (dnt(Γ), A)$)
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
        $dnt(dprf(#typing-rules.let)) = dnt(splitctx(Γ, Δ, Ξ)); \
            #h(4em)dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A));dnt(istm(#tctx($Δ$, ($x$, $A$, $q$)), p, e, B))
        $,
        $dnt(dprf(#typing-rules.let2)) = dnt(splitctx(Γ, Δ, Ξ)); \
            #h(4em)dnt(Δ) ⊗ dnt(istm(Ξ, p, a, A ⊗ B));dnt(istm(#tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), p, e, C))$,
        $dnt(dprf(#typing-rules.blk)) = dnt(#typing-rules.blk.premises.at(0));α^⊕;α$,)
])

=== Blocks

#align(center, [
    #rect($dnt(isblk(Γ, p, t, sans(L))): cal(C)_p (dnt(Γ), sans(L))$)
    #table(
        align: left + horizon, stroke: table-dbg, gutter: 1em,
        $dnt(dprf(#typing-rules.br)) = ...$,
        $dnt(dprf(#typing-rules.ite)) = ...$,
        $dnt(dprf(#typing-rules.let-blk)) = ...$,
        $dnt(dprf(#typing-rules.let2-blk)) = ...$,
        $dnt(dprf(#typing-rules.where)) = ...$,)
])