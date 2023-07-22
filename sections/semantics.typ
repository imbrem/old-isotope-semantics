#import "../isotope.typ": *
#import "syntax.typ": rel-rules, aff-rules

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
    rect($dnt(sans(L)): |cal(C)|$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(bcnil) = iobj$,
        $#dnt(lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))) = dnt(sans(L)) ⊕ (dnt(Γ) ⊗ dnt(A))$,
    ),
))

=== Structural Rules

#align(center, table(
    align: center + horizon, stroke: table-dbg,
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
))