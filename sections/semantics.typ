#import "../isotope.typ": *

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
        $dnt(cnil) = tobj$,
        $#dnt(tctx($Γ$, ($x$, $A$, $q$))) = dnt(Γ) ⊗ dnt(A)$,
    ),
    rect($dnt(sans(L)): |cal(C)|$),
    table(
        columns: 2, align: horizon, column-gutter: 2em, stroke: table-dbg,
        $dnt(bcnil) = iobj$,
        $#dnt(lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))) = dnt(sans(L)) ⊕ (dnt(Γ) ⊗ dnt(A))$,
    ),
))