#import "../isotope.typ": *

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
            $x$, $f med e$, $()$, $tt$, $ff$, $(a, b)$, 
            $klet x = a; e$, $klet (x, y) = a; e$,
            $lbl(ℓ)(A) med {t}$
        ),),
    ),
    (
        name: "Block",
        symbol: ("s", "t"),
        productions: (
            (
                $lbr(lbl(ℓ), a)$, /*$ljmp(lbl(ℓ), a)$,*/ $lite(e, s, t)$,
                $klet x = a; t$, $klet (x, y) = a; t$
            ),
            (
                $s kwhere [lbl(ℓ_i)(x_i: A_i) => { t_i }]_i$
            )
        ),
    )
);
#grammar(isotope-grammar)
The grammar given is parametrized over a set of _base types_ $X ∈ cal(T)$ and _instructions_ $f ∈ cal(I)$. 
We will denote the set of valid types with base types $cal(T)$ as $types(cal(T))$.
Note that we implicitly quotient up to α-equivalence, and that our grammar does not include a notion of function.

For the rest of this section, we will assume the existence of fixed-width bitvector types (e.g. `u64`), basic arithmetic (e.g. `+`, `>=`), and constant values (e.g. 63) of these types (which we may interpret as instructions taking a single argument `()`).

Consider the following simple program for calculating the factorial of `n`:
```isotope
'exit(i64) {
    br 'fact (0, 0) where 'fact(p: (i64, i64)) => {
        let (i, a) = p;
        if i >= n {
            // Branching to the exit label 'exit with argument a means the
            // term will evaluate to a, which is now equal to n!
            br 'exit a
        } else {
            br 'fact (i + 1, i * a)
        }
    }
}
```
Note that the program as a whole lies in the syntactic category of _terms_. If we introduce the syntax sugar `ret a` for branching to an anonymous exit label, we can instead write
```isotope
{
    br 'fact (0, 0) where 'fact(p: (i64, i64)) => {
        let (i, a) = p;
        if i >= n {
            ret a
        } else {
            br 'fact (i + 1, i * a)
        }
    }
}
```

Terms and targets being interleaved makes it possible to encapsulate control flow, which facilitates reasoning about rewriting and control-flow as well as program transformations such as inlining. For example, in a function to compute the absolute value and branch on it
```isotope
let x = y + 5;
let s = sgn x;
let abs = s * x;
if abs > 5 { ret 4 } else { ret 3 }
```
we could inline a plausible definition of `sgn` as follows:
```isotope
let x = y + 5;
let s = { 
    if x < 0 { ret -1 } 
    else if x == 0 { ret 0 } 
    else { ret 1 } 
};
let abs = s * x;
if abs > 5 { ret 4 } else { ret 3 }
```
Note the use of `else if` syntax sugar; in general,
```isotope
if p { P } else if q { Q } else { R }
```
desugars to
```isotope
if p { P } else { if q { Q } else { R } }
```
With the standard approach of encoding the control-flow graph without allowing nesting, we'd have to rewrite everything as a single block as follows
```isotope
let x = y + 5;
if x < 0 { br 'c -1 } 
else if x == 0 { br 'c 0 } 
else { br 'c 1 }
where 'c(s: i64) => {
    let abs = s * x;
    if abs > 5 { ret 4 } else { ret 3 }
}
```

The grammar also allows for multiple, mutually recursive label definitions in a single `where`-binding, as in the following program, which prints out the binary representation of `x`:
```isotope
print "0b";
br 'next x where
    'zero(x: i64) => {
        print "0";
        br 'next x
    }
    'one(x: i64) => { 
        print "1";
        br 'next x
    }
    'next(x: i64) => { 
        if x == 0 {
            ret
        } else if x % 2 == 0 {
            br 'zero (x >> 1)
        } else {
            br 'one (x >> 1)
        }
    };
```
Here, bare function calls `print s` are syntax sugar for unused bindings `let \_ = print s` to allow us to writing side-effectful expressions more easily; similarly, a bare `ret` is syntax sugar for `ret ()` (we will also shorten `br`s likewise). One gotcha is that label bindings cannot be used in a block nested in an expression in another block; for example,
```isotope
ret {
    if b { br 'label 9 } else { br 7 }
} where 'label(x: i64) => {
    print x;
    br (x + 5)
};

```
is _invalid_ code, since the label `'label` is used in the nested expression given as an argument to the `br`-statement, while
```isotope
if b { br 'label 9 } else { br 7 } where 'label(x: i64) => {
    print x;
    br (x + 5)
};
```
is a perfectly valid program with the desired semantics. On the other hand, this restriction does _not_ apply to `let`-bindings of _terms_ (versus _labels_).

== Syntax Sugar

We provide a variety of syntax sugar to make reading and writing programs easier, with the goal of, for the most part, emulating Rust's syntax. 

=== Blocks and Expressions

Where it would be otherwise unambiguous, we permit omitting the braces surrounding a block; for example, if the block
```isotope
if x == 0 {
    let e = 7; ret e
} else {
    ret 8
}
```
is encountered where a term is expected, it may be interpreted as the term
```isotope
{
    if x == 0 {
        let e = 7; ret e
    } else {
        ret 8
    }
}
```
We similarly allow omitting the `ret` keyword in blocks; for example,
```isotope
{ let x = 5;  x }
```
desugars to
```isotope
{ ret (let x = 5; x) }
```
While this behaviour might be confusing, since the user might expect
```isotope
{ let x = 5; ret x }
```
we will later require all such desugarings to be semantically equivalent, making the distinction moot.

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
if is_some x {
    let x = get_some x;
    if x == 0 {
        ret 5
    } else if x == 3 {
        // Note nested control flow is incorporated into the same block
        // This is to allow desugaring more complex constructions, such 
        // as breaks and loops.
        if y == 7 {
            ret 7
        } else {
            ret 'default
        }
    } else {
        ret 'default
    }
} else {
    ret 8
} where 'default => { big_calculation }
```
Similarly to `if`-statements, `match` statements may be interpreted as expressions as well as blocks. Other Rust-like matching constructs, like `let`-`else` statements or pattern destructures, are also supported.

Similarly, we support Rust-style control-flow constructs such as `for`, `while`, and `loop`; for example,
```isotope
while predicate {
    side_effect;
}
rest
```
desugars to
```isotope
br 'head where
    'head => if predicate {
        br 'body
    } else {
        br 'rest
    }
    'body => {
        side_effect;
        br 'head
    }
    'rest => rest
```

== Typing

In this section, we go over the rules defining well-typed `isotope` syntax. Our typing rules are parametrized by: 
- A map $sans("lin")$ from base types $A ∈ cal(T)$ to *quantities* $q ⊆ {rel, aff}$
- For each $A, B in types(cal(T))$, for each *purity* $p ⊆ {cen}$, a subset $cal(I)_p (A, B) ⊆ cal(I)$ of *instructions*, such that
    $ p ⊆ p' ==> cal(I)_p (A, B) ⊇ cal(I)_(p') (A, B) $
    We define $cal(I)_pure = cal(I)_{cen}$, and we call $f ∈ cal(I)_pure (A, B)$ *pure instructions*.
- A *loop purity* $pure_ℓ ⊆ {cen}$
Throughout this section, we assume variable names are _unique_, performing $α$-conversion as necessary to maintain this invariant

=== Judgements

We begin by giving a grammar for *contexts* and *label contexts* as follows:
#let isotope-ctx-grammar = (
    (
        name: "Context",
        symbol: ($Γ$, $Δ$, $Ξ$, $Θ$, $Φ$),
        productions: (
            ($cnil$, tctx($Γ$, ($x$, $A$, $q$))),
        )
    ),
    (
        name: "Label Context",
        symbol: ($sans(J)$, $sans(K)$, $sans(L)$),
        productions: ((
            $bcnil$,
            lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))
        ),),
    ),
);
#grammar(isotope-ctx-grammar)
where $q$ is a quantity and $p$ is a purity.
Where clear from context, we will coerce $rel, aff$, and $cen$ to ${rel}, {aff}$, and ${cen}$ respectively.

We may now introduce the following typing judgements:
#align(center)[#table(
    columns: 2,
    stroke: none,
    column-gutter: 2em,
    align: left,
    [*Syntax*],
    [*Meaning*],
    $istm(Γ, p, a, A)$,
    [$a$ is a term of type $A$ and purity $p$ in context $Γ$],
    $isblk(Γ, p, t, sans(L))$,
    [$t$ is a block with targets $sans(L)$ and purity $p$ in context $Γ$],
    $splitctx(Γ, Δ, Ξ)$,
    [$Γ$ splits into contexts $Δ$, $Ξ$],
    $joinctx(sans(K), sans(L))$,
    [$sans(K)$ is a subset of label-set $sans(L)$],
    $islin(q, A)$, [$A$ has linearity $q$]
)]
We also introduce the following abbreviations:
#align(center)[#table(
    columns: 3,
    stroke: none,
    column-gutter: 2em,
    align: left,
    [*Syntax*],
    [*Definition*],
    [*Meaning*],
    $dropctx(Γ, Δ)$,
    $splitctx(Γ, cnil, Δ)$,
    [$Γ$ is a weakening of $Δ$],
    $thyp(x, A)$,
    $thyp(x, A, {rel, aff})$,
    [],
    $istm(Γ, #{none}, a, A)$,
    $istm(Γ, ∅, a, A)$,
    [$a$ is a term of type $A$ in context $Γ$],
    $lhyp(lbl(ℓ), #{none}, Γ, A)$,
    $lhyp(lbl(ℓ), ∅, Γ, A)$,
    [],
    $isblk(Γ, #{none}, t, sans(L))$,
    $isblk(Γ, ∅, t, sans(L))$,
    [$t$ is a block with targets $sans(L)$ in context $Γ$],
    $islin(q', A^q)$,
    $islin(q', A) ∧ q' ⊆ q$,
    [],
    $rel(A)$,
    $islin(rel, A)$,
    [$A$ is relevant (can be split)],
    $aff(A)$,
    $islin(aff, A)$,
    [$A$ is affine (can be dropped)]
)]

#let typing-rules = (
    "base-lin": prft(name: "base-lin", $q ⊆ sans("lin")(X)$, $islin(q, X)$),
    "unit-lin": prft(name: "unit-lin", $islin(q, tobj)$),
    "bool-lin": prft(name: "bool-lin", $islin(q, bools)$),
    "pair-lin": prft(name: "pair-lin", $islin(q, A)$, $islin(q, B)$, $islin(q, A ⊗ B)$),
    "split-nil": prft(name: "split-nil", $splitctx(cnil, cnil, cnil)$),
    "split-left": prft(name: "split-left", 
        $splitctx(Γ, Δ, Ξ)$,
        $q' ⊆ q$,
        splitctx(
            tctx($Γ$, ($x$, $A$, $q$)), 
            tctx($Δ$, ($x$, $A$, $q'$)), 
            $Ξ$)
    ),
    "split-right": prft(name: "split-right", 
        $splitctx(Γ, Δ, Ξ)$,
        $q' ⊆ q$,
        splitctx(
            tctx($Γ$, ($x$, $A$, $q$)), 
            $Δ$, 
            tctx($Ξ$, ($x$, $A$, $q'$)))
    ),
    "split-dup": prft(name: "split-dup", 
        $splitctx(Γ, Δ, Ξ)$,
        $rel(A^q)$,
        $l, r ⊆ q$,
        splitctx(
            tctx($Γ$, ($x$, $A$, $q$)), 
            tctx($Δ$, ($x$, $A$, $l$)), 
            tctx($Ξ$, ($x$, $A$, $r$)))
    ),
    "split-drop": prft(name: "split-drop",
        $splitctx(Γ, Δ, Ξ)$,
        $aff(A^q)$,
        splitctx(tctx($Γ$, ($x$, $A$, $q$)), $Δ$, $Ξ$)
    ),
    "join-nil": prft(name: "join-nil",
        $joinctx(bcnil, bcnil)$
    ),
    "join-id": prft(name: "join-id",
        $joinctx(sans(L), sans(K))$,
        $p ⊇ p'$,
        joinctx(
            lctx($sans(L)$, ($lbl(ℓ)$, $p$, $Γ$, $A$)), 
            lctx($sans(K)$, ($lbl(ℓ)$, $p'$, $Γ$, $A$))),
    ),
    "join-ext": prft(name: "join-ext",
        $joinctx(sans(L), sans(K))$,
        joinctx(
            $sans(L)$, 
            lctx($sans(K)$, ($lbl(ℓ)$, $p$, $Γ$, $A$))),
    ),
    "var": prft(name: "var",
        $dropctx(Γ, thyp(x, A, q))$,
        $istm(Γ, p, x, A)$
    ),
    "app": prft(name: "app",
        $istm(Γ, p, a, A)$,
        $f ∈ cal(I)_p(A, B)$,
        $istm(Γ, p, f med a, B)$
    ),
    "unit": prft(name: "unit", $dropctx(Γ, cnil)$, $istm(Γ, p, (), tobj)$),
    "true": prft(name: "true", $dropctx(Γ, cnil)$, $istm(Γ, p, tt, bools)$),
    "false": prft(name: "false", $dropctx(Γ, cnil)$, $istm(Γ, p, ff, bools)$),
    "pair": prft(name: "pair",
        $splitctx(Γ, Δ, Ξ)$,
        $istm(Δ, p, a, A)$,
        $istm(Ξ, p, b, B)$,
        $istm(Γ, p, (a, b), A)$
    ),
    "let": prft(name: "let", 
        $splitctx(Γ, Δ, Ξ)$,
        istm(tctx($Δ$, ($x$, $A$, $q$)), $p$, $e$, $B$),
        $istm(Ξ, p, a, A)$,
        istm($Γ$, $p$, $klet x = a; e$, $B$)
    ),
    "let2": prft(name: "let2", 
        $splitctx(Γ, Δ, Ξ)$,
        istm(tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), $p$, $e$, $C$),
        $istm(Ξ, p, a, A ⊗ B)$,
        istm($Γ$, $p$, $klet (x, y) = a; e$, $C$)
    ),
    "blk": prft(name: "blk", 
        $isblk(Γ, p, t, lhyp(lbl(ℓ), p, cnil, A))$,
        $istm(Γ, p, lbl(ℓ)(A) med {t}, A)$
    ),
    "br": prft(name: "br", 
        $splitctx(Γ, Δ, Ξ)$,
        $joinctx(lhyp(lbl(ℓ), p, Δ, A), sans(L))$,
        $istm(Ξ, p, a, A)$,
        $isblk(Γ, p, lbr(lbl(ℓ), a), sans(L))$
    ),
    "ite": prft(name: "ite",
        $splitctx(Γ, Δ, Ξ)$,
        $isblk(Δ, p, e, bools)$,
        $isblk(Ξ, p, s, sans(L))$,
        $isblk(Ξ, p, t, sans(L))$,
        $isblk(Γ, p, lite(e, s, t), sans(L))$
    ),
    "let-blk": prft(name: "let-blk",
        $splitctx(Γ, Δ, Ξ)$,
        isblk(tctx($Δ$, ($x$, $A$, $q$)), $p$, $t$, $sans(L)$),
        $istm(Ξ, p, a, A)$,
        isblk($Γ$, $p$, $klet x = a; t$, $sans(L)$)
    ),
    "let2-blk": prft(name: "let2-blk",
        $splitctx(Γ, Δ, Ξ)$,
        isblk(tctx($Δ$, ($x$, $A$, $q$), ($y$, $B$, $q$)), $p$, $t$, $sans(L)$),
        $istm(Ξ, p, a, A ⊗ B)$,
        isblk($Γ$, $p$, $klet (x, y) = a; t$, $sans(L)$)
    ),
    "where": prft(name: "where",
        $∀ i, isblk(Δ_i, p, t_i, lctx(sans(L), [lhyp(lbl(ℓ_j), p ∩ pure_ℓ, Δ_j, A_j)]_j))$,
        $isblk(Γ, p, s, lctx(sans(L), [lhyp(lbl(ℓ_i), p, Δ_i, A_i)]_i))$,
        isblk($Γ$, $p$, $s kwhere [lbl(ℓ)_i(x_i: A_i) => {t_i}]_i$, $sans(L)$)
    )
)

#let table-dbg = none

=== Structural Rules

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.base-lin),
        dprf(typing-rules.unit-lin),
        dprf(typing-rules.bool-lin),
        dprf(typing-rules.pair-lin),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.split-nil),
        dprf(typing-rules.split-left),
        dprf(typing-rules.split-right),
    ),
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.split-dup),
        dprf(typing-rules.split-drop),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.join-nil),
        dprf(typing-rules.join-id),
        dprf(typing-rules.join-ext),
    ),
))

#let rel-rules = (
    "base": prft(name: "base-rel", $rel ∈ sans("lin")(X)$, $rel(X)$),
    "unit": prft(name: "unit-rel", $rel(tobj)$),
    "bool": prft(name: "bool-rel", $rel(bools)$),
    "pair": prft(name: "pair-rel", $rel(A)$, $rel(B)$, $rel(A ⊗ B)$),
)


#let aff-rules = (
    "base": prft(name: "base-aff", $aff ∈ sans("lin")(X)$, $aff(X)$),
    "unit": prft(name: "unit-aff", $aff(tobj)$),
    "bool": prft(name: "bool-aff", $aff(bools)$),
    "pair": prft(name: "pair-aff", $aff(A)$, $aff(B)$, $aff(A ⊗ B)$),
)

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(rel-rules.base),
        dprf(rel-rules.unit),
        dprf(rel-rules.bool),
        dprf(rel-rules.pair),
    ),
    table(
        columns: 4, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(aff-rules.base),
        dprf(aff-rules.unit),
        dprf(aff-rules.bool),
        dprf(aff-rules.pair),
    ),
))

=== Terms

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.var),
        dprf(typing-rules.app),
        dprf(typing-rules.pair),
    ),
    table(
        columns: 3, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.unit),
        dprf(typing-rules.true),
        dprf(typing-rules.false),
    ),
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.let),
        dprf(typing-rules.blk),
    ),
    dprf(typing-rules.let2),
))

=== Blocks

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    table(
        columns: 2, align: bottom, column-gutter: 2em, stroke: table-dbg,
        dprf(typing-rules.br),
        dprf(typing-rules.ite),
    ),
    dprf(typing-rules.let-blk),
    dprf(typing-rules.let2-blk),
    dprf(typing-rules.where),
))

== Metatheory

We begin this section by defining some basic metatheoretic judgements:
#align(center)[#table(
    columns: 2,
    stroke: none,
    column-gutter: 2em,
    align: left,
    [*Syntax*],
    [*Meaning*],
    $islin(q, Γ)$,
    [The context $Γ$ is of linearity $q$],
    $issub(γ, Θ, Γ, p)$,
    [The map $γ$ is a substitution from $Θ$ to $Γ$ with purity $p$],
    $lbrn(cal(L), sans(L), sans(K))$,
    [The map $cal(L)$ is a label-renaming from $sans(L)$ to $sans(K)$]
)]

=== Weakening

We now state some basic facts about context splitting and weakening:
- Weakening is transitive: $dropctx(Γ, Δ) ==> dropctx(Δ, Ξ) ==> dropctx(Γ, Ξ)$
- Weakening composes with splitting: $splitctx(Γ, Δ, Ξ) ∧ dropctx(Δ, Δ') ∧ dropctx(Ξ, Ξ') ==> splitctx(Γ, Δ', Ξ')$
- Splitting is commutative: $splitctx(Γ, Δ, Ξ) <==> splitctx(Γ, Ξ, Δ)$.

We may now state the _weakening lemma_:
#lemma(name: "Weakening")[
    Given $dropctx(Γ, Δ), joinctx(sans(L), sans(K))$, and $r ⊆ p$, then
    - If $istm(Δ, r, a, A)$, then $istm(Γ, p, a, A)$
    - If $isblk(Δ, r, t, sans(L))$, then $isblk(Γ, p, t, sans(K))$
]<syntax-wk>

=== Substitution

We begin by giving the typing rules for substitution
#let subst-rules = (
    "subst-nil": prft(
        $dropctx(Θ, cnil)$, $issub(cnil, Θ, cnil, p)$, 
        name: "subst-nil"),
    "subst-cons": prft(
        $issub(γ, Θ_Γ, Γ, p)$, 
        $istm(Θ_x, p, a, A)$,
        $islin(q, Θ_x)$,
        $splitctx(Θ, Θ_x, Θ_Γ)$,
        issub($[x ↦ a]γ$, $Θ$, $Γ, thyp(x, A, q)$, $p$),
        name: "subst-cons")
)

#align(center, table(
    align: center + horizon, stroke: table-dbg,
    dprf(subst-rules.subst-nil),
    dprf(subst-rules.subst-cons),
))

// Given a well-typed substitution $issub(γ, Θ, Γ, p)$, we define the capture-avoiding substitution of terms and targets as usual. We describe the substitution of a _context_ recursively as follows:
// $
// [γ]cnil &= cnil
// $
// We can then define the substitution of a _label context_ recursively as follows:
// $

// $

We may now state the substitution lemma as follows:
#lemma(name: "Substitution")[
    Given  $issub(γ, Θ, Γ, p)$, then
    - $istm(Θ, p, a, A) ==> istm(Γ, p, [γ]a, A)$
    - $isblk(Θ, p, t, [γ]sans(L)) ==> isblk(Θ, p, [γ]t, [γ]sans(L))$
]<syntax-subst>

We further have that
#lemma(name: "Substitution Composes")[
    Given  $issub(γ, Θ, Γ, p)$ and $issub(δ, Γ, Δ, p)$, then $issub(δ ∘ γ, Θ, Δ, p)$
]<syntax-subst-composes>