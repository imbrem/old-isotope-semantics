#import "@preview/curryst:0.1.1": rule, proof-tree

#import "@preview/ctheorems:1.1.2": *
#show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox("theorem", "Theorem")
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let lemma = thmbox("lemma", "Lemma")

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let lbl(labl) = $ #`^`labl$
#let let1(x, e) = $/*sans("let") med*/ #x = #e$
#let let2(x, y, e) = $/*sans("let") med*/ #x, #y = #e$
#let lite(e, s, t) = $sans("if") med #e med { #s } med sans("else") med { #t }$
#let lbr(l, e) = $sans("br") med #l med #e$
#let lblk(l, a, e) = $#l #a: #e$
#let lwhere(β, L) = $#β /*med sans("where")*/ med #L$
#let lwk(Γ, Δ) = $#Γ ↦ #Δ$
#let twk(L, K) = $#L ⇝ #K$
#let lto = $triangle.stroked.small.r$
#let sfor(e, x) = $#e ⧸ #x$

#let ltt = $sans("tt")$
#let lff = $sans("ff")$
#let Var = $sans("Var")$

#let dprf(tree) = box(baseline: 40%, proof-tree(tree))
#let entp(p) = $attach(⊢, br: #p)$
#let intp(p, A, B) = $sans("inst")_(#p)(#A, #B)$
#let tybox(judgement, typ) = rect(
  inset: 0.7em, 
  align(horizon, $[|#judgement|]: #typ$))

#let αiso = $attach(≅, br: α)$
#let αeq = $attach(≃, br: α)$

#let todos = counter("todos")
#let todo(message) = text(red, [
  #todos.step()
  *TODO #todos.display():* #message
])

#set heading (numbering: "1.")


#text(2em)[*The Denotational Semantics of SSA*]

In this article, we make the argument that SSA corresponds exactly to Freyd categories⋆. We stick a "⋆" after Freyd category since, _depending what we mean by SSA_, we might need a bit of additional structure; we're also going to be using a slightly weird definition of Freyd category. To make this argument, we need to show that
- *Freyd categories⋆ are SSA*: SSA can be given a semantics in terms of Freyd categories which respects the equations we expect to hold for SSA programs
- *SSA is a Freyd category⋆*: SSA programs quotiented over these equations themselves form a Freyd category⋆
So, two questions come to mind: what is Freyd category, and what is SSA?

#outline()

= Introduction to SSA

== Syntax of SSA

An SSA program consists of 

- _Instructions_ of the form $x, y = #`call` f med a med b med c$, some of which may be _terminators_ such as $#`ret` x$ or $#`br` lbl(ℓ) med e$, which are organized into
- _Basic blocks_, which are a sequence of instructions of which only the last is a terminator, parametrized by a set of arguments, which form a 
- _Control-flow graph_, with edges where one basic block calls another

For now, we will restrict ourselves to the basic terminators necessary to implement unstructured control-flow, namely branching to a label with an argument, or a boolean choice between terminators. Note that returns can be implemented as simply an unconditional branch to a special "exit label."

We can define an SSA program to be given by a _region_: a control-flow graph with a distinguished, single _entry block_ and (potentially) multiple _exit blocks_. We'll make our life a little bit easier and generalize instructions to _terms_, which will allow us to have nested _pure_ expressions in an instruction and to implement multi-argument instructions using tuples. Then, we obtain
- _Terms_ $e$: $x | f med e | () | (e, e')$
- _Bodies_ $b$: $dot | let1(x, e); dot | let2(x, y, e); dot$
- _Terminators_ $s, t$: $lbr(lbl(ℓ), e) | lite(e, s, t)$
- _Basic blocks_ $β$: $b;t$
- _Control-flow graphs_ $L$: $dot | L, lblk(lbl(ℓ), (x: A), β)$
- _Regions_ $r$: $lwhere(β, L)$
To type our syntax, we will need to introduce the following:
- _Types_ $A, B, C$: $X | A ⊗ B$
- _Contexts_ $Γ, Δ, Ξ$: $dot | Γ, x: A$
- _Targets_ $sans(L), sans(K), sans(J): dot | sans(L), lbl(ℓ)[Γ](A)$
We begin by introducing some structural judgements on contexts and targets as follows:
#let ctx-rules = (
  rule(name: "nil-wk", $lwk(dot, dot)$),
  rule(name: "cons-wk", $lwk(#$Γ, x: A$, #$Δ, x: A$)$, $lwk(Γ, Δ)$),
  rule(name: "drop-wk", $lwk(#$Γ, x: A$, Δ)$, $lwk(Γ, Δ)$, $x ∉ Δ$),
)

#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(ctx-rules.at(0)),
  proof-tree(ctx-rules.at(1)),
  proof-tree(ctx-rules.at(2))
))

#let trg-rules = (
  rule(name: "nil-twk", $twk(dot, dot)$),
  rule(name: "cons-twk", $twk(#$L, lbl(ℓ)[Γ](A)$, #$K, lbl(ℓ)[Δ](A)$)$, $twk(L, K)$, $lwk(Γ, Δ)$),
  rule(name: "drop-twk", $twk(L, #$K, lbl(ℓ)[Δ](A)$)$, $twk(L, K)$, $ℓ ∉ K$),
)

#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(trg-rules.at(0)),
  proof-tree(trg-rules.at(1)),
  proof-tree(trg-rules.at(2))
))

#todo[note that derivations for regular weakening are _unique_]

We can now give typing rules as follows:

#let term-rules = (
  rule(name: "var", $Γ entp(p) x: A$, $lwk(Γ, #$x: A$)$),
  rule(name: "app", $Γ entp(p) f med e: B$, $f: intp(p, A, B)$, $Γ entp(1) e: A$),
  rule(name: "pair", $Γ entp(p) (a, b): A ⊗ B$, $Γ entp(1) a: A$, $Γ entp(1) b: B$),
  rule(name: "nil", $Γ entp(p) (): bold(1)$),
  rule(name: "true", $Γ entp(p) ltt: bold(2)$),
  rule(name: "false", $Γ entp(p) lff: bold(2)$),
);
#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(term-rules.at(0)),
  proof-tree(term-rules.at(1)),
  proof-tree(term-rules.at(2)),
))
#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(term-rules.at(3)),
  // proof-tree(term-rules.at(4)),
  // proof-tree(term-rules.at(5)),
))


#let body-rules = (
  rule(name: "nil-st", $Γ entp(p) dot lto Δ$, $lwk(Γ, Δ)$),
  rule(name: "let", $Γ entp(p) let1(x, e); b lto Δ$, $Γ entp(p) e: A$, $Γ, x: A entp(p) b lto Δ$),
  rule(name: "let2", $Γ entp(p) let2(x, y, e); b lto Δ$, $Γ entp(p) e: A ⊗ B$, $Γ, x: A, y: B entp(p) b lto Δ$),
);
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(body-rules.at(0)),
  proof-tree(body-rules.at(1)),
))
#align(center, proof-tree(body-rules.at(2)))

#let terminator-rules = (
  rule(name: "br", $Γ ⊢ lbr(lbl(ℓ), e) lto sans(L)$, $Γ entp(p) e: A$, $twk(Δ, #$ℓ: A$)$),
  rule(name: "ite", 
    $Γ ⊢ lite(e, s, t) lto sans(L)$, 
    $Γ entp(1) e: bold(2)$, 
    $Γ ⊢ s lto sans(L)$, 
    $Γ ⊢ t lto sans(L)$),
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(terminator-rules.at(0)),
  proof-tree(terminator-rules.at(1)),
))

#let block-rule = rule(
  name: "blk", $Γ ⊢ b; t lto sans(L)$, $Γ entp(p) b: Δ$, $Δ ⊢ t: sans(L)$)
#align(center, proof-tree(block-rule))
#let cfg-rules = (
  rule(name: "nil-cf", $sans(L) ⊢ dot lto sans(K)$, $twk(sans(L), sans(K))$),
  rule(name: "cons-cf", 
    $sans(L) ⊢ L, lblk(lbl(ℓ), (x: A), t) lto sans(K)$, 
    $sans(L) ⊢ L lto sans(K), lbl(ℓ)[Γ](A)$,
    $Γ, x: A ⊢ t lto L$),
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(cfg-rules.at(0)),
  proof-tree(cfg-rules.at(1)),
))

#let region-rule = rule(name: "reg", $Γ ⊢ lwhere(β, L) lto sans(K)$, $Γ ⊢ β lto sans(L)$, $sans(L) ⊢ L lto sans(K)$)
#align(center, proof-tree(region-rule))

#todo[per-rule explanations]

#todo[coherence, but _not_ for blocks and therefore regions]

#todo[weakening theorems, "maximal blocks"]

#todo[CFGs don't weaken nicely, "one sidedness": "maximal cfgs"]

#todo[substitution and weakening for CFGs/blocks just got a lot more !FUN!]

#todo[match-statements?]

== Equational Theory of SSA

We now want to equip our syntax with an _equational theory_. We will want:
- $α$-rules, which allow us to rename bound variables, since naming should not effect semantics
- $β$-rules, which allow us to perform substitution of pure terms
- $η$-rules, which allow us to decompose and recompose products
- $δ$-rules, which will allow us to manipulate control-flow

=== $α$-Equivalence, Weakening, and SSA

Let's start by defining $α$-equivalence. While our final $α$-equivalence relation will be over terms defined in the same context, it is easier to define it in terms of the independently useful notion of _generalized $α$-equivalence_, in which we are also able to rename variables in the input and output contexts. In particular, we say two _contexts_ are $α$-equivalent if they are the same up to renaming of variables, i.e.
#let ctx-α-rules = (
  rule(name: "nil-α", $dot αeq dot$),
  rule(name: "cons-α", $Γ, x: A αeq Γ', x': A$, $Γ αeq Γ'$),
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(ctx-α-rules.at(0)),
  proof-tree(ctx-α-rules.at(1)),
))
We say two _weakenings_ are equivalent if their derivations are isomorphic, i.e.
#let wk-α-rules = (
  rule(name: "nil-α", $dot ↦ dot αeq dot ↦ dot$),
  rule(name: "skip-α", $Γ, x: A ↦ Δ αeq Γ', x': A ↦ Δ'$, $Γ ↦ Δ αeq Γ' ↦ Δ'$, $x ∉ Δ$, $x' ∉ Δ'$),
  rule(name: "cons-α", $Γ, x: A ↦ Δ, x: A αeq Γ', x': A ↦ Δ', x': A$, $Γ ↦ Δ αeq Γ' ↦ Δ'$),
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(wk-α-rules.at(0)),
  proof-tree(wk-α-rules.at(1)),
))
$
  #proof-tree(wk-α-rules.at(2))
$

Note in particular that if $Γ ↦ Δ αeq Γ' ↦ Δ'$, then $Δ αeq Δ'$ but $Γ$ is not necessarily $α$-equivalent to $Γ'$, since they may differ on dropped variables; however, $sans("len")(Γ) = sans("len")(Γ')$.

We can now define the $α$-equivalence of well-typed terms in a trivial manner:
#let tm-α-rules = (
  rule(name: "var-α", $Γ ⊢ x : A αeq Γ' ⊢ x' : A$, $Γ ↦ x : A αeq Γ' ↦ x' : A$),
  rule(name: "app-α", $Γ ⊢ f med e : A αeq Γ' ⊢ f med e' : A$, $f : intp(p, A, B)$, $Γ ⊢ e : A αeq Γ' ⊢ e' : A$),
  rule(name: "pair-α", $Γ ⊢ (l, r) : A ⊗ B αeq Γ' ⊢ (l', r') : A ⊗ B$, $Γ ⊢ l : A αeq Γ' ⊢ l' : A$, $Γ ⊢ r : B αeq Γ' ⊢ r' : B$),
  rule(name: "unit-α", $Γ ⊢ () : bold(1) αeq Γ' ⊢ () : bold(1)$/*, $sans("len")(Γ) = sans("len")(Γ')$*/)
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(tm-α-rules.at(0)),
  proof-tree(tm-α-rules.at(1)),
))
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(tm-α-rules.at(2)),
  proof-tree(tm-α-rules.at(3)),
))
In general, we have that if $Γ ⊢ e : A αeq Γ' ⊢ e' : A$ then $∃Δ, Δ'$ such that $Γ ↦ Δ αeq Γ' ↦ Δ'$, $Δ αeq Δ'$ and $Δ ⊢ e : A αeq Δ' ⊢ e' : A$.
Note that, leaving the context invariant, $αeq$ on terms is just the identity relation. 
The ability to vary the context, however, allows us to define α-equivalence of well-typed bodies as
follows:
#let blk-α-rules = (
  rule(name: "nil-α", $Γ ⊢ () lto Δ αeq Γ' ⊢ () lto Δ'$, $Γ ↦ Δ αeq Γ' ↦ Δ'$),
  rule(name: "let1-α", $Γ ⊢ let1(x, e); b lto Δ αeq Γ' ⊢ let1(x', e'); b' lto Δ'$, $Γ ⊢ e : A αeq Γ' ⊢ e' : A$, $Γ, x : A ⊢ b lto Δ αeq Γ', x' : A ⊢ b' lto Δ'$),
  rule(name: "let2-α", $Γ ⊢ let2(x, y, e); b lto Δ αeq Γ' ⊢ let2(x', y', e'); b' lto Δ'$, $Γ ⊢ e : A αeq Γ' ⊢ e' : A ⊗ B$, $Γ, x : A, y : B ⊢ b lto Δ αeq Γ', x' : A, y' : B ⊢ b' lto Δ'$),
)
$
#proof-tree(blk-α-rules.at(0))
$
$
#proof-tree(blk-α-rules.at(1))
$
$
#proof-tree(blk-α-rules.at(2))
$
Unlike for terms, for invariant input and output contexts, this is not merely the identity relation, since, for example, we have
#align(center + horizon, table(
  columns: 3,
  gutter: 2em,
  stroke: none,
  stack(dir: ltr, spacing: 1em,
    $⊢$,
    ```
    x = 5;
    y = x + 2;
    z = y + 7
    ```,
    $lto$,
    `z : i64`
  ),
  $αeq$,
  stack(dir: ltr, spacing: 1em,
    $⊢$,
    ```
    x = 5;
    y' = x + 2;
    z = y' + 7
    ```,
    $lto$,
    `z : i64`
  ),
))

For the case of control-flow, we can define the $α$-equivalence of targets to consist of renaming both labels and live variables, as follows:
#todo[reflow the above]
#let trg-α-rules = (
  rule(name: "nil-α", $dot αeq dot$),
  rule(name: "cons-α", $L, lbl(ℓ)[Γ](A) αeq L', lbl(ℓ')[Γ'](A)$, $L αeq L'$, $Γ αeq Γ'$)
)
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(trg-α-rules.at(0)),
  proof-tree(trg-α-rules.at(1)),
))

Target weakening $α$-equivalence can then be defined as follows:
#let twk-α-rules = (
  rule(name: "nil-α", $twk(dot, dot) αeq twk(dot, dot)$),
  rule(name: "cons-α", $twk(#$L, lbl(ℓ)[Γ](A)$, #$K, lbl(ℓ)[Δ](A)$) αeq twk(#$L', lbl(ℓ')[Γ'](A)$, #$K', lbl(ℓ')[Δ'](A)$)$, $twk(L, K) αeq twk(L', K')$, $Γ ↦ Δ αeq Γ' ↦ Δ'$),
  rule(name: "drop-α", $twk(L, #$K, lbl(ℓ)[Δ](A)$) αeq twk(L', #$K', lbl(ℓ')[Δ'](A)$)$, $twk(L, K) αeq twk(L', K')$, $lbl(ℓ) ∉ K$, $lbl(ℓ') ∉ K'$)
)

#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(twk-α-rules.at(0)),
  proof-tree(twk-α-rules.at(1)),
))
$
#proof-tree(twk-α-rules.at(2)),
$

#todo[stick some properties here?]

Using this, we may define $α$-equivalence for well-typed terminators as follows:
#let term-α-rules = (
  rule(name: "br-α", $Γ ⊢ lbr(ℓ, e) lto sans(L) αeq Γ' ⊢ lbr(ℓ', e) lto sans(L')$, 
    $Γ ⊢ e : A αeq Γ' ⊢ e : A$,
    $lbr(ℓ, e) lto sans(L) αeq lbr(ℓ', e) lto sans(L')$),
  rule(name: "ite-α", $Γ ⊢ lite(e, s, t) lto sans(L) αeq Γ ⊢ lite(e', s', t') lto sans(L')$, $Γ ⊢ e : bold(2) αeq Γ' ⊢ e' : bold(2)$, $Γ ⊢ s lto sans(L) αeq Γ' ⊢ s' lto sans(L')$, $Γ ⊢ t lto sans(L) αeq Γ' ⊢ t' lto sans(L')$),
)
$
#proof-tree(term-α-rules.at(0))
$
$
#proof-tree(term-α-rules.at(1))
$

Naïvely, one may use the above definitions to define $α$-equivalence for basic blocks as follows:
#let naive-bb-α-rule = rule(name: "blk-α", $Γ ⊢ b; t lto sans(L) αeq Γ' ⊢ b'; t' lto sans(L')$, $Γ entp(p) b lto Δ αeq Γ' entp(p) b' lto Δ'$, $Δ ⊢ t lto sans(L) αeq Δ' ⊢ t' lto sans(L')$)
$
#proof-tree(naive-bb-α-rule)
$

#todo[
  This definition, however, seems a little too strong, since the choice of $Δ,Δ'$ adds an extra degree of freedom to the above derivation. Indeed, this extra degree of freedom is present in the typing rules for basic blocks as well, since coherence fails here ... try "maximal blocks"? Not an issue for regions and generalized regions
]

Well-typed CFGs and regions can then be deemed $α$-equivalent as follows:

#let cfg-α-rules = (
  rule(name: "nil-cf-α", 
    $sans(L) ⊢ dot lto sans(K) αeq sans(L') ⊢ dot lto sans(K')$, 
    $twk(sans(L), sans(K)) αeq twk(sans(L'), sans(K'))$),
  rule(name: "cons-cf-α", 
    $sans(L) ⊢ L, lblk(lbl(ℓ), (x: A), β) lto sans(K) 
      αeq sans(L') ⊢ L', lblk(lbl(ℓ'), (x': A), β') lto sans(K')$, 
    $sans(L) ⊢ L lto sans(K), lbl(ℓ)[Γ](A) αeq sans(L') ⊢ L' lto sans(K), lbl(ℓ')[Γ'](A)$,
    $Γ ⊢ β lto sans(L) αeq Γ' ⊢ β' lto sans(L')$),
)
#let naive-reg-α-rule = rule(name: "reg-α",
  $Γ ⊢ lwhere(β, L) lto sans(K) αeq Γ' ⊢ lwhere(β', L') lto sans(K')$,
  $Γ ⊢ β lto sans(L) αeq Γ' ⊢ β' lto sans(L')$,
  $sans(L) ⊢ L lto sans(K) αeq sans(L') ⊢ L' lto sans(K')$
)
$
#proof-tree(cfg-α-rules.at(0))
$
$
#proof-tree(cfg-α-rules.at(1))
$
$
#proof-tree(naive-reg-α-rule)
$

#todo[this has the same problem with too many degrees of freedom]

On the other hand, determining whether untyped expressions are $α$-equivalent is quite challenging, since, when renaming a variable, we have to consider whether that variable is shadowed or not, and if so, where it is shadowed. 

#todo[footnote on "minimal typing" or "well-formedness"]

For example
...

One observation we can make, however, is that so far, we've given a grammar not for SSA per se, but rather for _three-address code_. In particular, non-SSA programs such as
$
#```
x = 0;
x = x + 1
```
$
are perfectly well-representable. This is a feature, not a bug, since it allows us to assign such programs a semantics and reason about transformations such as conversions to SSA form, as well as, potentially, optimizations and transformations defined on three-address code. For basic blocks, this poses little theoretical difficulty, since any non-SSA program is $α$-equivalent to a program in SSA form; for example, the above program can be rewritten as
$
#```
x0 = 0;
x1 = x0 + 1
```
$
Unfortunately, this does _not_ hold for programs containing general contral flow. For example, the program fragment
$
#```
^entry:
  x = 0;
  if b { br ^middle } else { br ^exit }
^middle:
  x = 1;
  br ^exit
^exit:
  x = x + 1
```
$
is _not_ $α$-equivalent to any program in SSA, since there are _two_ definitions for $x$ reaching the final assignment `x = x + 1`. Indeed; this is the motivation behind introducing arguments/$ϕ$-nodes in the first place, as it allows us to rewrite the above in SSA form as
$
#```
^entry:
  x0 = 0;
  if b { br ^middle } else { br ^exit(x0) }
^middle:
  x1 = 1;
  br ^exit(x1)
^exit(x2: i64):
  x3 = x2 + 1
```
$
$α$-equivalence for untyped program fragments in SSA form can be easily defined, since

#todo[consistent assignment of variables]

#todo[somewhere: "everything weakens to a duplicate-free context"]

#todo[somewhere: "everything is $α$-equivalent to a duplicate-free context"]

#todo[somewhere: "being duplicate free is preserved by weakening"]

=== $β$-Equivalence and Substitution

#todo[this]

=== $η$-Equivalence

#todo[this]

=== Generalized Regions

#todo[intro, why we want generalized regions]

We can generalize this slightly by fusing terminators, basic blocks, and regions into a single syntactic category, the _generalized region_, as follows:
- _Generalized regions_ $r, s, t$: $lbr(lbl(ℓ), e) | lite(e, s, t) | let1(x, e); t | let2(x, y, e); t | lwhere(t, L)$
Note that we remove dependencies on bodies $b$. One may also notice that the given grammar is slightly ambiguous: we can parse
$let1(x, e); lwhere(t, L)$ as $lwhere((let1(x, e); t), L)$ or $let1(x, e); (lwhere(t, L))$. We will always do the former, however, when both are well-typed, our equational theory should validate that these parses are equivalent, excusing the ambiguity.

The rules for terms remain unchanged; while the rules for generalized regions can be derived straightforwardly as follows:
#let gen-reg-rules = (
  rule(name: "let", 
    $Γ ⊢ let1(x, e); t lto sans(L)$, 
    $Γ entp(p) e: A$, $Γ, x: A ⊢ t lto sans(L)$),
  rule(name: "let2", 
    $Γ ⊢ let1((x, y), e); t lto sans(L)$, 
    $Γ entp(p) e: A ⊗ B$, $Γ, x: A, y: B ⊢ t lto sans(L)$),
  rule(name: "reg", 
    $Γ ⊢ lwhere(t, L) lto sans(K)$, 
    $Γ ⊢ t lto sans(L)$, $sans(L) ⊢ L lto sans(K)$),
);
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(terminator-rules.at(0)),
  proof-tree(terminator-rules.at(1)),
))
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(gen-reg-rules.at(0)),
  proof-tree(gen-reg-rules.at(1)),
))
#align(center, proof-tree(gen-reg-rules.at(2)))

We would like to define our equational theory in this generalized setting, and then show that via our equational theory every term can be normalized to standard SSA; this trivially induces an equational theory on standard SSA while making operations which modify control-flow much easier to define and reason about. 

#todo[$α$]

#todo[$β$]

#todo[$η$]

=== $δ$-Equivalence

#todo[this]

== Dominator Trees

#todo[alternative approach: dominator trees]

#todo[
  STUFF TO PROVE:
  - every well-typed dominator tree well-typed as a generalized region, and $α$-equivalent to SSA
  - dominator trees allow us untyped $α$, and therefore in particular de-Bruijn indices
  - if a generalized region is $α$-equivalent to SSA, it is $α δ$-equivalent to a dominator tree, but like only weak $δ$s ("κ"?)
  - so can just define our equational theory over dominator trees for Freyd case, _but_ dominator trees don't do linearity so well :(. Need region nonsense, "optical morphisms" or "optical trains" or smt :(.
]

= Freyd Categories are Basic Blocks

For the rest of this paper, we will analyze the syntactic and semantic metatheory of each syntactic class one-by-one, beginning with terms and block bodies in the setting of Freyd categories. Of course, that means we need to start with defining what a Freyd category is.

== Freyd Categories

For our purposes, a Freyd category is a category $cal(C)$, which we will write $cal(C)_0$, equipped with a wide subcategory $cal(C)_1$ of _pure_ morphisms, such that:
- $cal(C)$ is equipped with a binary operation $⊗: |cal(C)| × |cal(C)| -> |cal(C)|$ on objects, the _tensor product_
- $cal(C)_1$ is Cartesian with product $⊗$, i.e.
  - There are morphisms $π_l: A ⊗ B -> A$, $π_r: A ⊗ B -> B$
  - For all $f: cal(C)_1(A, B)$, $g: cal(C)_1(A, C)$, there is a unique morphism $⟨f, g⟩: cal(C)_1(A, B ⊗ C)$ such that $⟨f, g⟩;π_l = f$ and $⟨f, g⟩;π_2 = g$
- $cal(C)_0$ is a _symmetric premonoidal category_ with tensor $⊗$, i.e., is equipped with
  - Natural transformations $A ⊗ -: B ↦ A ⊗ B$ and $- ⊗ A: B ↦ B ⊗ A$
  - A natural isomorphism $α: (A ⊗ B) ⊗ C ≃ A ⊗ (B ⊗ C)$, the _associator_
  - An _identity object_ $I ∈ |cal(C)|$
  - Natural isomorphisms $λ: I ⊗ A ↦ A, ρ: A ⊗ I ↦ A$, the _left and right unitor_
  - Satisfying the _triangle law_ and _pentagon law_
  - A natural isomorphism $σ: A ⊗ B ↦ B ⊗ A$, the _symmetry_
  - Satisfying the _hexagon law_
- The premonoidal structure agrees with the Cartesian structure, i.e. for _pure_ morphisms $f$ in $cal(C)_1$, 
  - $A ⊗ f = A × f = id × f = ⟨π_l;id, π_r;f⟩$ 
  - $f ⊗ A = f × A = f × id = ⟨π_l;f, π_r;id⟩$
  - $I$ is an _initial object_: there is always a unique morphism $!_A: cal(C)_1(A, I)$.
    Note that there may be multiple, different morphisms in $cal(C)_0(A, I)$, but exactly one must be pure.

Note a traditional Freyd category is given by an identity-on-objects functor $cal(V) -> cal(C)$ from a Cartesian category $cal(V)$ to a symmetric premonoidal category $cal(C)$ preserving all symmetric premonoidal structure; we can get one in our sense by simply considering the image of this functor as a wide subcategory. The only additional flexibility the original definitions have is that there can be pure morphisms $f, g$ which are different in $cal(V)$ but equated when passed along the functor into $cal(C)$.

Note that $cal(C)_1$ does _not_ have to be the maximal Cartesian subcategory of $cal(C)_0$; it can even be as small as just the projections $π_l, π_r$, associators, unitors, symmetry, and initial morphisms $!$.

We introduce the following notation for premonoidal categories: given morphisms $f: cal(C)(A, B), g: cal(C)(A', B')$,
- $f ⋉ g = f ⊗ A';B ⊗ g: cal(C)(A ⊗ A', B ⊗ B')$ ("first $f$ then $g$")
- $f ⋊ g = A ⊗ g;f ⊗ B': cal(C)(A ⊗ A', B ⊗ B')$ ("first $g$ then $f$")
We say a morphism $f$ is _central_ if,
$
∀g. f ⋉ g = f ⋊ g ∧ g ⋉ f = g ⋊ f
$
Note that in a symmetric premonoidal category, $f ⋉ g = f ⋊ g <==> g ⋉ f = g ⋊ f$. For such morphisms, we will write
$
f ⊗ g = f ⋉ g = f ⋊ g
$
Note in particular that
$f ⊗ A = f ⊗ id$ and $A ⊗ f = id ⊗ f$.
We say a premonoidal category is _monoidal_ if it satisfies _sliding_, i.e.
$
∀f, g. f ⋉ g = f ⋊ g
$
i.e. that every morphism is central. Note that every Cartesian category is monoidal, but not every monoidal category is Cartesian.

We can give an alternative characterization of a Cartesian category $cal(C)_1$ as follows:
- $cal(C)_1$ is symmetric monoidal
- There is an _initial object_ $bold(1)$ such that every object $A$ is equipped with a unique morphism $!_A: A -> bold(1)$
- For all objects $A ∈ |cal(C)_1|$, there is a _diagonal morphism_ $Δ_A: A -> A ⊗ A$
- For all $f: cal(C)_1 (A, B)$, $g: cal(C)_1 (A, C)$, we have that $Δ_A;f ⊗ g: cal(C)_1(A, B ⊗ C)$ is the unique morphism such that
  $
  Δ_A;f ⊗ g;B ⊗ !_C;ρ_B = f wide
  Δ_A;f ⊗ g;!_B ⊗ C;λ_C = g
  $

All conventional Cartesian categories can be equipped with this structure, since we can define 
- $Δ_A = ⟨id_A, id_A⟩$ 
- $f ⊗ A = Δ_(B ⊗ A);⟨π_l;f, π_r⟩$, $A ⊗ f = Δ_(A ⊗ B);⟨π_l, π_r;f⟩$
- $ρ_A = π_l$, $λ_A = π_r$, $α_(A, B, C) = ⟨π_l;π_l, ⟨π_l;π_r, π_r⟩⟩$
- $σ_(A, B) = ⟨π_r, π_l⟩$
Note in particular that for a Freyd category $cal(C)$, these definitions for the associators, unitors, and symmetry of $cal(C)_1$ will agree with the corresponding morphisms in $cal(C)_0$. 

Similarly, all categories with this structure must be Cartesian, as we can define
$
  π_l = A ⊗ !_B;ρ_A wide wide
  π_r = !_A ⊗ B;λ_B wide wide
  ⟨f, g⟩ = Δ_A;f ⊗ g
$

This alternative characterization makes it much easier to reason about _substructurality_, and in particular the existence of affine, relevant, and linear objects missing $!$, $Δ$, and both respectively. We will consider categories with such objects in @substruct.

== Semantics of Basic Blocks

We will start by considering only terms and the bodies of basic blocks. Our goal is to give these a semantics in terms of Freyd categories, for which we will prove an equational theory. We then wish to show that bodies quotiented under this equational theory _themselves_ form a Freyd category, and hence, that Freyd categories are the _initial_, or _canonical_, semantics for SSA.

We begin by attempting to give a semantics for types, contexts, terms, and bodies in terms of an arbitrary Freyd category $cal(C)$.

We can interpret types and contexts as objects in $cal(C)$ in the obvious manner:
$
#tybox($A$, $|cal(C)|$) wide &
[|X|] = X wide &
[|A ⊗ B|] = [|A|] ⊗ [|B|] wide &
[|bold(1)|] = I \
#tybox($Γ$, $|cal(C)|$) wide &
[|dot|] = I wide &
[|Γ, x: A|] = [|Γ|] ⊗ [|A|] wide &
$
We may then interpret well-typed terms in a Freyd category $cal(C)$ as follows:
$
#tybox($Γ entp(p) e: A$, $cal(C)_p ([|Γ|], [|A|])$)
$
$
[|#dprf(term-rules.at(0))|] = [|Γ ↦ x: A|] wide
[|#dprf(term-rules.at(1))|] = [|f|] ∘ [|Γ entp(1) e: A|]
$
$
[|#dprf(term-rules.at(2))|] 
  &= ⟨[|Γ entp(1) a: A|], [|Γ entp(1) b: B|]⟩
  \ &= Δ_([|Γ|]);[|Γ entp(1) a: A|] ⊗ [|Γ entp(1) b: B|]
$
$
[|#dprf(term-rules.at(3))|] = !_([|Γ|]) wide
[|#dprf(ctx-rules.at(0))|] = id_I wide
[|#dprf(ctx-rules.at(2))|] = π_l;[|Γ ↦ Δ|]
$
$
[|#dprf(ctx-rules.at(1))|] = [|Γ ↦ Δ|] ⊗ id_A
$
Well-typed block bodies can then be interpreted as follows:
$
#tybox($Γ entp(p) b: Δ$, $cal(C)_p ([|Γ|], [|Δ|])$)
$
$
[|#dprf(body-rules.at(0))|] &= [|Γ ↦ Δ|] \
[|#dprf(body-rules.at(1))|] &= 
  Δ_[|Γ|];[|Γ|] ⊗ [|Γ entp(p) e: A|];[|Γ, x: A entp(p) b: Δ|] \
[|#dprf(body-rules.at(2))|] &= Δ_[|Γ|]
  ;[|Γ|] ⊗ [|Γ entp(p) e: A ⊗ B|]
  ;α^(-1); \
  & #h(2em) [|Γ, x: A, y: B entp(p) b: Δ|]
$

#todo[per-rule explanations]

#todo[bad renaming, good renaming...]

#todo[quotienting under renaming...]

#todo[is this part of the metatheory section? maybe separate section for "coherence"?]

#todo[pull up to syntax section]

== Metatheory

#todo[SSA property not quite compositional _enough_; insures for subterms, but is not insured _by_ subterms, Pull down to equational theory section?]

#todo[equational theory holds under renaming, maybe?]

A quick sanity check for our semantics so far is that it respects _semantic weakening_.
(_Syntactic_) weakening is a property of our type system, provable by a straightforward induction, which says that
- If $Γ ↦ Δ$ and $Δ entp(p) e: A$, then $Γ entp(p) e: A$
- If $Γ ↦ Δ$ and $Δ entp(p) b: Ξ$, then $Γ entp(p) b: Ξ$
- If $Γ entp(p) b: Δ$ and $Δ ↦ Ξ$, then $Γ entp(p) b: Ξ$

#todo[issue: what about renaming. cycle back to previous discussion...]

#todo[option 1: contexts allow repetition, makes things ambiguous, lose _coherence_, but weakening still holds]
#todo[option 2: contexts do _not_ allow repetition: semantic weakening only holds for terms in SSA form]
#todo[essentially: weakening-on-derivations vs. weakening-on-terms]

We would like our semantics to be compatible with this property: in particular, we want that
$
[|Γ ↦ Δ|];[|Δ entp(p) e: A|] &= [|Γ entp(p) e: A|] \
[|Γ ↦ Δ|];[|Δ entp(p) b: Ξ|] &= [|Γ entp(p) b: Ξ|] \
[|Γ entp(p) b: Δ|];[|Δ ↦ Ξ|] &= [|Γ entp(p) b: Ξ|]
$
This can also be proved by a relatively trivial induction.

#todo[pull up to coherence section...]

Another important sanity check is that our semantics does not depend on such details as the names of variables. Of course, this is obvious by inspection, but nonetheless it makes sense to state this formally, as it will help us in formally reasoning about things such as the SSA property later. 

#todo[not so obvious now, is it...]

In particular, we can define the _renaming_ of a term under a (partial, injective) map $ρ: Var -> Var$ recursively as follows:
#align(center, stack(dir: ltr, spacing: 2em,
  $[ρ]x = ρ(x)$,
  $[ρ](f med e) = f med [ρ]e$,
  $[ρ]() = ()$,
  $[ρ](e, e') = ([ρ]e, [ρ]e')$,
))
Similarly, we can proceed to define the renaming of a _body_ as follows:
#align(center, stack(dir: ltr, spacing: 2em,
  $[ρ]dot = dot$,
  $[ρ](let1(x, e); b) = let1(ρ(x), [ρ]e); [ρ]b$,
))
$
[ρ](let1((x, y), e); b) = let1((ρ(x), ρ(y)), [ρ]e); [ρ]b
$
Note that the renaming of a _body_ also changes the variables used in a `let`-binding.
Contexts can also be renamed in the obvious fashion:
#align(center, stack(dir: ltr, spacing: 2em,
  $[ρ]dot = dot$,
  $[ρ](Γ, x: A) = [ρ]Γ, ρ(x): A$,
))
It follows that
$
Γ entp(p) e: A ==> [ρ]Γ entp(p) [ρ]e: A quad "and" quad
Γ entp(p) b: Δ ==> [ρ]Γ entp(p) [ρ]b: [ρ]Δ
$
Semantically, it is quite trivial to show that $[|[ρ]Γ|] = [|Γ|]$ and therefore that
$
[|Γ entp(p) e: A|] = [|[ρ]Γ entp(p) [ρ]e: A|] quad "and" quad
[|Γ entp(p) b: Δ|] = [|[ρ]Γ entp(p) [ρ]b: [ρ]Δ|]
$
This is a very important property, as it means that we can reason about the semantics of SSA without having to worry about the names of variables.

#todo[quotienting by _internal renaming_, SSA property preservation]

#todo[pointer to later: quotienting by _external renaming_]

Another important property in type theory is _substitution_: that we can replace all uses of a variable with its (pure) definition to get a well-typed term.

#todo[definition of substitution: insist on _finite support_ for Reasons (TM)]

#todo[syntactic substitution for terms]

#todo[syntactic substitution for bodies: progress + preservation]

#todo[nominal nonsense: define operation on quotient, then _pick_]

#todo[substitution to block; block version of substitution theorem...]

#todo[renaming vs substitution]

== Equational Theory

We may hence define a structural equivalence relation on well-typed terms and block bodies as follows:

#todo[parametrization by (equivalence) relation on terms...]

#todo[think about (generalized) peephole rewrites]

#todo[is $α$ fine here? Note this generates a PER-family, as does $α$-equivalence...]

$
#tybox(
  $Γ entp(p) e ≅ e': A$, 
  $[|Γ entp(p) e: A|] = [|Γ entp(p) e': A|]$)
$
#let term-struct-rules = (
  rule(name: "var-cong",
    $Γ entp(p) x ≃ x: A$, $Γ ↦ x: A$),
  rule(name: "app-cong",
    $Γ entp(p) f med e ≅ f med e'$, 
    $Γ entp(p) e ≅ e'$),
  rule(name: "pair-cong",
    $Γ entp(p) (a, b) ≅ (a', b')$, 
    $Γ entp(p) a ≅ a'$, $Γ entp(p) b ≅ b'$),
  rule(name: "η-nil",
    $Γ entp(p) e ≅ e': bold(1)$,
    $Γ entp(1) e: bold(1)$,
    $Γ entp(1) e': bold(1)$),
)
#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(term-struct-rules.at(0)),
  proof-tree(term-struct-rules.at(1)),
  proof-tree(term-struct-rules.at(3)),
))
#align(center, proof-tree(term-struct-rules.at(2)))
$
#tybox(
  $Γ entp(p) b ≅ b': Δ$, 
  $[|Γ entp(p) b: Δ|] = [|Γ entp(p) b': Δ|]$)
$
#let body-struct-rules = (
  rule(name: "symm", 
    $Γ entp(p) b' ≅ b$, 
    $Γ entp(p) b ≅ b'$),
  rule(name: "trans", 
    $Γ entp(p) b ≅ b''$, 
    $Γ entp(p) b ≅ b'$, $Γ entp(p) b' ≅ b'': Δ$),
  rule(name: "nil-cong", $Γ entp(p) dot ≅ dot: Δ$, $Γ ↦ Δ$),
  rule(name: "let-cong", 
    $Γ entp(p) let1(x, e); b ≅ let1(x, e'); b': Δ$, 
    $Γ entp(p) e ≅ e': A$,
    $Γ, x: A entp(p) b ≅ b': Δ$),
  rule(name: "let2-cong", 
    $Γ entp(p) let2(x, y, e); b ≅ let2(x, y, e'); b': Δ$, 
    $Γ entp(p) e ≅ e' A ⊗ B$,
    $Γ, x: A, y: B entp(p) b ≅ b': Δ$),
  rule(name: "α",
    $Γ entp(p) b ≅ [ρ]b: Δ$, 
    $Γ entp(p) b: Δ$, $Γ entp(p) [ρ]b: Δ$),
  rule(name: "β-let",
    $Γ entp(p) let1(x, e); b ≅ [sfor(e, x)]b: Δ$, 
    $Γ entp(1) e: A$,
    $Γ entp(p) let1(x, e); b: Δ$,
    $Γ entp(p) [sfor(e, x)]b: Δ$),
  rule(name: "β-let2",
    $Γ entp(p) let2(x, y, (e, e')) ≅ [sfor(e', y)][sfor(e, x)]b$,
    $Γ entp(p) let2(x, y, (e, e')); b: Δ$,
    $Γ entp(p) [sfor(e', y)][sfor(e, x)]b: Δ$),
  rule(name: "η-let2",
    $Γ entp(p) let2(x, y, e);let1(z, (x, y));b ≅ let1(z, e);b: Δ$,
    $Γ entp(p) let1(z, e);b: Δ$
  )
)
#align(center, table(
  columns: 3,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(body-struct-rules.at(0)),
  proof-tree(body-struct-rules.at(1)),
  proof-tree(body-struct-rules.at(2)),
))
#align(center, proof-tree(body-struct-rules.at(3)))
#align(center, proof-tree(body-struct-rules.at(4)))
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  proof-tree(body-struct-rules.at(5)),
  proof-tree(body-struct-rules.at(6)),
))
#align(center, proof-tree(body-struct-rules.at(7)))
#align(center, proof-tree(body-struct-rules.at(8)))
Note that for β-let2, $Γ entp(p) let2(x, y, (e, e')); b : Δ$ implies that $Γ entp(1) e: A$ and $Γ entp(1) e': B$, so these do not need to be added as hypotheses.

#todo[explanation of each rule]

#todo[fix $α$-conversion]

#todo[
  Some of the rules we can prove:
  - Pure operations are central (substitution in the middle)
  - Pure operations are affine
  - Pure operations are relevant
  - Non-deleting substitution
  - "$η$ for let": $f(g(a))$ and $(f(a), g(b))$, relationship to A-normal form
]

== Operations on Bodies

We can define the catenation of bodies as follows:
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  $dot;b' = b'$,
  $(let1(x, e); b);b' = let1(x, e);(b;b')$,
))
This satisfies the expected equations, e.g. $b;dot = b$ and $b_1;(b_2;b_3) = (b_1;b_2);b_3$. We furthermore have that
$
#proof-tree(rule($Γ entp(p) b;b': Ξ$, $Γ entp(p) b: Δ$, $Γ entp(p) b': Ξ$))
$
and, in particular,
$
[|Γ entp(p) b;b': Ξ|] = [|Γ entp(p) b: Δ|];[|Δ entp(p) b': Ξ|]
$

#todo[separate syntactic and semantic results]

Finally, we have congruence properties
$
Δ entp(p) b' ≅ b'': Ξ ==> Γ entp(p) b;b' ≅ b;b'': Ξ wide
Γ entp(p) b ≅ b': Δ ==> Γ entp(p) b;b'' ≅ b';b'': Ξ
$

== Basic Blocks are a Freyd Category

#todo[define syntax parametrized by types, instructions; quotient by $α$]

#todo[this is a category]

#todo[quotient further by structural rules]

#todo[this is a Freyd category]

#todo[the denotational semantics becomes a compiler pass sending us to A-normal form, when taken from syntax to syntax]

#todo[think about (generalized) peephole rewrites, for MLIR-isms]

#todo["what if nothing is pure": still, this is the right model, since tuples are pure, and tuples are nice. With no tuples we don't need Freyd, just premonoidal, and we end up with some strict premonoidal nonsense. ]

= Elgot Distributive Freyd Categories are SSA

== Elgot Categories

#todo[write out definition here]

== Distributive Categories

#todo[write out definition here]

== Semantics of Control-Flow Graphs

#todo[write out semantics here]

#todo[
  Structural rewrites on CFGs:
  - Congruence
  - Block rewrites
  - CFG-level $β$, somehow... this is a combined substitute + eliminate... see below...
  - $α$ renaming; see above
  - Permutation
]

== Metatheory

#todo[this]

== Equational Theory

#todo[
  Semantic rewrites on CFGs:
  - Unreachable code elimination
  - Jump-threading (maybe structural)
  - If-then-else elimination:
    - `true`/`false` $==>$ unconditional branch
    - merge equal branches regardless of discriminator
    - `if e { br ^ℓ true } else { br ^ℓ false } ==> br ^ℓ e`... do we need a primitive negation operator? otherwise, how do we show that
      `if e { br ^ℓ false } else { br ^ℓ true } ^ℓ(e): ...`... ah, via pushing blocks, which can be pulling blocks
  - Pushing blocks across an if-then-else, which should hopefully do $β$ in the central + relevant + affine model by float-to-bottom, jump-thread, splat, and remerge (maybe structural)
  - Fixpoint
  - Uniformity
  - Codiagonal
]

== SSA is an Elgot Distributive Freyd Category

#todo[We want to show that this gives us a Freyd category with a distributive Elgot structure. And that's SSA! Yay!]

#todo[for blocks this is still A-normal form; does this do anything to the CFG? maybe...]

= Substructurality <substruct>

#todo[this... stick blurbs here?]

== Substructural Categories

In a Freyd category $cal(C)$, morphisms in $cal(C)_1$ are _pure_: given $f: cal(C)_1(A, B)$ and $g: cal(C)_0(A', B')$, we have that $f$ is:
- *central*: $f ⋉ g = f ⋊ g$ and $g ⋉ f = g ⋊ f$
- *relevant*#footnote[
    Note that, for simplicity, we will currently ignore the case of relevant but non-central morphisms, which are defined as satisfying $f;Δ = Δ;f ⋉ f = Δ;f ⋊ f$, since this class of morphisms is _not_ closed under composition. For example, consider a morphism $f$ which crashes if a flag is set, and $f'$ which sets the flag. $f$ and $f'$ are both clearly relevant, _but_ $f;f';Δ ≠ Δ;(f;f')⋉(f;f')$, since the former will run fine while the latter will crash, as the $f$ on the right will run after the $f'$ on the left sets the flag.
    #todo[should we say relevant means relevant + central and then _weakly relevant_ just relevant? Seems inconsistent with affine, though... unless we do the same thing... Or we could do _discardable_ is affine + central and _copyable_ is relevant + central, though we should check @fuhrmann-1999 for precedent.]
  ]: $f;Δ_B = Δ_A;f ⊗ f$
- *affine*: $f;!_B = !_A$
These properties enable us to substitute expressions with pure morphisms for semantics, regardless of how variables are used or where they appear in a program. They are also _sufficient_ conditions for a morphism $f$ to be pure: given a Freyd category $cal(C)$, we can define its _pure center_ $cal(Z)_(a, r)(cal(C))$ to be the subcategory of all morphisms which are central, pure, and affine. This is indeed a subcategory, since
- Given $f, f'$ central, $f;f'$ is central since
  - $(f;f') ⋉ g = f ⊗ -;f' ⋉ g = f ⊗ -;f' ⋊ g = f ⋉ g;- ⊗ f' = f ⋊ g;- ⊗ f' = (f;f') ⋊ g$
  - $g ⋉ (f;f') = g ⋉ f;- ⊗ f' = g ⋊ f;- ⊗ f' = - ⊗ f;g ⋉ f' = - ⊗ f;g ⋊ f' = g ⋊ (f;f')$
- Given $f, f'$ relevant and central, $f;f'$ is relevant and central since
  $
    f;f';Δ = f;Δ;f' ⊗ f' = Δ;f ⊗ f;f' ⊗ f' = Δ;(f;f') ⊗ (f;f')
  $
- Given $f, f'$ affine, $f;f'$ is affine since
  $f;f';! = f;! = !$
It is similarly trivial to show that $cal(Z)^(a, r)(cal(C))$ is closed under tensor products and contains all associators, unitors, and symmetries, and hence that it satisfies all the properties necessary to be $cal(C)_1$ (though, in general, $cal(C)_1 ⊆ cal(Z)_(a, r)(cal(C))$).

We now ask which of these properties are _necessary_ to be able to reason algebraically aboud expressions. Substituting _non-central_ morphisms does not make sense in general, since moving an instruction to its usage site necessarily requires a change in the order of execution. However, if a variable is used exactly once, since the result is never duplicated or discarded, it should be safe to substitute an expression whose denotation is a morphism that is merely central, rather than pure. Similarly, if a variable is used _at most_ once, it should be safe to substitute an expression whose denotation is a morphism that is merely central and _affine_, while, if a variable is used _at least_ once, it should be safe to substitute an expression whose denotation is a morphism that is merely central and _relevant_. 

#todo[blurb about generalized peephole rewrites and why this matters?]

Since being central/relevant/affine are closed under composition and tensors (for central morphisms), we can define the _center_ of $C$, $cal(Z)(cal(C))$, to be the wide subcategory of central morphisms, the _relevant center_ $cal(Z)^(r)(cal(C))$ to be the wide subcategory of all morphisms which are central and relevant, and the _affine center_ $cal(Z)^(a)(cal(C)) ⊆ cal(Z)(cal(C))$ to be the wide subcategory of all morphisms which are central and affine. We can then write the _pure center_ as follows: $cal(Z)^(a, r)(cal(C)) = cal(Z)^(a)(cal(C)) ∪ cal(Z)^(r)(cal(C))$.

In this spirit, we can generalize the notion of Freyd categories to _substructural Freyd categories_ by postulating the existence of, for each _quantity_ $q ⊆ {a, r}$, wide subcategories $cal(C)_1^q ⊆ cal(Z)^q (cal(C))$, such that:
- $cal(C)_1 = cal(C)_1^(a, r)$
- $∀q, cal(C)^q_1 ⊆ cal(Z)^q (cal(C))$
- $∀q' ⊆ q, cal(C)^q_1 ⊇ cal(C)^(q')_1$
- $cal(C)_1^q$ is closed under tensor products
We say a substructural Freyd category is _modular_ if $cal(C)_1^(a, r) = cal(C)_1^a ∩ cal(C)_1^r$, which is true if and only if $∀q, q'. cal(C)_1^(q ∪ q') = cal(C)_1^q ∩ cal(C)_1^(q')$.

Note in particular that _every_ Freyd category $cal(C)$ may be interpreted as substructural in the following ways:
- Taking $∀q, cal(C)_1^q = cal(C)_1$. This is the _minimal_ substructural Freyd category compatible with $cal(C)$.
- Taking $cal(C)_1^r = cal(Z)^(r)(cal(C))$, $cal(C)_1^a = cal(Z)^(a)(cal(C))$, and $cal(C)_1^(a, r) = cal(Z)^(a, r)(cal(C))$ This is the _maximal_ substructural Freyd category compatible with $cal(C)$.

#todo[blurb about complete lattice... probably a footnote is best...]

#todo[segue to discuss nonlinear objects, "our typing rules already need to support nonlinearity"...]

#todo[blurb about usefulness in e.g. separation logic. contrast w/ quantifier-free refinement types model...]

Following @premonoidal-string-diagrams-mario-2022, we define an _effectful category_ $cal(C)$ to be a generalization of a Freyd category for which $cal(C)_1$ is not necessarily Cartesian, but rather simply symmetric monoidal. That is, an effecful category $cal(C)$ is a premonoidal category $cal(C)_0$ equipped with a wide subcategory $cal(C)_1 ⊆ cal(Z)(cal(C))$ which contains all symmetric monoidal structure of $cal(Z)(cal(C))$.

#todo[substructural effectful categories]

#todo[Freyd means every object is affine + relevant $==>$ Cartesian]

#todo[in particular, full subcategory of affine + relevant objects would be Cartesian]

#pagebreak()

#bibliography("references.bib")

#pagebreak()

#set heading(numbering: "A.1.")
#counter(heading).update(())
#text(2em)[*Appendix*]

= Proofs

#todo[this should probably just be formalized, with pointers...]

We begin by stating some of the basic properties of weakenings:
- If $Γ ↦ Δ$ and $Δ ↦ Ξ$, then $Γ ↦ Ξ$
  #proof[
    By induction on the derivation of $Γ ↦ Δ$:
    - (nil-wk): since $Δ = dot$, by inversion, $Ξ = dot$, and hence $Γ ↦ Ξ$ by (nil-wk)
    - (cons-wk): taking $Γ = Γ', x: A$ and $Δ = Δ', x: A$ and assuming $Γ' ↦ Δ'$, case anaylsis on $Δ', x: A -> Ξ$ yields either
      - (cons-wk): in which case $Ξ = Ξ', x: A$ and $Δ' ↦ Ξ'$; therefore, $Γ' ↦ Ξ'$ by induction. Applying (cons-wk) yields $Γ = Γ', x: A ↦ Ξ = Ξ', x: A$ as desired
      - (drop-wk): in which case $Δ' ↦ Ξ$ and $x ∉ Ξ$, therefore $Γ' ↦ Ξ$ by induction. Applying (drop-wk) yields $Γ = Γ', x: A ↦ Ξ$ as desired
    - (drop-wk): taking $Γ = Γ', x: A$ and assuming $Γ' ↦ Δ$ and $x ∉ Δ$, by induction we have $Γ' ↦ Ξ$; furthermore, since $Δ ↦ Ξ$ we must have $x ∉ Ξ$, and therefore that $Γ = Γ', x: A ↦ Ξ$ by (drop-wk) as desired
  ]