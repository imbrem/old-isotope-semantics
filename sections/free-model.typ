#import "@preview/curryst:0.1.1": rule, proof-tree

#let lbl(labl) = $ #`^`labl$
#let llet(x, e) = $sans("let") med #x = #e$
#let lite(e, s, t) = $sans("if") med #e med { #s } med sans("else") med { #t }$
#let lbr(l, e) = $sans("br") med #l med #e$
#let lblk(l, a, e) = $#l #a: #e$
#let lwhere(β, L) = $#β med sans("where") med #L$
#let lwk(Γ, Δ) = $#Γ ↦ #Δ$
#let twk(L, K) = $#L ⇝ #K$
#let lto = $triangle.stroked.small.r$

#let ltt = $sans("tt")$
#let lff = $sans("ff")$
#let Var = $sans("Var")$

#let dprf(tree) = box(baseline: 40%, proof-tree(tree))
#let entp(p) = $attach(⊢, br: #p)$
#let intp(p, A, B) = $sans("inst")_(#p)(#A, #B)$
#let tybox(judgement, typ) = rect(
  inset: 0.7em, 
  align(horizon, $[|#judgement|]: #typ$))

= SSA is Freyd Categories⋆

In this article, we make the argument that SSA corresponds exactly to Freyd categories⋆. We stick a "⋆" after Freyd category since, _depending what we mean by SSA_, we might need a bit of additional structure; we're also going to be using a slightly weird definition of Freyd category. To make this argument, we need to show that
- *Freyd categories⋆ are SSA*: SSA can be given a semantics in terms of Freyd categories which respects the equations we expect to hold for SSA programs
- *SSA is a Freyd category⋆*: SSA programs quotiented over these equations themselves form a Freyd category⋆
So, two questions come to mind: what is Freyd category, and what is SSA?

== SSA

An SSA program consists of 

- _Instructions_ of the form $x, y = #`call` f med a med b med c$, some of which may be _terminators_ such as $#`ret` x$ or $#`br` lbl(ℓ) med e$, which are organized into
- _Basic blocks_, which are a sequence of instructions of which only the last is a terminator, parametrized by a set of arguments, which form a 
- _Control-flow graph_, with edges where one basic block calls another

For now, we will restrict ourselves to the basic terminators necessary to implement unstructured control-flow, namely branching to a label with an argument, or a boolean choice between terminators. Note that returns can be implemented as simply an unconditional branch to a special "exit label."

We can define an SSA program to be given by a _region_: a control-flow graph with a distinguished, single _entry block_ and (potentially) multiple _exit blocks_. We'll make our life a little bit easier and generalize instructions to _terms_, which will allow us to have nested _pure_ expressions in an instruction and to implement multi-argument instructions using tuples. Then, we obtain
- _Terms_ $e$: $x | f med e | () | (e, e')$
- _Bodies_ $b$: $dot | llet(x, e); dot | llet((x, y), e); dot$
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
  rule(name: "drop-wk", $lwk(#$Γ, x: A$, Δ)$, $lwk(Γ, Δ)$),
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
  rule(name: "drop-twk", $twk(L, #$K, lbl(ℓ)[Δ](A)$)$, $twk(L, K)$),
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
  rule(name: "nil-st", $Γ entp(p) dot: Δ$, $lwk(Γ, Δ)$),
  rule(name: "let", $Γ entp(p) llet(x, e); b: Δ$, $Γ entp(p) e: A$, $Γ, x: A entp(p) b: Δ$),
  rule(name: "let2", $Γ entp(p) llet((x, y), e); b: Δ$, $Γ entp(p) e: A ⊗ B$, $Γ, x: A, y: B entp(p) b: Δ$),
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

We can generalize this slightly by fusing terminators, basic blocks, and regions into a single syntactic category, the _generalized region_, as follows:
- _Generalized regions_ $r, s, t$: $lbr(lbl(ℓ), e) | lite(e, s, t) | llet(x, e); t | llet((x, y), e); t | lwhere(t, L)$
Note that we remove dependencies on blocks $b$. We would like to define our equational theory in this generalized setting, and then show that via our equational theory every term can be normalized to standard SSA; this trivially induces an equational theory on standard SSA while making operations which modify control-flow much easier to define and reason about. One may also notice that the given grammar is slightly ambiguous: we can parse
$llet(x, e); lwhere(t, L)$ as $lwhere((llet(x, e); t), L)$ or $llet(x, e); (lwhere(t, L))$. We will always do the former, however, when both are well-typed, our equational theory should validate that these parses are equivalence, excusing the ambiguity.

The rules for terms remain unchanged; while the rules for generalized regions can be derived straightforwardly as follows:
#let gen-reg-rules = (
  rule(name: "let", 
    $Γ ⊢ llet(x, e); t lto sans(L)$, 
    $Γ entp(p) e: A$, $Γ, x: A ⊢ t lto sans(L)$),
  rule(name: "let2", 
    $Γ ⊢ llet((x, y), e); t lto sans(L)$, 
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

We can define the _renaming_ of a term under a map $ρ: Var -> Var$ recursively as follows:
#align(center, stack(dir: ltr, spacing: 2em,
  $[ρ]x = ρ(x)$,
  $[ρ](f med e) = f med [ρ]e$,
  $[ρ]() = ()$,
  $[ρ](e, e') = ([ρ]e, [ρ]e')$,
))
Similarly, we can proceed to define the renaming of a _body_ as follows:
#align(center, stack(dir: ltr, spacing: 2em,
  $[ρ]dot = dot$,
  $[ρ](llet(x, e); b) = llet(ρ(x), [ρ]e); [ρ]b$,
))
$
[ρ](llet((x, y), e); b) = llet((ρ(x), ρ(y)), [ρ]e); [ρ]b
$
Note that the renaming of a _body_ also changes the variables used in a `let`-binding.

If a renaming $ρ$ is injective, it follows that
$
Γ entp(p) e: A ==> [ρ]Γ entp(p) [ρ]e: A quad "and" quad
Γ entp(p) b: Δ ==> [ρ]Γ entp(p) [ρ]b: [ρ]Δ
$
In general, we will consider blocks and regions satisfying the _SSA property_; namely, that no variable is ever "shadowed." In particular, no two `let`-bindings may write to the same variable, and no `let`-binding may overwrite a variable from the environment.

Capture-avoiding renaming nonsense...

Uniqueness of variables, $α$-classes of bodies, CFGs, etc ...

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
  - There is always a unique morphism $!_A: cal(C)_1(A, I)$.
    Note that there may be multiple, different morphisms in $cal(C)_0(A, I)$, but exactly one must be pure.

Note a traditional Freyd category is given by an identity-on-objects functor $cal(V) -> cal(C)$ from a Cartesian category $cal(V)$ to a symmetric premonoidal category $cal(C)$ preserving all symmetric premonoidal structure; we can get one in our sense by simply considering the image of this functor as a wide subcategory. The only additional flexibility the original definitions have is that there can be pure morphisms $f, g$ which are different in $cal(V)$ but equated when passed along the functor into $cal(C)$.

TODO: alternative $Δ-!$ characterization of Cartesian structure...

TODO: pointer to effectful, substructural categories

== Freyd Categories are Basic Blocks

We can interpret well-typed terms in a Freyd category $cal(C)$ as follows:
$
#tybox($Γ entp(p) e: A$, $cal(C)_p ([|Γ|], [|A|])$)
$
//TODO: semantically, should there not be a multi-equation container of sorts...
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
[|#dprf(term-rules.at(3))|] = !_([|Γ|])
$
Weakening is simply interpreted in the underlying Cartesian structure as follows:
...
Well-typed blocks may then be interpreted as follows
...

We can define the catenation of bodies as follows:
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  $dot;b' = b'$,
  $(llet(x, e); b);b' = llet(x, e);(b;b')$,
))
This satisfies the expected equations, e.g. $b;dot = b$ and $b_1;(b_2;b_3) = (b_1;b_2);b_3$. We furthermore have
#align(center, proof-tree(rule($Γ ⊢ b;b': Ξ$, $Γ ⊢ b: Δ$, $Γ ⊢ b': Ξ$)))

TODO: show catenation respects semantics...

TODO: substititution; α-renaming...

TODO: advanced α-renaming?

Structural rewrites on bodies:
- Congruence
- $α$ renaming; see above
- Pure $β$ rules (note: this will need to be fixed for sub-structurality)
- Pure is relevant + affine $==>$ regular $β$
- Pure is central (?) 
- $η$ rules
Want to show that this gives us a Freyd category. Congruence should mean composition always respects these.

== Basic Blocks are a Freyd Category

TODO: this denotational semantics is just a compiler pass sending us to A-normal form

== Elgot Distributive Freyd Categories

TODO: write out definition here

== Elgot Distributive Freyd Categories are SSA

TODO: write out semantics here

Structural rewrites on CFGs:
- Congruence
- Block rewrites
- CFG-level $β$, somehow... this is a combined substitute + eliminate... see below...
- $α$ renaming; see above
- Permutation

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

We want to show that this gives us a Freyd category with a distributive Elgot structure. And that's SSA! Yay!

== SSA is an Elgot Distributive Freyd Category

TODO: for blocks this is still A-normal form; does this do anything to the CFG? maybe...

== Effectful Categories

...

== Substructural Effectful Categories

...

== Substructural Basic Blocks are a Substructural Effectful Category

...

== Substructural SSA is a Substructural Distributive Effectful Category

...