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

#let todos = counter("todos")
#let todo(message) = align(center, text(red, [
  #todos.step()
  *TODO #todos.display():* #message
]))

#set heading (numbering: "1.")

= SSA is Freyd Categories⋆

#todo[_The_ denotational semantics of SSA]

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

In general, we will often consider blocks and regions satisfying the _SSA property_; namely, that no variable is ever "shadowed." In particular, no two `let`-bindings may write to the same variable, and no `let`-binding may overwrite a variable from the environment. This assumption will make reasoning significantly simpler. One useful fact about the SSA property is that, if it holds for a given expression, it also holds for all sub-expressions of that expression.

#todo[Uniqueness of variables, $α$-classes of bodies, CFGs, etc ...]

#todo[can we define a renaming _to_ something in SSA? Note: this means we can _never_ use a shadowed variable! etc...]

#todo[terminology such as SSA term, SSA region, etc...]

We can generalize this slightly by fusing terminators, basic blocks, and regions into a single syntactic category, the _generalized region_, as follows:
- _Generalized regions_ $r, s, t$: $lbr(lbl(ℓ), e) | lite(e, s, t) | llet(x, e); t | llet((x, y), e); t | lwhere(t, L)$
Note that we remove dependencies on bodies $b$. One may also notice that the given grammar is slightly ambiguous: we can parse
$llet(x, e); lwhere(t, L)$ as $lwhere((llet(x, e); t), L)$ or $llet(x, e); (lwhere(t, L))$. We will always do the former, however, when both are well-typed, our equational theory should validate that these parses are equivalent, excusing the ambiguity.

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

#todo[per-rule explanations]

We would like to define our equational theory in this generalized setting, and then show that via our equational theory every term can be normalized to standard SSA; this trivially induces an equational theory on standard SSA while making operations which modify control-flow much easier to define and reason about.

#todo[SSA property equivalence class... pull renaming up here?]

#todo[SSA property is preserved by injective renamings; so quotient by these]

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

All conventional Cartesian categories have this structure, since we can define 
- $Δ_A = ⟨id_A, id_A⟩$ 
- $f ⊗ A = Δ_(B ⊗ A);⟨π_l;f, π_r⟩$, $A ⊗ f = Δ_(A ⊗ B);⟨π_l, π_r;f⟩$
- $ρ_A = π_l$, $λ_A = π_r$, $α_(A, B, C) = ⟨π_l;π_l, ⟨π_l;π_r, π_r⟩⟩$
- $σ_(A, B) = ⟨π_r, π_l⟩$
Note in particular that for a Freyd category $cal(C)$, these definitions for the associators, unitors, and symmetry of $cal(C)_1$ will agree with the corresponding morphisms in $cal(C)_0$.

Similarly, all categories with this structure must be Cartesian, as we can define
- $π_l = A ⊗ !_B;ρ_A$, $π_r = !_A ⊗ B;λ_B$
- $⟨f, g⟩ = Δ_A;f ⊗ g$

This alternative characterization makes it clearer how we can generalize our semantics to consider substructurality, which we will  do in @substruct.

== Freyd Categories are Basic Blocks

We will start by considering only terms and the bodies of basic blocks. Our goal is to give these a semantics in terms of Freyd categories, for which we will prove an equational theory. We then wish to show that bodies quotiented under this equational theory _themselves_ form a Freyd category, and hence, that Freyd categories are the _initial_, or _canonical_, semantics for SSA.

=== Semantics

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

=== Metatheory

A quick sanity check for our semantics so far is that it respects _semantic weakening_.
(_Syntactic_) weakening is a property of our type system, provable by a straightforward induction, which says that
- If $Γ ↦ Δ$ and $Δ entp(p) e: A$, then $Γ entp(p) e: A$
- If $Γ ↦ Δ$ and $Δ entp(p) b: Ξ$, then $Γ entp(p) b: Ξ$
- If $Γ entp(p) b: Δ$ and $Δ ↦ Ξ$, then $Γ entp(p) b: Ξ$
We would like our semantics to be compatible with this property: in particular, we want that
$
[|Γ ↦ Δ|];[|Δ entp(p) e: A|] &= [|Γ entp(p) e: A|] \
[|Γ ↦ Δ|];[|Δ entp(p) b: Ξ|] &= [|Γ entp(p) b: Ξ|] \
[|Γ entp(p) b: Δ|];[|Δ ↦ Ξ|] &= [|Γ entp(p) b: Ξ|]
$
This can also be proved by a relatively trivial induction.

Another important property in type theory is _substitution_: that we can replace all uses of a variable with its (pure) definition to get a well-typed term.

#todo[definition of substitution]

#todo[syntactic substitution for terms]

#todo[syntactic substitution for bodies: progress + preservation]

#todo[pointer to nominal nonsense]

#todo[substitution to block; block version of substitution theorem...]

#todo[renaming intro; or pull-up]

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

#todo[renaming of contexts]

If a renaming $ρ$ is injective, it follows that
$
Γ entp(p) e: A ==> [ρ]Γ entp(p) [ρ]e: A quad "and" quad
Γ entp(p) b: Δ ==> [ρ]Γ entp(p) [ρ]b: [ρ]Δ
$

#todo[renaming vs substitution]

#todo[Capture-avoiding renaming (nominal) nonsense...]

#todo[equivalence class, SSA property nonsense...]

=== Equational Theory

We may hence define a structural equivalence relation on well-typed terms and block bodies as follows:

#todo[parametrization by (equivalence) relation on terms...]

#todo[think about (generalized) peephole rewrites]

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
    $Γ entp(p) llet(x, e); b ≅ llet(x, e'); b': Δ$, 
    $Γ entp(p) e ≅ e': A$,
    $Γ, x: A entp(p) b ≅ b': Δ$),
  rule(name: "let2-cong", 
    $Γ entp(p) llet((x, y), e); b ≅ llet((x, y), e'); b': Δ$, 
    $Γ entp(p) e ≅ e' A ⊗ B$,
    $Γ, x: A, y: B entp(p) b ≅ b': Δ$),
  rule(name: "α",
    $Γ entp(p) b ≅ [ρ]b: Δ$, 
    $Γ entp(p) b: Δ$, $Γ entp(p) [ρ]b: Δ$),
  rule(name: "β-let",
    $Γ entp(p) llet(x, e); b ≅ [sfor(e, x)]b: Δ$, 
    $Γ entp(1) e: A$,
    $Γ entp(p) llet(x, e); b: Δ$,
    $Γ entp(p) [sfor(e, x)]b: Δ$),
  rule(name: "β-let2",
    $Γ entp(p) llet((x, y), (e, e')) ≅ [sfor(e', y)][sfor(e, x)]b$,
    $Γ entp(p) llet((x, y), (e, e')); b: Δ$,
    $Γ entp(p) [sfor(e', y)][sfor(e, x)]b: Δ$),
  rule(name: "η-let2",
    $Γ entp(p) llet((x, y), e);llet(z, (x, y));b ≅ llet(z, e);b: Δ$,
    $Γ entp(p) llet(z, e);b: Δ$
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
Note that for β-let2, $Γ entp(p) llet((x, y), (e, e')); b : Δ$ implies that $Γ entp(1) e: A$ and $Γ entp(1) e': B$, so these do not need to be added as hypotheses.

#todo[explanation of each rule]

#todo[
  Some of the rules we can prove:
  - Pure operations are central (substitution in the middle)
  - Pure operations are affine
  - Pure operations are relevant
  - Non-deleting substitution
  - "$η$ for let": $f(g(a))$ and $(f(a), g(b))$, relationship to A-normal form
]

=== Operations on Bodies

We can define the catenation of bodies as follows:
#align(center, table(
  columns: 2,
  gutter: 2em,
  align: bottom,
  stroke: none,
  $dot;b' = b'$,
  $(llet(x, e); b);b' = llet(x, e);(b;b')$,
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

== Basic Block Bodies are a Freyd Category

#todo[define syntax parametrized by types, instructions; quotient by $α$]

#todo[this is a category]

#todo[quotient further by structural rules]

#todo[this is a Freyd category]

#todo[the denotational semantics becomes a compiler pass sending us to A-normal form, when taken from syntax to syntax]

#todo[think about (generalized) peephole rewrites, for MLIR-isms]

#todo["what if nothing is pure": still, this is the right model, since tuples are pure, and tuples are nice. With no tuples we don't need Freyd, just premonoidal, and we end up with some strict premonoidal nonsense. ]

== Elgot Distributive Freyd Categories

#todo[write out definition here]

== Elgot Distributive Freyd Categories are SSA

#todo[write out semantics here]

#todo[
  Structural rewrites on CFGs:
  - Congruence
  - Block rewrites
  - CFG-level $β$, somehow... this is a combined substitute + eliminate... see below...
  - $α$ renaming; see above
  - Permutation
]

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

We want to show that this gives us a Freyd category with a distributive Elgot structure. And that's SSA! Yay!

== SSA is an Elgot Distributive Freyd Category

#todo[for blocks this is still A-normal form; does this do anything to the CFG? maybe...]

= Substructural SSA is Substructural Effectful Categories⋆ <substruct>

== Effectful Categories

#todo[this...]

== Substructural Effectful Categories

#todo[this...]

== Substructural Basic Blocks is Substructural Effectful Categories

#todo[this...]

== Substructural SSA is Substructural Elgot Effectful Categories

#todo[this...]

= Substructural SSA is Substructural 2-Posets⋆

== 2-Posets

#todo[this...]

== Substructural Effectful 2-Posets

#todo[this...]

== Substructural Basic Blocks is Substructural Effectful 2-Posets

#todo[this...]

== Elgot 2-Posets

#todo[this...]

== Substructural SSA is Substructural Elgot 2-Posets

#todo[this...]

#todo[factor into appendix?]

== The Optical Category

#todo[this...]

== Dominator-Tree Syntax

#todo[this]

#todo[think about split vs. splat...]

#todo[appendix with proofs? or do we just formalize?]

#todo[fun with projections]

#todo[fun with directed centrality: _acquire_ and _release_...]