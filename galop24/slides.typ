#import "@preview/polylux:0.3.1": *
#import "@preview/curryst:0.1.0": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

#let highline(it) = [
  #show regex("(phi|add|sub|brz|ret|call)\s") : kw => strong(kw)
  #show regex("'.\w*") : label => text(purple, label)
  #show regex("//.*") : line => text(gray.darken(50%), line)
  #show regex(".*//.*✗") : line => text(red, line)
  #show regex(".*//.*✔") : line => text(green, line)
  #show regex(".*//.*‖") : line => text(yellow.darken(50%), line)
  #it
]

#show raw.where(lang: "isotope"): highline;

#title-slide[
  = SSA is Freyd Categories
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami

  University of Cambridge
  
  January 14

  GALOP'24 -- London
]

#focus-slide[
  = What is SSA?
]

#focus-slide[
  = Static Single Assignment
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n
      m = n
      n = t
      i = sub i 1
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0          
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n
      m = n          // ✗
      n = t          
      i = sub i 1    
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0          // ⇐
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n
      m = n          // ✗
      n = t          
      i = sub i 1    
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0          
      n = 1          // ⇐
      brz i 'exit 'loop
    'loop:
      t = add m n
      m = n          // ✗
      n = t          // ✗
      i = sub i 1    
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n
      m = n          // ✗
      n = t          // ✗
      i = sub i 1    // ✗
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n    // ✔
      m = n          // ✗
      n = t          // ✗
      i = sub i 1    // ✗
      brz i 'exit 'loop
    'exit:
      ret m
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon, stack(dir: ltr, spacing: 3em,
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m = 0
      n = 1
      brz i 'exit 'loop
    'loop:
      t = add m n    
      m = n          
      n = t          
      i = sub i 1    
      brz i 'exit 'loop
    'exit:
      ret m
    ```, $==>$,
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m0 = 0
      n0 = 1
      brz i 'exit(m0)          // ‖
            'loop(i, m0, n0)   // ‖
    'loop(i0, m1, n1):         // ‖
      m2 = n1
      n2 = add m1 n1
      i1 = sub i0 1
      brz i1 'exit(m2)         // ‖
             'loop(i1, m2, n2) // ‖
    'exit(m3):                 // ‖
      ret m3
    ```
  ))
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m0 = 0
      n0 = 1
      brz i 'exit 'loop
    'loop:     
      i0 = phi ('entry => i) ('loop => i1)  // ‖
      m1 = phi ('entry => m0) ('loop => m2) // ‖     
      n1 = phi ('entry => n0) ('loop => n2) // ‖            
      m2 = n1
      n2 = add m1 n1
      i1 = sub i0 1
      brz i1 'exit 'loop                   
    'exit:                               
      m3 = phi ('entry => m0) ('loop => m2) // ‖
      ret m3
    ```
  ]
]

#focus-slide[
  = So, why SSA?
]

#slide[
  = Wide Usage of SSA
  #line-by-line[
    - Classical compilers
    - MLIR:
      #line-by-line(start: 3)[
      - GPU (SPIR-V)
      - CPU
      - FPGA -- CIRCT
      - Even quantum computing!
      ]
  ]
]

#slide[
  = Practice
  #line-by-line[
    - Easier to reason about variables
    - $==>$ strength reduction, scalar replacement
    - $==>$ conditional constant propagation
    - Easier to compute dependencies
    - $==>$ easier dataflow analyses (e.g. analysis passes)
    - $==>$ easier register allocation
  ]
]

#slide[
  = Practice: Algebraic Reasoning
  - Easier to reason about variables: #only("7-", [*substitution*])
  #only("2-", align(center + horizon, stack(dir: ltr, spacing: 3em,
    ```isotope
      ...
      x = add y z
      brz b 'one 'two
    'one:
      w = sub x y
      t = add w y
      ...
    ```,
    only("3-", $==>$),
    [
      #only("3", 
        ```isotope      
          ...
          x = add y z
          brz b 'one 'two
        'one:
          // substitute x
          w = sub (add y z) y
          t = add w y
          ...
        ```
      )
      #only("4",
        ```isotope      
          ...
          x = add y z
          brz b 'one 'two
        'one:
          // (y + z) - y == z
          w = z
          t = add w y
          ...
        ```
      )
      #only("5",
        ```isotope      
          ...
          x = add y z
          brz b 'one 'two
        'one:
          t = add z y
          ...
        ```
      )
      #only("6-",
        ```isotope      
          ...
          x = add y z
          brz b 'one 'two
        'one:
          t = x
          ...
        ```
      )
    ]
    )))
]

#slide[
  = Practice: Dependency Analysis
  #align(center + horizon, 
    stack(dir: ltr, spacing: 3em,
      ```isotope
      ...
      x = add a b
      call print x
      y = add x b
      z = add x a
      call print y
      ...
      ```,
      $==>$,
      image("ssa-dfg-1.svg", width: 30%)
    ))
]

/*
#slide[
  = Practice: Control-Flow Analysis
  #align(center + horizon, 
    [
      #only("1", image("ssa-cfg-1.svg", height: 80%))
      #only("2", image("ssa-cfg-1-dom.svg", height: 80%))
      #only("3", 
      stack(dir: ltr, spacing: 3em,
        image("ssa-cfg-1-dom.svg", height: 80%),
        image("ssa-dfg-2.svg", height: 80%)
      ))
    ]
  )
]
*/

#slide[
  = Theory

  #v(2em)

  #align(center)[*Wide usage* $==>$ *Underlying Categorical Structure*]

  #v(2em)
  
  #uncover("2-")[Examples:]
  #line-by-line(start: 3)[
    - String diagrams $==>$ Monoidal categories
    - STLC $==>$ Cartesian closed categories
    - Effects $==>$ Monads
    - *Call-by-value $==>$ Freyd categories*
  ]
]

#slide[
  = Freyd Categories
  #align(center + horizon, stack(dir: ttb, spacing: 2em,
     grid(
      columns: 5,
      column-gutter: 3em,
      row-gutter: 0.5em,
      uncover("1-", $cal(C)_1$),
      uncover("3-", $-->_#[i.o.o]^((-)^↑)$),
      uncover("3-", $Z(cal(C)_0)$),
      uncover("3-", $↪$),
      uncover("2-", $cal(C)_0$),
      uncover("1-")[
        (Cartesian)
      ],
      [], [], [],
      uncover("2-")[
        (Premonoidal)
      ],
    ),
    {
      only("4", $⊗: cal(C) × cal(C)_0 -> cal(C)_0$)
      only("5", $A ⊗ -, - ⊗ A: cal(C)_0 -> cal(C)_0$)
      let forall_stmt = $∀f,$;
      stack(
        dir: ltr,
        spacing: 2em,
        uncover("8-", forall_stmt),
        {
          only("6", $f ⊗ -;- ⊗ g$)
          only("7-", $f ⊗ -;- ⊗ g "PRE"$)
        },
        {
          only("6-7", $≠$)
          only("8-", $=$)
        },
        {
          only("6", $- ⊗ g;f ⊗ -$)
          only("7-", $- ⊗ g;f ⊗ - "PRE"$)
        },
        hide(forall_stmt)
      )
    },
    uncover("8-", $==> g ∈ Z(C)(A, B)$)
  ))
]

//TODO: monoidal, premonoidal diagrams

#slide[
  = Call-by-value is Freyd categories
  #align(center + horizon, image("ssa-dfg-1.svg", width: 45%))
]

#let tst(purity) = $attach(⊢, br: purity)$
#let upg(e, purity) = $#e^(attach(↑, br: purity))$

#let arr(purity, left, right) = $left attach(->, br: purity) right$
#let expr-var(ctx, purity, var, ty) = rule(name: "var", $ctx tst(purity) var: ty$, $var: ty ∈ ctx$)
#let expr-tt(ctx, purity) = rule(name: "tt", $ctx tst(purity) sans("tt"): bold(2)$, $$)
#let expr-ff(ctx, purity) = rule(name: "ff", $ctx tst(purity) sans("ff"): bold(2)$, $$)
#let expr-app(c, f, p) = rule(name: "app", c, f, p)
#let expr-pair(c, l, r) = rule(name: "pair", c, l, r)
#let expr-pi(c, l) = rule(name: $π$, c, l)

#let dnt(p) = $[|#block(p)|]$

#slide[
  = Call-by-value: Notation

  #align(center + horizon, stack(dir: ttb, spacing: 3em,
    stack(dir: ltr, spacing: 3em,
      $
      A &::= X | A × B \
      Γ &::= dot | Γ, x: A
      $,
      uncover("2-", $
      [|A|], [|X|], [|Γ|] &: |cal(C)_0| \
      [|A × B|] &= [|A|] × [|B|] \
      [|Γ, x: A|] &= [|Γ|] × [|A|]
      $)
    ),
    uncover("3-", $[|Γ tst(p) a: A|]: cal(C)_p ([|Γ|], [|A|])$),
    uncover("4-", $f: arr(p, A, B) ==> [|f|] ∈ cal(C)_p (A, B)$),
  ))

    /*
    $
    #dnt(proof-tree(expr-var($Γ$, $p$, $x$, $A$))) = π_x
    $
    $
    #dnt(proof-tree(expr-app($Γ tst(p) f med a: B$, $f: arr(p, A, B)$, $Γ tst(1) a: A$))) 
      = [|f|];dnt[|Γ tst(1) a med A|]^(↑_p)
    $
    $
    #dnt(proof-tree(expr-pair($Γ tst(1) (a, b): A × B$, $Γ tst(1) a: A$, $Γ tst(1) b: B$)))
      = ⟨[|Γ tst(1) a: A|], [|Γ tst(1) b: B|]⟩ 
    $
    $
    #dnt(proof-tree(expr-pi($Γ tst(1) π_i e: A_i$, $Γ tst(1) e: A_0 × A_1$)))
      = [|Γ tst(1) e: A_0 × A_1|];π_i
    $
    */
]

#slide[
  = Call-by-value: Expressions
  #align(center + horizon, stack(spacing: 3em,
        only("2-", $
        #dnt(proof-tree(expr-var($Γ$, $p$, $x$, $A$))) = upg(π_x, p)
        $),
        only("3-", $
        ∀f ∈ cal(C)_q (A, B), upg(f, p) = "if" q < p "then" f^↑ "else" f: cal(C)_p (A, B)
        $),
        only("4-", $
        #dnt(proof-tree(expr-app($Γ tst(p) f med a: B$, $f: arr(p, A, B)$, $Γ tst(1) a: A$))) 
          = [|f|];upg([|Γ tst(1) a med A|], p)
        $),
  ))
]

#slide[
  = Call-by-value: Products
  #align(center + horizon, stack(spacing: 3em,
      $[|Γ tst(p) a: A|]: cal(C)_p ([|Γ|], [|A|])$,
      only("2-", $
      #dnt(proof-tree(expr-pair($Γ tst(1) (a, b): A × B$, $Γ tst(1) a: A$, $Γ tst(1) b: B$)))
        = ⟨[|Γ tst(1) a: A|], [|Γ tst(1) b: B|]⟩ 
      $),
      only("3-", $
      #dnt(proof-tree(expr-pi($Γ tst(1) π_i e: A_i$, $Γ tst(1) e: A_0 × A_1$)))
        = [|Γ tst(1) e: A_0 × A_1|];π_i
      $)
  ))
]

#slide[
  = Call-by-value: Upgrade
  #align(center + horizon, stack(spacing: 3em,
    $
    Γ tst(1) a: A ==> Γ tst(0) a: A
    $,
    only("2-",
    $
    [|Γ tst(1) a: A|]^↑ = [|Γ tst(0) a: A|]
    $)
  ))
]

#let gto = $triangle.stroked.small$

#let bb-nil(ctxin, ctxout) = rule(name: "bb-nil", $ctxin ⊢ dot gto ctxout$, $ctxin ↦ ctxout$)
#let bb-cons(c, a, b) = rule(name: "bb-cons", c, a, b)

#slide[
  = Call-by-value: Basic blocks
  #align(center + horizon, stack(spacing: 3em,
  $
  [|Γ ⊢ b gto Δ|]: cal(C)_0 ([|Γ|], [|Δ|])
  $,
  $
  #dnt(proof-tree(bb-nil($Γ$, $Δ$))) = upg([|Γ ↦ Δ|], p)
  "where"
  [|Γ ↦ Δ|]: cal(C)_1 ([|Γ|], [|Δ|])
  $,
  $
  #dnt(proof-tree(bb-cons($Γ ⊢ "let" x = a; b gto Δ$, $Γ tst(0) a: A$, $Γ, x: A ⊢ b gto Δ$))) = #block($⟨sans("id"), [|Γ ⊢ a: A|]⟩ 
    \ #h(2em) ;[|Γ, x: A ⊢ b gto Δ|]$)
  $))
]

#slide[
  = Control-flow

  #align(center + horizon, 
      image("ssa-cfg-2.svg", height: 80%),
  )
]

#slide[
  = Coproducts

  #align(center + horizon, 
    stack(dir: ltr, spacing: 1em,
      image("ssa-cfg-2.svg", height: 80%),
      $==>$,
      $[|#[`'entry`]|];([|#[`'left`]|] + [|#[`'right`]|]);[|#[`'exit`]|]$
    )
  )
]

#let lbl(label) = $quote.single label$

#slide[
  = Block Judgement

    #align(center + horizon, 
    stack(dir: ltr, spacing: 2em,
      $Γ ⊢ #[`'entry`] gto #[`'left`], #[`'right`]$,
      $==>$,
      image("ssa-cfg-2-tree.svg", height: 60%),
    )
  )
]

#slide[
  = Label-contexts
  
  #align(center + horizon, stack(spacing: 1em,
    stack(dir: ltr, spacing: 3em, 
      $L ::= dot | L, lbl(ℓ)[Γ](A)$,
      uncover("2-", $[|L|] &: |cal(C)_0| \ [|dot|] &= bold(0) \ [|L, lbl(ℓ)[Γ](A)|] &= [|L|] + [|Γ|] × [|A|] $)
    ),
    uncover("3-", stack(dir: ltr, spacing: 3em,
      $[|Γ ⊢ t gto L|]: cal(C)_0 ([|Γ|], [|L|])$,
      $==>$,
      image("ssa-cfg-diagram.svg", height: 55%),
    ))
  ))
]

#let bl-let(c, a, t) = rule(name: "bl-let", c, a, t)
#let bl-ite(c, e, s, t) = rule(name: "ite", c, e, s, t)
#let bl-br(c, a, l) = rule(name: "br", c, a, l)
#let ite(e, s, t) = $"if" e med { s } "else" { t }$

#slide[
  = Branching

  #align(center + horizon, stack(spacing: 3em,
    $
    dnt(#proof-tree(bl-br($Γ ⊢ "br" lbl(ℓ) med a gto L$, $Γ tst(1) a: A$, $lbl(ℓ)[Γ](A) ↦ L$)))
    $,
    only("2-", $
    lbl(ℓ)[Γ](A) ↦ L <==> ∃Δ, Γ ↦ Δ ∧ lbl(ℓ)[Δ](A) ∈ L
    $),
    only("3-", $
    dnt(#proof-tree(bl-ite($Γ ⊢ ite(e, s, t) gto L$, $Γ tst(1) e: bold(2)$, $Γ ⊢ s gto L$, $Γ ⊢ t gto L$)))
    $)
  ))
]

#slide[
  = Merging control flow
  
  #align(center + horizon, {
    only("1", image("ssa-cfg-2-tree.svg", height: 60%))
    only("2", image("ssa-cfg-2-gamma.svg", height: 80%))
  })
]

#slide[
  = Looping control flow
  
  #align(center + horizon, image("ssa-cfg-1.svg", height: 60%))
]

#slide[
  = Elgot structure

  $
  (-)^†: cal(C)_0(A, B + A) -> cal(C)_0(A, B)
  $
  #line-by-line(start: 2)[
    - *Fixpoint:* $f;[sans("id");f^†] = f^†$
    - *Naturality:* $(f;g + sans("id"))^† = f^†;g$
    - *Codiagonal:* $(f^†)^† = (f;[sans("id"), ι_1])^†$
    - *Uniformity:* $h;f = g;id + h ==> h;f^† = g^†$
    - *Lemma:* if there is a _unique_ fixpoint operator, it is an Elgot operator
  ]
]

//TODO: Elgot diagrams

#slide[
  = Terminators vs. Generalized SSA
  #align(center + horizon, stack(dir: ltr, spacing: 1em,
    $
    B &::= b;t \
    P &::= dot | P, lbl(ℓ)(x: A) => B
    $,
    {
      only("2", "vs.")
      only("3", $≤$)
    },
    only("2-", $
    #proof-tree(bl-let($Γ ⊢ "let" x = a; t gto L$, $Γ tst(p) a: A$, $Γ, x: A ⊢ t gto L$))
    $)
  ))
]

#let bl-where(c, t, w) = rule(name: "bl-where", c, t, w)
#let cfg-nil(L) = rule(name: "cfg-nil", $#L ⊢ dot gto #L$)
#let cfg-cons(c, w, t) = rule(name: "cfg-cons", c, w, t)

#slide[
  = Where-blocks

  #align(center + horizon, stack(spacing: 3em,
    stack(dir: ltr, spacing: 3em,
      $W &::= dot | W, lbl(ℓ)(x: A) => t$,
      $[|L ⊢ W gto K|]: cal(C)_0([|L|], [|K|] + [|L|])$
    ),
    $dnt(#proof-tree(bl-where($Γ ⊢ t "where" W gto K$, $Γ ⊢ t gto L$, $L ⊢ W gto K$)))
    = [|Γ ⊢ t gto L|];[|L ⊢ W gto K|]^†
    $,
    $dnt(#proof-tree(cfg-nil($L$))) = sans("id")$,
  ))
]

#slide[
  #align(center + horizon, stack(spacing: 3em,
    $[|L ⊢ W gto K|]: cal(C)_0([|L|], [|K|] + [|L|])$,
    $dnt(#proof-tree(cfg-cons($L ⊢ W, lbl(ℓ)(x: A) => t gto K$, $L ⊢ W gto K, lbl(ℓ)[Γ](A)$, $Γ, x: A ⊢ t gto L$)))
    \ #h(4em) =
    [|L ⊢ W gto K, lbl(ℓ)[Γ](A)|];[[ι_0, [|Γ, x: A ⊢ t gto L|];ι_1], ι_1]
    $,
    [TODO: where-gadget diagram]
  ))
]

#slide[
  = Where-gadget, continued
  TODO: more where-gadget diagrams, to get the point across
]

#slide[
  = Concrete models
  #line-by-line[
  - A monad is *Elgot* if its Kliesli category has an Elgot operator
  - $A ↦ A + E$
  - $A ↦ cal(P)(A)$
  - The state transformer of an Elgot monad
  - The reader transformer of an Elgot monad
  - The writer transformer of an Elgot monad
  - In our paper: give an Elgot monad for nondeterministic, potentially infinite monoidal traces; show this can be used to reason about printing, heap access, and TSO-style weak memory!
  ]
]

#slide[
  = Substitution and Rewriting
  #only("2-", [- Substitution of pure terms])
  #only("4-", [- In-place rewriting of impure terms])
  #align(center + horizon, {
  only("2", stack(dir: ltr, spacing: 3em,
    ```isotope
    '0:
      x = add y z
      ...
    ...
    'n:
      t = add x y
      ...
    ...
    ```,
    $==>$,
    ```isotope
    '0:
      x = add y z
      ...
    ...
    'n:
      t = add (add y z) y
      ...
    ...
    ```
  ))
  only("3", stack(dir: ltr, spacing: 3em,
    ```isotope
    x = add y z
    t = x
    ```,
    $==>$,
    ```isotope
    t = add y z
    ```
  ))
  only("4", stack(dir: ltr, spacing: 3em,
    ```isotope
    ...
    x = call print_double 5
    ...
    ```,
    $==>$,
    ```isotope
    ...
    x = call print 10
    ...
    ```
  ))
  })
]

#slide[
  = Future Work
  #line-by-line[
    - Names are not (nicely) compositional
    - `where` construction is too complex
    - Want to support _regions_ to be able to reason about MLIR
    - Want to formalize `isotope` in Lean
  ]
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]