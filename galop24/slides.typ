#import "@preview/polylux:0.3.1": *

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
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m0 = 0
      n0 = 1
      brz i 'exit(m0) 'loop(i, m0, n0)
    'loop(i0, m1, n1):
      m2 = n1
      n2 = add m1 n1
      i1 = sub i0 1
      brz i1 'exit(m2) 'loop(i1, m2, n2)
    'exit(m3):
      ret m3
    ```
  ]
]

#slide[
  #show raw: r => text(size: 17pt, r)
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m0 = 0
      n0 = 1
      brz i 'exit(m0) 'loop(i, m0, n0)       // ‖
    'loop(i0, m1, n1):                       // ‖
      m2 = n1
      n2 = add m1 n1
      i1 = sub i0 1
      brz i1 'exit(m2) 'loop(i1, m2, n2)     // ‖
    'exit(m3):                               // ‖
      ret m3
    ```
  ]
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
      i0 = phi ('entry => i) ('loop => i1) // ‖
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

#slide[
  = Theory

  #v(2em)

  #align(center)[*Wide usage* $==>$ *Underlying Categorical Structure*]

  #v(2em)
  
  #line-by-line(start: 2)[
    Examples:
    - String diagrams $==>$ Monoidal categories
    - STLC $==>$ Cartesian closed categories
    // - Effects $==>$ Monads
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
      uncover("1-", $cal(V)$),
      uncover("3-", $-->_#[i.o.o]$),
      uncover("3-", $Z(cal(C))$),
      uncover("3-", $↪$),
      uncover("2-", $cal(C)$),
      uncover("1-")[
        (Cartesian)
      ],
      [], [], [],
      uncover("2-")[
        (Premonoidal)
      ],
    ),
    {
      only("4", $⊗: cal(C) × cal(C) -> cal(C)$)
      only("5", $A ⊗ -, - ⊗ A: cal(C) -> cal(C)$)
      let forall_stmt = $∀f,$;
      stack(
        dir: ltr,
        spacing: 2em,
        uncover("8-", forall_stmt),
        {
          only("6", "MON. DIAGRAM")
          only("7-", "PM. DIAGRAM")
        },
        {
          only("6-7", $≠$)
          only("8-", $=$)
        },
        {
          only("6", "MON. DIAGRAM")
          only("7-", "PM. DIAGRAM")
        },
        hide(forall_stmt)
      )
    },
    uncover("8-", $==> g ∈ Z(C)(A, B)$)
  ))
]

#slide[
  = Call-by-value is Freyd categories
  #align(center + horizon, image("ssa-dfg-1.svg", width: 45%))
]

#slide[
  = Basic blocks are call-by-value
  ...
]

#slide[
  = Branching control-flow
  ...
]

#slide[
  = General control-flow
  ...
]

#slide[
  = Substitution
  ...
]

#slide[
  = Rewriting
  ...
]

#slide[
  = Impure substitutions
  ...
]

#slide[
  = Concrete models
  ...
]

#slide[
  = Names and Compositionality
  ...
]

#slide[
  = Future Work: Regions
  ...
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]