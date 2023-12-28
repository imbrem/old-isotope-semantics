#import "@preview/polylux:0.3.1": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

#let highline(it) = [
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
  
  February 21

  TUPLE'24 -- Edinburgh
]

#focus-slide[
  = What is SSA?
]

#focus-slide[
  = Static Single Assignment
]

#slide[
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
  #align(center + horizon)[
    ```isotope
    // Compute fibonacci(i)
    'entry:
      m0 = 0
      n0 = 1
      brz i 'exit(m0) 'loop(i, m0, n0)   // ‖
    'loop(i0, m1, n1):                   // ‖
      m2 = n1
      n2 = add m1 n1
      i1 = sub i0 1
      brz i1 'exit(m2) 'loop(i1, m2, n2) // ‖
    'exit(m3):                           // ‖
      ret m3
    ```
  ]
]

#slide[
  = Why?
  ...
]

#slide[
  = Wide Usage of SSA
  ...
  - Classical compilers
  - MLIR observations:
    - GPU (SPIR-V)
    - CPU
    - FPGA -- CIRCT
    - Even Quantum
  - Wide usage $==>$ Universal Property
]

#slide[
  = Type-theoretic Presentation of SSA
  ...
  - Basic-block terminator collection view
  - Generalizing very slightly?
]

#slide[
  = Categorical Semantics
  ...
  - Of pure expressions
    - Cartesian!
    - Begin drawing dataflow!
  - Of straight-line code
    - Premonoidal $==>$ Freyd!
  - Of branching control-flow
    - Coproducts
  - Of general control-flow
    - Elgot structure
]

#slide[
  = Drawing Control-flow
  ...
]


#slide[
  = Concrete Models: Monads
  ...
]

#slide[
  = Cool Models: Weak Memory
  ...
]

// #slide[
//   = Linearity
//   ...
//   - Mainstream:
//     - Memory allocation
//     - Separation logic
//     - Functional optimization/escape analysis
//   - Speculative:
//     - Quantum
//   - It's called an _Effectful Category_


//   Probably no time for more than this...
// ]