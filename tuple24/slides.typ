#import "@preview/polylux:0.3.1": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

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
    ```
    # Compute fibonacci(i)
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
  ... SSAify previous
]

#slide[
  Why?
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