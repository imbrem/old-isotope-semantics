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
  = Wide Usage of SSA
  #line-by-line[
    - Classical compilers
    - MLIR observations:
      #line-by-line(start: 3)[
      - GPU (SPIR-V)
      - CPU
      - FPGA -- CIRCT
      - Even Quantum
      ]
  ]
  #only("7-")[
    - Wide usage $==>$ Underlying Categorical Structure?
      #line-by-line(start: 8)[
        - STLC $==>$ Cartesian closed categories
        - Effects $==>$ Monads
        - *Call-by-value $==>$ Freyd categories*
      ]
  ]
]

#slide[
  = Call-by-value and Freyd categories
  ...
  - What is a Freyd category
  - What is call-by-value
  - "Monads without slightly higher-order types": see nLab
    - Make sense for purely first-order languages
    - If $T X$ exists, has a universal property, decoupling relationship
]

#slide[
  = SSA and call-by-value
  ...
  - The difference is control flow!
    - Coproducts to the rescue!
  - General control flow specifically!
    - Elgot structure to the rescue!
  - $==>$ Freyd categories are for _straight-line_ code
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
    - Freyd!
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

#slide[
  = Linearity
  ...
]

#slide[
  = Future work: Regions
  ...
  - MLIR
  - Citations for this?
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]