#import "typst-cd.typ": node, arr, commutative_diagram

#lorem(40)

#align(center)[#commutative_diagram(
  node((0, 0), [$X$]),
  node((0, 1), [$Y$]),
  node((1, 0), [$X \/ "ker"(f)$]),
  arr((0, 0), (0, 1), [$f$], label_pos: -1em),
  arr((1, 0), (0, 1), [$tilde(f)$]),
  arr((0, 0), (1, 0), [$pi$]),
)]

#lorem(40)

#align(center)[#commutative_diagram(width: 300pt, height: 200pt,
  node((0, 0), [$pi_1(X sect Y)$]),
  node((0, 1), [$pi_1(Y)$]),
  node((1, 0), [$pi_1(X)$]),
  node((1, 1), [$pi_1(Y) ast.op_(pi_1(X sect Y)) pi_1(X)$]),
  arr((0, 0), (0, 1), [$i_1$], label_pos: -1em, "inj"),
  arr((0, 0), (1, 0), [$i_2$], "inj"),
  arr((1, 0), (2, 2), [$j_1$], curve: -15deg, "surj"),
  arr((0, 1), (2, 2), [$j_2$], label_pos: -1em, curve: 20deg, "def"),
  arr((1, 1), (2, 2), [$k$], label_pos: 0, "dashed", "bij"),
  arr((1, 0), (1, 1), [], "dashed", "inj", "surj"),
  arr((0, 1), (1, 1), [], "dashed", "inj"),
  node((2, 2), [$pi_1(X union Y)$])
)]

#lorem(40)

#align(center)[#commutative_diagram(width: 400pt, height: 120pt,
  node((0, 0), [$A$]),
  node((0, 1), [$B$]),
  node((0, 2), [$C$]),
  node((0, 3), [$D$]),
  node((0, 4), [$E$]),
  node((1, 0), [$A'$]),
  node((1, 1), [$B'$]),
  node((1, 2), [$C'$]),
  node((1, 3), [$D'$]),
  node((1, 4), [$E'$]),
  arr((0, 0), (0, 1), [$a$]),
  arr((0, 1), (0, 2), [$b$]),
  arr((0, 2), (0, 3), [$c$]),
  arr((0, 3), (0, 4), [$d$]),
  arr((1, 0), (1, 1), [$a'$]),
  arr((1, 1), (1, 2), [$b'$]),
  arr((1, 2), (1, 3), [$c'$]),
  arr((1, 3), (1, 4), [$d'$]),
  arr((0, 0), (1, 0), [$alpha$]),
  arr((0, 1), (1, 1), [$beta$]),
  arr((0, 2), (1, 2), [$gamma$]),
  arr((0, 3), (1, 3), [$delta$]),
  arr((0, 4), (1, 4), [$epsilon$]),
)]

#lorem(40)

