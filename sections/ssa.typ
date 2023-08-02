#import "../isotope.typ": *

= SSA Form

We say a term is _branch free_ if it does not contain any nested blocks. We say a block is in _SSA form_ if all its nested terms are branch free. We say a term is in _SSA form_ if it consists of a single block in SSA form.

We say a term is _trivial_ if it is either a variable, a constant, or a pair of trivial terms. We say a term is _simple_ if it is trivial or if it is a function applied to a trivial term. We say a block is in _A-normal form_ if all its nested terms are simple; note that this implies the block is in SSA form. 

== Transformation

We define the SSA transform as follows:

$
#rect($sans("Value"): sans("Var") -> sans("Term") -> sans("Block") -> sans("Block")$)
$
$
sans("Value")(x, e, t) &= (klet x = e; t) & "if" x "is simple" \
sans("Value")(x, f med e, t) &= sans("Value")(y, e, (klet x = f med y; t))  \
sans("Value")(x, (a, b), t) &= sans("Value")(y, a, sans("Value")(z, b, (klet x = (y, z); t))) \
sans("Value")(x, (klet y = a; e), t) &= sans("Value")(y, a, sans("Value")(x, e, t)) \
sans("Value")(x, (klet (y, z) = a; e), t) &= sans("Value")(b, a, (klet (x, y) = b; sans("Value")(x, e, t))) \
sans("Value")(x, lbl(ℓ)(A){s}, t) &= [lbl(ℓ)(x) ↦ t]sans("SSA")(s)
$
$
#rect($sans("SSA"): sans("Block") -> sans("Block")$)
$
$
sans("SSA")(lbr(lbl(ℓ), a)) = sans("Value")(x, a, lbr(lbl(ℓ), x)) \
sans("SSA")(lite(e, s, t)) = sans("Value")(x, e, lite(x, sans("SSA")(s), sans("SSA")(t))) \
sans("SSA")(klet x = a; t) = sans("Value")(x, a, sans("SSA")(t)) \
sans("SSA")(klet (x, y) = a; t) = sans("Value")(b, a, (klet (x, y) = b; sans("SSA")(t))) \
sans("SSA")(s kwhere [lbl(ℓ)_i(x_i: A_i) => {t_i}]_i) = (sans("SSA")(s) kwhere [lbl(ℓ)_i(x_i: A_i) => {sans("SSA")(t_i)}]_i) 
$
We have that
$
isblk(Γ, p, (klet x = a; t), sans(L)) ==> isblk(Γ, p, sans("Value")(x, a, t), sans(L)) \
isblk(Γ, p, t, sans(L)) ==> isblk(Γ, p, sans("SSA")(t), sans(L))
$
$sans("SSA")(t)$, $sans("Value")(x, a, t)$ are in A-normal form.

== Semantics

We have that
$
dnt(isblk(Γ, p, sans("Value")(x, a, t), sans(L))) refines dnt(isblk(Γ, p, (klet x = a; t), sans(L))) \
dnt(isblk(Γ, p, sans("SSA")(t), sans(L))) refines dnt(isblk(Γ, p, t, sans(L)))
$