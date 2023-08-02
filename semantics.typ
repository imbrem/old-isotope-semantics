#import "isotope.typ": *
#show: doc => isotope-report(
    title: "Isotope IR Semantics",
    authors: (
        (
            name: "Jad Elkhaleq Ghalayini",
            affiliation: "University of Cambridge",
            email: "jeg74@cl.cam.ac.uk"
        ),
    ),
    doc
)

#let table-dbg = none;

#include "sections/syntax.typ"
#include "sections/semantics.typ"
#include "sections/ssa.typ"

#pagebreak()
#bibliography("references.bib")
#pagebreak()

// #show: isotope-appendix