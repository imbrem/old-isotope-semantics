#import "utils/grammar.typ": *
#import "utils/proof.typ": *

// Report template
#let isotope-report(
  title: none,
  authors: (),
  doc,
) = {
    // `isotope` syntax highlighting
    show raw.where(lang: "isotope"): it => [
        #show regex("\b(let|br|jmp|if|else|for|in|match|while|loop|ret|where)\b") : keyword => text(weight:"bold", keyword, maroon)
        #show regex("\b[0-9][a-zA-Z0-9_]*\b") : cnst => text(cnst, olive)
        #show regex("\"([^\"]|(\\\\[\s\S]))*\"") : strlit => text(strlit, olive)
        #show regex("\'\pL*"): lbl => text(lbl, navy)
        #it
    ]

    if type(authors) == "dictionary" {
        authors = (authors,)
    }
    [
        #set align(top)
        #text(2em)[*#title*]
        #{
            for author in authors {
                grid(
                    gutter: 10pt,
                    author.name,
                    if "affiliation" in author [
                        #emph(author.affiliation)
                    ],
                    if "email" in author [
                        #link("mailto:" + author.email)
                    ]
                )
            }
        }
        #set heading(numbering: "1.")
        //#set math.text(font: "Inria Serif")
        #outline(title: auto, depth: 2)
        #pagebreak()

        #set page(
            numbering: "1"
        )

        #doc
    ]
}

// Category theory macros:
#let iobj = $bold(0)$
#let tobj = $bold(1)$
#let bools = $bold(2)$

// `isotope` macros:

// `isotope` objects:
#let types = $sans("Types")$

// `isotope` keywords
#let klet = $sans("let")$
#let kin = $sans("in")$
#let tt = $sans("true")$
#let ff = $sans("false")$
#let kif = $sans("if")$
#let kelse = $sans("else")$
#let kbr = $sans("br")$
#let kjmp = $sans("jmp")$
#let kwhere = $sans("where")$

// `isotope` syntax
#let lbl(x) = $mono("'")#x$
#let lbr(loc, ..args) = {
    let args = args.pos();
    $kbr loc #args.join($med$)$
};
#let ljmp(loc, ..args) = {
    let args = args.pos();
    $kjmp loc #args.join($med$)$
};
#let lite(b, t, f) = $kif #b med { #t } kelse { #f }$
#let lop(..args) = {
    $args.pos().join(med)$
}