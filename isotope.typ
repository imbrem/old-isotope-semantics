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
        #show regex("(//.*)"): comment => text(comment, olive)
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
#let idm = $sans("id")$
#let iobj = $bold(0)$
#let tobj = $bold(1)$
#let munit = $sans(I)$
#let bools = $bold(2)$

// Denotational semantics macros
#let dnt(inner) = $[|inner|]$

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
    $kbr med loc med #args.join($med$)$
};
// #let ljmp(loc, ..args) = {
//     let args = args.pos();
//     $kjmp med loc med #args.join($med$)$
// };
#let lite(b, t, f) = $kif #b med { #t } kelse { #f }$
#let lop(..args) = {
    $args.pos().join(med)$
}

// `isotope` judgement syntax
#let cen = $sans("cen")$
#let rel = $sans("rel")$
#let aff = $sans("aff")$
#let pure = $sans("pure")$
#let cnil = $dot.op$
#let bcnil = $⋄$
#let thyp(var, ty, ..args) = $#var: ty^(#args.pos().at(0, default: none))$
#let tctx(..args) = {
    let targs = ()
    for arg in args.pos() {
        if type(arg) == "array" {
            arg = thyp(arg.at(0), arg.at(1), arg.at(2, default: none))
        }
        targs.push(arg)
    }
    if targs.len() > 0 {
        $#targs.join($,$)$
    } else {
        $cnil$
    }
}
#let lhyp(label, purity, ctx, arg) = $label^purity [ctx](arg)$
#let lctx(..args) = {
    let targs = ()
    for arg in args.pos() {
        if type(arg) == "array" {
            arg = lhyp(arg.at(0), arg.at(1), arg.at(2), arg.at(3))
        }
        targs.push(arg)
    }
    if targs.len() > 0 {
        $#targs.join($,$)$
    } else {
        $bcnil$
    }
}
#let istm(ctx, purity, tm, ty) = $ctx ⊢_purity tm: ty$
#let isblk(ctx, purity, blk, bctx) = $ctx ⊢_purity blk triangle.stroked.small bctx$
#let splitctx(src, ..subctx) = {
    let subctx = subctx.pos().join(";");
    $src arrow.r.bar subctx$
}
#let dropctx(src, subctx) = {
    $src arrow.r.bar subctx$
}
#let joinctx(..args) = {
    let subctx = args.pos();
    let dest = subctx.pop()
    let subctx = subctx.join($;$)
    $subctx ⇝ dest$
}
#let islin(purity, ty) = $sans("lin")_(#purity)(#ty)$
