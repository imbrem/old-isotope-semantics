// Template
#let isotope-report(
  title: none,
  authors: (),
  doc,
) = {
    if type(authors) == "dictionary" {
        authors = (authors,)
    }
    let title-page = page([
        #set align(bottom)
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
        #v(2.5cm)
    ])
    [
    #title-page
    #outline(title: auto, depth: 2)
    #pagebreak()
    #doc
    ]
}

// Syntax
#let grammar(g, debug_stroke: none) = {
    let cells = ()
    for rule in g {
        let name = if "name" in rule { 
            if rule.name != none { 
                rect(stroke: debug_stroke, strong(rule.name + ":"))
            } 
        };
        let symbols = if type(rule.symbol) == "array" {
            rule.symbol.join($,$)
        } else {
            rule.symbol
        };
        let lhs = $#symbols ::= $;
        let productions = if type(rule.productions) == "array" {
            rule.productions
        } else {
            (rule.productions,)
        };
        for row in productions {
            cells.push(align(horizon, name))
            cells.push(align(right + horizon, rect(stroke: debug_stroke, lhs)));
            let row = if type(row) == "array" {
                row.join(rect(stroke: debug_stroke, $ | $))
            } else {
                row
            }
            cells.push(align(horizon, rect(stroke: debug_stroke, $#row$)));
            lhs = $|$;
            name = none;
        }
    }
    grid(columns: 3, ..cells)
}

// Proof trees
// Note: nested trees are not particularly pretty right now as the line length is long
// This should be fixed eventually
#let dprfm(
    p, 
    spacing: 0.2cm,
    debug_stroke: none) = {
    let premises = stack(dir: ltr, ..p.premises);
    block(
        [$
            #text(maroon)[#p.name] premises / 
            #rect(stroke: debug_stroke, $#p.conclusion$)
        $]
    )
}
#let dprf(
    p, 
    spacing: 0.2cm,
    debug_stroke: none,
    ..args) = {
    let premises = ()
    let first = true;
    for premise in p.premises {
        let premise = if type(premise) == "dictionary" {
            dprf(
                premise, 
                spacing: spacing, 
                debug_stroke: debug_stroke, 
                ..args)
        } else {
            premise
        };
        let inset = if first { (:) } else { (left: spacing) } 
        first = false;
        premises.push(
            align(bottom, box(inset: inset, 
                rect(stroke: debug_stroke, $premise$)
            ))
        )
    }
    p.premises = premises
    dprfm(p, spacing: spacing, debug_stroke: debug_stroke, ..args)
}
#let prft(name: none, ..args) = {
    let premises = args.pos();
    let conclusion = premises.pop();
    (
        premises: premises,
        conclusion: conclusion,
        name: name,
    )
}
#let prf(name: none, ..args) = {
    let premises = args.pos();
    dprf(prft(name: name, ..premises), ..args.named())
}

// Denotational semantics
#let dnt(term) = $ [| term |] $

// Math space
#let aq = h(0.2778em); // 5mu from LaTeX

// Symbols
#let abort = $sans("abort")$
#let llet = $sans("let")$
#let lin = $sans("in")$
#let iobj = $bold(0)$
#let tobj = $bold(1)$
#let bools = $bold(2)$
#let ltt = $sans("true")$
#let lff = $sans("false")$
#let munit = $I$
#let cnil = $dot.op$
#let bcnil = $diamond.stroked.small$
#let lbr = $sans("br")$
#let br(..args) = {
    let args = args.pos();
    let result = $lbr #args.join(aq)$;
    result
};
#let lbl(x) = $mono("'")#x$
#let lif = $sans("if")$
#let lelse = $sans("else")$
#let lite(b, t, f) = $lif #b aq { #t } lelse { #f }$

// Syntax macros
#let splits(src, ..subctx) = {
    let subctx = subctx.pos().join($;$);
    $src arrow.r.bar subctx$
}
#let istm(ctx, tm, ty) = $ctx models tm: ty$
#let isblk(bctx, ctx, blk, ty) = $
    bctx;ctx models blk triangle.stroked.small ty$