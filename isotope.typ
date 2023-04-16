// Commutative diagrams
#import "typst-cd/typst-cd.typ": node, arr, commutative_diagram

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
    #set heading(numbering: "1.")
    //#set math.text(font: "Inria Serif")
    #outline(title: auto, depth: 2)
    #pagebreak()

    #set page(
        numbering: "1"
    )

    #show raw.where(lang: "isotope"): it => [
        #show regex("\b(let|br|if|else|for|in|match|while|loop|ret|where)\b") : keyword => text(weight:"bold", keyword, maroon)
        #show regex("\b[0-9][a-zA-Z0-9_]*\b") : cnst => text(cnst, olive)
        #it
    ]

    #doc
    ]
}

#let isotope-appendix(doc) = {
    set heading(numbering: "A.1.")
    counter(heading).update(())
    text(2em)[*Appendix*]
    doc
}

//TODO: fix counter for duplicate theorems...
#let theorem-counter = counter("theorem")
#let theorem(body, name: none, numbered: true) = locate(location => {
  let lvl = counter(heading).at(location)
  let i = theorem-counter.at(location).first()
  if numbered { theorem-counter.step() }
  let top = if lvl.len() > 0 { lvl.first() } else { 0 }
  show: block.with(spacing: 11.5pt)
  {
    strong([Theorem])
    if numbered [ *#top.#i*]
    if name != none [ (#emph(name))]
    if numbered or name != none [*.*]
  }
  [ ]
  emph(body)
})
//Note: lemmas use the theorem counter for now
#let lemma(body, name: none, numbered: true) = locate(location => {
  let lvl = counter(heading).at(location)
  let i = theorem-counter.at(location).first()
  if numbered { theorem-counter.step() }
  let top = if lvl.len() > 0 { lvl.first() } else { 0 }
  show: block.with(spacing: 11.5pt)
  {
    strong([Lemma])
    if numbered [ *#top.#i*]
    if name != none [ (#emph(name))]
    if numbered or name != none [*.*]
  }
  [ ]
  emph(body)
})

#let definition-counter = counter("definition")
#let definition(body, name: none, numbered: true) = locate(location => {
  let lvl = counter(heading).at(location)
  let i = definition-counter.at(location).first()
  if numbered { definition-counter.step() }
  let top = if lvl.len() > 0 { lvl.first() } else { 0 }
  show: block.with(spacing: 11.5pt)
  {
    strong([Definition])
    if numbered [ *#top.#i*]
    if name != none [ (#emph(name))]
    if numbered or name != none [*.*]
  }
  [ ]
  emph(body)
})

#let proof(body) = block(spacing: 11.5pt, {
  emph[Proof.]
  [ ] + body
  h(1fr)
  box(scale(160%, origin: bottom + right, sym.square.stroked))
})

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
    let premises = stack(dir: ltr, ..p.premises)
    block(
        [$
            #text(size: 0.7em, maroon)[#p.name] premises / 
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
    if p.premises.len() == 0 {
        p.premises.push($$)
    }
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
#let idm = $sans("id")$
#let Set = $sans("Set")$
#let Pfn = $sans("Pfn")$
#let Rel = $sans("Rel")$
#let SetP = $Set_•$
#let Pos = $sans("Pos")$
#let Mon = $sans("Mon")$
#let fcomp(functor, left, right) = $functor_(left, right)$
#let qq = h(2em)
#let opp(cat) = $cat^(sans("op"))$
#let Cat = $sans("Cat")$
#let niso = $≃$
#let pset = $cal(P)$
#let ltimes = $⋉$
#let rtimes = $⋊$
#let cen(cat) = $Z(#cat)$
#let adj(left, right, unit: none, counit: none) = $#left ⊣ #right$
#let lhyp(ctx, purity, label, arg) = $ctx triangle_purity label(arg)$
#let thyp(var, ty, ..args) = $#var: ty^(#{
    if args.pos().len() > 0 {
        args.pos().at(0)
    } else {
        none
    }
})$
#let issub(name, defctx, varctx, ..args) = {
    let purity = if args.pos().len() >= 1 {
        args.pos().at(0)
    }
    $name: defctx ->_purity varctx$
}
#let ssub(tm, var) = $tm slash var$
#let slft(subst) = $subst^↑$
#let submap(lsub, rsub) = $lsub ≤ rsub$
#let labmap(label, subst) = $sans("labmap")(label, subst)$
#let smite(base) = $sans("ite")_base$
#let lcen = $sans("cen")$
#let lrel = $sans("rel")$
#let laff = $sans("aff")$

// Syntax macros
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
    $subctx arrow.r.squiggly dest$
}
#let subctx(small, big) = $small ≤ big$
#let types(base) = $sans("Type")(#base)$
#let rel(ty, ..args) = $#ty^(#{
    if args.pos().len() > 0 {
        args.pos().at(0)
    } else {
        none
    }
}) sans("rel")$
#let aff(ty, ..args) = $#ty^(#{
    if args.pos().len() > 0 {
        args.pos().at(0)
    } else {
        none
    }
}) sans("aff")$
#let islin(purity, ty) = $#ty aq sans("lin")_(#purity)$
#let istm(ctx, purity, tm, ty) = $ctx ⊢_purity tm: ty$
#let isblk(ctx, bctx, purity, blk, ty) = $
    ctx;bctx ⊢_purity blk triangle.stroked.small ty$
#let dwng(body, purity: none) = $body^(↓_purity)$
#let instof(purity, func) = $sans("inst")_purity(func)$

#let row-den(..args) = {
    align(center)[#table(
        columns: args.pos().len(),
        column-gutter: 2em,
        align: horizon,
        stroke: none,
        ..args
    )]
};