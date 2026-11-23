#let ink = rgb("#242322")
#let muted = rgb("#595650")
#let rule-color = rgb("#c0bab0")
#let serif = "New Computer Modern"
#let sans = "Arial"
#let short-title = "Alpöge-Claude-Riemann Theorem"
#let author-name = "GPT-6.2 Astra"
#let chapter(title) = { pagebreak(weak: true); heading(level: 1, title) }
#let front(title) = { pagebreak(weak: true); heading(level: 1, numbering: none, title) }
#let part(n,title,blurb,guide) = {
  pagebreak(weak: true)
  v(26mm)
  text(font: sans, size: 10pt, tracking: 0.08em, upper(n))
  v(5mm)
  heading(level: 1, numbering: none, [#title])
  block(width: 92%)[#set par(justify: false, first-line-indent: 0pt)
    #text(size: 13pt, style: "italic", blurb)]
  v(15mm)
  block(width: 96%)[#set par(justify: false, first-line-indent: 0pt)
    #grid(columns: (auto, 1fr), column-gutter: 10pt, row-gutter: 9pt, ..guide)
  ]
}
#let claim(title, body) = block(width: 100%, above: 8pt, below: 6pt, breakable: true)[
  #text(weight: "bold")[#title.] #emph(body)
]
#let proof(body) = block(width: 100%, above: 4pt, below: 6pt, breakable: true)[
  #emph[Proof.] #body #h(1fr)#box(width: 5.1pt, height: 5.1pt, stroke: 0.65pt + ink)
]
#let example(title, body) = block(width: 100%, above: 7pt, below: 6pt, breakable: true)[
  #text(weight: "bold")[#title.] #body
]
#let note(title, body) = block(width: 100%, inset: (left: 8pt, top: 2pt, bottom: 2pt), stroke: (left: 0.7pt + rule-color), above: 8pt, below: 8pt, breakable: true)[
  #text(weight: "bold")[#title.] #body
]
#let src(module, label) = link("https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/" + module.replace(".", "/") + ".lean", label)
#let source-note(body) = block(above: 7pt, below: 2pt)[#text(size: 8.8pt, fill: muted)[#strong[Source notes.] #body]]
#let Re = math.op("Re")
#let Im = math.op("Im")
#let ord = math.op("ord")
#let varphi = sym.phi
#let varpi = sym.pi.alt
#let vartheta = sym.theta.alt
#let Gal = math.op("Gal")
#let len = math.op("length")
#let tr = math.op("tr")
#let vol = math.op("vol")
#let Sha = math.op("Sha")
#let nmid = [∤]
#let header = context {
  let p = counter(page).get().first()
  let heads = query(heading.where(level: 1)).filter(it => it.location().page() <= here().page())
  let title = if heads.len() > 0 { heads.last().body } else { short-title }
  set text(font: serif, size: 8.2pt, fill: muted)
  if calc.even(p) { [#p #h(1fr) #emph(short-title)] } else { [#emph(title) #h(1fr) #p] }
  v(3pt)
  line(length: 100%, stroke: 0.35pt + rule-color)
}
#let layout(body) = {
  set document(title: short-title, author: author-name, keywords: ("Riemann hypothesis", "Dirichlet L-functions", "theta correspondence", "analytic number theory"))
  set text(font: serif, size: 11.3pt, lang: "en", fill: ink)
  set par(justify: true, leading: 0.60em, spacing: 0.68em, first-line-indent: 0.95em)
  set page(width: 161mm, height: 238mm, margin: (inside: 20.5mm, outside: 18mm, top: 22.5mm, bottom: 20mm), binding: left, header: header, header-ascent: 7mm)
  set heading(numbering: "1.1")
  set math.equation(numbering: none)
  set figure.caption(separator: [.#h(0.35em)])
  set outline(indent: 1.05em)
  show heading.where(level: 1): it => block(width: 100%, above: 0pt, below: 16pt, sticky: true)[
    #set par(justify: false, first-line-indent: 0pt)
    #if it.numbering != none { [#text(size: 10.4pt, font: sans, weight: "semibold", tracking: 0.06em)[CHAPTER #context counter(heading).display("1")] #v(5pt)] }
    #text(size: 22pt, weight: "bold", hyphenate: false)[#it.body]
    #v(4pt)
    #line(length: 100%, stroke: 0.65pt + ink)
  ]
  show heading.where(level: 2): it => block(width: 100%, above: 10pt, below: 4pt, sticky: true)[#set par(justify: false, first-line-indent: 0pt)
    #text(size: 13.2pt, weight: "bold")[#if it.numbering != none { [#context counter(heading).display("1.1") #h(0.45em)] }#it.body]]
  show outline.entry: it => {
    if it.element.numbering == none {
      set text(weight: "bold")
      if it.element.body == [Origins and mathematical tools] or it.element.body == [The proof] { v(3pt) }
      it
    } else { it }
  }
  show link: set text(fill: rgb("#18465c"))
  body
}
#let jacket() = {
  page(width: 161mm, height: 238mm, margin: (left: 18mm, right: 16mm, top: 21mm, bottom: 17mm), fill: rgb("#f0ce4e"), header: none, footer: none)[
    #set par(justify: false, first-line-indent: 0pt)
    #set text(fill: rgb("#201e18"))
    #text(font: sans, size: 10.7pt, tracking: 0.08em, weight: "bold")[GRADUATE MATHEMATICS]
    #v(6mm)
    #line(length: 100%, stroke: 1.1pt)
    #v(13mm)
    #text(size: 33pt, weight: "bold", hyphenate: false)[Alpöge-Claude-#linebreak()Riemann Theorem]
    #v(11mm)
    #text(size: 15pt)[GPT-6.2 Astra]
    #v(1fr)
    #line(length: 27mm, stroke: 1.1pt)
    #v(3mm)
    #text(size: 13pt, style: "italic")[Prime sums, theta lifts, and zeros of Dirichlet $L$-functions]
    #v(6mm)
    #text(font: sans, size: 9pt)[Revised expanded edition #h(0.55em) 2026]
  ]
}
