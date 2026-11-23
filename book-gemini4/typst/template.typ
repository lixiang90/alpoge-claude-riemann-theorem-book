// ============================================================================
// Springer GTM-Inspired Typst Book Template
// For: "Alpöge–Claude–Riemann Theorem"
// ============================================================================

#let gtm-yellow = rgb("#F5C71A")
#let gtm-navy = rgb("#17253B")
#let gtm-accent = rgb("#243B5E")
#let gtm-rule = rgb("#8C96A5")
#let gtm-tint = rgb("#F6F7FA")
#let gtm-lean-bg = rgb("#F4F6F8")
#let gtm-lean-border = rgb("#3A5A8C")

// Counters
#let part-counter = counter("gtm-part")
#let chapter-counter = counter("gtm-chapter")
#let thm-counter = counter("gtm-thm")
#let eq-counter = counter(math.equation)
#let ex-counter = counter("gtm-ex")

// State to track current chapter/section titles for running headers
#let current-chapter = state("gtm-current-chapter", "")
#let current-section = state("gtm-current-section", "")
#let is-opener-page = state("gtm-is-opener", false)

// Helper: chapter-prefixed numbering
#let ch-num() = {
  let c = chapter-counter.get().first()
  if c == 0 { "" } else { str(c) + "." }
}

// ============================================================================
// Part Opener
// ============================================================================
#let part-page(number, title, subtitle: none, summary: none) = {
  pagebreak(weak: true)
  part-counter.step()
  current-chapter.update("Part " + number + ": " + title)
  current-section.update("")
  [
    #metadata((kind: "part", number: number, title: title)) <gtm-part-marker>
    #v(3.2cm)
    #align(right)[
      #set text(hyphenate: false)
      #set par(first-line-indent: 0pt, justify: false)
      #text(size: 13pt, weight: "regular", tracking: 0.14em, fill: gtm-accent)[
        #upper[Part #number]
      ]
      #v(0.4cm)
      #line(length: 100%, stroke: 1.2pt + gtm-navy)
      #v(0.5cm)
      #text(size: 22.5pt, weight: "bold", fill: gtm-navy)[#title]
      #if subtitle != none {
        v(0.35cm)
        text(size: 11.5pt, style: "italic", fill: luma(70))[#subtitle]
      }
      #v(0.4cm)
      #line(length: 45%, stroke: 0.5pt + gtm-rule)
    ]
    #if summary != none {
      v(1.6cm)
      pad(left: 1.5cm)[
        #set par(justify: true, leading: 0.65em)
        #text(size: 9.8pt, fill: luma(50))[#summary]
      ]
    }
  ]
  pagebreak(weak: true)
}

// ============================================================================
// Chapter Opener
// ============================================================================
#let chapter(title, short-title: none, epigraph: none, epigraph-source: none, overview: none, label-name: none) = {
  pagebreak(weak: true)
  chapter-counter.step()
  thm-counter.update(0)
  ex-counter.update(0)
  counter(math.equation).update(0)

  let st = if short-title != none { short-title } else { title }
  context {
    let c = chapter-counter.get().first()
    current-chapter.update("Chapter " + str(c) + ". " + st)
  }
  current-section.update("")

  // Level-1 heading for chapter opener and outline/TOC
  context {
    let c = chapter-counter.get().first()
    block(above: 0pt, below: 0pt)[
      #v(1.4cm)
      #text(size: 11.5pt, tracking: 0.08em, fill: gtm-accent, weight: "medium")[
        CHAPTER #c
      ]
      #v(0.25cm)
      #line(length: 100%, stroke: 0.9pt + gtm-navy)
      #v(0.35cm)
      #heading(level: 1, numbering: "1.", outlined: true)[#title]
      #if label-name != none { label(label-name) }
      #v(0.25cm)
      #line(length: 100%, stroke: 0.35pt + gtm-rule)
    ]
  }

  if epigraph != none {
    v(0.55cm)
    align(right)[
      #box(width: 78%)[
        #set par(justify: false, leading: 0.55em)
        #text(size: 8.8pt, style: "italic", fill: luma(65))[#epigraph]
        #if epigraph-source != none {
          linebreak()
          v(0.15cm)
          text(size: 8.3pt, style: "normal", fill: luma(85))[--- #epigraph-source]
        }
      ]
    ]
  }

  if overview != none {
    v(0.55cm)
    block(
      width: 100%,
      fill: gtm-tint,
      stroke: (left: 2pt + gtm-accent),
      inset: (left: 10pt, right: 10pt, top: 8pt, bottom: 8pt),
      radius: (right: 2pt),
    )[
      #set par(justify: true, leading: 0.6em)
      #text(size: 9.2pt)[#overview]
    ]
  }

  v(0.6cm)
}

// ============================================================================
// Appendix Chapter Opener
// ============================================================================
#let appendix-chapter(letter, title, overview: none) = {
  pagebreak(weak: true)
  chapter-counter.update(0)
  thm-counter.update(0)
  ex-counter.update(0)
  counter(math.equation).update(0)
  current-chapter.update("Appendix " + letter + ". " + title)
  current-section.update("")

  block(above: 0pt, below: 0pt)[
    #v(1.4cm)
    #text(size: 11.5pt, tracking: 0.08em, fill: gtm-accent, weight: "medium")[
      APPENDIX #letter
    ]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.35cm)
    #heading(level: 1, numbering: none, outlined: true)[Appendix #letter: #title]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]

  if overview != none {
    v(0.5cm)
    block(
      width: 100%,
      fill: gtm-tint,
      stroke: (left: 2pt + gtm-accent),
      inset: (left: 10pt, right: 10pt, top: 8pt, bottom: 8pt),
    )[
      #set par(justify: true, leading: 0.6em)
      #text(size: 9.2pt)[#overview]
    ]
  }
  v(0.55cm)
}

// ============================================================================
// Mathematical Theorem-like Environments (Springer GTM style)
// ============================================================================
#let math-env(kind, title: none, italic-body: true, body) = {
  thm-counter.step()
  v(0.55em)
  block(breakable: true, width: 100%)[
    #context {
      let num = ch-num() + str(thm-counter.get().first())
      strong[#kind #num]
      if title != none {
        [ ]
        strong[(#title)]
      }
      strong[.]
      [ ]
      if italic-body {
        emph(body)
      } else {
        body
      }
    }
  ]
  v(0.55em)
}

#let theorem(title: none, body) = math-env("Theorem", title: title, italic-body: true, body)
#let proposition(title: none, body) = math-env("Proposition", title: title, italic-body: true, body)
#let lemma(title: none, body) = math-env("Lemma", title: title, italic-body: true, body)
#let corollary(title: none, body) = math-env("Corollary", title: title, italic-body: true, body)
#let conjecture(title: none, body) = math-env("Conjecture", title: title, italic-body: true, body)
#let definition(title: none, body) = math-env("Definition", title: title, italic-body: false, body)
#let remark(title: none, body) = math-env("Remark", title: title, italic-body: false, body)
#let example(title: none, body) = math-env("Example", title: title, italic-body: false, body)

#let proof(title: none, body) = {
  v(0.2em)
  block(breakable: true, width: 100%)[
    #if title != none {
      emph[Proof (#title).]
    } else {
      emph[Proof.]
    }
    [ ]
    #body
    #h(1fr) $square$
  ]
  v(0.45em)
}

// Lean 4 Formalization Box
#let lean-note(title: "Lean 4 Formalization", module: none, body) = {
  v(0.45em)
  block(
    breakable: true,
    width: 100%,
    fill: gtm-lean-bg,
    stroke: (left: 2.2pt + gtm-lean-border, rest: 0.4pt + luma(210)),
    inset: (x: 10pt, y: 8pt),
    radius: 2pt,
  )[
    #block(above: 0pt, below: 0.55em)[
      #set par(justify: false, first-line-indent: 0pt, leading: 0.55em)
      #text(size: 9pt, weight: "bold", fill: gtm-navy)[#title]
      #if module != none {
        let mod-txt = if type(module) == str {
          module.replace(regex("([/._])([^\\s])"), m => m.captures.at(0) + "\u{200B}" + m.captures.at(1))
        } else {
          module
        }
        h(0.45em)
        text(size: 8.0pt, font: "DejaVu Sans Mono", fill: gtm-accent, hyphenate: false)[(#mod-txt)]
      }
    ]
    #set text(size: 9.1pt)
    #body
  ]
  v(0.45em)
}

// Historical / Conceptual Insight Box
#let insight-box(title: "Conceptual Insight", body) = {
  v(0.45em)
  block(
    breakable: true,
    width: 100%,
    fill: rgb("#FFFDF2"),
    stroke: (left: 2.2pt + gtm-yellow, rest: 0.4pt + rgb("#E6D58A")),
    inset: (x: 10pt, y: 8pt),
    radius: 2pt,
  )[
    #block(above: 0pt, below: 0.55em)[
      #set par(justify: false, first-line-indent: 0pt, leading: 0.55em)
      #text(size: 9.2pt, weight: "bold", fill: gtm-navy)[#title]
    ]
    #set text(size: 9.2pt)
    #body
  ]
  v(0.45em)
}

// Exercises section at end of chapter
#let exercises(items) = {
  v(0.8cm)
  heading(level: 2, numbering: none)[Exercises]
  v(0.2cm)
  for item in items {
    ex-counter.step()
    context {
      let num = ch-num() + str(ex-counter.get().first())
      block(breakable: true, above: 0.35em, below: 0.35em)[
        *#num.* #item
      ]
    }
  }
}

// ============================================================================
// Main Book Layout Wrapper
// ============================================================================
#let gtm-book(
  title: "Alpöge–Claude–Riemann Theorem",
  subtitle: "From Riemann's 1859 Memoir to Chained Theta Lifts and Formal Verification",
  author: "Gemini 4 Neon",
  body,
) = {
  set document(title: title, author: author)

  // Royal Octavo trim size: 162mm x 240mm (123mm text column)
  set page(
    width: 162mm,
    height: 240mm,
    margin: (inside: 21mm, outside: 18mm, top: 22mm, bottom: 22mm),
    header-ascent: 7.5mm,
    header: context {
      let pg = counter(page).get().first()
      let loc = here()
      // Suppress header on very early frontmatter or chapter/part openers
      if pg <= 4 { return }
      // Check if a level-1 heading or part marker occurs on this exact page
      let h1s = query(heading.where(level: 1)).filter(h => h.location().page() == loc.page())
      let parts = query(<gtm-part-marker>).filter(p => p.location().page() == loc.page())
      if h1s.len() > 0 or parts.len() > 0 { return }

      let ch = current-chapter.get()
      let sec = current-section.get()
      let display-pg = counter(page).display()

      set text(size: 8.3pt, fill: luma(60))
      if calc.even(pg) {
        grid(
          columns: (auto, 1fr),
          align: (left, right),
          [#display-pg],
          [#emph(ch)],
        )
      } else {
        grid(
          columns: (1fr, auto),
          align: (left, right),
          [#emph(if sec != "" { sec } else { ch })],
          [#display-pg],
        )
      }
      v(-0.55em)
      line(length: 100%, stroke: 0.35pt + luma(170))
    },
    footer: context {
      let pg = counter(page).get().first()
      let loc = here()
      if pg <= 2 { return }
      let h1s = query(heading.where(level: 1)).filter(h => h.location().page() == loc.page())
      if h1s.len() > 0 {
        align(center)[#text(size: 8.5pt, fill: luma(60))[#counter(page).display()]]
      }
    },
  )

  // Typography: Classic Computer Modern with generous leading for inline math
  set text(
    font: ("New Computer Modern", "Libertinus Serif"),
    size: 9.8pt,
    lang: "en",
    hyphenate: true,
  )
  show math.equation: set text(font: "New Computer Modern Math")
  show math.equation.where(block: true): set block(above: 0.95em, below: 0.95em)
  show math.equation.where(block: true): it => {
    if sys.inputs.at("audit", default: "0") == "1" {
      layout(size => {
        let m = measure(it)
        if m.width > size.width - 1mm {
          [#metadata((
            ch: chapter-counter.get().first(),
            eq: counter(math.equation).get().first(),
            page: here().page(),
            w: calc.round(m.width.mm(), digits: 1),
            maxw: calc.round(size.width.mm(), digits: 1),
          )) <eq-overflow>]
        }
        it
      })
    } else {
      it
    }
  }
  show raw.where(block: true): set text(font: "DejaVu Sans Mono", size: 8.0pt)
  show raw.where(block: false): it => {
    let s = it.text
    let s = s.replace(regex("([/._])([^\\s])"), m => m.captures.at(0) + "\u{200B}" + m.captures.at(1))
    let s = s.replace(regex("([a-z0-9])([A-Z])"), m => m.captures.at(0) + "\u{200B}" + m.captures.at(1))
    text(font: "DejaVu Sans Mono", size: 0.84em, hyphenate: false, s)
  }

  set par(
    justify: true,
    leading: 0.76em,
    first-line-indent: 1.2em,
    spacing: 0.82em,
  )

  // Equation numbering (chapter.eq)
  set math.equation(numbering: n => context {
    let c = chapter-counter.get().first()
    if c == 0 { "(" + str(n) + ")" } else { "(" + str(c) + "." + str(n) + ")" }
  })

  // Headings styling
  show heading.where(level: 1): it => {
    set par(first-line-indent: 0pt, justify: false)
    text(size: 19pt, weight: "bold", fill: gtm-navy)[#it.body]
  }

  show heading.where(level: 2): it => {
    set par(first-line-indent: 0pt, justify: false)
    v(0.75em, weak: true)
    context {
      let c = chapter-counter.get().first()
      let nums = counter(heading).get()
      let sec-str = if c > 0 and nums.len() >= 2 {
        str(c) + "." + str(nums.at(1))
      } else {
        ""
      }
      if it.numbering != none and sec-str != "" {
        current-section.update(sec-str + " " + it.body)
        text(size: 12pt, weight: "bold", fill: gtm-navy)[#sec-str #h(0.45em) #it.body]
      } else {
        text(size: 12pt, weight: "bold", fill: gtm-navy)[#it.body]
      }
    }
    v(0.35em, weak: true)
  }

  show heading.where(level: 3): it => {
    set par(first-line-indent: 0pt, justify: false)
    v(0.55em, weak: true)
    context {
      let c = chapter-counter.get().first()
      let nums = counter(heading).get()
      let sub-str = if c > 0 and nums.len() >= 3 {
        str(c) + "." + str(nums.at(1)) + "." + str(nums.at(2))
      } else {
        ""
      }
      if it.numbering != none and sub-str != "" {
        text(size: 10.4pt, weight: "bold", fill: gtm-accent)[#sub-str #h(0.4em) #it.body]
      } else {
        text(size: 10.4pt, weight: "bold", fill: gtm-accent)[#it.body]
      }
    }
    v(0.25em, weak: true)
  }

  set heading(numbering: "1.1.1")

  // Code blocks (Lean 4)
  show raw.where(block: true): it => {
    v(0.45em)
    block(
      width: 100%,
      fill: gtm-lean-bg,
      stroke: 0.4pt + luma(205),
      inset: (x: 8pt, y: 7pt),
      radius: 2pt,
      breakable: true,
    )[
      #set par(leading: 0.62em, justify: false)
      #it
    ]
    v(0.45em)
  }

  body
}
