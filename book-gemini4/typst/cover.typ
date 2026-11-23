// ============================================================================
// Cover Page & Frontmatter Title Pages for "Alpöge–Claude–Riemann Theorem"
// ============================================================================
#import "template.typ": gtm-yellow, gtm-navy, gtm-accent, gtm-rule, gtm-tint

#let cover-page() = {
  page(
    width: 162mm,
    height: 240mm,
    margin: 0mm,
    header: none,
    footer: none,
    fill: gtm-yellow,
  )[
    // Top thin dark accent strip
    #place(top + left)[
      #rect(width: 162mm, height: 6mm, fill: gtm-navy)
    ]

    // Neutral series header
    #place(top + left, dx: 19mm, dy: 16mm)[
      #box(width: 124mm)[
        #grid(
          columns: (1fr, auto),
          align: (left + bottom, right + bottom),
          [#text(size: 11.5pt, weight: "medium", tracking: 0.06em, fill: gtm-navy)[
            Formal Mathematics
          ]],
          [#text(size: 10.5pt, weight: "medium", tracking: 0.04em, fill: gtm-navy)[
            Proof of Riemann Hypothesis
          ]],
        )
        #v(2.5mm)
        #line(length: 100%, stroke: 0.9pt + gtm-navy)
      ]
    ]

    // Author block
    #place(top + left, dx: 19mm, dy: 34mm)[
      #box(width: 124mm)[
        #set par(first-line-indent: 0pt, justify: false)
        #text(size: 15.5pt, weight: "bold", fill: gtm-navy)[
          Gemini 4 Neon
        ]
        #v(2mm)
        #text(size: 10.5pt, weight: "regular", fill: rgb("#2A3548"))[
          Expository Monograph on the Formal Proof by Levent Alpöge & Claude
        ]
      ]
    ]

    // Main Title Block
    #place(top + left, dx: 19mm, dy: 58mm)[
      #box(width: 124mm)[
        #set par(leading: 0.48em, justify: false, first-line-indent: 0pt)
        #set text(hyphenate: false)
        #text(size: 26pt, weight: "bold", fill: gtm-navy)[
          Alpöge–Claude–Riemann\ Theorem
        ]
        #v(5mm)
        #line(length: 44mm, stroke: 1.4pt + gtm-navy)
        #v(4.5mm)
        #set par(leading: 0.62em)
        #text(size: 11pt, style: "italic", fill: rgb("#2A3548"))[
          From Riemann's 1859 Memoir to Chained Theta Lifts,
          Automorphic Multiplicity, and Formal Verification in Lean 4
        ]
      ]
    ]

    // Central Mathematical Graphic: Critical Strip + Zeros + Theta Lift Chain
    #place(top + left, dx: 19mm, dy: 116mm)[
      #box(
        width: 124mm,
        height: 82mm,
        fill: rgb("#FFFDF5"),
        stroke: 0.8pt + gtm-navy,
        radius: 1.5pt,
      )[
        // Subtle critical strip shading (0 < Re(s) < 1)
        #place(top + left, dx: 27mm, dy: 8mm)[
          #rect(width: 34mm, height: 64mm, fill: rgb("#FDF3C7").transparentize(35%), stroke: none)
        ]

        // Axes for the s-plane
        #place(top + left, dx: 13mm, dy: 64mm)[
          #line(length: 62mm, stroke: 0.6pt + gtm-navy)
        ]
        #place(top + left, dx: 27mm, dy: 8mm)[
          #line(start: (0mm, 0mm), end: (0mm, 64mm), stroke: 0.6pt + gtm-navy)
        ]
        // Re(s) = 1 line
        #place(top + left, dx: 61mm, dy: 8mm)[
          #line(start: (0mm, 0mm), end: (0mm, 64mm), stroke: (paint: gtm-rule, thickness: 0.5pt, dash: "dashed"))
        ]
        // Critical line Re(s) = 1/2
        #place(top + left, dx: 44mm, dy: 8mm)[
          #line(start: (0mm, 0mm), end: (0mm, 64mm), stroke: 1.1pt + rgb("#B22222"))
        ]

        // Non-trivial zeros on Re(s) = 1/2
        #let zero-ys = (54.0, 48.8, 45.2, 40.3, 38.2, 33.4, 30.6, 27.9, 23.8, 21.6, 18.2, 14.5)
        #for y in zero-ys {
          place(top + left, dx: 44mm - 1.2mm, dy: y * 1mm - 1.2mm)[
            #circle(radius: 1.2mm, fill: gtm-navy, stroke: 0.5pt + white)
          ]
        }

        // Labels on s-plane
        #place(top + left, dx: 25.5mm, dy: 66mm)[#text(size: 7pt, fill: gtm-navy)[$0$]]
        #place(top + left, dx: 41.5mm, dy: 66mm)[#text(size: 7pt, fill: rgb("#B22222"))[$1/2$]]
        #place(top + left, dx: 60mm, dy: 66mm)[#text(size: 7pt, fill: gtm-navy)[$1$]]
        #place(top + left, dx: 15mm, dy: 10mm)[#text(size: 7.5pt, fill: gtm-navy)[$s$-plane]]
        #place(top + left, dx: 46mm, dy: 10mm)[#text(size: 7pt, fill: rgb("#B22222"))[$rho = 1/2 + i gamma$]]
        #place(top + left, dx: 64mm, dy: 62mm)[#text(size: 7pt, fill: gtm-navy)[$sigma$]]

        // Divider between analytic plane and automorphic chain
        #place(top + left, dx: 78mm, dy: 10mm)[
          #line(start: (0mm, 0mm), end: (0mm, 62mm), stroke: 0.4pt + luma(200))
        ]

        // Right panel: Chained Theta Lifts U(X_0) -> U(X_1) -> ... -> U(X_m)
        #place(top + left, dx: 82mm, dy: 10mm)[
          #text(size: 7.2pt, weight: "bold", fill: gtm-navy)[Chained Theta Lifts]
        ]
        #place(top + left, dx: 82mm, dy: 15.5mm)[
          #text(size: 6.5pt, style: "italic", fill: luma(80))[$m approx sqrt(X)$ lifts]
        ]

        #let nodes = (
          (y: 23mm, lbl: [$U(X_0)$]),
          (y: 34mm, lbl: [$U(X_1)$]),
          (y: 45mm, lbl: [$U(X_2)$]),
          (y: 61mm, lbl: [$U(X_m)$]),
        )
        #for n in nodes {
          place(top + left, dx: 86mm, dy: n.y)[
            #rect(
              width: 28mm,
              height: 6.5mm,
              fill: gtm-tint,
              stroke: 0.6pt + gtm-navy,
              radius: 1.5pt,
            )[
              #align(center + horizon)[#text(size: 7.5pt, fill: gtm-navy)[#n.lbl]]
            ]
          ]
        }
        // Arrows between nodes
        #place(top + left, dx: 100mm, dy: 29.5mm)[
          #line(start: (0mm, 0mm), end: (0mm, 4.3mm), stroke: 0.7pt + gtm-accent)
        ]
        #place(top + left, dx: 100mm, dy: 40.5mm)[
          #line(start: (0mm, 0mm), end: (0mm, 4.3mm), stroke: 0.7pt + gtm-accent)
        ]
        #place(top + left, dx: 98.3mm, dy: 52.5mm)[
          #text(size: 8.5pt, fill: gtm-accent)[$dots.v$]
        ]
        #place(top + left, dx: 83mm, dy: 70.5mm)[
          #text(size: 6.4pt, fill: gtm-accent)[$pi |-> pi plus.square mu_j [t]$]
        ]
      ]
    ]

    // Bottom Navy Band
    #place(bottom + left)[
      #rect(width: 162mm, height: 26mm, fill: gtm-navy)[
        #pad(x: 19mm, y: 6mm)[
          #grid(
            columns: (1fr, auto),
            align: (left + horizon, right + horizon),
            [
              #set par(first-line-indent: 0pt, justify: false)
              #set text(hyphenate: false)
              #text(size: 10.5pt, weight: "bold", fill: white, tracking: 0.03em)[
                Formal Mathematics · Proof of Riemann Hypothesis
              ]
              #v(1.5mm)
              #text(size: 8pt, fill: luma(200))[
                Verified in Lean 4 (Mathlib) · November 2026
              ]
            ],
            [
              #box(width: 11mm, height: 11mm, stroke: 0.9pt + gtm-yellow, radius: 1.5pt)[
                #align(center + horizon)[
                  #text(size: 13pt, weight: "bold", fill: gtm-yellow)[$zeta$]
                ]
              ]
            ],
          )
        ]
      ]
    ]
  ]
}

// ============================================================================
// Half-Title and Full Title Pages
// ============================================================================
#let frontmatter-title-pages() = {
  // Page i: Half-title
  page(header: none, footer: none)[
    #set par(first-line-indent: 0pt, justify: false)
    #set text(hyphenate: false)
    #v(4.5cm)
    #align(left)[
      #text(size: 11pt, tracking: 0.08em, fill: gtm-accent)[Formal Mathematics · Proof of Riemann Hypothesis]
      #v(0.8cm)
      #text(size: 20pt, weight: "bold", fill: gtm-navy)[Alpöge–Claude–Riemann\ Theorem]
    ]
  ]

  // Page ii: Series / Context page
  page(header: none, footer: none)[
    #set par(first-line-indent: 0pt, justify: true, leading: 0.75em)
    #v(1fr)
    #text(size: 8.8pt, fill: luma(85))[
      This expository monograph presents a self-contained graduate-level account of the
      Alpöge–Claude proof of the Riemann Hypothesis and Generalized Riemann Hypothesis,
      grounded directly in the formally verified Lean 4 library released on November 20, 2026
      and independently certified by the Lean FRO and Mathlib community.
    ]
    #v(1cm)
  ]

  // Page iii: Full Title Page
  page(header: none, footer: none)[
    #set par(first-line-indent: 0pt, justify: false)
    #set text(hyphenate: false)
    #v(2.2cm)
    #text(size: 15.5pt, weight: "bold", fill: gtm-navy)[Gemini 4 Neon]
    #v(0.25cm)
    #text(size: 10.5pt, fill: gtm-accent)[Based on the Formally Verified Lean 4 Proof by Levent Alpöge & Claude]
    #v(1.6cm)
    #line(length: 100%, stroke: 1.2pt + gtm-navy)
    #v(0.6cm)
    #text(size: 24pt, weight: "bold", fill: gtm-navy)[Alpöge–Claude–Riemann\ Theorem]
    #v(0.45cm)
    #set par(leading: 0.65em)
    #text(size: 11pt, style: "italic", fill: luma(60))[
      From Riemann's 1859 Memoir to Chained Theta Lifts, Automorphic Multiplicity,
      and Formal Verification in Lean 4
    ]
    #v(0.6cm)
    #line(length: 100%, stroke: 0.5pt + gtm-rule)
    #v(1fr)
    #grid(
      columns: (auto, 1fr),
      gutter: 10pt,
      align: (left + horizon, left + horizon),
      [
        #box(width: 9mm, height: 9mm, fill: gtm-navy, radius: 1pt)[
          #align(center + horizon)[#text(size: 11pt, weight: "bold", fill: gtm-yellow)[$zeta$]]
        ]
      ],
      [
        #text(size: 10.5pt, weight: "bold", fill: gtm-navy)[Formal Mathematics · Proof of Riemann Hypothesis]\
        #text(size: 8.5pt, fill: luma(80))[First Edition · November 2026]
      ],
    )
    #v(0.8cm)
  ]

  // Page iv: Colophon page
  page(header: none, footer: none)[
    #v(1fr)
    #set text(size: 8.4pt, fill: luma(75))
    #set par(leading: 0.68em, first-line-indent: 0pt)
    *Alpöge–Claude–Riemann Theorem* \
    Author: *Gemini 4 Neon* \
    An Expository Monograph Based on the Formal Proof in Lean 4 by Levent Alpöge and Claude.

    #v(0.7em)
    *Primary Formal Source:* \
    `leanprover-community/riemann-hypothesis` (mirroring `https://alpo.ge/lean.tar.gz.part01`--`part14`) \
    Lean Toolchain: `leanprover/lean4:v4.33.1` · Mathlib target: `theorem riemannHypothesis : RiemannHypothesis`

    #v(0.7em)
    *Primary Narrative Source:* \
    Levent Alpöge, *Remark* (`https://alpo.ge/remark.pdf`), November 20, 2026.

    #v(0.7em)
    *Typography:* \
    Typeset with Typst 0.14.0 in New Computer Modern and New Computer Modern Math,
    formatted in royal octavo (162 mm × 240 mm) as an independent monograph in
    Formal Mathematics.

    #v(0.7em)
    *Edition:* November 2026.
  ]
}
