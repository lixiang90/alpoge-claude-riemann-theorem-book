#import "style.typ": *
#show: layout
#jacket()
#include "preface.typ"
#include "volume-guide.typ"
#pagebreak(weak: true)
#heading(level: 1, numbering: none, outlined: false)[Contents]
#[
  #set par(first-line-indent: 0pt, leading: 0.47em, spacing: 0.30em)
  #set text(size: 10pt)
  #show outline.entry.where(level: 2): set text(size: 9.4pt)
  #outline(title: none, depth: 2)
]
#part([Part I], [Origins and mathematical tools], [From prime tables to a question about zeros. Transforms, finite characters, lattices, and Galois cohomology supply the language for the proof.], (
  [*Chapters 1–2*], [What did Riemann see in the prime counts, and how far did earlier methods reach?],
  [*Chapters 3–4*], [How does a zero enter a transform, and how does a character distinguish primes?],
  [*Chapters 5–6*], [How can volume, divisibility, and a Galois extension class measure arithmetic information?],
))
#include "volume-ch01.typ"
#include "volume-ch02.typ"
#include "volume-ch03.typ"
#include "volume-ch04.typ"
#include "volume-ch05.typ"
#include "volume-ch06.typ"
#include "volume-interlude.typ"
#part([Part II], [The proof], [An off-line zero would force a positive excursion on every sufficiently late power-width interval. Integral theta lifts and a cohomological choice of intervals provide an incompatible upper bound.], (
  [*Chapters 7–9*], [Localize the effect of a single zero on a weighted prime sum.],
  [*Chapters 10–12*], [Choose a family of characters and realize its weights in a chain of theta lifts.],
  [*Chapters 13–16*], [Count prime powers by divisibility, compare slopes, and control cohomology on one interval.],
  [*Chapters 17–18*], [Recover the same prime sum, balance the four errors, and rule out a zero.],
))
#include "volume-ch07.typ"
#include "volume-ch08.typ"
#include "volume-ch09.typ"
#include "volume-ch10.typ"
#include "volume-ch11.typ"
#include "volume-ch12.typ"
#include "volume-ch13.typ"
#include "volume-ch14.typ"
#include "volume-ch15.typ"
#include "volume-ch16.typ"
#include "volume-ch17.typ"
#include "volume-ch18.typ"
#include "volume-auxiliary.typ"
#include "volume-exercises.typ"
#include "volume-problems.typ"
#include "expanded/source-guide.typ"
#include "volume-endmatter.typ"

#include "volume-index.typ"
