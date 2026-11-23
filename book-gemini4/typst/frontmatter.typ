// ============================================================================
// Frontmatter: Preface, Reader's Guide, Table of Contents, Notation
// ============================================================================
#import "template.typ": gtm-navy, gtm-accent, gtm-rule, gtm-tint, current-chapter, current-section

#let frontmatter() = {
  set page(numbering: "i")
  counter(page).update(5)
  current-chapter.update("Preface")
  current-section.update("")

  // ---- PREFACE ----
  pagebreak(weak: true)
  block(above: 0pt, below: 0pt)[
    #v(1.2cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.3cm)
    #heading(level: 1, numbering: none, outlined: true)[Preface]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]
  v(0.5cm)

  [
    On November 20, 2026, Levent Alpöge released a brief four-page announcement titled *Remark* together with a fourteen-part compressed archive containing a complete, assumption-free formal proof in Lean 4 of the Riemann Hypothesis and the Generalized Riemann Hypothesis for all Dirichlet $L$-functions, discovered and formalized in collaboration with Anthropic's AI system Claude. Within forty-eight hours, independent verification efforts led by the Lean Focused Research Organization (FRO), the Mathlib Initiative, and researchers worldwide confirmed that the library compiles cleanly against Mathlib's longstanding formal statement `RiemannHypothesis`, depends exclusively on Lean's three standard logical axioms (`propext`, `Quot.sound`, `Classical.choice`), and passes scrutiny by independent proof checkers including `comparator`, `nanoda`, `con-leche`, and `con-ron`.

    Yet this historic milestone arrived in an unprecedented form. Rather than a conventional journal article or monograph, the proof first appeared as roughly seventeen million lines of machine-checked Lean 4 code spanning more than 149,000 source files across ten interconnected libraries. As Alpöge himself observed in his announcement, machine-generated prose translations of such a formalization easily exceed 250,000 pages while obscuring the conceptual architecture beneath mechanical proof steps. What the mathematical community—and the next generation of number theorists, graduate students, and advanced undergraduates—needs is a coherent, human-centered mathematical exposition that reveals *why* the proof works, how its ideas grow organically out of 167 years of research since Bernhard Riemann's 1859 memoir, and how every major component maps onto the verified formal library.

    This monograph is written as a self-contained graduate-level mathematical exposition to meet that need. Our guiding principle is *progressive illumination*. Rather than plunging the reader immediately into iterated theta lifts on totally definite unitary groups or Harder–Narasimhan slopes of Hermitian lattices, we build the landscape step by step:

    - *Part I* develops the classical theory of the Riemann zeta function and Dirichlet $L$-functions, surveys 167 years of attempts on the Riemann Hypothesis (from Hadamard and de la Vallée Poussin to Weil, Deligne, and Selberg), and presents a self-contained treatment of Stepanov's elementary method over finite fields—the conceptual ancestor of the Alpöge–Claude proof.
    - *Part II* introduces the six modern mathematical pillars mobilized by the proof: Mellin transforms and Landau's nonvanishing criterion; automorphic representations on $op("GL")_n$ and totally definite unitary groups; the Weil representation, theta correspondence, and seesaw duality; complex multiplication, formal groups, and local divisibility at inert primes; Arakelov geometry and Bost's slope inequality; and Galois cohomology, Poitou–Tate duality, and cyclotomic Iwasawa towers.
    - *Part III* presents the complete architecture and core arguments of the Alpöge–Claude proof, anchored directly in the verified Lean 4 source (`leanprover-community/riemann-hypothesis`). We trace the full logical spine from `Main.lean` through the analytic reduction at scale $[Y, Y^(3/2)]$, the chain of $m approx sqrt(X)$ theta lifts synthesizing "automorphic multiplicity" over $bb(Z)$, the integral structure and relative trace formula, the divisor-slope master inequality (`DivIneqObjU`) and height bound (`HeightS`), and the weakened Vandiver window (`VWin`) constructed via Behrend's sphere theorem.
    - *Part IV* examines the formalization itself—its ten-library architecture, independent verification pipeline, and axiom audit—and closes with a discussion of expected simplifications, extensions to the Extended Riemann Hypothesis, and the new era of human–AI mathematical collaboration.

    Throughout the text, formal declarations and module paths from `leanprover-community/riemann-hypothesis` appear in dedicated *Lean 4 Formalization* boxes, allowing readers to cross-reference every major mathematical step with the machine-checked artifact. Each chapter concludes with a curated set of exercises ranging from foundational computations to research-level explorations.
  ]

  // ---- TABLE OF CONTENTS ----
  pagebreak(weak: true)
  current-chapter.update("Contents")
  current-section.update("")
  block(above: 0pt, below: 0pt)[
    #v(1.2cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.3cm)
    #heading(level: 1, numbering: none, outlined: false)[Contents]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]
  v(0.4cm)
  {
    set par(first-line-indent: 0pt)
    show outline.entry.where(level: 1): it => {
      v(0.45em, weak: true)
      strong(it)
    }
    outline(title: none, depth: 2, indent: 1.4em)
  }

  // ---- LIST OF NOTATION ----
  pagebreak(weak: true)
  current-chapter.update("Notation and Conventions")
  current-section.update("")
  block(above: 0pt, below: 0pt)[
    #v(1.2cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.3cm)
    #heading(level: 1, numbering: none, outlined: true)[Notation and Conventions]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]
  v(0.4cm)

  table(
    columns: (32%, 68%),
    stroke: (x: none, y: 0.35pt + luma(215)),
    inset: (x: 4pt, y: 5pt),
    align: (left, left),
    [*Symbol*], [*Meaning*],
    [$s = sigma + i t$], [Complex variable with $sigma = op("Re")(s)$, $t = op("Im")(s)$],
    [$zeta(s), xi(s)$], [Riemann zeta function and completed zeta function],
    [$L(s, chi), Lambda(s, chi)$], [Dirichlet $L$-function and completed $L$-function for character $chi$],
    [$Lambda(n)$], [von Mangoldt function ($log p$ if $n = p^k$, $0$ otherwise)],
    [$S_a (x)$], [Smoothed sum $sum_(1 <= n <= x) a(n)(x \/ n - 1)$ (`Formalism.Sa`)],
    [$K \/ K_0$], [CM number field $K$ over its maximal totally real subfield $K_0$],
    [$cal(O)_K, bb(A)_K, bb(A)_(K,f)$], [Ring of integers, adeles, and finite adeles of $K$],
    [$U(X), U(p, q)$], [Unitary group of a Hermitian space $X$ (definite or signature $(p,q)$)],
    [$theta_phi (g, h)$], [Theta kernel and theta lift on a unitary dual pair $(U(V), U(W))$],
    [$pi plus.square mu_j [t]$], [Isobaric automorphic transfer induced by a theta lift step],
    [$D, Omega$], [Invariant derivation on a CM elliptic curve and its fundamental period],
    [$hat(op("deg"))(overline(E)), mu_max, mu_min$], [Arakelov degree, maximal and minimal Harder–Narasimhan slopes],
    [$op("ph")(nu)$], [Logarithmic Stirling function $nu log nu - nu$ (`Formalism.LatticeIndexTer.ph`)],
    [$op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$], [Tate–Shafarevich / Selmer kernel at twist $-e$ (`Formalism.GaloisCohomology.Sha`)],
    [$x, epsilon, L, b, a$], [Primary asymptotic scales: $L = x^epsilon$, $b = e^L$, $a = x b$],
    [$m approx sqrt(X)$], [Length of the iterated theta-lift chain $U(X_0) -> dots.c -> U(X_m)$],
  )
}
