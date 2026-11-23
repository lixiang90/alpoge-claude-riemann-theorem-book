// ============================================================================
// Master Document: Alpöge–Claude–Riemann Theorem
// Formal Mathematics Expository Monograph
// ============================================================================
#import "template.typ": gtm-book, part-page
#import "cover.typ": cover-page, frontmatter-title-pages
#import "frontmatter.typ": frontmatter

// Part I: Origins, History, and Analytic Foundations
#import "ch01_riemann_memoir.typ": ch01
#import "ch02_dirichlet_grh.typ": ch02
#import "ch03_history_approaches.typ": ch03
#import "ch04_stepanov_method.typ": ch04

// Part II: Mathematical Machinery and Preliminaries
#import "ch05_explicit_formula_landau.typ": ch05
#import "ch06_automorphic_unitary.typ": ch06
#import "ch07_theta_correspondence.typ": ch07
#import "ch08_cm_curves_divisibility.typ": ch08
#import "ch09_arakelov_bost.typ": ch09
#import "ch10_galois_cohomology_iwasawa.typ": ch10

// Part III: The Alpöge–Claude Proof of RH and GRH
#import "ch11_proof_blueprint.typ": ch11
#import "ch12_analytic_reduction.typ": ch12
#import "ch13_chained_theta_lifts.typ": ch13
#import "ch14_local_divisibility_integral.typ": ch14
#import "ch15_slope_master_inequality.typ": ch15
#import "ch16_vandiver_window_synthesis.typ": ch16

// Part IV: Formalization in Lean 4, Verification, and Perspectives
#import "ch17_lean_formalization.typ": ch17
#import "ch18_simplifications_outlook.typ": ch18

// Appendices & Backmatter
#import "app_a_lean_map.typ": app-a
#import "app_b_parameters.typ": app-b
#import "backmatter.typ": backmatter

#show: gtm-book.with(
  title: "Alpöge–Claude–Riemann Theorem",
  subtitle: "From Riemann's 1859 Memoir to Chained Theta Lifts, Automorphic Multiplicity, and Formal Verification in Lean 4",
  author: "Gemini 4 Neon",
)

// Cover and Frontmatter
#cover-page()
#frontmatter-title-pages()
#frontmatter()

// Switch to Arabic page numbering for main matter
#set page(numbering: "1")
#counter(page).update(1)

// ============================================================================
// PART I
// ============================================================================
#part-page(
  "I",
  "Origins, History, and Analytic Foundations",
  subtitle: "From Riemann's 1859 Memoir to Stepanov's Multiplicity Paradigm",
  summary: [
    Part I establishes the classical landscape of the Riemann Hypothesis and the Generalized Riemann Hypothesis. We begin with Bernhard Riemann's landmark 1859 memoir on the zeta function and its extension to Dirichlet $L$-functions, survey 167 years of analytic, spectral, and geometric paradigms culminating in the November 2026 announcement, and present a self-contained treatment of Stepanov's elementary method over finite fields---the conceptual ancestor of the Alpöge--Claude proof.
  ],
)
#ch01()
#ch02()
#ch03()
#ch04()

// ============================================================================
// PART II
// ============================================================================
#part-page(
  "II",
  "Mathematical Machinery and Preliminaries",
  subtitle: "Six Modern Pillars Mobilized in the Proof",
  summary: [
    Part II develops the six modern theories that interlock inside the Alpöge--Claude proof: smoothed prime sums and Landau's nonvanishing criterion; automorphic representations on totally definite unitary groups and $op("GL")_n$; the Weil representation, theta lifts, and seesaw duality; complex multiplication, formal groups, and inert-prime divisibility; Arakelov geometry and Bost's slope inequality; and Galois cohomology, Poitou--Tate duality, and cyclotomic Iwasawa towers via Behrend's sphere construction.
  ],
)
#ch05()
#ch06()
#ch07()
#ch08()
#ch09()
#ch10()

// ============================================================================
// PART III
// ============================================================================
#part-page(
  "III",
  "The Alpöge–Claude Proof of the Riemann Hypothesis",
  subtitle: "Chained Theta Lifts, Bost's Slope Inequality, and the Weakened Vandiver Window",
  summary: [
    Part III presents the complete proof of the Generalized Riemann Hypothesis and the classical Riemann Hypothesis, anchored directly in the verified Lean 4 codebase `leanprover-community/riemann-hypothesis`. Beginning with a global architectural blueprint from `Main.lean`, we trace the analytic reduction at scale $[Y, Y^(3/2)]$, the chain of $m approx sqrt(X)$ theta lifts synthesizing automorphic multiplicity, the glued integral structure and relative trace formula, the divisor-slope master inequality (`DivIneqObjU`) and height bound (`HeightS`), and the weakened Vandiver window (`VWin`) that closes the argument.
  ],
)
#ch11()
#ch12()
#ch13()
#ch14()
#ch15()
#ch16()

// ============================================================================
// PART IV
// ============================================================================
#part-page(
  "IV",
  "Formal Verification in Lean 4 and Open Horizons",
  subtitle: "Auditing a Twenty-Million-Line Proof and Looking Beyond 2026",
  summary: [
    Part IV turns to the formal artifact itself and the future it opens. We dissect the ten-library Lean 4 architecture, its statement-integrity and independent-checker verification pipeline (`comparator`, `nanoda`, `con-leche`, `con-ron`), and its strict three-axiom audit, before surveying unconditional consequences, collateral discoveries in algebraic $K$-theory, avenues for massive simplification, and extensions toward the Extended and Grand Riemann Hypotheses.
  ],
)
#ch17()
#ch18()

// ============================================================================
// APPENDICES & BACKMATTER
// ============================================================================
#app-a()
#app-b()
#backmatter()
