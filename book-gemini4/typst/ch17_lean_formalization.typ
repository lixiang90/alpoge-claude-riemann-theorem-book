// ============================================================================
// Chapter 17: Inside the Lean 4 Formalization and Independent Verification
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch17() = [
  #chapter(
    "Inside the Lean 4 Formalization and Independent Verification",
    short-title: "Lean 4 Formalization and Verification",
    epigraph: "We are not only interested in whether a theorem is true, nor merely in whether a proof is correct; we want to be certain beyond doubt that the statement we proved is the one we meant, that no hidden assumption slipped in, and that the reasoning can be checked by an independent mind—or an independent machine.",
    epigraph-source: "After N. G. de Bruijn, The Mathematical Vernacular (1970)",
    overview: [
      A proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet $L$-functions that spans twenty million lines of machine-checked code presents an unprecedented mathematical and engineering artifact. Having developed the conceptual architecture of the Alpöge–Claude proof in Chapters 4 through 16—from Stepanov's auxiliary-polynomial philosophy and chained theta lifts to Harder–Narasimhan slopes, Arakelov intersection bounds, and character-box elimination—we now open the hood of the Lean 4 repository `leanprover-community/riemann-hypothesis`. This chapter examines the ten-library architecture of the codebase, the subtle problem of *statement integrity* (ensuring that the formalized theorem matches both Mathlib's `RiemannHypothesis` and Google DeepMind's pre-existing `formal-conjectures` benchmark without definitional cheating), the sandboxed multi-kernel verification pipeline (`comparator`, `leanchecker-paranoid`, `nanoda`, `con-leche`, `con-ron`, and `lean4lean`), the classical axiom audit (`propext`, `Quot.sound`, `Classical.choice`), and finally the epistemological lessons of human–AI collaboration in formal mathematics.
    ],
    label-name: "ch-lean-formalization",
  )

  == Anatomy of a 20-Million-Line Formal Library

  When Levent Alpöge and Claude publicly released the formal proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet $L$-functions on November 20, 2026 (announced in `alpo.ge/remark.pdf` together with a fourteen-part compressed archive `lean.tar.gz` of $239,275,554$ bytes, decompressing to $1.03$ gigabytes of Lean 4 source), the mathematical community was confronted with an object unlike any previous formalization in history. Earlier landmark formalizations—such as Gonthier's proofs of the Four Color Theorem and the Odd Order Theorem in Coq/Rocq, Hales's Flyspeck verification of the Kepler Conjecture in HOL Light and Isabelle, or the Liquid Tensor Experiment in Lean 3—measured in the tens or hundreds of thousands of lines. By contrast, the initial release of the Alpöge–Claude proof comprised $175,187$ `.lean` files containing $17,374,215$ lines of code ($15,531,759$ non-blank lines), zero comments, $818,755$ `theorem` and `lemma` declarations, and $242,067$ definitions, structures, typeclasses, instances, and inductive types, with every single file lying in the transitive import closure of the top-level module `Main`.

  Immediately following the release, the Lean community established the `leanprover-community/riemann-hypothesis` repository with two complementary mandates. The first mandate was *independent verification*: freezing the exact original archive at commit `40e56bab`, auditing its dependencies and axioms, and subjecting its exported proof terms to multiple independent proof checkers in network-isolated sandboxes. The second mandate was *accessibility and refactoring* on the `main` branch: migrating the project from Lean `v4.33.1` through `v4.36.0` to `v4.37.0-rc1`, pruning unused declarations, normalizing formatting and module boundaries, adding documentation, and deploying a distributed build cache (`rh-cache.taucetiproject.org`) so that working mathematicians can inspect and edit individual modules within minutes rather than compiling for hours on a 48-core server with half a terabyte of memory.

  In the refactored `main` branch of `leanprover-community/riemann-hypothesis`, the codebase comprises exactly $149,217$ `.lean` files totaling $20,788,900$ lines of Lean 4 code. (The decrease in file count from $175,187$ to $149,217$ reflects the elimination of redundant auxiliary modules and consolidation of small files, while the increase in line count from $17.4$ million to $20.8$ million reflects explicit formatting, Mathlib `v4.36+` API migrations, and community refactoring.)

  === The Ten-Library Architecture in `lakefile.toml`

  Lean 4's build system, Lake, organizes the project (`name = "tree"`, source root `src/`) into ten `[[lean_lib]]` targets declared in `lakefile.toml`, plus an eleventh verification-only library `Challenge` appended below a strict boundary marker so that Continuous Integration (CI) can verify that the submission's build configuration remains untouched. An excerpt of `lakefile.toml` illustrates the global compiler discipline enforced across the entire proof:

  ```toml
  name = "tree"
  srcDir = "src"
  defaultTargets = [
    "CompanionTheory", "Development", "Formalism",
    "GroundTheory", "GroundTheoryFields", "Lemmata",
    "PositivityTheory", "ReciprocityTheory", "Supplements", "Main"
  ]
  moreLeanArgs = ["--tstack=400000"]

  [leanOptions]
  autoImplicit = false
  relaxedAutoImplicit = false
  maxSynthPendingDepth = 3
  pp.unicode.fun = true
  maxHeartbeats = 4000000
  ```

  Several engineering parameters in this configuration deserve notice. Setting `autoImplicit = false` and `relaxedAutoImplicit = false` forbids Lean from silently introducing unbound variables as implicit universal quantifiers—a classic source of accidentally vacuous or misstated lemmas in large developments. The flag `--tstack=400000` allocates a $400$ megabyte thread stack for deeply nested kernel and elaborator recursions, while `maxHeartbeats = 4000000` raises the deterministic elaboration budget twentyfold above Lean's default ($200,000$) to accommodate heavy typeclass inference and algebraic-geometric rewriting. Even more revealing is the split between `GroundTheory` and `GroundTheoryFields`: the two subdirectories `GroundTheory.LocalFields.+` and `GroundTheory.GlobalFields.+` are carved into their own Lake library solely so that they can receive a dedicated typeclass-synthesis budget (`synthInstance.maxHeartbeats = 400000`), reflecting the intense diamond-resolution pressure of simultaneous topological, metric, valuation, and algebraic structures on local and global fields.

  Table 17.1 summarizes the exact empirical file and line counts of the `main` branch across all libraries.

  #figure(
    table(
      columns: (auto, 1fr, auto, auto, auto),
      inset: (x: 6pt, y: 5pt),
      align: (left, left, right, right, right),
      stroke: (x, y) => (
        top: if y == 0 { 1.1pt + gtm-navy } else if y == 1 or y == 10 { 0.6pt + gtm-navy } else { 0.25pt + luma(210) },
        bottom: if y == 10 { 1.1pt + gtm-navy } else { none },
      ),
      fill: (_, y) => if y == 0 { gtm-tint } else if y == 10 { gtm-tint } else { none },
      [*Library*], [*Primary Mathematical Role*], [*Files*], [*Lines*], [*Share*],
      [`Development`], [Core proof engine: abelian varieties, automorphic arithmetic, character boxes, étale cohomology, resolution of singularities, Weil bounds], [121,214], [15,474,506], [74.4%],
      [`Formalism`], [Quantitative analytic/Arakelov machinery: Harder–Narasimhan slopes, Hermitian curvature, Wach lifts, theta supremum bounds, zero-free regions], [15,292], [3,172,983], [15.3%],
      [`GroundTheory` (+ `GroundTheoryFields`)], [Foundations above Mathlib: local/global fields, arithmetic geometry, automorphic forms, Brauer groups, $p$-adic Hodge theory, Tate cohomology], [6,667], [1,120,090], [5.4%],
      [`ReciprocityTheory`], [Adelic approximation, class field theory, Chebotarev density, geometry of numbers, $L^2$-$macron(partial)$ estimates, semistable reduction, theta summability], [3,581], [678,634], [3.3%],
      [`CompanionTheory`], [Archimedean & spectral companions: Harish-Chandra modules, real groups, spectral geometry, eightfold theory, thickening estimates], [1,946], [269,609], [1.3%],
      [`PositivityTheory`], [Positivity criteria, representation-theoretic and automorphic positivity packages, formalized published theorems], [355], [58,090], [0.3%],
      [`Lemmata`], [Reusable algebraic, Hermitian linear-algebraic, determinant, and analytic glue (`GeneralBFact*`, `FirstBlockLemma*`, `DetNormLeProdRows`)], [158], [14,830], [0.1%],
      [Root (`Main`, `Statements`, `Challenge`)], [Public theorem signatures, top-level assembly (`Main.lean`), and Mathlib-only verification challenge (`Challenge.lean`)], [3], [103], [$< 0.01$%],
      [`Supplements`], [Packaging of top-level kernel claims (`Supplements/Kernels/MainTheorems.lean`)], [1], [55], [$< 0.01$%],
      [*Total*], [*Complete formalization (`leanprover-community/riemann-hypothesis`, `main`)*], [*149,217*], [*20,788,900*], [*100.0%*],
    ),
    caption: [Empirical breakdown of the ten-library architecture of `leanprover-community/riemann-hypothesis` (`main` branch). Share percentages are by line count; the original November 20, 2026 release contained $175,187$ files and $17,374,215$ lines.],
  )

  === Mathematical Role of Each Library

  Viewing Table 17.1 from the bottom of the dependency hierarchy upward reveals a cleanly stratified mathematical edifice built atop Mathlib (pinned in `lakefile.toml` to a verified commit of `leanprover-community/mathlib4`):

  1. *`GroundTheory` and `GroundTheoryFields`* ($6,667$ files, $1,120,090$ lines): These two libraries supply the foundational arithmetic-geometric infrastructure absent from Mathlib at the time of the proof. `GroundTheoryFields` formalizes the algebraic and topological theory of `LocalFields` and `GlobalFields`, while `GroundTheory` spans ten major sub-packages visible directly in `lakefile.toml`: `ArithmeticGeometry`, `AutomorphicForms`, `Brauer`, `FunctionField`, `HeightsAndTheta`, `IdeleRoots`, `PAdicHodge`, `PowerSubgroups`, `ProfiniteCohomology`, and `TateCohomology`. Together they furnish the basic language of adeles, ideles, Galois cohomology, Brauer–Hasse–Noether invariants, and height functions used throughout the remainder of the monograph.

  2. *`ReciprocityTheory`* ($3,581$ files, $678,634$ lines): Building on `GroundTheory`, this library develops the reciprocity and analytic-adelic toolkit: `AdeleApproximation`, `ClassFieldTheory`, `Chebotarev`, `GroupCohomology`, `ReductiveGroups`, `SemistableReduction`, `GeometryOfNumbers`, `DualLattices`, `ReducedBases`, `L2DbarEstimates`, `ThetaQuasiPeriods`, and `ThetaSummability`. In the conceptual narrative of Chapters 7–11, this is where global class field theory meets the geometry of Hermitian lattices and the $L^2$-estimates governing theta kernels.

  3. *`CompanionTheory`* ($1,946$ files, $269,609$ lines): Whereas `ReciprocityTheory` handles the arithmetic and adelic side, `CompanionTheory` formalizes the archimedean, Lie-theoretic, and spectral machinery: `RealGroups`, `HarishChandraModules`, `AutomorphicTheory`, `SpectralGeometry`, `ThickeningEstimates`, and `EightfoldTheory`. These modules control the archimedean local factors, $(frak(g), K)$-module cohomology, and spectral thickening inequalities required when passing from discrete automorphic multiplicities to analytic bounds.

  4. *`PositivityTheory`* ($355$ files, $58,090$ lines): Organized into `AutomorphicForms`, `Representations`, and `PublishedTheorems`, this compact library isolates the positivity mechanisms—including representation-theoretic unitarity and formalized versions of classical positivity theorems—that convert spectral or geometric non-negativity into zero-free constraints.

  5. *`Formalism`* ($15,292$ files, $3,172,983$ lines): The second-largest library in the repository (15.3% of all lines) implements the quantitative machinery of the proof across nearly a hundred focused subdirectories. Here live `HarderNarasimhan`, `HermitianCurvature`, `HermitianLattices`, `LatticeSlopes`, `LatticeTheta`, `MeanHeightDescent`, `MahlerMeasure`, `PeriodIntegrals`, `ThetaLiftIndependence`, `ThetaSupremumBounds`, `WachModuleLifts`, `WeaklyAdmissibleFiltrations`, `GaloisIrreducibility`, `MirabolicMackeyTheory`, `LocalToGlobal`, `ZeroFreeRegion`, and `ZetaNonvanishing`. If `GroundTheory` defines the objects, `Formalism` proves the sharp quantitative inequalities about them.

  6. *`Lemmata`* ($158$ files, $14,830$ lines): A utility layer of small, self-contained algebraic and analytic lemmas—matrix determinant bounds (`DetNormLeProdRows`, `DetMonotoneStarMulSelf`), Hermitian sesquilinear identities (`HermitianSesquilinear`), discrete valuation quotients, simultaneous eigenvector extractions, and families of block-matrix estimates (`FirstBlockLemmaA`–`K`, `GeneralBFact*`)—factored out to keep import graphs shallow.

  7. *`Development`* ($121,214$ files, $15,474,506$ lines): Accounting for nearly three-quarters (74.4%) of the entire formalization, `Development` houses the deep, specialized pillars of the proof in seven subdirectories: `AbelianVarietyTheory`, `AutomorphicArithmetic`, `AutomorphicSpectrum`, `DiscreteGroups`, `EtaleCohomology`, `ResolutionOfSingularities`, and `WeilBound`. Notice the presence of `ResolutionOfSingularities` (including functorial embedded resolution, which reappears in Section 17.3 in connection with mutual reflexive inductives), `EtaleCohomology`, and `WeilBound`: rather than axiomatizing Deligne's Weil bounds or Hironaka's resolution of singularities, the formalization constructs the required portions from scratch inside Lean 4. The entire proof culminates inside `Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`, which establishes the master nonvanishing theorem `UpperTheory.FinalTheorems.everyCharacter`.

  8. *`Supplements`* ($1$ file, $55$ lines): Contains `Supplements/Kernels/MainTheorems.lean`, which packages `allChi`, `rhOfAll`, `claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta`, and `critAll` into a single summary interface.

  9. *`Main`* (root modules `Statements.lean` and `Main.lean`, plus `Challenge.lean` for Comparator; $3$ files, $103$ lines): The tiny apex of the $20.8$-million-line pyramid. `Main.lean` invokes `UpperTheory.FinalTheorems.everyCharacter` and applies the elementary functional-equation reductions `Claim.zeta` and `Claim.strip` to deduce all five headline theorems in just fourteen lines of actual theorem declarations.

  #insight-box(title: "Why Twenty Million Lines? The Granularity of Machine-Generated Proofs")[
    A natural first reaction among mathematicians is astonishment at the sheer scale: why does a proof of RH and GRH take $20.8$ million lines of Lean 4? Three structural factors explain this scale. First, *zero-axiom self-containment*: Mathlib did not yet contain étale cohomology, resolution of singularities, general global class field theory, Harish-Chandra modules, $p$-adic Hodge theory, or Arakelov Harder–Narasimhan theory, so the formalization had to build substantial swaths of twentieth- and twenty-first-century arithmetic geometry from first principles. Second, *module-level parallelism*: splitting the proof into $tilde.op 150,000$ small `.lean` files allows both automated synthesis and Lake's parallel compiler to work on thousands of independent subgoals simultaneously without blowing up per-file memory or elaboration heartbeats. Third, *uncompressed machine style*: AI-generated formal proofs favor explicit, repetitive, locally self-contained lemmas over the aggressively polymorphic abstractions that human Mathlib maintainers craft over years of refactoring. Much of the community's ongoing work on `main` consists of collapsing this redundancy without altering the underlying mathematical logic.
  ]

  == Statement Integrity: `Challenge.lean`, `Statements.lean`, and `formal-conjectures`

  A persistent misconception about interactive theorem provers is that once a file compiles with zero errors and zero `sorry`s, the mathematical claim is automatically settled. In reality, a proof assistant verifies only a *relative* logical assertion: that a proof term $p$ inhabits a type $T$ in a given environment $Gamma$, written $Gamma tack.r p : T$. It cannot by itself tell whether the type $T$ faithfully encodes the Riemann Hypothesis as understood by mathematicians since 1859. This gap is known as the *statement-integrity problem* (or *specification problem*).

  === Taxonomy of Definitional Cheating

  Before examining how the repository closes this gap, it is instructive to catalog the subtle ways a formal statement can be vacuously true or misaligned with standard mathematics—whether through malice, oversight, or type-elaboration quirks:

  - *Shadowing or redefining core objects*: If a submission defines its own `riemannZeta` (for instance, setting it identically equal to $1$) or shadows Mathlib's namespace, a proof of `∀ s, riemannZeta s = 0 → s.re = 1 / 2` becomes trivial.
  - *Integer-division traps*: In Lean 4, `1 / 2` at type `ℕ` or `ℤ` evaluates to `0` by floor division. If the statement accidentally wrote `(s.re : ℤ) = 1 / 2` or coerced an integer division `(1 / 2 : ℕ)` into `ℝ`, the theorem would assert `s.re = 0` or something nonsensical. In `Challenge.lean`, every `1 / 2` is compared directly with `s.re : ℝ`, so Lean elaborates `/` as real division.
  - *Junk values at poles*: In Mathlib, `riemannZeta` is a total function `ℂ → ℂ`. At its simple pole $s = 1$, Mathlib assigns a conventional "junk value" (coming from the Hurwitz zeta continuation) rather than leaving `riemannZeta 1` undefined. Any faithful statement must explicitly exclude $s = 1$ (and check whether the trivial zeros $-2(n+1)$ are properly excluded without accidentally excluding nontrivial zeros).
  - *Instance hijacking during elaboration*: Even if the surface syntax of a theorem looks identical to Mathlib's, Lean elaborates typeclass arguments (such as `NeZero N`, `CommRing ℂ`, or `DecidablePred`) using whatever instances are currently in scope. If a theorem statement is written in a file that imports the submission's $149,000$ modules, a non-standard typeclass instance defined deep inside the submission could be silently synthesized in place of Mathlib's canonical instance, altering the kernel-level meaning of the statement!

  === The Clean-Room Design of `Challenge.lean`, `Statements.lean`, and `Main.lean`

  To defeat all four failure modes simultaneously, the verification architecture separates the *specification* from the *proof* into three minimal root files totaling just $103$ lines.

  First, `src/Challenge.lean` ($27$ lines) imports *nothing except Mathlib*. It states the four custom propositions and the five target theorems, using `by sorry` as placeholder proofs:

  ```lean
  import Mathlib

  def RiemannZetaZerosOnLine : Prop :=
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

  def DirichletLNonvanishingRightOfHalf : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

  def DirichletLZerosOnLine : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

  def PrimitiveDirichletLZerosOnLine : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

  /-- The headline claim, stated with Mathlib's definition only. -/
  theorem riemannHypothesis : RiemannHypothesis := by sorry
  theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := by sorry
  theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by sorry
  theorem LFunction_eq_zero_re : DirichletLZerosOnLine := by sorry
  theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by sorry
  ```

  Observe how transparent and auditable `Challenge.lean` is: a mathematician with basic familiarity with Lean 4 can audit every single symbol in two minutes. The headline theorem `riemannHypothesis` uses Mathlib's pre-existing `RiemannHypothesis` predicate directly; `riemannZeta_eq_zero_re` writes out the exact equivalent condition explicitly; and the three Dirichlet $L$-function theorems cover nonvanishing for $op("Re")(s) > 1/2$ (for every modulus $N >= 1$ and every character $chi$, including imprimitive ones, since the extra Euler factors $1 - chi(p) p^(-s)$ of an imprimitive character vanish only on $op("Re")(s) = 0$) as well as confinement of critical-strip zeros to $op("Re")(s) = 1/2$ for both arbitrary and primitive characters.

  On the solution side, `src/Statements.lean` ($20$ lines) declares the same four `Prop` definitions as a Lean `module` importing *only* `Mathlib.NumberTheory.LSeries.DirichletContinuation`—zero files from the submission are imported. This guarantees that the elaborated types of the four propositions cannot be contaminated by any instance or notation from the proof tree. Finally, `src/Main.lean` imports `Statements` and the two top-level conclusion modules of `Development` (`Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip` and `MainConclusion`), and discharges all five theorems:

  ```lean
  theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
    UpperTheory.FinalTheorems.everyCharacter

  theorem riemannHypothesis : RiemannHypothesis :=
    Claim.zeta LFunction_ne_zero_of_half_lt_re

  theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

  theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
    Claim.strip LFunction_ne_zero_of_half_lt_re

  theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
    intro N _ χ _ s h₀ h₁ hz
    exact LFunction_eq_zero_re N χ s h₀ h₁ hz
  ```

  Notice the logical elegance of this reduction: the entire $20.8$-million-line engine proves a single master statement, `DirichletLNonvanishingRightOfHalf` (no zero of $L(chi, s)$ in the half-plane $op("Re")(s) > 1/2$, except the pole of the principal character at $s = 1$). From this single theorem, the reflection symmetry of the functional equation (`Claim.strip` and `Claim.zeta`, proved using Mathlib's functional equation for $L(chi, s)$ and $zeta(s)$) immediately rules out zeros in $0 < op("Re")(s) < 1/2$ as well, yielding both RH and GRH on the critical strip.

  === Cross-Checking Against Google DeepMind's `formal-conjectures`

  Even with `Challenge.lean` importing only Mathlib, a skeptical observer might still ask: *were those five statements written after the proof was announced, potentially tailored to what the proof happened to establish?* To eliminate even this residual doubt, the repository maintains a second, independent Comparator setup inside `comparator/` that judges the proof against statements authored *before* the November 2026 announcement by independent contributors to Google DeepMind's `formal-conjectures` repository (`FormalConjectures/Millennium/RiemannHypothesis.lean` at commit `d8d031d4`, dated November 19, 2026).

  In `formal-conjectures`, Salvatore Mercuri authored `GRH.trivialZeros` and `GRH.generalized_riemann_hypothesis` in November 2025 (a full year before the proof), and `franzhusch` added `RiemannHypothesis.riemannHypothesis` in March 2026. Their statement of GRH is notably stricter on its face than `PrimitiveDirichletLZerosOnLine`: rather than restricting $s$ to the open critical strip $0 < op("Re")(s) < 1$, it quantifies over *all* $s in bb(C)$ outside the explicit set of trivial zeros:

  ```lean
  noncomputable def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
    if q = 1 then { -2 * (n + 1) | (n : ℕ) } else
      if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
        { -2 * n | (n : ℕ) }

  theorem generalized_riemann_hypothesis (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
      (hs_nontrivial : s ∉ Int.cast '' trivialZeros χ) :
      s.re = 1 / 2 := by
    sorry
  ```

  To bridge the submission's `Main.lean` to `formal-conjectures`, the community wrote `comparator/FormalConjecturesBridge.lean` (importing only `Statements.lean` and Mathlib, and none of the submission's proofs), which proves the exact biconditional:

  #proposition(title: "Equivalence of Critical-Strip GRH and All-Plane GRH")[
    Over Mathlib's definition of `DirichletCharacter.LFunction`, the proposition `PrimitiveDirichletLZerosOnLine` is logically equivalent to `GRH.generalized_riemann_hypothesis`.
  ]

  #proof[
    We split the complex plane $bb(C)$ into three regions for a primitive character $chi mod q$ ($q >= 1$):
    1. *Region $op("Re")(s) >= 1$*: Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (for $s != 1$ or $q > 1$) together with `riemannZeta_one_ne_zero` (handling Mathlib's nonzero junk value at $q = 1, s = 1$) guarantees $L(chi, s) != 0$.
    2. *Critical strip $0 < op("Re")(s) < 1$*: Here `PrimitiveDirichletLZerosOnLine` applies directly, forcing $op("Re")(s) = 1/2$.
    3. *Left half-plane $op("Re")(s) <= 0$*: Since $chi$ is primitive, its inverse $chi^(-1)$ is also primitive, and $op("Re")(1 - s) >= 1$, so $L(chi^(-1), 1 - s) != 0$ by Region 1. By the completed $L$-function functional equation (without even needing the explicit value of the root number), the completed function $Lambda(chi, s)$ is nonzero at $s$. Since $Lambda(chi, s) = Gamma_bb(R)(s + a) L(chi, s)$ (where $a in {0, 1}$ encodes the parity of $chi$), $L(chi, s)$ can vanish only at the poles of the archimedean Gamma factor—which are precisely the integers in `GRH.trivialZeros χ` (negative even integers $-2(n+1)$ for $q = 1$, negative odd integers $-2n - 1$ for odd $chi$, and non-positive even integers $-2n$ for even $chi$ with $q > 1$).
    Conversely, because every element of `GRH.trivialZeros χ` is a non-positive integer, any zero in $0 < op("Re")(s) < 1$ is automatically nontrivial, so `GRH.generalized_riemann_hypothesis` implies `PrimitiveDirichletLZerosOnLine`.
  ]

  #lean-note(title: "Subtle Kernel-Identity Pitfalls in Cross-Repository Comparison", module: "comparator/FormalConjecturesChallenge.lean")[
    Because `comparator` compares *every* constant transitively referenced by a theorem statement by exact kernel name and definition (roughly $53,000$ constants for `GRH.generalized_riemann_hypothesis`, of which three live outside Mathlib), aligning `FormalConjecturesChallenge.lean` with `FormalConjecturesSolution.lean` revealed two instructive subtleties of Lean 4's elaborator:
    1. *Module-sensitive proof terms*: The `DecidablePred` instance for `χ.Odd` uses `by rfl`, which Lean compiles into an auxiliary constant ending in `._proof_1`. Inside a `module` file, Lean types this constant as `ψ (-1) = -1 ↔ ψ.Odd`, whereas in a non-module file it unfolds `ψ.Odd` to `ψ (-1) = -1 ↔ ψ (-1) = -1`. Comparator immediately rejected an early non-module copy with `Const does not match between challenge and target`.
    2. *Auxiliary constants for numeric literals*: The literal `2` in `1 / 2` carries an implicit proof of `Nat.AtLeastTwo 2`. Inside a `def` body, Lean lifts that proof into a fresh auxiliary constant; inside a `theorem` signature, Lean leaves it inline. Using `type_of%` in `FormalConjecturesSolution.lean` ensures byte-for-byte kernel identity of the theorem type.
    Finally, to prevent any pull request from weakening the specification, a dedicated CI workflow (`challenge-files.yml`, always executed from the base branch) freezes six specification files—`src/Challenge.lean`, `comparator.json`, `export-targets.txt`, and their three counterparts in `comparator/`—rejecting any pull request that modifies a single byte of them.
  ]

  == Independent Verification Pipeline (`comparator`, `nanoda`, `con-leche`, `con-ron`)

  To understand *why* a twenty-million-line proof can be trusted without any human reading all $149,217$ files, we must examine the architecture of Lean 4's trusted kernel and the multi-checker verification pipeline built around it.

  === The de Bruijn Criterion and Lean 4's Trusted Kernel

  In 1970, Nicolaas Govert de Bruijn articulated what is now called the *de Bruijn criterion* for trustworthy proof assistants: a verification system should separate the complex, heuristic, potentially buggy *proof-finding engine* (tactics, elaborator, typeclass search, unification, metaprogramming) from a small, simple, auditable *proof-checking kernel*. Every theorem accepted by the system must be compiled down to an explicit proof term in a formal type theory and typechecked from scratch by the kernel.

  Lean 4's kernel implements a variant of the *Calculus of Inductive Constructions* (CIC), characterized by:
  - A cumulative hierarchy of predicative universes `Sort 1` (`Type 0`), `Sort 2` (`Type 1`), $dots.c$, sitting above an impredicative, proof-irrelevant universe of propositions `Sort 0` (`Prop`).
  - Dependent function types `(x : A) → B x` ($Pi$-types), with $beta$-reduction, $eta$-equivalence, and structural recursion / pattern matching for strictly positive inductive types.
  - Definitional proof irrelevance: if $p, q : P$ where $P : op("Prop")$, then $p$ and $q$ are definitionally equal ($p equiv q$) in the kernel.
  - Native quotient types (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) with a single computation rule `Quot.lift f h (Quot.mk r a) ≡ f a`.

  This separation between elaborator and kernel proved directly relevant during the community's static audit of the Alpöge–Claude submission (`verification/static-scan.txt`). A full text search across all $175,187$ original files confirmed zero occurrences of `axiom`, `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `debug.*`, or `skipKernelTC`, and confirmed that no file performed filesystem I/O or spawned processes. However, the static scan *did* uncover custom metaprogramming tactics in a handful of files:
  - `Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean` defines a tactic `kexactB` (used in $67$ files) that elaborates a term and assigns it directly to a metavariable goal without asking the elaborator to check type agreement.
  - `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean` defines `kcopy`, which rebuilds a structure term field by field and assigns it similarly.
  - `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean` programmatically duplicates declarations via `addDecl`.

  Because `kexactB` and `kcopy` skip the *elaborator's* type check, they look alarming at first glance. Yet under the de Bruijn criterion, skipping the elaborator cannot compromise soundness: every declaration produced by `addDecl` or tactic elaboration is still handed to the kernel, which rejects any ill-typed term unconditionally.

  Even so, *a single kernel implementation is still software*, written in C++ (roughly $10,000$ lines in Lean 4) and linked against the Lean runtime. Indeed, the history of Lean 4 in 2026 underscores why relying on a single kernel version is insufficient. The original submission was pinned to Lean `v4.33.1` (released August 21, 2026), which already included critical soundness fixes from `v4.32.2` and `v4.33.0` (such as wrong-structure projections `#14576`, `is_def_eq` caching `#14806`, `is_prop` `#14807`, and non-uniform inductive occurrences `#14582`). Yet Lean `v4.34.1` later patched runtime bugs (`#15241` and `#15289`) that could theoretically be exploited on deliberately crafted inputs in the official C++ kernel—while leaving kernels not built on the Lean runtime completely unaffected. For this reason, the verification community treated a passing `lake build` on `v4.33.1` as only *preliminary* evidence, and required full replay through Lean `v4.36.0+` and completely independent proof checkers.

  === The Three-Step Sandboxed Verification Workflow

  Compiling untrusted Lean source code executes arbitrary Lean metaprograms during elaboration. A malicious submission could theoretically overwrite compiled `.olean` files in the workspace, tamper with cached Mathlib artifacts, or exfiltrate data if compiled on a networked host. To neutralize these threats, `leanprover-community/riemann-hypothesis` uses a strict three-step sandboxed verification protocol built on `lean4export` and `lake comparator`.

  ```bash
  export LEAN_ABORT_ON_PANIC=1        # match Comparator's fail-fast policy
  export LAKE_ARTIFACT_CACHE=false    # never trust prebuilt submission caches

  # Step 1: Clean-room Challenge export (submission NEVER compiled here)
  MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 \
    lake exe mathlib/cache get
  lake build Challenge
  lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

  # Step 2: Sandboxed Solution build & export (network-isolated container/VM)
  lake build Main
  lake env leanexport Main -- $(cat export-targets.txt) > solution.export

  # Step 3: Isolated Judgment (empty directory, bubblewrap sandbox, no network)
  lake comparator --config comparator.json \
    --challenge-from-export challenge.export \
    --solution-from-export solution.export
  ```

  Let us trace the security and mathematical guarantees of each step:

  - *Step 1 (Clean-Room Challenge Export)*: In a fresh clone where the submission has never been compiled, the verifier fetches *only* Mathlib's official build cache (`cache.mathlib.org/mathlib4`), never the project's own cache (`lake exe cache get`). It builds `Challenge` and invokes `leanexport` to serialize the exact kernel environment required for the targets in `export-targets.txt` into a plain-text NDJSON/export stream `challenge.export` (roughly $356$ MB). Because no submission code ever ran in this directory, `challenge.export` is an incorruptible ground-truth specification.
  - *Step 2 (Sandboxed Solution Build and Export)*: In a completely separate, network-disabled rootless container (for example, `podman run --network none --read-only --cap-drop all --security-opt no-new-privileges`, with the Lean toolchain mounted read-only), the verifier compiles `Main` from scratch. On a 48-core server with $503$ GB of RAM, a full build of the original $175,187$-module tree takes $7$ to $10$ hours. (An unexpected engineering bottleneck encountered at this scale is that Lake emits a `.setup.json` file listing the full transitive import closure of every module; averaging $6$ MB each across $175,187$ modules, these transient metadata files would consume over a *terabyte* of disk unless pruned periodically once each module's `.trace` file is written.) Once built, `leanexport` runs inside a second read-only sandbox to serialize the transitive closure of `Main` into `solution.export`—a single $61.57$-gigabyte file ($61,570,595,788$ bytes, taking $tilde.op 80$ minutes and $163$ GB peak RAM to generate). Only this static text file crosses the sandbox boundary; the judge treats it as completely untrusted data.
  - *Step 3 (Independent Judgment via `lake comparator`)*: From an empty directory containing only `comparator.json`, `challenge.export`, and `solution.export`, `lake comparator` launches its checkers inside a Linux `bubblewrap` sandbox with zero network access. It performs three decisive checks:
    1. *Declaration & type identity*: Every theorem listed in `comparator.json` exists in `solution.export` with a kernel type *identical* to its type in `challenge.export`, and every transitive constant appearing in those types (every Mathlib definition of `riemannZeta`, `Complex`, `DirichletCharacter.LFunction`, etc.) matches byte-for-byte.
    2. *Axiom audit*: The transitive axiom footprint of every target theorem in `solution.export` is a subset of `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`). Any `sorryAx` or extra axiom causes immediate rejection before any kernel even runs.
    3. *Multi-kernel replay*: The entire $61.57$-gigabyte proof stream is re-typechecked from the ground up by Lean's own kernel and every external kernel configured in `comparator.json`.

  #remark(title: "Why Export Checksums Are Deterministic Even When .olean Files Are Not")[
    Independent verifiers reproducing the build on different machines (Andrew Sutherland at MIT, `ishaan2006`, and `patunz`) initially observed a puzzling phenomenon: out of $175,187$ compiled `.olean` files, $98,219$ differed in their SHA-256 hashes between builds located in different filesystem directories! Investigation (`verification/NOTES.md`, Issue #6) traced this to `Lean.Linter.recordLints`: whenever a module emits a linter message, Lean records the absolute source file path inside the `.olean`'s `lintLogExt` environment extension. Crucially, `lean4export` serializes *only kernel declarations*, never environment extensions or linter logs. Consequently, when `ishaan2006` and Sutherland exported their independently built trees from different directories, both produced *byte-for-byte identical* $61,570,595,788$-byte `solution.export` files with matching SHA-256 hash `5ea74b912147c5c9...`, confirming complete reproducibility of the proof object.
  ]

  === Independent External Checkers: `leanchecker-paranoid`, `nanoda`, `con-leche`, `con-ron`, and `lean4lean`

  The ultimate defense against a latent bug in any single proof-checker implementation is *software diversity*: checking the same exported proof terms with multiple kernels written by different authors, in different programming languages, using different internal architectures. The repository's verification ecosystem involves five distinct checkers beyond Lean's standard C++ kernel:

  1. *`leanchecker-paranoid` ("Lean paranoid")*: A hardened build of Lean's kernel that disables aggressive caching shortcuts and performs exhaustive, paranoid re-verification of every declaration from the export stream. In `comparator.json`, it is invoked as `leanchecker-paranoid --silent --from-export`.
  2. *`nanoda` (`nanoda_bin`)*: A completely independent external typechecker for Lean 4 written from scratch in Rust. Because `nanoda` shares zero code with Lean's C++ kernel and does not link against the Lean runtime, it is immune to C++ memory-safety bugs, reference-count overflows, or Lean runtime vulnerabilities (such as `#15241` and `#15289`). On the $371$ MB Mathlib-sized smoke test ($54,461$ declarations), `nanoda` verified the entire export in $14$ seconds using $0.41$ GB of RAM—roughly five times faster and half the memory of Lean's own kernel ($70$ s, $0.75$ GB).
  3. *`con-leche` and `con-ron`*: Two further independent external checkers for Lean 4 exports (with `con-leche` written in Lean/Rust ecosystems and `con-ron` in Rust), bundled with `lake comparator --paranoid`. Their encounter with the Alpöge–Claude proof provided one of the most illuminating real-world episodes in formal-verification engineering. When run on the full $61.57$ GB export, the stock versions of `con-leche` and `con-ron` bundled with Lean `v4.36.0` exited with status code `2`—not because of any logical flaw in the proof, but because both checkers intentionally declined to model *mutual inductive blocks containing a reflexive member*. Deep inside `Development/ResolutionOfSingularities`, the formalization defines `FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate` mutually with `OrderCertificate`, where a constructor carries a functional argument `hcert : ∀ z hz, PrincipalizationCertificate ...` (a higher-order recursive occurrence of the type being defined). Lean's CIC kernel, `leanchecker-paranoid`, and `nanoda` all support mutual reflexive inductives cleanly. Subsequently, an updated `compare` branch of `con-leche` (`con-leche --compare`) verified the entire `formal-conjectures` solution export—accepting $1,468,413$ declarations and confirming both `RiemannHypothesis.riemannHypothesis` and `GRH.generalized_riemann_hypothesis` in just $182$ seconds on $94$ cores!
  4. *`lean4lean`*: A re-implementation of the Lean 4 kernel *written inside Lean 4 itself* (by Mario Carneiro), designed to serve as a formally verifiable reference specification of Lean's type theory. Unlike the export-based checkers, `lean4lean --fresh Main` replays compiled `.olean` files directly. Because Lean `v4.36` redefined `Decidable` in the core library, checking a `v4.33.1` build requires a `v4.33.1`-compiled `lean4lean`.

  #figure(
    table(
      columns: (auto, auto, 1fr, auto),
      inset: (x: 6pt, y: 5pt),
      align: (left, left, left, left),
      stroke: (x, y) => (
        top: if y == 0 { 1.1pt + gtm-navy } else if y == 1 { 0.6pt + gtm-navy } else { 0.25pt + luma(210) },
        bottom: if y == 6 { 1.1pt + gtm-navy } else { none },
      ),
      fill: (_, y) => if y == 0 { gtm-tint } else { none },
      [*Checker*], [*Language*], [*Architecture & Role*], [*Input Format*],
      [Lean 4 Kernel], [C++], [Reference CIC kernel embedded in `lean` (`v4.36+`)], [`.olean` / export],
      [`leanchecker-paranoid`], [C++], [Hardened Lean kernel with strict re-checking], [`.export` stream],
      [`nanoda`], [Rust], [Independent clean-room Lean 4 kernel; immune to Lean runtime bugs], [`.export` stream],
      [`con-leche`], [Rust], [High-throughput parallel independent checker (`--compare` verified $1.47$M decls in $182$ s on $94$ cores)], [`.export` stream],
      [`con-ron`], [Rust], [Independent checker; strict inductive-model validation], [`.export` stream],
      [`lean4lean`], [Lean 4], [Formal-specification kernel written in Lean 4 itself], [`.olean` files],
    ),
    caption: [Independent proof checkers employed in the verification ecosystem of `leanprover-community/riemann-hypothesis`.],
  )

  === Auditing the Trusted Computing Base (TCB)

  No formal verification eliminates trust entirely; rather, it *compresses* trust from $20,788,900$ lines of complex number theory into a minuscule *Trusted Computing Base* (TCB). After a successful sandboxed Comparator run across Lean's kernel, `leanchecker-paranoid`, `nanoda`, and `con-leche`, what exactly must a skeptic still trust?
  1. *Logical soundness of CIC + three classical axioms*: That Lean's type theory together with `propext`, `Quot.sound`, and `Classical.choice` is consistent (examined in Section 17.4).
  2. *Faithfulness of Mathlib's definitions*: That Mathlib's `riemannZeta` and `DirichletCharacter.LFunction` agree with the classical analytic continuations of $sum n^(-s)$ and $sum chi(n) n^(-s)$ (audited by hundreds of mathematicians over years, and cross-checked against `formal-conjectures`).
  3. *Agreement of independent kernels*: For a false theorem to slip past Lean's C++ kernel, `leanchecker-paranoid`, `nanoda`, and `con-leche` simultaneously, *all* of them would have to share a matching soundness bug triggered by the same proof term—an event of vanishingly small probability.
  4. *Integrity of `lean4export` and the host hardware/OS*: That the exporter faithfully serialized the declarations and that the CPU/OS executed the checkers without hardware faults or sandbox escapes.

  == Axiom Audit and Classical Foundations

  The file `export-targets.txt` sits at the root of `leanprover-community/riemann-hypothesis` and consists of just four lines. Yet those four lines define the entire logical boundary of the proof:

  ```text
  Quot Quot.mk Quot.lift Quot.ind
  riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
  propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam
  ```

  Each line serves a precise structural purpose in `lean4export`:
  - *Line 1* exports Lean's four built-in quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`), which are kernel primitives rather than user-defined inductives.
  - *Line 2* lists the five target theorems whose full proof trees must be exported and verified.
  - *Line 3* lists the three and only three permitted axioms: `propext`, `Quot.sound`, and `Classical.choice`.
  - *Line 4* lists kernel-recognized primitive operations (such as `Nat.add`, `Nat.gcd`, `String.ofList`, and elaboration markers `outParam`, `optParam`) that external checkers need in their environment to handle Lean's literal representations and kernel-level natural-number arithmetic.

  === The Three Standard Axioms of Lean 4 and Mathlib

  Every theorem in `Main.lean`—and both theorems in `FormalConjecturesSolution.lean`—depends *strictly* on the standard classical axiom triad of Lean 4:

  1. *Propositional Extensionality (`propext`)*:
     ```lean
     axiom propext {a b : Prop} : (a ↔ b) → a = b
     ```
     Logically equivalent propositions are equal as terms of type `Prop`. Combined with Lean's built-in definitional proof irrelevance, this makes `Prop` behave like a classical two-element truth-value object (once excluded middle is added).

  2. *Quotient Soundness (`Quot.sound`)*:
     ```lean
     axiom Quot.sound {α : Sort u} {r : α → α → Prop} {a b : α} :
       r a b → Quot.mk r a = Quot.mk r b
     ```
     Related elements become equal in the quotient type `Quot r`. Remarkably, `Quot.sound` is strong enough to *prove* function extensionality (`funext`: if $forall x, f(x) = g(x)$, then $f = g$) as a theorem inside Lean 4 without assuming `funext` as a separate axiom!

  3. *Axiom of Choice (`Classical.choice`)*:
     ```lean
     axiom Classical.choice {α : Sort u} : Nonempty α → α
     ```
     Given a propositional witness `Nonempty α` that a type $alpha$ is inhabited (which lives in `Prop` and therefore cannot be pattern-matched to extract a data term in `Type u`), `Classical.choice` non-constructively produces an element of $alpha$.

  A celebrated theorem of Radu Diaconescu (1975) shows that in the presence of propositional extensionality and quotients (hence function extensionality), the Axiom of Choice *implies* the Law of Excluded Middle (`Classical.em`). Because this derivation is a classic gem of mathematical logic that directly explains why Lean does not need `Classical.em` as a fourth axiom, we record it here in full.

  #theorem(title: "Diaconescu's Theorem in Lean 4")[
    From `propext`, `Quot.sound` (via `funext`), and `Classical.choice`, the Law of Excluded Middle holds: for every proposition $P : op("Prop")$, $P or not P$.
  ]

  #proof[
    Fix $P : op("Prop")$, and define two predicates $U, V : op("Bool") -> op("Prop")$ by
    $ U(b) := (b = op("true")) or P, quad V(b) := (b = op("false")) or P. $
    Both subtypes ${b : op("Bool") mid(|) U(b)}$ and ${b : op("Bool") mid(|) V(b)}$ are inhabited (witnessed by `true` and `false`, respectively). Applying `Classical.choice` yields two elements $u, v : op("Bool")$ satisfying $U(u)$ and $V(v)$. Since equality on `Bool` is decidable, either $u = v$ or $u != v$:
    - *Case 1: $u = v$*. Because $U(u)$ holds, either $u = op("true")$ or $P$ holds; because $V(v)$ holds, either $v = op("false")$ or $P$ holds. If $P$ fails, then $u = op("true")$ and $v = op("false")$, contradicting $u = v$. Thus $P$ must hold.
    - *Case 2: $u != v$*. We claim $not P$. Suppose for contradiction that $P$ holds. Then for every $b : op("Bool")$, both $U(b)$ and $V(b)$ are true, so $U(b) <-> V(b)$. By `propext` and `funext`, we obtain the equality of predicates $U = V$. Because $u$ and $v$ were obtained by applying the *same* function `Classical.choice` to the *same* proof-irrelevant `Nonempty` witness on equal subtypes, it follows that $u = v$, contradicting $u != v$. Hence $not P$.
    In either case, $P or not P$ holds.
  ]

  === Strictly Forbidden Axioms and Soundness Traps

  Equally important as what is *present* in `export-targets.txt` is what is *absent*:

  - *Zero `sorryAx`*: The escape-hatch axiom `sorryAx : ∀ (α : Sort u) (synthetic : Bool), α` is completely absent. Every single one of the $tilde.op 800,000$ lemmas in the transitive closure of `Main` has a complete, kernel-checked proof term.
  - *Zero `Lean.ofReduceBool` and `Lean.trustCompiler`*: In Lean 4, the tactic `native_decide` proves decidable propositions by compiling them to native C/machine code via the Lean compiler, running the binary, and asserting the result via the axiom `Lean.ofReduceBool`. While convenient for finite computations, `Lean.ofReduceBool` expands the TCB by hundreds of thousands of lines—including Lean's entire code generator, IR optimizer, C compiler, and runtime! Crucially, `comparator.json` *forbids* `Lean.ofReduceBool` and `Lean.trustCompiler`. Any finite arithmetic or interval check in the Alpöge–Claude proof is verified purely by kernel reduction or algebraic proof terms, never by trusting the native compiler.
  - *Zero custom `axiom`, `unsafe`, or `@[implemented_by]` overrides*: No mathematical conjecture (not Deligne's Weil bounds, not Hironaka's resolution of singularities, not the Arthur–Selberg trace formula, not any numerical zero-verification table) is assumed as an axiom. Everything rests solely on the three standard axioms of classical mathematics.

  === Consistency Strength and $Pi_1^0$ Conservativity of RH

  A graduate student trained in logic might ask: *how strong is Lean's foundational system compared to ZFC?* By work of Benjamin Werner and Mario Carneiro, Lean's type theory with $omega$ universes plus `propext`, `Quot.sound`, and `Classical.choice` is equiconsistent with ZFC augmented by countably many inaccessible cardinals (specifically, `Type u` models a Grothendieck universe $V_(kappa_u)$). Does this mean the Alpöge–Claude proof of the Riemann Hypothesis secretly depends on large cardinals?

  Almost certainly not, for two distinct reasons. First, in practice, the proof uses only low universe levels (`Type 0`, `Type 1`, `Type 2`) to manipulate standard algebraic and analytic structures—never the existence of inaccessible cardinals. Second, and even more fundamentally, the Riemann Hypothesis is an *arithmetical $Pi_1^0$ sentence*! By classical results of Kreisel, Matiyasevich–Davis–Robinson–Putnam, and Lagarias's elementary reformulation
  $ sigma(n) <= H_n + e^(H_n) log(H_n) quad (forall n >= 1), $
  where $sigma(n) = sum_(d mid(|) n) d$ and $H_n = sum_(k=1)^n 1/k$, RH is equivalent to a universal statement $forall n in bb(N), Phi(n)$ with a primitive-recursive predicate $Phi(n)$. (Equivalently, if RH were false, a zero $rho$ with $op("Re")(rho) > 1/2$ could be enclosed in a rational rectangle on which the argument principle $(2 pi i)^(-1) integral.cont (zeta'/zeta)(s) dif s >= 1$ is certified by finite rigorous interval arithmetic—a finite, mechanically checkable refutation.) Therefore, any consistent formal system that proves RH *cannot* be proving a falsehood: if RH were false, a concrete finite counterexample would make even Peano Arithmetic prove $not op("RH")$, rendering Lean's type theory (and ZFC + inaccessibles) inconsistent! Thus, as long as ZFC with Grothendieck universes is merely *consistent*—a foundational assumption shared by essentially all modern algebraic geometry—a kernel-verified Lean 4 proof of `RiemannHypothesis` establishes the truth of the Riemann Hypothesis in the standard model $bb(N)$ and $bb(C)$.

  == Human–AI Collaboration in Formal Mathematics

  We close this chapter—and the technical body of the monograph—by stepping back from `lakefile.toml` and `nanoda` to reflect on the broader mathematical significance of how this proof came into being. The Alpöge–Claude–Riemann Theorem is not merely the resolution of a 167-year-old problem; it is a watershed in the sociology and epistemology of mathematics, demonstrating a genuinely new mode of human–AI collaboration.

  === Division of Intellectual Labor

  In reading the conceptual architecture developed across Chapters 4 through 16 alongside the $20.8$-million-line Lean 4 repository, a clear and striking division of intellectual labor emerges between Levent Alpöge and Claude:

  - *Human conceptual steering and geometric intuition*: Alpöge supplied the overarching mathematical vision, taste, and strategic judgment. This included identifying the right *toy models* (the Stepanov auxiliary-polynomial perspective from Chapter 4, the $op("GL")_2$ and function-field prototypes, and the realization that higher-rank chained theta lifts could force incompatible Harder–Narasimhan slope and multiplicity bounds on a hypothetical off-line zero), diagnosing when a proposed analytic estimate had the wrong scaling law, proposing architectural pivots when an obstruction appeared, and insisting on formalizing every step in Lean 4 so that no subtle gap could hide behind hand-waving.
  - *Machine synthesis, cross-field stamina, and formalization at scale*: Claude contributed an extraordinary breadth of technical execution across disparate domains—combining higher-rank automorphic representations, Harish-Chandra modules, Arakelov geometry, $p$-adic Hodge theory, étale cohomology, and functorial resolution of singularities—together with the superhuman clerical endurance required to translate hundreds of thousands of intermediate estimates into $818,755$ machine-checked theorems with zero `sorry`s. Where a human mathematician might spend a decade building just one of the ten libraries in Table 17.1 (such as `GroundTheory` or `Development/ResolutionOfSingularities`) before ever testing whether the final contradiction closes, the human–AI partnership could iterate on global proof architectures while keeping the entire edifice formally sound.

  === Machine-Checked Validity vs. Human Mathematical Understanding

  The completion of a $20.8$-million-line verified proof sharpens an ancient philosophical distinction in mathematics: the difference between *validity* and *understanding*.

  A multi-kernel verification by Lean's kernel, `leanchecker-paranoid`, `nanoda`, and `con-leche` settles *validity* to a degree of certainty that human refereeing has never approached. No human referee—not even a committee of fifty world experts reading for ten years—could verify $818,755$ lemmas across ten subfields without overlooking a sign error, a missing hypothesis, or a subtle edge case at a ramified prime. In this narrow but vital sense, formal verification solves the *crisis of complexity* in modern mathematics.

  Yet *validity is not understanding*. A $61.57$-gigabyte `solution.export` file tells us *that* every nontrivial zero of $zeta(s)$ and $L(chi, s)$ lies on $op("Re")(s) = 1/2$, with absolute logical certainty; it does not, by itself, transmit the *why* into a human mind, nor does it immediately tell us how to generalize the method to Dedekind zeta functions of number fields, automorphic $L$-functions on $op("GL")_n$, or the Birch and Swinnerton-Dyer conjecture.

  Human mathematical understanding requires *conceptual compression*: distilling $149,217$ files into a surveyable sequence of ideas, identifying which hypotheses are genuinely load-bearing and which were merely artifacts of an automated proof search, isolating reusable theorems (such as the sharper Harder–Narasimhan slope inequalities or the chained theta-lift nonvanishing criteria), and naming the underlying geometric phenomena cleanly. That is precisely the dual purpose of the post-release community effort in `leanprover-community/riemann-hypothesis`—which aims to refactor the machine-generated tree to Mathlib levels of readability and modularity—and of expository monographs such as the present volume.

  In 1900, David Hilbert declared in his Paris address that in mathematics there is no *ignorabimus*—no problem forever beyond our reach. More than a century later, the Alpöge–Claude proof of the Riemann Hypothesis suggests a corollary that neither Riemann nor Hilbert could have foreseen: that the deepest peaks of mathematics may be climbed not by human intuition alone, nor by brute computational force alone, but by the synthesis of human conceptual imagination, artificial reasoning at scale, and the uncompromising clarity of a small, independently verified logical kernel.

  #exercises((
    [Explain why setting `autoImplicit = false` and `relaxedAutoImplicit = false` in `lakefile.toml` is critical for statement integrity in a large Lean 4 formalization. Construct a short, concrete Lean 4 theorem statement that is *false* as intended, yet becomes *vacuously provable* if `autoImplicit = true` silently binds a misspelled identifier.],
    [In `src/Challenge.lean`, the theorem `LFunction_eq_zero_re` quantifies over *every* modulus $N >= 1$ and *every* Dirichlet character $chi mod N$, including imprimitive characters, for $0 < op("Re")(s) < 1$. Explain mathematically why the hypothesis $0 < op("Re")(s)$ is essential for imprimitive characters: where do the extra zeros of an imprimitive Dirichlet $L$-function $L(chi, s)$ lie relative to the primitive character $chi^*$ inducing $chi$?],
    [Compare `PrimitiveDirichletLZerosOnLine` (in `src/Challenge.lean`) with `GRH.generalized_riemann_hypothesis` (in `comparator/FormalConjecturesChallenge.lean`). Using the completed $L$-function functional equation from Chapter 2, verify every case of the set `GRH.trivialZeros χ` (namely $q = 1$, odd $chi$, and even $chi$ with $q > 1$), and explain why $s = 0$ is a trivial zero when $chi$ is even and $q > 1$, but *not* when $q = 1$.],
    [In Section 17.4, we noted that `funext` (function extensionality) is not listed in `export-targets.txt` as an axiom, even though `propext`, `Quot.sound`, and `Classical.choice` are. Prove `funext` directly from `Quot.sound` and `Quot.lift` (hint: define a relation $r$ on functions $alpha -> beta$ by $r(f, g) := forall x, f(x) = g(x)$, form the quotient `Quot r`, and lift the evaluation map $f |-> f(x)$).],
    [Suppose a submitted Lean 4 proof of a theorem $T$ compiles cleanly, passes `#print axioms T`, and reports `[propext, Quot.sound, Classical.choice, Lean.ofReduceBool]`. Explain why `lake comparator` rejects this submission, what `Lean.ofReduceBool` represents, and how a bug in the Lean compiler (even with a 100% bug-free kernel) could allow a proof of `False` using `Lean.ofReduceBool`.],
    [In the three-step verification protocol of Section 17.3, why does the README explicitly warn *against* running `lake exe cache get` before `lake build Challenge`, instructing the verifier to use `MATHLIB_CACHE_GET_URL=... lake exe mathlib/cache get` instead? Describe a concrete attack scenario if the verifier built `Challenge` in the same directory after fetching an untrusted project cache.],
    [Explain the role of *strict positivity* for inductive types in the Calculus of Inductive Constructions, and explain what makes `FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate` (mutually declared with `OrderCertificate`) a *mutual reflexive inductive* type. Why is a mutual reflexive inductive still strictly positive and logically sound, even though `con-leche` and `con-ron` initially declined to accept it?],
  ))
]
