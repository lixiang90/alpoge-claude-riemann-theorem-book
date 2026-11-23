// ============================================================================
// Chapter 11: Global Architecture of the Alpöge–Claude Proof
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch11() = [
  #chapter(
    "Global Architecture of the Alpöge–Claude Proof",
    short-title: "Global Architecture of the Proof",
    epigraph: "The proof of a great theorem is rarely a single stroke of lightning; it is an engineered bridge whose piers rest in distant valleys, joined at the center by a keystone that makes the whole structure rigid.",
    epigraph-source: "From the editorial notes on the formalization",
    overview: [
      Part III opens with a complete architectural blueprint of the Alpöge–Claude proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet $L$-functions. Before entering the technical depths of Chapters 12–16, we map the entire logical edifice from the five headline theorems in `Main.lean` down to the five interlocking mathematical pillars that drive the contradiction. We trace the exact top-down dependency DAG—from `MainConclusion.everyCharacter` through `every_character_of_literature_of_vWin`, `every_character_of_theta_integrals_local_matching`, and `every_character_of_green_v_win` to the central junction `zeroFreeAll_of_topG` at scale exponent $lambda = 3/2$. We then explain how the analytic reduction, the chain of $m approx sqrt(X)$ theta lifts, local divisibility at inert primes, Arakelov slope inequalities (`DivIneqObjU`, `HeightS`, `CovolumeBoundOfX`), and the weakened Vandiver window (`VWin`) lock together, verify the master parameter hierarchy from `DivIneqTopAnchorU.lean` and `ExistsPageN.lean`, and provide a chapter-by-chapter reading guide and Lean 4 cross-reference across the ten libraries of the verified formalization.
    ],
    label-name: "ch-proof-blueprint",
  )

  Having assembled the classical analytic foundations in Part I and the six modern mathematical toolkits in Part II, we are now ready to survey the Alpöge–Claude proof as a single, unified machine. A formalization spanning nearly 150,000 Lean 4 files and more than twenty million lines of code can easily appear impenetrable if approached from the bottom up. Viewed from the top down, however, the proof possesses a remarkably clean, modular architecture. Every component exists to serve a single overarching strategy: a vast arithmetic generalization of Stepanov's polynomial method (Chapter 4), in which the auxiliary polynomial vanishing to high order at rational points is replaced by a *chain of iterated theta lifts* on totally definite unitary groups, and Bézout's degree bound is replaced by *Bost's Arakelov slope inequality* on Hermitian lattices.

  This chapter serves as the master map for Part III. In Section 11.1 we examine the five headline theorems exported by `Main.lean` and prove completely how all five follow from a single half-plane nonvanishing statement. Section 11.2 traces the exact top-down logical spine of the Lean 4 proof and displays its complete dependency DAG. Section 11.3 explains the five mathematical pillars and the precise interfaces by which they interlock. Section 11.4 dissects the master parameter hierarchy—the exact scaling laws governing $x$, $epsilon$, $L$, $b$, $a$, $m$, $2^e$, $q$, and $d$—and demonstrates why every inequality closes with room to spare. Finally, Section 11.5 provides a reading guide to Chapters 12–16 together with a comprehensive Lean 4 library map.

  == The Five Headline Theorems (`Main.lean` and `Statements.lean`)

  At the apex of the entire formalization sit two remarkably concise files: `src/Statements.lean` (20 lines) and `src/Main.lean` (56 lines). Together, they establish the exact interface between the twenty-million-line proof and the standard definitions of the Riemann zeta function `riemannZeta` and Dirichlet $L$-functions `DirichletCharacter.LFunction` in Mathlib.

  In `Statements.lean`, four propositions are defined purely in terms of Mathlib's analytic continuation of $zeta(s)$ and $L(s, chi)$, without referencing a single internal concept of the proof:

  #definition(title: "The Four Statements in Statements.lean")[
    Let $zeta(s)$ denote the Riemann zeta function and, for each integer $N >= 1$ and Dirichlet character $chi : (bb(Z) \/ N bb(Z))^times -> bb(C)^times$, let $L(s, chi)$ denote its meromorphically continued Dirichlet $L$-function. The four target propositions are:
    1. (`RiemannZetaZerosOnLine`) For every $s in bb(C)$, if $zeta(s) = 0$, $s != -2(n + 1)$ for all $n in bb(N)$, and $s != 1$, then $op("Re")(s) = 1/2$.
    2. (`DirichletLNonvanishingRightOfHalf`) For every $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $op("Re")(s) > 1/2$, if $chi != 1$ or $s != 1$, then $L(s, chi) != 0$.
    3. (`DirichletLZerosOnLine`) For every $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $0 < op("Re")(s) < 1$, if $L(s, chi) = 0$, then $op("Re")(s) = 1/2$.
    4. (`PrimitiveDirichletLZerosOnLine`) For every $N >= 1$, every *primitive* Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $0 < op("Re")(s) < 1$, if $L(s, chi) = 0$, then $op("Re")(s) = 1/2$.
  ]

  Note that `RiemannZetaZerosOnLine` is definitionally identical to Mathlib's longstanding predicate `RiemannHypothesis`. The file `Main.lean` proves five headline theorems—corresponding to these four propositions plus `RiemannHypothesis` explicitly—by feeding a single master theorem, `UpperTheory.FinalTheorems.everyCharacter`, into an elementary complex-analytic reduction module `ClaimStrip.lean`.

  #theorem(title: "The Five Headline Theorems of Main.lean")[
    The following five statements hold unconditionally:
    1. *Half-plane nonvanishing (`LFunction_ne_zero_of_half_lt_re`):* For every modulus $N >= 1$, every Dirichlet character $chi mod N$, and every $s in bb(C)$ with $op("Re")(s) > 1/2$ and $(chi, s) != (1, 1)$, we have $L(s, chi) != 0$.
    2. *Riemann Hypothesis (`riemannHypothesis`):* Every nontrivial zero of $zeta(s)$ satisfies $op("Re")(s) = 1/2$.
    3. *Riemann zeta zeros on the critical line (`riemannZeta_eq_zero_re`):* `RiemannZetaZerosOnLine` holds.
    4. *Generalized Riemann Hypothesis (`LFunction_eq_zero_re`):* For every modulus $N >= 1$ and every Dirichlet character $chi mod N$, every zero of $L(s, chi)$ in the critical strip $0 < op("Re")(s) < 1$ satisfies $op("Re")(s) = 1/2$.
    5. *Primitive GRH (`LFunction_eq_zero_re_of_isPrimitive`):* For every modulus $N >= 1$ and every primitive Dirichlet character $chi mod N$, every zero of $L(s, chi)$ in $0 < op("Re")(s) < 1$ satisfies $op("Re")(s) = 1/2$.
  ]

  The logical dependency among these five theorems is completely transparent and is worth proving in full right here, because it clarifies exactly what the deep machinery of Chapters 12–16 actually needs to establish. Everything flows from item (1), which in `Main.lean` is a one-line alias for `UpperTheory.FinalTheorems.everyCharacter`.

  #proposition(title: "Reduction from Half-Plane Nonvanishing to Critical-Line Zeros")[
    Assume `DirichletLNonvanishingRightOfHalf`: for every $N >= 1$, every character $chi mod N$, and every $s in bb(C)$ with $op("Re")(s) > 1/2$ and $(chi, s) != (1, 1)$, we have $L(s, chi) != 0$. Then `DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine`, `RiemannZetaZerosOnLine`, and `RiemannHypothesis` all follow.
  ]

  #proof[
    We reproduce the exact three-step argument of `ClaimStrip.lean`.

    *Step 1: Reduction of zeros in the critical strip to primitive characters (`Claim.prim_zero`).* Let $chi$ be a Dirichlet character modulo $N$, let $chi^*$ be the unique primitive character inducing $chi$ (of conductor $f = op("cond")(chi) | N$), and suppose $L(s, chi) = 0$ with $0 < op("Re")(s) < 1$. In particular $s != 1$, so the level-change Euler product identity holds at $s$:
    $ L(s, chi) = L(s, chi^*) product_(p | N) (1 - chi^*(p) p^(-s)). $
    For every prime $p | N$, we have $|chi^*(p)| <= 1$ and $|p^(-s)| = p^(-op("Re")(s)) < 1$ since $op("Re")(s) > 0$. Hence every Euler factor $1 - chi^*(p) p^(-s)$ is strictly nonzero. Because the product vanishes and none of the finite Euler factors vanish, we must have $L(s, chi^*) = 0$.

    *Step 2: Functional-equation reflection (`Claim.gamma_ne_zero` and `Claim.prim_reflect`).* Let $psi$ be a primitive character modulo $M$ and suppose $L(s, psi) = 0$ with $0 < op("Re")(s) < 1$. Write $Lambda(s, psi)$ for the completed $L$-function and $gamma_psi (s)$ for its archimedean gamma factor, equal to $Gamma_bb(R) (s) = pi^(-s/2) Gamma(s/2)$ if $psi$ is even and $Gamma_bb(R) (s + 1) = pi^(-(s+1)/2) Gamma((s+1)/2)$ if $psi$ is odd. Since $Gamma(z)$ has no zeros in $bb(C)$ and no poles in $op("Re")(z) > 0$, we have $gamma_psi (s) != 0$ for all $op("Re")(s) > 0$. From $L(s, psi) = Lambda(s, psi) / gamma_psi (s)$ (valid for $s != 0$) and $L(s, psi) = 0$, we deduce $Lambda(s, psi) = 0$.

    Now invoke the functional equation for the primitive character $psi$ (Chapter 2):
    $ Lambda(1 - s, psi^(-1)) = epsilon(psi^(-1)) M^(s - 1/2) Lambda(s, psi), $
    where $epsilon(psi^(-1))$ is the root number. Since $Lambda(s, psi) = 0$, it follows that $Lambda(1 - s, psi^(-1)) = 0$. Because $op("Re")(1 - s) = 1 - op("Re")(s) > 0$, we have $1 - s != 0$, so dividing by $gamma_(psi^(-1)) (1 - s)$ yields $L(1 - s, psi^(-1)) = 0$.

    *Step 3: Trichotomy on the critical strip (`Claim.strip`) and extension to $zeta(s)$ (`Claim.zeta`).* Suppose $L(s, chi) = 0$ with $0 < op("Re")(s) < 1$. Compare $op("Re")(s)$ with $1/2$:
    - If $op("Re")(s) > 1/2$, we immediately contradict `DirichletLNonvanishingRightOfHalf` (as $s != 1$).
    - If $op("Re")(s) < 1/2$, then Step 1 gives $L(s, chi^*) = 0$ and Step 2 gives $L(1 - s, (chi^*)^(-1)) = 0$ with $op("Re")(1 - s) = 1 - op("Re")(s) > 1/2$ and $1 - s != 1$ (since $s != 0$). This again contradicts `DirichletLNonvanishingRightOfHalf`.
    - Therefore $op("Re")(s) = 1/2$, proving `DirichletLZerosOnLine`, and `PrimitiveDirichletLZerosOnLine` is an immediate specialization.

    Finally, suppose $zeta(s) = 0$ with $s != 1$ and $s != -2(n + 1)$ for all $n in bb(N)$. We have $s != 0$ because $zeta(0) = -1/2 != 0$. We split into three regions according to $op("Re")(s)$:
    - If $0 < op("Re")(s) < 1$, then since $L(s, chi_0) = zeta(s)$ for the trivial character $chi_0$ modulo $1$, `DirichletLZerosOnLine` gives $op("Re")(s) = 1/2$.
    - If $op("Re")(s) >= 1$, then $zeta(s) != 0$ by Hadamard–de la Vallée Poussin nonvanishing (`riemannZeta_ne_zero_of_one_le_re`), contradiction.
    - If $op("Re")(s) <= 0$, then $Gamma_bb(R) (s) != 0$ (its only poles are at $s = 0, -2, -4, dots.c$, all excluded by hypothesis and $s != 0$; wait: $Gamma_bb(R) (s)$ has no zeros, and in Mathlib `Gammaℝ s = 0` occurs precisely at the nonpositive even integers $s = -2n$, because `Gammaℝ` is defined via `Gamma` which returns $0$ at its poles in Mathlib's total-function convention!). Thus $xi(s) = zeta(s) Gamma_bb(R) (s) = 0$. By the functional equation $xi(1 - s) = xi(s) = 0$, we obtain $zeta(1 - s) = 0$ with $op("Re")(1 - s) >= 1$, contradicting `riemannZeta_ne_zero_of_one_le_re`.

    Hence $op("Re")(s) = 1/2$, proving `RiemannZetaZerosOnLine` and `RiemannHypothesis`.
  ]

  #remark(title: "Why Nonvanishing in Re(s) > 1/2 for All Characters Is the Natural Target")[
    Notice that even if one only wanted the classical Riemann Hypothesis for $zeta(s)$, the Alpöge–Claude method naturally proves the Generalized Riemann Hypothesis for *all* Dirichlet characters $chi$ simultaneously. The reason is structural: the analytic reduction (Section 11.3.1) operates on Dirichlet characters $psi$ twisted through cyclotomic–quadratic fields $E$, and the functional-equation reflection in `Claim.strip` requires nonvanishing of $L(s, chi^(-1))$ whenever $L(s, chi)$ is tested. In fact, `UpperTheory.Top.imprimitive` (in `CharacterBoxes/Imprimitive.lean`) shows that it suffices to prove nonvanishing in $op("Re")(s) > 1/2$ for *primitive* characters (`Formalism.HC.ZeroFreeAll`), from which all imprimitive characters follow by the same Euler-factor argument as in Step 1 above.
  ]

  #lean-note(title: "Lean 4 Formalization: The Verified Entry Point", module: "src/Statements.lean, src/Main.lean, ClaimStrip.lean")[
    In `src/Main.lean`, the five headline theorems are proved in just twelve lines of code:
    - `LFunction_ne_zero_of_half_lt_re := UpperTheory.FinalTheorems.everyCharacter`
    - `riemannHypothesis := Claim.zeta LFunction_ne_zero_of_half_lt_re`
    - `riemannZeta_eq_zero_re := riemannHypothesis`
    - `LFunction_eq_zero_re := Claim.strip LFunction_ne_zero_of_half_lt_re`
    - `LFunction_eq_zero_re_of_isPrimitive` introduces `N`, `χ`, `s` and delegates directly to `LFunction_eq_zero_re`.

    The independent verification harness `Challenge.lean` re-declares these exact five types using *only* Mathlib imports (with `sorry` proofs). The `comparator` tool exports both `Challenge` and `Main` via `leanexport`, checks definitional type equality of all five declarations, confirms that the only axioms used are Lean's three standard axioms (`propext`, `Quot.sound`, `Classical.choice`), and validates the proof terms independently with both the Lean kernel and the third-party checker `nanoda`.
  ]

  == The Top-Down Logical Spine

  We now descend from `UpperTheory.FinalTheorems.everyCharacter` down through the upper layers of the formalization. Remarkably, the entire twenty-million-line proof funnels through a narrow, crystal-clear chain of six landmark theorems before fanning out into the five mathematical pillars. Understanding this spine is the single most effective way to navigate the proof without getting lost in its scale.

  === Tracing the Six-Step Chain

  Let us follow the exact Lean 4 proof terms from top to bottom.

  *Link 1 (`MainConclusion.lean`): Discharging the Galois Local–Global Axiom.*
  The top theorem `UpperTheory.FinalTheorems.everyCharacter` is proved in a single line:
  ```lean
  theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
    UpperTheory.FinalTheorems.everyCharacter_of_row
      UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  ```
  Here `UpperTheory.EveryCharacter` is definitionally `DirichletLNonvanishingRightOfHalf`. The single input `h = UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` is the *strong local–global compatibility theorem for Galois representations attached to regular algebraic, conjugate self-dual, cuspidal automorphic representations of $op("GL")_n$ over CM fields* (the Shin / Caraiani / Clozel–Harris–Taylor–Thorne lineage, formalized from scratch inside `Development` and `CompanionTheory` and packaged as `Row0b IsRecT`).

  *Link 2 (`MainConclusion.lean`): Splitting into the Two Grand Tracks.*
  The theorem `everyCharacter_of_row` splits the proof into two parallel, massive sub-engines:
  ```lean
  theorem UpperTheory.FinalTheorems.everyCharacter_of_row
      (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
      UpperTheory.EveryCharacter :=
    UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
      { caraianiLocalGlobalDual := h
        localLanglandsExists := UpperTheory.Zero.LLC.recTExists
        galoisRepOfPolarizedPairLit := h }
      (UpperTheory.One.vwin_of_row h)
  ```
  Observe the remarkable economy of `OpenLiteratureStatements` in `EveryCharacterOfLiteratureOfVWin.lean`: during the development of the proof, dozens of deep published theorems (Deligne–Ribet, Clozel purity, Casselman–Wallach, Howe duality, Siegel–Weil, arithmetic Hilbert–Samuel, Nadel vanishing, Moriwaki bigness, Poitou–Tate duality, Bhatt–Scholze prismatic cohomology, etc.) were gradually formalized and eliminated as hypotheses until *only three fields* remained in `OpenLiteratureStatements`:
  - `caraianiLocalGlobalDual` (discharged by `h`),
  - `localLanglandsExists` (discharged by `UpperTheory.Zero.LLC.recTExists`, the formalized Local Langlands correspondence for $op("GL")_n$), and
  - `galoisRepOfPolarizedPairLit` (also discharged by `h`).

  Simultaneously, `UpperTheory.One.vwin_of_row h` (in `VwinOfRow.lean`) takes that same Galois local–global theorem `h` together with base change (`UpperTheory.BaseChangeIdentities.baseChangeN`) and invokes `UpperTheory.One.Join.automorphic_window_of_inputs` to produce `UpperTheory.Top.VWin`—the *Weakened Vandiver Window* theorem!

  *Link 3 (`EveryCharacterOfLiteratureOfVWin.lean`): Assembling Theta Matching and the Covolume Bound.*
  Inside `every_character_of_literature_of_vWin`, the proof constructs the complete bundle of formalized literature theorems (over one hundred individual theorems, grouped into `published_results_eigen`, `published_results_first`, and `published_results_arithmetic`) and passes them to:
  ```lean
  UpperTheory.Lit.every_character_of_theta_integrals_local_matching
    published_results_eigen
    published_results_first
    hTheta.1 hTheta.2
    (SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt ...)
    local_langlands_gl_recT_exists_of_literature
    hV
  ```
  Here two major bridges enter:
  1. `hTheta = theta_integrals_agree_and_local_matching_of_literature O`: the matching of global theta integrals and local orbital/zeta integrals between the definite unitary group side and the relative trace formula / $op("GL")_n$ side.
  2. `topCovolSlim2_use_alt_alt ... : GlobalTheory.CovTop.CovolumeBoundOfX`: the Arakelov-geometric covolume lower bound, assembled from resolution of singularities in characteristic zero, Poincaré–Lelong, arithmetic Hilbert–Samuel (`hsUse_outright`), Moriwaki bigness (`moriwakiBig_outright`), Fargues exactness, Zarhin's trick, nef Riemann–Roch, integral toroidal compactifications of Siegel moduli spaces, Kodaira–Spencer isomorphisms, and Grothendieck deformation theory.

  *Link 4 (`TopPlug.lean`): Assembling `HypsAlt` and Passing to Primitive Characters.*
  The theorem `every_character_of_theta_integrals_local_matching` builds an inhabitant of the master hypothesis bundle
  $ op("HypsAlt") (cal(C) |-> op("Closed") cal(C) (op("Fm") |-> op("LinkN") op("Fm"))) space op("DefiniteSideCondition") $
  (defined in `ThirdPlaceSeries/Hyps.lean`), combines it with Green's character-table theorem `hG : GlobalTheory.GLq.Green` for finite general linear groups $op("GL")_n (bb(F)_q)$ and the Vandiver window `hV : UpperTheory.Top.VWin`, and calls `UpperTheory.Top.every_character_of_green_v_win`. This immediately reduces `UpperTheory.EveryCharacter` to `Formalism.HC.ZeroFreeAll` (nonvanishing in $op("Re")(s) > 1/2$ for all *primitive* Dirichlet characters) via `UpperTheory.Top.imprimitive`.

  *Link 5 (`TopPlug.lean`): The Central Junction at $lambda = 3/2$.*
  The single most illuminating equation in the entire formalization is the three-line proof of `zero_free_all_of_green_v_win` in `TopPlug.lean`:
  ```lean
  theorem UpperTheory.Top.zero_free_all_of_green_v_win
      (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm)
                             DefiniteSideCondition)) :
      Formalism.HC.ZeroFreeAll :=
    h.elim fun h =>
      UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
        (forall_goal_of_shape_of_hyps _ _ _ _
          (shape_closed_link_n_of_green hG) trivial trivial h)
        (fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ))
  ```
  Every piece of the proof meets at this junction:
  - The *analytic engine* `zeroFreeAll_of_topG` operates at window exponent $lambda = 3/2 > 1$ (proved by `norm_num`).
  - The *left branch* `forall_goal_of_shape_of_hyps` transforms the automorphic, theta-lift, local-divisibility, and Arakelov-geometry bundle `HypsAlt` (plus Green's character theory `hG`) into the predicate `TopG`: whenever a family requirement `G.req` admits a host field (`HostExW la G.req`) and satisfies the Vandiver hypothesis (`HypV`), the family class `G.cls la` is *chain-connected* (`FamilyClassConnected (G.cls la)`), which forbids the oscillatory divergence forced by an off-line zero.
  - The *right branch* `fun ψ => supplyChi ψ (hV ψ)` converts the weakened Vandiver window `hV ψ : VWinAt ψ 401` into the host-field existence statement `HostExW (3/2) (GChi ψ).req`, by pairing `VWinAt ψ 401` with `admissibleClassesTwistedChar` (which produces admissible twisted character classes at the required scales).

  *Link 6 (`ZeroFreeAllOfTopG.lean`): Closing the Analytic Contradiction.*
  Finally, `zeroFreeAll_of_topG` invokes `zeroFreeOn_of_tiedWin_cyc` (from `Formalism.SharpRestriction`), supplying the geometric-mean level comparison `level_gm_le_on_family_scales` and the Mellin–Landau lower bound `formB`. If any primitive Dirichlet character $psi$ had a zero $rho$ with $op("Re")(rho) > 1/2$, the Mellin–Landau machinery would violate `ChainTied` on the connected family produced by `TopG` over the host field supplied by `supplyChi`. Contradiction!

  === The Complete Proof Dependency DAG

  The diagram below displays the full top-down architecture of the Alpöge–Claude proof, showing how the two grand feeder tracks—the *Automorphic / Theta / Arakelov Track* on the left and the *Galois / Iwasawa / Vandiver Track* on the right—arise from the same foundational Galois local–global theorem and converge at `zeroFreeAll_of_topG (la := 3/2)`.

  #v(0.4em)
  #figure(
    block(
      width: 100%,
      inset: 8pt,
      fill: gtm-tint,
      stroke: 0.6pt + gtm-rule,
      radius: 3pt,
    )[
      #let dag-box(title, sub, fill-col: white, border-col: gtm-navy, w: 100%) = rect(
        width: w,
        fill: fill-col,
        stroke: 0.8pt + border-col,
        radius: 2.5pt,
        inset: (x: 6pt, y: 5pt),
      )[
        #align(center)[
          #text(size: 8.1pt, weight: "bold", fill: gtm-navy)[#title]
          #if sub != none {
            linebreak()
            text(size: 7.2pt, fill: luma(65))[#sub]
          }
        ]
      ]
      #let arrow-up = align(center)[#text(size: 9pt, weight: "bold", fill: gtm-accent)[$arrow.t$]]

      // Level 1: Headline Theorems
      #dag-box(
        [Five Headline Theorems (`Main.lean`)],
        [`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`],
        fill-col: rgb("#EBF1F8"),
        border-col: gtm-navy,
      )
      #v(0.15em)
      #align(center)[#text(size: 7.4pt, fill: gtm-accent)[$arrow.t$ #h(0.3em) `Claim.zeta`, `Claim.strip` (`ClaimStrip.lean`)]]
      #v(0.15em)

      // Level 2: EveryCharacter
      #dag-box(
        [`LFunction_ne_zero_of_half_lt_re` = `MainConclusion.everyCharacter`],
        [`everyCharacter_of_row galoisLocalGlobalStrong_recParameter`],
        fill-col: rgb("#F3F6FA"),
      )
      #v(0.15em)
      #align(center)[#text(size: 7.4pt, fill: gtm-accent)[$arrow.t$ #h(0.3em) `every_character_of_literature_of_vWin` $<-$ `every_character_of_theta_integrals_local_matching`]]
      #v(0.15em)

      // Level 3: TopPlug
      #dag-box(
        [`TopPlug.every_character_of_green_v_win` $->$ `imprimitive` $->$ `zero_free_all_of_green_v_win`],
        [Central Junction: `zeroFreeAll_of_topG (la := 3/2)`],
        fill-col: rgb("#FFF9E6"),
        border-col: rgb("#C49A00"),
      )
      #v(0.2em)

      // Split Arrows
      #grid(
        columns: (1fr, 1fr),
        gutter: 8pt,
        align(center)[#text(size: 7.4pt, fill: gtm-accent)[$arrow.t$ #h(0.2em) `TopG` via `forall_goal_of_shape_of_hyps`]],
        align(center)[#text(size: 7.4pt, fill: gtm-accent)[$arrow.t$ #h(0.2em) `HostExW (3/2)` via `supplyChi`]],
      )
      #v(0.2em)

      // Level 4: Two Parallel Tracks
      #grid(
        columns: (1fr, 1fr),
        gutter: 8pt,
        dag-box(
          [Track A: `HypsAlt` & `DefiniteSideCondition`],
          [`shape_closed_link_n_of_green hG` + `theta_integrals_agree` + `CovolumeBoundOfX`],
          fill-col: white,
        ),
        dag-box(
          [Track B: Weakened Vandiver Window `VWin`],
          [`vwin_of_row h` + `admissibleClassesTwistedChar` ($C_t = 401$, `WinPair`, `IsChiField`)],
          fill-col: white,
        ),
      )
      #v(0.2em)

      // Level 5: Five Pillars
      #grid(
        columns: (1fr, 1fr, 1fr, 1fr, 1fr),
        gutter: 4pt,
        dag-box(
          [Pillar 1],
          [Mellin–Landau at $[Y, Y^(3/2)]$],
          fill-col: rgb("#F7F9FC"),
        ),
        dag-box(
          [Pillar 2],
          [Chained Theta Lifts $m approx sqrt(X)$],
          fill-col: rgb("#F7F9FC"),
        ),
        dag-box(
          [Pillar 3],
          [Inert Divisibility & RTF Gluing],
          fill-col: rgb("#F7F9FC"),
        ),
        dag-box(
          [Pillar 4],
          [`DivIneqObjU`, `HeightS`, Bost Slope],
          fill-col: rgb("#F7F9FC"),
        ),
        dag-box(
          [Pillar 5],
          [Iwasawa Towers & Behrend Sphere],
          fill-col: rgb("#F7F9FC"),
        ),
      )
      #v(0.2em)
      #align(center)[#text(size: 7.4pt, fill: gtm-accent)[$arrow.t$ #h(0.3em) Unified Foundation]]
      #v(0.15em)

      // Level 6: Foundation
      #dag-box(
        [Formalized Foundations (`OpenLiteratureStatements` + 10 Libraries)],
        [`galoisLocalGlobalStrong_recParameter`, `recTExists`, `baseChangeN`, Siegel–Weil, Arithmetic Hilbert–Samuel, Poitou–Tate, Green Characters],
        fill-col: rgb("#EEF2F7"),
        border-col: gtm-accent,
      )
    ],
    caption: [Top-down logical dependency DAG of the Alpöge–Claude proof in Lean 4, showing the exact theorem chain from `Main.lean` down to the five mathematical pillars.],
  )
  #v(0.4em)

  == The Five Mathematical Pillars and How They Interlock

  The diagram above shows *how* the Lean 4 declarations fit together; we now explain *why* they work mathematically. Why does the Riemann Hypothesis yield to an attack combining Mellin–Landau windows, chained theta lifts on definite unitary groups, local divisibility at inert primes, Arakelov slope inequalities, and a weakened Vandiver theorem? The answer lies in the way five classical obstructions cancel one another out when assembled into a single engine.

  === Pillar 1: Analytic Reduction (Mellin–Landau at Scale $[Y, Y^(3/2)]$)

  Recall from Chapter 5 that Landau's nonvanishing theorem turns a hypothetical zero $rho = beta + i gamma$ of $L(s, psi)$ with $beta > 1/2$ into a *persistent lower bound* on the oscillations of the prime-counting sum—or, more cleanly, on the smoothed arithmetic sum
  $ S_a (x) = sum_(1 <= n <= x) a(n) (x / n - 1), $
  whose Mellin transform is $integral_1^oo S_a (x) x^(-s-1) dif x = (1 / (s(s+1))) sum_(n=1)^oo a(n) n^(-s)$.

  In the classical prime number theorem, one only asks whether $S_a (x)$ is $o(x)$. To refute a zero at $beta > 1/2$, one must show that certain prime-power sums over *every* sufficiently large dyadic or polynomial window $[Y, Y^lambda]$ cannot exhibit the $Omega(x^beta)$ oscillations forced by the pole of $-L'/L(s, psi)$ at $s = rho$. In the Alpöge–Claude proof, the analytic reduction is encapsulated in `zeroFreeAll_of_topG` (`ZeroFreeAllOfTopG.lean`) and `zeroFreeOn_of_tiedWin_cyc` (`Formalism.SharpRestriction`), with the window exponent fixed at
  $ lambda = 3 / 2. $

  Why $lambda = 3/2$? Two competing pressures determine $lambda$:
  - On the *analytic* side, $lambda$ must be strictly greater than $1$ so that a Mellin window $[Y, Y^lambda]$ is wide enough (on a logarithmic scale, $[log Y, lambda log Y]$) to detect the oscillatory contribution of an off-line zero $rho$ via Landau's criterion without losing control of the truncation error. Any fixed $lambda > 1$ suffices analytically.
  - On the *arithmetic* side, the weakened Vandiver window `VWin` (Pillar 5) guarantees a "clean" interval of scales of the form $[Y, Y^2]$ inside $[X^(1/J), X]$ on which the Selmer/Tate–Shafarevich groups of the cyclotomic–quadratic host fields $E$ are tightly bounded. Choosing $lambda = 3/2$ ensures that $[Y, Y^(3/2)]$ sits comfortably inside $[Y, Y^2]$ with room to spare for dyadic shifts and level comparisons (`level_gm_le_on_family_scales`).

  More precisely, assuming $L(rho, psi) = 0$ with $op("Re")(rho) > 1/2$, the analytic reduction produces a family of scales $x in [Y, Y^(3/2)]$ at which a certain prime-level ratio—encoding the discrepancy between the actual distribution of primes splitting in the cyclotomic–quadratic host field $E$ and the main term—must jump across a threshold. The goal of Pillars 2–4 is to prove `ChainTied` (and hence `FamilyClassConnected (GChi ψ).cls (3/2)`): that no such jump can occur along any connected chain of scales where the Vandiver bound `HypV` holds.

  === Pillar 2: Automorphic Multiplicity via Chained Theta Lifts $U(X_0) -> dots.c -> U(X_m)$

  This is the conceptual heart of the Alpöge–Claude breakthrough—the direct descendant of Stepanov's method (Chapter 4).

  In Stepanov's proof of the Weil bound for a curve $C \/ bb(F)_q$, one constructs a nonzero auxiliary polynomial $P(x, y)$ of controlled degree that vanishes to *high multiplicity* $m approx sqrt(q)$ at every $bb(F)_q$-rational point. Because a nonzero polynomial cannot have more zeros (counted with multiplicity) than its degree, one obtains an upper bound on $|C(bb(F)_q)|$. For decades, number theorists asked what could possibly play the role of "a function vanishing to multiplicity $m approx sqrt(x)$ at prime places" over $bb(Z)$, where there is no Frobenius endomorphism acting on polynomials and no obvious ring of auxiliary functions with both high-order vanishing and controlled archimedean size.

  Alpöge and Claude's radical answer is to synthesize *automorphic multiplicity* using a *chain of iterated theta lifts* between totally definite unitary groups:
  $ U(X_0) -> U(X_1) -> U(X_2) -> dots.c -> U(X_m), quad m approx sqrt(x). $
  Let $K \/ K_0$ be a CM field over its maximal totally real subfield $K_0$, constructed from the cyclotomic–quadratic host field $E$ of Pillar 5. Each $X_j$ ($0 <= j <= m$) is a totally definite Hermitian space over $K$ of rank $n_j$ (growing linearly with $j$, with $k + m <= N$, where $N$ is the ambient rank). At each step $j -> j + 1$, the global theta correspondence (Chapter 7) associated to the unitary dual pair $(U(X_j), U(X_(j+1)))$ maps an automorphic form $f_j$ on $U(X_j)(bb(A)_(K_0))$ to a theta lift $f_(j+1) = theta_(phi_j) (f_j)$ on $U(X_(j+1))(bb(A)_(K_0))$.

  On the spectral ($op("GL")_n$ base-change) side, each theta lift step performs an *isobaric augmentation*:
  $ pi_j |-> pi_(j+1) = pi_j plus.square mu_j [t], $
  appending a fresh Hecke character twist $mu_j$ (with carefully chosen archimedean weight and conductor) to the automorphic representation. Why is this a faithful analogue of Stepanov's multiplicity $m$?
  1. *Multiplicative amplification:* Each of the $m$ steps contributes an independent local divisibility factor at the chosen inert primes $y in op("Tw")$, so the *total* divisibility index across the chain scales linearly in $m$—just as requiring derivatives $D^0, D^1, dots.c, D^(m-1)$ to vanish multiplies the zero count by $m$.
  2. *Nonvanishing via Rallis inner product and seesaw duality:* To ensure the final lifted form $f_m$ is *nonzero* (the analogue of $P(x, y) != 0$ in Stepanov's method!), one evaluates its Petersson inner product via the Rallis inner product formula and Siegel–Weil formula (Chapter 7). Nonvanishing reduces to the nonvanishing of a central $L$-value and local doubling zeta integrals—which is why `SiegelEisensteinContinuation`, `SiegelWeilStd`, and `DoublingMethodLocalZetaIntegrals` all appear in `EveryCharacterOfLiteratureOfVWin.lean`.
  3. *Controlled rank and weight growth:* Because $U(X_j)$ is *totally definite* at all archimedean places ($U(X_j)(K_(0, v)) approx U(n_j)$ is compact!), the space of automorphic forms of fixed level and weight is *finite-dimensional*, and its dimension and archimedean norms are governed by classical Weyl dimension formulas and highest-weight representation theory. The chain length $m approx sqrt(x)$ keeps the ambient rank $N$ and all combinatorial overhead strictly *polynomial* in $x$, while the divisibility gain is governed by the *sub-exponential* scale $b = exp(x^epsilon)$!

  #insight-box(title: "The Stepanov–Alpöge–Claude Dictionary")[
    Every element of Stepanov's proof over $bb(F)_q$ has a precise counterpart in the Alpöge–Claude proof over $bb(Z)$:
    - *Curve $C \/ bb(F)_q$ and Frobenius $F$* $arrow.l.r.long$ *CM field $K \/ K_0$ and inert prime places $y in op("Tw")$*
    - *Auxiliary polynomial $P(x, y)$* $arrow.l.r.long$ *Global automorphic form on $U(X_m)$ built by $m$ chained theta lifts*
    - *Vanishing to order $m approx sqrt(q)$* $arrow.l.r.long$ *Chain length $m approx sqrt(x)$ yielding $m$-fold local lattice divisibility*
    - *Nonvanishing $P != 0$ (Wronskian / Hasse derivatives)* $arrow.l.r.long$ *Nonvanishing of $theta_(phi_m) dots.c theta_(phi_1) (f_0)$ via Rallis inner product & doubling method*
    - *Bézout's theorem ($op("deg") P >= m dot.c |C(bb(F)_q)|$)* $arrow.l.r.long$ *Bost's Arakelov slope inequality (`DivIneqObjU` + `HeightS` + `CovolumeBoundOfX`)*
    - *Automatic smoothness over $bb(F)_q$* $arrow.l.r.long$ *Weakened Vandiver Window (`VWin`) controlling Selmer obstructions*
  ]

  === Pillar 3: Local Divisibility at Inert Primes and Integral Structure Gluing via RTF

  Where does the actual arithmetic divisibility come from? In Stepanov's proof, vanishing to order $m$ at an $bb(F)_q$-point comes from the identity $x^q - x = 0$ and its Hasse derivatives. Over $bb(Z)$, the analogous divisibility is harvested at *inert primes* of the CM extension $K \/ K_0$ via four interlocking arithmetic mechanisms (Chapters 8 and 14):

  1. *CM Elliptic Curves and Chowla–Selberg Periods:* Over the host field $E$ (and its CM quadratic extension $K$), one attaches CM elliptic curves $A$ with good reduction outside a small set of places (`cmCurveGoodOutsidePrime`). The invariant derivation $D$ and fundamental period $Omega$ of $A$ satisfy the Chowla–Selberg formula, linking the archimedean period $log Omega$ to logarithmic derivatives of Dirichlet $L$-functions and gamma values. At inert primes $y$, the formal group of $A$ is supersingular of height $2$, forcing high $p$-adic divisibility of the values of iterated differential operators $D^k$ on theta functions (analogous to the Hurwitz–Katz divisibility of Eisenstein series and CM theta constants).
  2. *Weyl Branching and Lowest-Alcove Irreducibility:* To pass from scalar CM values to vector-valued automorphic forms on $U(X_j)$, one decomposes the restriction of irreducible algebraic representations of $U(n_j)$ along the chain of embeddings using Weyl branching rules. In characteristic $p$, keeping the integral structure intact without collapsing modulo $p$ requires that the relevant Weyl modules remain irreducible in the lowest alcove (`WeylModuleSimpleClosedLowestAlcove`, `induced_simple_lowest_alcove_of_literature`).
  3. *Siegel Mass Formula and Genus Volumes:* Because $U(X_j)$ is totally definite, the double coset space $U(X_j)(K_0) without U(X_j)(bb(A)_(K_0, f)) / K_f$ is a finite set of Hermitian lattice classes in a genus. The weighted cardinality of this finite set is governed by the Siegel–Tamagawa mass formula (`GenusMassAt`, `MassRatioUnderVolume`, `ClassNumberFormula₂`). This mass formula controls the number of local lattice classes and ensures that the global integral lattice $R$ has a well-calibrated covolume.
  4. *Integral Structure Gluing via the Relative Trace Formula (RTF):* Locally at each finite place $y$, the theta-lift chain and the definite unitary group define local integral lattices $M_j$ and $T_(l, j) (mu_y)$ with local indices `idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y)))` and Hermitian Gram-determinant valuations `jw (HT j (μ y)) y (Tl j (μ y))`. To compare the *definite* unitary side (where divisibility is computed) with the *indefinite / $op("GL")_n$* side (where automorphic multiplicity and base change live), the proof uses a relative trace formula and local orbital-integral matching (`theta_integrals_agree_and_local_matching`, `DefiniteSideCondition`, `IndefiniteRealisationBoundedRows` inside `HypsAlt`). This glues the local lattices into a single global $cal(O)_K$-lattice $R subset.eq K^D$ whose localizations agree with the twisted lattices `matLat (ι (μ y)) (abelian₂ (μ y))` at every finite place $y$.

  In `DivIneqTopAnchorU.lean`, the net output of Pillar 3 is recorded in a single nonnegative real number $F_0$:
  $ F_0 = sum_(j in J) sum_(y in op("Tw")) op("lw")(y) dot.c op("ramw")(y) dot.c F_0 (y, j), $
  representing the weighted total local divisibility harvested across all $m = |J|$ steps of the theta chain and all active inert places $y in op("Tw")$.

  === Pillar 4: Arakelov Geometry and Bost's Slope Inequality (`DivIneqObjU`, `HeightS`, `CovolumeBoundOfX`)

  Once Pillar 2 has built the nonzero $m$-step theta lift and Pillar 3 has encoded its local divisibility into a global Hermitian lattice $R$ over $cal(O)_K$ with archimedean metrics $X_E, X_Q, X_W, X_T$, Pillar 4 delivers the *global arithmetic contradiction* via Arakelov geometry and Bost's slope inequality (Chapters 9 and 15).

  Recall Bost's fundamental principle (Chapter 9): if $phi : overline(E) -> overline(F)$ is an injective morphism of Hermitian vector bundles over $op("Spec")(cal(O)_K)$, then the Arakelov slope of $overline(E)$ is bounded above by the maximal Harder–Narasimhan slope of $overline(F)$ plus the archimedean operator-norm defect $log norm(phi)_oo$:
  $ hat(mu)(overline(E)) <= hat(mu)_max (overline(F)) + log norm(phi)_oo. $
  More generally, if $phi$ is divisible by a large integral ideal (or has large local lattice indices `idx` at finite places $y in op("Tw")$), then the Arakelov degree of the image drops by the log-norm of the divisibility ideal—contributing $-2 F_0$ to the left-hand side!

  In `Formalism/DivisorInequality/DivIneqTopAnchorU.lean`, this Arakelov engine is crystallized into two master propositions—`DivIneqObjU` and `HeightS`—backed by the covolume lower bound `CovolumeBoundOfX` from `TopCovolSlim2Use.lean`:

  1. *The Master Divisor-Slope Inequality (`DivIneqObjU`):* Given the Hermitian vector bundle data $(K, K_0, D, X_E, X_Q, X_W, X_T, R, M_j, T_(l, j))$ and the Harder–Narasimhan slope parameters $mu_C, mu_0$, together with the local index bounds at $y in op("Tw")$, `DivIneqObjU` concludes:
     $
       &mu_C + h_u - 2 F_0 \
       &quad <= sum_(t in op("TT")) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T) \
       &quad + (50 C_0 + 10) (|op("TT")| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)).
     $
     Here $op("ph")(nu) = nu log nu - nu$ is the logarithmic Stirling function (`Formalism.LatticeIndexTer.ph`), $a_T (t)$ measures the local archimedean weight at each place $t in op("TT")$, $log Omega$ is the CM period, $log T$ is the theta-constant normalization, and $h_u$ is the upper-bound budget for the total Arakelov height. Look closely at the left-hand side versus the right-hand side:
     - The term $-2 F_0$ on the left (or $+2 F_0$ moved to the right) represents the massive *divisibility gain* from Pillar 3.
     - The term $mu_C$ is bounded *from below* by the covolume bound `CovolumeBoundOfX`.
     - The term $h_u$ is bounded *from above* by `HeightS`.
     - On the right-hand side, the main Stirling-entropy term $m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T$ is precisely calibrated against $2 F_0$ and $mu_C$ so that a hypothetical off-line zero forces the left-hand side to strictly exceed the right-hand side!

  2. *The Master Height Bound (`HeightS`):* To control $h_u$, `HeightS` bounds the sum of the projective height $h_P$ (on the Siegel/unitary moduli space) and the fiber heights $sum_(j in J) h_K (j)$ minus the lower spectral term $m_lambda$:
     $ h_P + sum_(j in J) h_K (j) - m_lambda <= h_u. $
     Its proof decomposes $h_P$ via integral toroidal compactifications of Siegel moduli spaces (`SiegelToroidalIntegral`, `ToroidalCompactificationBis`), Chow forms (`ChowFormHeightComparison`, `FubiniStudyChowHeightFormula`), and log-Kodaira–Spencer isomorphisms, while $h_K (j)$ is controlled by archimedean theta-constant bounds (`logth0`, `logOmτ`) and Stirling estimates (`ph (ν j ρ i)`).

  3. *The Covolume Bound (`CovolumeBoundOfX`):* Proved in `TopCovolSlim2Use.lean` (`topCovolSlim2_use_alt_alt`), this supplies the crucial lower bound on the arithmetic volume / covolume of the lattice of small sections. It brings together the full force of modern Arakelov geometry: arithmetic Hilbert–Samuel (`hsUse_outright`), Moriwaki's bigness theorem (`moriwakiBig_outright`), Nadel vanishing and $L^2$-extension (`l2_extension_log_canonical`, `nadel_vanishing_and_non_klt_divisor`), Poincaré–Lelong (`poincareLelong`), Fargues exactness (`fargues_exact`), Zarhin's trick (`zarhin_statement`), and small-section injectivity (`small_sections_injective`).

  === Pillar 5: Weakened Vandiver Window (`VWin`) over Cyclotomic–Quadratic Towers

  Even with Pillars 1–4 in place, one subtle arithmetic obstacle remains: when one constructs the CM host field $K \/ K_0$ from a cyclotomic–quadratic field $E$ of huge conductor, uncontrolled $ell$-torsion in the class group (or, more generally, in the higher Bloch–Kato Selmer / Tate–Shafarevich groups $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$) could corrupt the integral structure of the automorphic forms and destroy the local-to-global divisibility bound!

  Classically, the *Vandiver conjecture* asserts that a prime $p$ never divides the class number $h^+$ of the maximal real subfield $bb(Q)(zeta_p)^+$. The Vandiver conjecture is completely open—and looks as hopeless as ever for arbitrary conductors. How does the Alpöge–Claude proof bypass it?

  The answer is Pillar 5 (`ExistsPageN.lean` and `VwinOfRow.lean`): instead of proving the Vandiver conjecture at *every* scale, the proof establishes a *Weakened Vandiver Window* (`VWin`) that holds *unconditionally* on a clean polynomial window $[Y, Y^2]$ inside every sufficiently large interval $[X^(1/J), X]$!

  Let us record the exact mathematical definitions from `CharacterBoxes/ExistsPageN.lean`.

  #definition(title: "The Cyclotomic–Quadratic Host Field IsChiField")[
    Let $psi$ be a primitive Dirichlet character of conductor $N_psi$, and let $e, q, d in bb(N)$ be positive integers. A number field $E$ satisfies `IsChiField psi e q d E` if there exist an integer $N >= 1$ divisible by $2^(e+2)$, $N_psi$, $q$, and $d$, a $bb(Q)$-algebra embedding $j : E -> bb(Q)(zeta_N)$, and a primitive $N$-th root of unity $zeta in bb(Q)(zeta_N)$ such that an automorphism $tau in op("Gal")(bb(Q)(zeta_N) \/ bb(Q))$ with $tau(zeta) = zeta^a$ fixes $j(E)$ pointwise if and only if:
    1. $a equiv plus.minus 1 mod 2^(e+2)$,
    2. $psi(a) = 1$,
    3. $(a / q) = 1$ (Jacobi symbol), and
    4. $(a / d) = 1$ (Jacobi symbol).
  ]

  Observe immediately that condition (1) forces complex conjugation ($a equiv -1 mod N$) to fix $E$ whenever $psi(-1) = 1$ and $(-1/q)(-1/d) = 1$—or more generally, $E$ is a totally real subfield of $bb(Q)(zeta_N)$ built by intersecting the $2$-adic cyclotomic tower $bb(Q)(zeta_(2^(e+2)))^+$, the character field of $psi$, and the two quadratic fields cut out by the primes $q$ and $d$.

  #definition(title: "The Auxiliary Prime Pair WinPair")[
    For real parameters $epsilon > 0$ and $Y > 1$, a pair of primes $(q, d)$ satisfies `WinPair eps Y q d` if:
    1. $q$ is prime with $q equiv 3 mod 8$ and
       $ 1 / 2 Y^(epsilon/5) < log q <= Y^(epsilon/5); $
    2. $d$ is prime with $d equiv 7 mod 16$ and
       $ 1 / 2 Y^(epsilon/5) (log Y)^2 < log d <= Y^(epsilon/5) (log Y)^2; $
    3. $q | d + 1$; and
    4. for every odd prime $p <= Y^(epsilon/5)$, we have $p | d + 1$.
  ]

  The divisibility conditions $q | d + 1$ and $p | d + 1$ for all odd primes $p <= Y^(epsilon/5)$ are a stroke of arithmetic artistry: because $d equiv -1 mod p$ and $d equiv 7 mod 16$, the quadratic reciprocity law forces the Legendre symbol $(-d / p)$ (and splitting behavior at $2$ and $q$) to align uniformly across all small primes $p <= Y^(epsilon/5)$! This guarantees a rich, predictable supply of inert and split primes for the CM field $K = E(sqrt(-d))$ (or its quadratic twist by $q$ and $d$).

  #definition(title: "The Log-Weighted Selmer Bound VVle and Weakened Vandiver Window VWin")[
    For a number field $E$, a cutoff $t in bb(N)$, and a budget $B in bb(R)$, we say `VVle E t B` holds if, for every algebraic closure $Omega \/ E$ and every compatible system of $ell$-adic Galois cohomology data `ld`:
    1. for every prime $ell$ and every integer $1 <= e < t$, the Tate–Shafarevich / Selmer length $op("shaLen")(ell, e)$ is finite; and
    2. for every finite set $S$ of primes,
       $ sum_(ell in S) (log ell) sum_(1 <= e < t) op("shaLen")(ell, e) <= B. $
    For a primitive character $psi$, exponent $0 < epsilon < 1/52$, cutoff exponent $C_t > 0$, and scale function $e : bb(R) -> bb(N)$ satisfying the dyadic level condition `PageN eps x (e x)`:
    $ x^(2 + 8 epsilon) <= 2^(e(x)) <= 2 x^(2 + 8 epsilon) quad (forall x >= 1), $
    we say `VAt psi eps Ct q d e x` holds if every number field $E$ satisfying `IsChiField psi e q d E` obeys
    $ op("VVle") E space floor(x^(C_t)) space sqrt(exp(x^epsilon)). $
    Finally, `VWinAt psi Ct` asserts that for every $0 < epsilon < 1/52$ and every `PageN`-function $e$, there exist $J >= 1$ and $X_0 in bb(R)$ such that for every $X >= X_0$ and every pair $(q, d)$ satisfying `WinPair eps (X^(1/J)) q d`, there exists a scale $Y$ with
    $ X^(1/J) <= Y <= Y^2 <= X $
    such that `VAt psi eps Ct q d (e x) x` holds for *all* $x in [Y, Y^2]$. The global predicate `VWin` is simply
    $ op("VWin") : equiv forall psi, space op("VWinAt") psi space 401. $
  ]

  Look at the numbers in `VWin`: the Selmer length is summed over all Tate twists $1 <= e < floor(x^(401))$ and weighted by $log ell$ over all primes $ell$, yet the total log-weighted length is bounded by
  $ B = sqrt(exp(x^epsilon)) = exp(1/2 x^epsilon) = sqrt(b). $
  Because $b = exp(x^epsilon)$ is the main exponential scale of the Arakelov inequality (Pillar 4), a Selmer obstruction of size $sqrt(b)$ is *strictly negligible* compared to $b$—it is swallowed effortlessly by the error budget of `DivIneqObjU`!

  How is `VWin` proved unconditionally in `vwin_of_row` (`VwinOfRow.lean` and Chapter 16)? Roughly speaking, any violation of `VVle` at a prime $ell$ and twist $e$ produces a nontrivial Galois cohomology class in $op("Ш")^1$, which via Poitou–Tate duality, Bloch–Kato local conditions, and modularity/automorphy lifting (using `galoisLocalGlobalStrong_recParameter` and `baseChangeN`) forces a congruence between distinct automorphic representations (or a high-multiplicity eigenform) in the $2$-adic Iwasawa tower. Because the total number of such congruences across a huge range $[X^(1/J), X]$ is bounded by a global dimension/density estimate, a pigeonhole argument using *Behrend's sphere theorem* (in `ModularityArgument/ThresholdArguments/DenseThresholdCases`) proves that the "bad" scales $x$ cannot cover every quadratic window $[Y, Y^2] subset.eq [X^(1/J), X]$. Thus a clean window $[Y, Y^2]$ is *guaranteed* to exist!

  === How the Five Pillars Interlock into a Single Contradiction

  Let us now step back and watch all five pillars turn together in a single cycle:
  1. *Assume for contradiction* that some primitive Dirichlet character $psi$ has a zero $rho = beta + i gamma$ with $beta > 1/2$.
  2. *Pillar 5 (`VWin` + `supplyChi`)* fixes a small $0 < epsilon < 1/52$, selects an auxiliary prime pair $(q, d)$ satisfying `WinPair`, and locates a clean window $[Y, Y^2] subset.eq [X^(1/J), X]$ on which the cyclotomic–quadratic host fields $E$ (`IsChiField psi (e x) q d E`) obey the weakened Vandiver bound `VVle` up to twist $floor(x^(401))$ with budget $sqrt(b)$.
  3. *Pillar 1 (`zeroFreeAll_of_topG` at $lambda = 3/2$)* restricts attention to the sub-window $[Y, Y^(3/2)] subset.eq [Y, Y^2]$. The hypothetical off-line zero $rho$ forces an oscillatory discrepancy in the smoothed prime sums over $[Y, Y^(3/2)]$, contradicting `FamilyClassConnected (GChi ψ).cls (3/2)` if we can show that the family is `ChainTied`.
  4. *Pillar 2 (Chained Theta Lifts)* constructs, at each scale $x in [Y, Y^(3/2)]$, a chain of $m approx sqrt(x)$ iterated theta lifts $U(X_0) -> dots.c -> U(X_m)$ over the CM field $K \/ K_0$ built from $E$, producing a nonzero automorphic form with $m$-fold isobaric multiplicity.
  5. *Pillar 3 (Local Divisibility & RTF Gluing)* exploits the CM curves, Chowla–Selberg periods, lowest-alcove Weyl branching, and Siegel mass formulas at the inert primes $y in op("Tw")$—all kept unobstructed by the `VVle` bound from Pillar 5—and glues the local integral structures via the relative trace formula into a global Hermitian lattice $R$ with total divisibility $F_0$.
  6. *Pillar 4 (`DivIneqObjU` + `HeightS` + `CovolumeBoundOfX`)* applies Bost's Arakelov slope inequality to $R$. The lower bound on $mu_C$ (`CovolumeBoundOfX`), the upper bound on $h_u$ (`HeightS`), and the divisibility gain $2 F_0$ clash with the Stirling-entropy upper bound in `DivIneqObjU`, forcing the family to be `ChainTied` and contradicting the off-line zero $rho$ from Step 1.

  No single pillar could succeed alone: without Pillar 2, one has no multiplicity $m approx sqrt(x)$ to beat the archimedean height; without Pillar 3, the theta lifts have no local divisibility; without Pillar 4, local divisibility cannot be converted into a global contradiction; without Pillar 5, Selmer obstructions in the cyclotomic tower break the integral structure; and without Pillar 1, there is no bridge from a single zero of $L(s, psi)$ to the arithmetic window $[Y, Y^(3/2)]$.

  == The Master Parameter Hierarchy

  In any proof by asymptotic contradiction—from Thue–Siegel–Roth and Baker's linear forms in logarithms to Stepanov's method—the ultimate test of viability is whether the *parameter inequalities* actually close. One of the most reassuring features of the Alpöge–Claude proof is that its parameter hierarchy is not perched on a razor's edge: it leverages a decisive *separation of scales* between polynomial powers of $x$ and the sub-exponential scale $b = exp(x^epsilon)$.

  In this section, we extract the exact parameter relations from `Formalism/DivisorInequality/DivIneqTopAnchorU.lean` (lines 197–215 and 267–273) and `CharacterBoxes/ExistsPageN.lean` (lines 70–92), organize them into a master hierarchy table, and prove why every single side condition holds asymptotically for large $x$.

  === The Primary Scales and Their Roles

  Fix a sufficiently large primary scale $x >= 1$ and an exponent $epsilon$ in the open interval
  $ 0 < epsilon < 1 / 52. $
  From $(x, epsilon)$, the proof defines a three-tier ladder of scales:
  $ L := x^epsilon, quad b := exp(L) = exp(x^epsilon), quad a := x dot.c b = x exp(x^epsilon). $
  Notice the logarithmic scale $L_a := log(a dot.c r_d)$, where $r_d >= 1$ is the conductor/discriminant parameter satisfying $log r_d <= L$. Since $log x <= L$ for $x$ large (as $epsilon > 0$), we immediately have
  $ L <= L_a = log x + L + log r_d <= 3 L = 3 x^epsilon. $
  Thus $L_a asymp x^epsilon$, while $b = exp(x^epsilon)$ is *sub-exponential* in $x$—strictly larger than *every* fixed power $x^C$ ($C > 0$), yet strictly smaller than any exponential $exp(c x)$!

  Alongside $(L, b, a)$, the proof sets five structural parameters:
  1. *Theta-chain length:* $m approx sqrt(x)$ (satisfying $1 <= m$ and $m = |J|$).
  2. *Ambient unitary rank and base rank:* $1 <= k$, $k + m <= N$, with $N$ polynomial in $x$ (specifically $N = O(x^(O(1)))$).
  3. *Dyadic cyclotomic level:* $e = e(x) in bb(N)$ chosen via `exists_pageN` to satisfy
     $ x^(2 + 8 epsilon) <= 2^e <= 2 x^(2 + 8 epsilon). $
     Hence $e = (2 + 8 epsilon) log_2 x + O(1)$, and the $2$-adic cyclotomic conductor $2^(e+2)$ scales as $x^(2 + 8 epsilon)$.
  4. *Auxiliary primes $(q, d)$ in `WinPair`:* at the outer window scale $Y_0 = X^(1/J)$,
     $ 1 / 2 Y_0^(epsilon/5) < log q <= Y_0^(epsilon/5), quad 1 / 2 Y_0^(epsilon/5) (log Y_0)^2 < log d <= Y_0^(epsilon/5) (log Y_0)^2, $
     with $q equiv 3 mod 8$, $d equiv 7 mod 16$, $q | d + 1$, and $p | d + 1$ for every odd prime $p <= Y_0^(epsilon/5)$.
  5. *Vandiver cutoff and Selmer budget:* $C_t = 401$, so the Tate-twist cutoff is $t = floor(x^(401))$, and the log-weighted Selmer budget is
     $ B = sqrt(exp(x^epsilon)) = exp(1/2 x^epsilon) = b^(1/2). $

  The table below summarizes the complete parameter hierarchy and its exact correspondence with the Lean 4 source.

  #v(0.35em)
  #table(
    columns: (17%, 27%, 22%, 34%),
    stroke: (x: none, y: 0.35pt + luma(205)),
    fill: (col, row) => if row == 0 { rgb("#EBF1F8") } else if calc.odd(row) { white } else { gtm-tint },
    inset: (x: 5pt, y: 5pt),
    align: (left, left, left, left),
    [*Parameter*], [*Asymptotic Scale*], [*Lean Identifier*], [*Role in the Proof*],
    [$x$], [$x in [Y, Y^(3/2)]$, $x -> oo$], [`x : ℝ`], [Primary analytic & geometric scale],
    [$epsilon$], [$0 < epsilon < 1/52$], [`eps : ℝ`], [Sub-exponential exponent],
    [$L$], [$L = x^epsilon$], [`L = x ^ eps`], [Logarithmic scale of $b$ and $r_d$],
    [$b$], [$b = exp(x^epsilon)$], [`b = Real.exp L`], [Sub-exponential buffer beating all $x^C$],
    [$a$], [$a = x exp(x^epsilon)$], [`a = x * b`], [Main archimedean weight scale ($a = x b$)],
    [$L_a$], [$L_a = log(a r_d) asymp x^epsilon$], [`La = Real.log (a * rd)`], [Log-height factor in `DivIneqObjU`],
    [$m$], [$m approx sqrt(x)$], [`m = Fintype.card J`], [Length of theta-lift chain $U(X_0) -> dots.c -> U(X_m)$],
    [$2^e$], [$[x^(2 + 8 epsilon), 2 x^(2 + 8 epsilon)]$], [`PageN eps x e`], [Conductor of $2$-adic cyclotomic tower],
    [$log q$], [$asymp Y^(epsilon/5)$], [`WinPair.q_lo / q_up`], [First auxiliary prime ($q equiv 3 mod 8$)],
    [$log d$], [$asymp Y^(epsilon/5) (log Y)^2$], [`WinPair.d_lo / d_up`], [Second auxiliary prime ($d equiv 7 mod 16$, $p | d+1$)],
    [$t$], [$floor(x^(401))$], [`⌊x ^ Ct⌋₊`, `Ct = 401`], [Tate-twist cutoff in `VVle` / `VWin`],
    [$B$], [$exp(x^epsilon / 2) = sqrt(b)$], [`Real.sqrt (Real.exp (x ^ eps))`], [Total log-weighted Selmer budget],
    [$lambda$], [$lambda = 3/2$], [`la := 3 / 2`], [Mellin–Landau window $[Y, Y^(3/2)] subset.eq [Y, Y^2]$],
  )
  #v(0.35em)

  === Why Every Side Condition Closes with Room to Spare

  A first glance at `DivIneqTopAnchorU.lean` reveals a daunting list of side inequalities (lines 153–210):
  $
    &m^3 N^2 L <= b, quad m eta N L <= b, quad k N <= b, \
    &N^2 log g <= b, quad N log(f N) <= b,
  $
  $ b' N <= a, quad m k b' <= a, quad (k b)^8 <= g, quad B_0 = f m b x^epsilon. $
  Yet mathematically, the verification that all of these inequalities hold simultaneously is astonishingly clean. It rests on *three fundamental scale comparisons*.

  #proposition(title: "Asymptotic Closure of the Master Parameter Hierarchy")[
    Let $0 < epsilon < 1/52$, and set $L = x^epsilon$, $b = exp(L)$, and $a = x b$. Suppose the structural parameters $m, k, N, f, S, eta, log g, c_e$ grow at most polynomially in $x$ (specifically $m asymp sqrt(x)$, and $k, N, f, log g <= x^(C)$ for fixed constants), while $b' <= x^(1/4) b$ and $N_c <= p_N b$. Then for all sufficiently large $x$:
    1. *Sub-exponential dominance over polynomial overhead:* Every polynomial combination of $(x, m, k, N, f, L, log g)$ is $o(b)$. In particular, $m^3 N^2 L <= b$, $k N <= b$, $N^2 log g <= b$, and $N log(f N) <= b$ hold with exponentially widening margins.
    2. *Main-term dominance over error terms in `DivIneqObjU`:* Writing $B_0 = f m b x^epsilon$, the error terms $(50 C_0 + 10) (|op("TT")| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c))$ are dominated by the leading Stirling-entropy term $m a_T log a_T$ whenever $a_T asymp a = x b$ and the polynomial degree of $f m$ is controlled relative to $x$ and $a$.
    3. *Chebyshev–Linnik feasibility of `WinPair`:* For all sufficiently large $Y$, the interval
       $ [exp(1/2 Y^(epsilon/5) (log Y)^2), exp(Y^(epsilon/5) (log Y)^2)] $
       contains primes $d equiv 7 mod 16$ divisible modulo $d + 1$ by both $q$ and every odd prime $p <= Y^(epsilon/5)$.
  ]

  #proof[
    We verify each of the three mechanisms explicitly.

    *Part 1 (Sub-exponential vs. polynomial).* For any fixed exponent $A > 0$, we have
    $ log(x^A / b) = A log x - x^epsilon -> -oo quad "as" x -> oo, $
    because $epsilon > 0$. Consequently $x^A / b -> 0$ faster than any inverse power of $x$. Since $m, k, N, f, L = x^epsilon$, and $log g$ are all bounded by fixed powers of $x$, every product such as $m^3 N^2 L$, $k N$, $N^2 log g$, or $N log(f N)$ is $O(x^A)$ for some fixed $A$, and therefore strictly smaller than $b = exp(x^epsilon)$ for all sufficiently large $x$. Likewise, in the Selmer budget of Pillar 5, any polynomial factor times $B = sqrt(b) = exp(1/2 x^epsilon)$ is $o(b)$, because $exp(1/2 x^epsilon) / exp(x^epsilon) = exp(-1/2 x^epsilon)$ decays sub-exponentially!

    *Part 2 (Leading Stirling term vs. error terms).* Consider the leading term in `DivIneqObjU`:
    $
      &m (op("ph")(a_T) - a_T log Omega) - a_T log T \
      &quad = m a_T (log a_T - 1 - log Omega) - a_T log T.
    $
    When $a_T asymp a = x b$, we have $log a_T = log x + x^epsilon + O(1) approx L_a$, so the main term has magnitude $asymp m a L_a = m x b L_a$. Compare this with the two error blocks on the right-hand side of `DivIneqObjU`:
    - The first error block is $(50 C_0 + 10) |op("TT")| a L_a$. Since $|op("TT")| <= f$ while the main term carries the multiplicity factor $m |op("TT")| a L_a$, the ratio of the first error block to the main term is $O(1 / m) = O(x^(-1/2)) -> 0$! This is precisely *why* the theta chain must have length $m -> oo$ (specifically $m approx sqrt(x)$): it suppresses the $|op("TT")| a L_a$ error by a factor of $m$.
    - The second error block is $(50 C_0 + 10) c_e m (x^epsilon B_0 + (log x)^2 N_c)$, where $B_0 = f m b x^epsilon$. Its ratio to the main term $m a L_a = m x b L_a$ is
      $ (x^epsilon dot.c f m b x^epsilon) / (x b L_a) = (f m x^(2 epsilon)) / (x L_a) = (f m x^epsilon) / x. $
      Here the sub-exponential factor $b$ *cancels completely* between numerator and denominator! What remains is a pure power-of-$x$ comparison: because $m approx sqrt(x)$ and $f$ is bounded by a small power of $x^epsilon$ (coming from the `WinPair` / `PageN` degree), we have $f m x^epsilon << x$ as long as $epsilon$ is sufficiently small—which is the exact origin of the upper bound $epsilon < 1/52$!

    *Part 3 (Feasibility of `WinPair`).* Let $Z = Y^(epsilon/5)$, and consider the congruence system for $d$:
    $
      &d equiv 7 mod 16, quad d equiv -1 mod q, \
      &d equiv -1 mod p space (forall "odd prime" p <= Z).
    $
    By the Chinese Remainder Theorem, this defines a single primitive residue class modulo
    $ M := 16 dot.c op("lcm")(q, product_(3 <= p <= Z) p). $
    Let us estimate $log M$ using Chebyshev's bound $theta(Z) = sum_(p <= Z) log p = (1 + o(1)) Z$ (Chapter 1) and the upper bound $log q <= Z$:
    $
      log M &<= log 16 + log q + sum_(3 <= p <= Z) log p \
            &<= (2 + o(1)) Z = (2 + o(1)) Y^(epsilon/5).
    $
    By Linnik's theorem (`Development.AutomorphicArithmetic.ThetaCorrespondence.Linnik`), there exists an absolute constant $L_"Linnik"$ such that the least prime in any reduced residue class modulo $M$ is at most $M^(L_"Linnik")$, i.e., has logarithm at most $L_"Linnik" log M = O(Y^(epsilon/5))$. Since the target interval for $log d$ in `WinPair` is
    $ (1 / 2 Y^(epsilon/5) (log Y)^2, space Y^(epsilon/5) (log Y)^2], $
    which exceeds $L_"Linnik" log M$ by a full factor of $(log Y)^2 -> oo$, Linnik's theorem (and in fact the prime number theorem in arithmetic progressions at this range, with a $(log Y)^2$ margin!) guarantees an abundance of primes $d$ satisfying `WinPair eps Y q d` for all large $Y$.
  ]

  #remark(title: "Why the Threshold Is Specifically 0 < eps < 1/52")[
    The reader may wonder where the exact fraction $1/52$ in `VWinAt` (`ExistsPageN.lean`, line 88) comes from. It is not a deep arithmetic constant like $1/2$; it is an explicit *bookkeeping budget* that collects all $O(epsilon)$ exponent losses across the five pillars. Specifically:
    - The dyadic cyclotomic level `PageN` uses conductor $2^e asymp x^(2 + 8 epsilon)$ (an $8 epsilon$ loss).
    - The auxiliary primes $q, d$ in `WinPair` have $log q asymp Y^(epsilon/5)$ and $log d asymp Y^(epsilon/5) (log Y)^2$, which ensures that $log q + log d << L = x^epsilon$ even after raising $Y$ to $Y^(3/2)$ or $Y^2$.
    - The error factor `llx <= ce * x ^ eps` and `B0 = f * m * b * x ^ eps` in `DivIneqObjU` contribute additional $O(epsilon)$ powers of $x$ against the $x^(1/2)$ margin left by $m approx sqrt(x)$.
    - The Behrend-sphere density threshold in `VwinOfRow` and `admissibleClassesTwistedChar` requires a small positive fraction of the exponent to absorb the density-to-window conversion.

    Summing these losses yields a total coefficient well below $52$, so imposing $0 < epsilon < 1/52$ guarantees that every exponent inequality across the entire proof holds strictly and uniformly. Similarly, the Tate-twist cutoff $C_t = 401$ in `VWin` is chosen generously above the maximal weight-degree polynomial needed to transfer divisibility through the $m$-step theta chain, ensuring that `VVle.mono` (monotonicity in $t$) always covers every twist encountered in the proof.
  ]

  === The Role of the Stirling Function $op("ph")(nu) = nu log nu - nu$

  A striking feature of both `DivIneqObjU` and `HeightS` is the ubiquitous appearance of the function
  $ op("ph")(nu) := nu log nu - nu quad (nu > 0), $
  defined in `Formalism.LatticeIndexTer.ph`. Why does Stirling's approximation $log(nu !) approx nu log nu - nu$ sit at the very center of the master inequality?

  In classical complex analysis and transcendence theory (and in Bost's proof of the Grothendieck–Katz $p$-curvature conjecture), when one differentiates a function $nu$ times, Cauchy's integral formula multiplies the archimedean norm by $nu !$, contributing $+ op("ph")(nu)$ to the archimedean log-norm (the upper bound on the height). Conversely, at a finite prime $p$, the divided power $D^nu / nu !$ has denominator $nu !$, whose $p$-adic valuation is governed by Legendre's formula $v_p (nu !) = (nu - s_p (nu)) / (p - 1)$. In the Alpöge–Claude proof, the $m$-step theta chain acts on automorphic forms of archimedean weight parameters $nu_(j, rho, i)$ whose sum over $i$ equals
  $ sum_i nu_(j, rho, i) = cases(a_T (rho) + k w_(j, rho) + delta_(j, rho) & "if" rho in op("TT"), k w_(j, rho) + delta_(j, rho) & "if" rho in.not op("TT")) $
  (`DivIneqTopAnchorU.lean`, line 192). The archimedean norm of the iterated differential/theta operators produces $sum_i op("ph")(nu_(j, rho, i))$, while the CM period normalization subtracts $(sum_i nu_(j, rho, i)) log Omega$. By convexity of $op("ph")$ (since $op("ph")''(nu) = 1 / nu > 0$), the difference $sum_i op("ph")(nu_(j, rho, i)) - log H_(j, rho)$ is controlled by $op("ph")(a_T (rho))$ plus a controlled error $e_E (j, rho)$. Thus the exact balance between archimedean factorial growth ($+ m op("ph")(a_T)$), CM period scaling ($- m a_T log Omega$), and finite-place divisibility ($- 2 F_0$) is what drives the final contradiction.

  == Reading Guide to Chapters 12–16 and Lean 4 Cross-Reference

  With the global blueprint in hand, the remainder of Part III unpacks each of the five pillars in complete mathematical detail. Each chapter is written to be read both as a self-contained graduate exposition and as a guided companion to the verified Lean 4 source:

  - *Chapter 12 (Analytic Reduction: Mellin Transforms, Landau Windows, and `ZeroFreeAllOfTopG`):* Develops the analytic engine of Pillar 1. Starting from the smoothed sum $S_a (x)$ and Mellin inversion, we prove Landau's window nonvanishing criterion at exponent $lambda = 3/2$, construct the character-box family `GChi ψ`, and prove `zeroFreeAll_of_topG` from `zeroFreeOn_of_tiedWin_cyc` and `level_gm_le_on_family_scales`.
  - *Chapter 13 (Automorphic Multiplicity: Chained Theta Lifts on Totally Definite Unitary Groups):* Develops Pillar 2. We construct the chain $U(X_0) -> dots.c -> U(X_m)$ of length $m approx sqrt(x)$, establish the isobaric transfer $pi |-> pi plus.square mu_j [t]$ via definite unitary base change (`baseChangeN`), and prove global nonvanishing of the iterated theta lift using the Rallis inner product formula, Siegel–Weil, and the doubling method.
  - *Chapter 14 (Local Divisibility at Inert Primes, Integral Structures, and the Relative Trace Formula):* Develops Pillar 3. We analyze the CM elliptic curves over $E$, the Chowla–Selberg period relations, lowest-alcove Weyl branching, the Siegel–Tamagawa mass formula (`GenusMassAt`, `ClassNumberFormula₂`), and the relative trace formula / local matching (`theta_integrals_agree_and_local_matching`, `DefiniteSideCondition`) that glues the local lattices into the global lattice $R$ with total divisibility $F_0$.
  - *Chapter 15 (Arakelov Geometry, Bost's Slope Inequality, and the Master Inequalities):* Develops Pillar 4. We prove the three Arakelov pillars—`DivIneqObjU`, `HeightS`, and `CovolumeBoundOfX` (`topCovolSlim2_use_alt_alt`)—showing how Harder–Narasimhan slopes, toroidal compactifications of Siegel moduli spaces, Chow-form height comparisons, arithmetic Hilbert–Samuel, Moriwaki bigness, and Nadel vanishing combine to produce the numerical contradiction.
  - *Chapter 16 (The Weakened Vandiver Window, Cyclotomic–Quadratic Towers, and Behrend's Sphere):* Develops Pillar 5. We prove `vwin_of_row` and `supplyChi`: constructing the `WinPair` primes via Linnik's theorem, bounding Selmer lengths `VVle` via Poitou–Tate duality, Bloch–Kato local conditions, and `galoisLocalGlobalStrong_recParameter`, and applying Behrend's sphere theorem to extract the clean window $[Y, Y^2]$ on which `VWin` holds.

  Part IV (Chapters 17–18) then steps back from the mathematics to examine the Lean 4 formalization itself—its modular engineering, independent verification by `comparator` and `nanoda`, axiom audit, and future mathematical horizons.

  #lean-note(title: "Lean 4 Formalization: The Ten-Library Architecture and Module Map", module: "lakefile.toml")[
    The verified Lean 4 repository (`leanprover-community/riemann-hypothesis`) comprises *149,217 `.lean` source files* totaling *20,788,900 lines of code*, organized into *10 Lake libraries* (as declared in `lakefile.toml`, built atop Mathlib):

    #v(0.25em)
    #table(
      columns: (24%, 76%),
      stroke: (x: none, y: 0.3pt + luma(200)),
      inset: (x: 4pt, y: 4pt),
      align: (left, left),
      [*Library*], [*Primary Mathematical Role*],
      [`Main`], [Exports `Statements.lean` and `Main.lean` (the five headline theorems).],
      [`Formalism`], [Core definitions and master inequalities: `DivIneqObjU`, `HeightS` (`DivIneqTopAnchorU.lean`), `Formalism.HC.ZeroFreeAll`, `SharpRestriction`, `GaloisCohomology`, `HarderNarasimhan`, `MirabolicMackeyTheory`.],
      [`Development`], [Top-level proof assembly: `AutomorphicArithmetic` (`CharacterBoxes`, `MainConclusion.lean`, `ExistsPageN.lean`, `TopPlug.lean`, `VwinOfRow.lean`, `ThetaCorrespondence`), `AbelianVarietyTheory`, `AutomorphicSpectrum`, `WeilBound`, `DiscreteGroups`.],
      [`GroundTheory`], [Foundational theories: `ArithmeticGeometry`, `AutomorphicForms`, `Brauer`, `FunctionField`, `HeightsAndTheta`, `IdeleRoots`, `PAdicHodge`, `PowerSubgroups`, `ProfiniteCohomology`, `TateCohomology`.],
      [`GroundTheoryFields`], [Dedicated library for `GroundTheory.LocalFields` and `GroundTheory.GlobalFields` (split out with tuned `synthInstance.maxHeartbeats`).],
      [`CompanionTheory`], [Real Lie groups, discrete series exhaustion, unitary dual admissibility (`RealGroups`), $p$-adic cyclotomic Galois cohomology (`AutomorphicTheory`), and adelic spectral geometry (`SpectralGeometry`).],
      [`PositivityTheory`], [Arakelov positivity, Moriwaki bigness, arithmetic Hilbert–Samuel (`HilbertSamuelMoriwaki`), Deligne–Ribet, Nadel vanishing, Poincaré–Lelong, Bernstein–Zelevinsky classification, and Siegel Eisenstein series.],
      [`ReciprocityTheory`], [Toroidal compactification charts, chart restriction, Arakelov geometry bridges, and local–global reciprocity infrastructure.],
      [`Lemmata`], [Reusable analytical, algebraic, and combinatorial lemmas supporting the higher libraries.],
      [`Supplements`], [Auxiliary bridges, numeric estimates, and supplementary compatibility results.],
    )
    #v(0.25em)

    *Cross-Reference for Chapters 11–16:*
    - *Chapter 11:* `Main.lean`, `Statements.lean`, `ClaimStrip.lean`, `MainConclusion.lean`, `TopPlug.lean`, `EveryCharacterOfLiteratureOfVWin.lean`.
    - *Chapter 12:* `ZeroFreeAllOfTopG.lean`, `Imprimitive.lean`, `LevelGmLeOnFamilyScales.lean`, `Formalism/SharpRestriction/`.
    - *Chapter 13:* `ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, `BaseChangeIdentities/DefiniteNHolds.lean`, `WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/`.
    - *Chapter 14:* `ThirdPlaceSeries/Hyps.lean`, `ThirdPlaceSeries/DefiniteSideCondition.lean`, `Formalism/LocalToGlobal/`, `AbelianVarietyTheory/Proofs/DivisorProofs/CmCurveGoodOutsidePrime.lean`.
    - *Chapter 15:* `Formalism/DivisorInequality/DivIneqTopAnchorU.lean`, `ThirdPlaceSeries/TopCovolSlim2Use.lean`, `PositivityTheory/`, `HodgeBundleWeights/`.
    - *Chapter 16:* `CharacterBoxes/ExistsPageN.lean`, `CharacterBoxes/SupplyChi.lean`, `DenseThresholdCases/VwinOfRow.lean`, `CoprimeRanks/AdmChi.lean`, `ThetaCorrespondence/Linnik.lean`.
  ]

  #exercises((
    [*(From `DirichletLNonvanishingRightOfHalf` to `Claim.strip` and `Claim.zeta`.)* Let $chi$ be an imprimitive Dirichlet character modulo $N$ induced by a primitive character $chi^*$ of conductor $f | N$.
      (a) Verify that the Euler factor $1 - chi^*(p) p^(-s)$ has infinitely many zeros on the imaginary axis $op("Re")(s) = 0$ whenever $chi^*(p) != 0$, and explain why `Claim.prim_zero` requires $op("Re")(s) > 0$.
      (b) Complete the proof of `Claim.zeta` for $op("Re")(s) <= 0$ without using Mathlib's total-function convention for `Gamma`, by working directly with the poles of $Gamma_bb(R) (s) = pi^(-s/2) Gamma(s/2)$ at $s = 0, -2, -4, dots.c$.],
    [*(Primitive Reduction via `imprimitive`.)* Show that `Formalism.HC.ZeroFreeAll` (nonvanishing of $L(s, psi)$ in $op("Re")(s) > 1/2$ for every *primitive* Dirichlet character $psi$, except $psi = 1$ at $s = 1$) implies `DirichletLNonvanishingRightOfHalf` for *all* Dirichlet characters $chi$ modulo every $N >= 1$. Why can we not drop the condition $op("Re")(s) > 1/2$ in the implication?],
    [*(Galois Theory of `IsChiField`.)* Let $psi$ be a primitive Dirichlet character of conductor $N_psi$, let $e >= 1$, and let $(q, d)$ be distinct odd primes with $q equiv 3 mod 8$, $d equiv 7 mod 16$, and $gcd(q d, 2 N_psi) = 1$. Suppose $E$ satisfies `IsChiField psi e q d E`.
      (a) Express the degree $[E : bb(Q)]$ in terms of $e$, the order of $psi$, and the parity of $psi(-1)$ when $N = op("lcm")(2^(e+2), N_psi, q, d)$.
      (b) Prove that $E$ is totally real if and only if $psi(-1) = 1$ (check the value of $(-1/q)$ and $(-1/d)$ using $q equiv 3 mod 8$ and $d equiv 7 mod 16$).
      (c) Describe the Frobenius splitting of an odd prime $p <= Y^(epsilon/5)$ in the quadratic subfields $bb(Q)(sqrt(-q))$ and $bb(Q)(sqrt(-d))$ using the `WinPair` condition $p | d + 1$.],
    [*(Chebyshev–Linnik Feasibility of `WinPair`.)* Let $Z = Y^(epsilon/5)$ with $0 < epsilon < 1/52$, and let $M = 16 q product_(3 <= p <= Z, space p != q) p$ where $q$ is a prime with $1/2 Z < log q <= Z$.
      (a) Using Chebyshev's bound $theta(Z) = sum_(p <= Z) log p <= 2 Z$, show that $log M <= 3 Z + log 16$.
      (b) Assuming Linnik's theorem with constant $L_"Linnik" = 5$ (Xylouris's bound), find an explicit threshold $Y_0$ (in terms of $epsilon$) such that for all $Y >= Y_0$, we have $L_"Linnik" log M < 1/2 Y^(epsilon/5) (log Y)^2$.
      (c) Why is the extra factor $(log Y)^2$ in `WinPair.d_lo` so convenient compared to a mere constant multiple of $Y^(epsilon/5)$?],
    [*(Sub-Exponential Dominance in `DivIneqObjU`.)* Fix $epsilon = 1/60$, $L = x^epsilon$, $b = exp(L)$, and $a = x b$. Suppose $m = floor(sqrt(x))$, $k = floor(x^(1/4))$, $N = k + m$, $f = floor(x^(2 epsilon))$, and $log g = x^(3 epsilon)$.
      (a) Verify explicitly that each of the inequalities $m^3 N^2 L <= b$, $k N <= b$, $N^2 log g <= b$, and $N log(f N) <= b$ from `DivIneqTopAnchorU.lean` holds for all sufficiently large $x$.
      (b) Compute the asymptotic order of the ratio $(x^epsilon B_0) / (a L_a)$, where $B_0 = f m b x^epsilon$ and $L_a = log(a r_d)$ with $log r_d <= L$, and check that it tends to $0$ as a negative power of $x$.],
    [*(Convexity of the Stirling Function `ph`.)* Let $op("ph")(nu) = nu log nu - nu$ for $nu > 0$ (and $op("ph")(0) = 0$).
      (a) Show that $op("ph")$ is strictly convex on $[0, oo)$ and satisfies the superadditivity inequality $op("ph")(u + v) >= op("ph")(u) + op("ph")(v) + (u + v) log 2$ when $u = v$.
      (b) If $sum_(i=1)^r nu_i = A$ with $nu_i >= 0$, prove that
      $ A log(A / r) - A <= sum_(i=1)^r op("ph")(nu_i) <= op("ph")(A). $
      (c) Explain how this inequality clarifies the hypothesis $(sum_i op("ph")(nu_(j, rho, i))) - log H_(j, rho) <= op("ph")(a_T (rho)) + e_E (j, rho)$ in `DivIneqObjU`.],
    [*(Window Nesting and the Choice $lambda = 3/2$.)* In `TopPlug.lean`, `zeroFreeAll_of_topG` is called with `la := 3/2`, while `VWinAt` supplies a clean window $[Y, Y^2]$ inside $[X^(1/J), X]$.
      (a) Show that for every $Y >= 1$, the Mellin window $[Y, Y^(3/2)]$ is contained in $[Y, Y^2]$, and that for any $c > 0$ there exists $Y_1$ such that $[Y, c Y^(3/2)] subset.eq [Y, Y^2]$ for all $Y >= Y_1$.
      (b) What happens if one tries to take $lambda = 1$ in `zeroFreeAll_of_topG`? What happens if one takes $lambda = 5/2$ while keeping `VWinAt`'s window $[Y, Y^2]$ unchanged?],
    [*(The Selmer Budget $sqrt(b)$ vs. Classical Vandiver.)* In `VAt`, the log-weighted sum of Selmer lengths up to twist $t = floor(x^(401))$ is bounded by $B = sqrt(exp(x^epsilon)) = b^(1/2)$.
      (a) Suppose that for some number field $E$, the classical Vandiver conjecture failed at a prime $ell <= x^(10)$ with $ell$-part of the class number equal to $ell^r$. How large would $r$ have to be before this single prime alone violated `VVle E t B`?
      (b) Explain conceptually why replacing "zero $ell$-torsion for all $E$" (Vandiver) by "total log-weighted Selmer length $<= sqrt(b)$ on a clean window $[Y, Y^2]$" (`VWin`) makes the statement provable via automorphic density and Behrend's sphere theorem, while still being strong enough for `DivIneqObjU`.],
    [*(Analyzing `OpenLiteratureStatements`.)* Inspect the three fields of `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` in `EveryCharacterOfLiteratureOfVWin.lean`: `caraianiLocalGlobalDual`, `localLanglandsExists`, and `galoisRepOfPolarizedPairLit`.
      (a) Why are `caraianiLocalGlobalDual` and `galoisRepOfPolarizedPairLit` both discharged by the single theorem `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` in `MainConclusion.lean`?
      (b) Why does `vwin_of_row` also depend on that same local–global compatibility theorem, making `galoisLocalGlobalStrong_recParameter` the single most central foundational bridge in the entire proof DAG?],
  ))
]
