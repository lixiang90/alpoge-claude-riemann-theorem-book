// ============================================================================
// Appendix A: Module Map of the Lean 4 Formalization
// ============================================================================
#import "template.typ": appendix-chapter, theorem, proposition, lemma, remark, lean-note, insight-box, gtm-navy, gtm-accent, gtm-tint, gtm-rule

// Helper for compact, GTM-styled cross-reference tables
#let map-table(columns: (24%, 38%, 38%), header, ..rows) = {
  set text(size: 8.3pt)
  set par(justify: false, leading: 0.5em)
  table(
    columns: columns,
    stroke: (x: none, y: 0.35pt + luma(215)),
    fill: (_, y) => if y == 0 { gtm-tint } else if calc.odd(y) { white } else { rgb("#FAFBFD") },
    inset: (x: 5pt, y: 4.5pt),
    align: (left, left, left),
    table.header(..header.map(h => text(weight: "bold", fill: gtm-navy, size: 8.4pt)[#h])),
    ..rows,
  )
}

#let app-a() = [
  #appendix-chapter(
    "A",
    "Module Map of the Lean 4 Formalization",
    overview: [
      This appendix provides a comprehensive, structured cross-reference guide mapping every major mathematical theorem, definition, and conceptual pillar developed in Chapters 1–16 of this monograph to its exact Lean 4 file path and declaration name in the verified repository `leanprover-community/riemann-hypothesis`. We document the ten-library build architecture declared in `lakefile.toml` (spanning 149,217 `.lean` files), trace the complete logical spine from `Main.lean` down to the arithmetic, analytic, automorphic, geometric, and cohomological engines, and catalog both the three-field interface `OpenLiteratureStatements` and the sixty-plus classical literature theorems formalized from scratch in `EveryCharacterOfLiteratureOfVWin.lean`.
    ],
  )

  == Architectural Overview of the Ten Libraries

  The formal proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet $L$-functions in `leanprover-community/riemann-hypothesis` is organized in `lakefile.toml` into ten default build targets (together with a thin `Challenge` target used by external proof-checker harnesses such as `comparator`). All ten libraries compile against a single pinned revision of Mathlib (`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`) with strict elaboration flags (`autoImplicit = false`, `relaxedAutoImplicit = false`, `maxHeartbeats = 4000000`, `moreLeanArgs = ["--tstack=400000"]`). Across the entire dependency tree, the headline theorems in `Main.lean` depend exclusively on Lean 4's three standard logical axioms: propositional extensionality (`propext`), quotient soundness (`Quot.sound`), and the axiom of choice (`Classical.choice`).

  Conceptually, the ten libraries form a five-layer dependency hierarchy:
  + *Foundation Layer* (`GroundTheory`, `GroundTheoryFields`, `Lemmata`, `Supplements`): core definitions and reusable lemmas in local/global fields, profinite and Tate cohomology, Brauer groups, $p$-adic Hodge theory, arithmetic geometry, and Hermitian/matrix calculus.
  + *Classical Reciprocity and Companion Layer* (`ReciprocityTheory`, `CompanionTheory`, `PositivityTheory`): class field theory, Chebotarev density, geometry of numbers, $L^2$ $overline(partial)$-estimates, Harish-Chandra modules, real unitary groups, discrete series exhaustion, and the Stage-1 bridges for published theorems.
  + *Formalism Layer* (`Formalism`): the self-contained analytic, algebraic, geometric, and cohomological interface statements—including `ZeroFreeRegion`, `LandauZeroFreeBounds`, `FormalGroupLog`, `FormalGroupWitt`, `HarderNarasimhan`, `DivisorInequality` (`DivIneqObjU`, `HeightS`), and `GaloisCohomology` (`Sha`, `VFormula`).
  + *Development Layer* (`Development`): the main proving engine, comprising 121,214 files partitioned into seven major sub-libraries (`AbelianVarietyTheory`, `AutomorphicArithmetic`, `AutomorphicSpectrum`, `WeilBound`, `EtaleCohomology`, `ResolutionOfSingularities`, and `DiscreteGroups`).
  + *Entrypoint Layer* (`Main`): the public theorem statements (`Statements.lean`) matching Mathlib's `RiemannHypothesis` and their five-line derivations (`Main.lean`) from `UpperTheory.FinalTheorems.everyCharacter`.

  #map-table(
    columns: (22%, 11%, 23%, 44%),
    ([Library Target], [Files], [Book Chapters], [Primary Mathematical Role]),
    [`Main`], [2], [Ch. 1, 2, 11, 16], [Public statements (`Statements.lean`) and top-level proofs (`Main.lean`) of `riemannHypothesis`, `LFunction_ne_zero_of_half_lt_re`, and `LFunction_eq_zero_re`.],
    [`Development` / `AbelianVarietyTheory`], [81,319], [Ch. 8, 9, 13, 14], [CM curves, abelian schemes, dual abelian varieties, semistable reduction, toroidal compactifications, Arakelov Hilbert–Samuel, and `RankVal` global twisting.],
    [`Development` / `AutomorphicArithmetic`], [17,522], [Ch. 2, 7, 11–15], [Top-level proof spine: `CharacterBoxes`, `ThetaCorrespondence`, `AutomorphicVarieties/ModularityArgument`, `Foundations` (LLC, base change, Galois reps), and `CMTraceForms`.],
    [`Development` / `AutomorphicSpectrum`], [13,644], [Ch. 6, 7, 12], [Cuspidal spectrum of $op("GL")_n$, rapid decay on Siegel sets, geometric lemma, Iwasawa admissibility, and published algebraic/geometric/metric bridges.],
    [`Development` / `WeilBound`], [6,798], [Ch. 6, 7, 9, 12, 13], [Bernstein–Zelevinsky theory, generic unitary dual, Siegel–Weil formula, Siegel Eisenstein continuation, doubling method, Rallis inner product, Poitou–Tate, and Arakelov cycle heights.],
    [`Development` / `EtaleCohomology`], [1,307], [Ch. 10, 15], [Étale and $ell$-adic cohomology, crystalline comparison inputs, and cohomological descent for automorphic Galois representations.],
    [`Development` / `ResolutionOfSingularities`], [499], [Ch. 9, 14], [Characteristic-zero resolution of singularities and principalization of ideal sheaves supporting Arakelov intersection theory.],
    [`Development` / `DiscreteGroups`], [125], [Ch. 6, 12], [Global irreducibility and the local converse theorem for $op("GL")_n$ (`LConvFinal.lean`).],
    [`Formalism`], [15,292], [Ch. 5, 8–11, 14, 15], [All 88 formalized interface namespaces: Mellin–Landau bounds, zero-free regions, formal groups, Harder–Narasimhan slopes, `DivIneqObjU`, `HeightS`, and `GaloisCohomology`.],
    [`GroundTheory`], [6,176], [Ch. 6–10], [Ten foundational sub-trees: `ArithmeticGeometry`, `AutomorphicForms`, `Brauer`, `FunctionField`, `HeightsAndTheta`, `IdeleRoots`, `PAdicHodge`, `PowerSubgroups`, `ProfiniteCohomology`, `TateCohomology`.],
    [`GroundTheoryFields`], [491], [Ch. 8, 10], [`GroundTheory/LocalFields` and `GroundTheory/GlobalFields`, compiled with dedicated typeclass synthesis heartbeat budget (`400000`).],
    [`ReciprocityTheory`], [3,581], [Ch. 8, 9, 10], [Class field theory, Chebotarev density, adele approximation, dual lattices, geometry of numbers, $L^2$ $overline(partial)$-estimates, semistable reduction, and theta quasi-periods.],
    [`CompanionTheory`], [1,946], [Ch. 6, 7, 10, 12], [Real reductive groups, Harish-Chandra modules, discrete series exhaustion, Archimedean unitary dual, spectral geometry, and $p$-adic cyclotomic Galois cohomology.],
    [`PositivityTheory`], [355], [Ch. 6, 7, 12], [Automorphic positivity, Weil representations, Zariski density, unit annihilation, and Stage-1 `PublishedTheorems` assembly.],
    [`Lemmata`], [158], [Ch. 5–15], [Reusable algebraic, analytic, valuation, and matrix-determinant lemmas (including `DetMonotoneStarMulSelf`, `HermitianSesquilinear`, and `GeneralBFact` families).],
    [`Supplements`], [1], [Ch. 7, 12], [`Supplements/Kernels`: auxiliary kernel-construction helpers.],
  )

  #remark(title: "Total File Inventory")[
    Summing the ten default targets plus `Challenge.lean` yields $2 + 121214 + 15292 + 6176 + 491 + 3581 + 1946 + 355 + 158 + 1 + 1 = 149217$ `.lean` source files. The intentional split of `GroundTheoryFields` out of `GroundTheory` isolates heavy local/global field instance synthesis from the rest of the library, keeping incremental compilation tractable.
  ]

  == Table 1: Headline Theorems and the Logical Spine

  The entire proof executes as a clean linear cascade of implications at the top level. Starting from the unconditional construction of automorphic Galois representations with local-global compatibility (`galoisLocalGlobalStrong_recParameter`) and the existence of the Local Langlands Correspondence (`recTExists`), the library proves the weakened Vandiver window `VWin` (`vwin_of_row`), combines it with the sixty-plus formalized classical pillars (`every_character_of_literature_of_vWin`) to obtain nonvanishing of every Dirichlet $L$-function in $op("Re")(s) > 1\/2$ (`everyCharacter`), and deduces both GRH and RH via the functional equation (`Claim.strip`, `Claim.zeta`).

  #map-table(
    columns: (20%, 42%, 38%),
    ([Monograph Result], [Lean 4 File Path (under `src/`)], [Declaration & Chapter Ref.]),
    [Formal statement of RH & GRH], [`Statements.lean`], [`RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine` (Ch. 1, 2)],
    [Riemann Hypothesis (Mathlib)], [`Main.lean`], [`riemannHypothesis : RiemannHypothesis`, `riemannZeta_eq_zero_re` (Ch. 1, 16)],
    [Generalized RH (all Dirichlet $L$)], [`Main.lean`], [`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive` (Ch. 2, 16)],
    [Critical-strip reflection], [`Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`], [`Claim.prim_zero`, `Claim.prim_reflect`, `Claim.strip`, `Claim.zeta` (Ch. 2)],
    [Unconditional nonvanishing in $op("Re")(s) > 1\/2$], [`Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`], [`UpperTheory.FinalTheorems.everyCharacter`, `everyCharacter_of_row` (Ch. 11, 16)],
    [Master implication from literature + `VWin`], [`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`], [`UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (Ch. 11, 16)],
    [Weakened Vandiver window `VWin`], [`Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`], [`UpperTheory.One.vwin_of_row : RowT -> VWin` (Ch. 15)],
    [Definition of `VVle`, `WinPair`, `PageN`, `VWin`], [`Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean`], [`UpperTheory.Top.VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin`, `exists_pageN` (Ch. 10, 15, App. B)],
    [Window transfer $[W, W^2] -> [Z, Z^(3\/2)]$], [`Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean`], [`UpperTheory.Top.winPairs` (Ch. 11, 15, App. B)],
    [Rank-degree ceiling $t <= x^400$ for $epsilon < 1\/52$], [`Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`], [`UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo` (Ch. 11, App. B)],
    [Top-level zero-free implication], [`Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean`], [`UpperTheory.Top.TopG`, `zeroFreeAll_of_topG` (Ch. 11)],
    [Master divisor–slope & height inequalities], [`Formalism/DivisorInequality/DivIneqTopAnchorU.lean`], [`Formalism.DivisorInequality.DivIneqObjU`, `HeightS` (Ch. 14, App. B)],
    [Local-global compatibility anchor], [`Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`], [`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (Ch. 10, 15)],
    [Local Langlands existence anchor], [`Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`], [`UpperTheory.Zero.LLC.recTExists` (Ch. 6, 12)],
  )

  == Table 2: Analytic, Mellin–Landau, and Zero-Free Region Modules

  Chapters 1, 2, 5, and 11 reduce GRH to ruling out a putative zero $rho_0 = beta_0 + i gamma_0$ with $beta_0 > 1\/2$ by detecting a forced oscillation or sign-change in smoothed prime-power sums $S_a (x) = sum_(1 <= n <= x) a(n)(x\/n - 1)$ on a dyadic-polynomial window $[Z, Z^(3\/2)]$. The formalization builds the classical de la Vallée Poussin zero-free region, Landau's nonvanishing criterion, the Siegel–Walfisz theorem for arithmetic progressions, and the logarithmic-derivative bounds completely inside `Formalism/` and `Development/AutomorphicArithmetic/CharacterBoxes/`.

  #map-table(
    columns: (22%, 40%, 38%),
    ([Mathematical Concept], [Lean 4 Module Path (under `src/`)], [Key Declarations & Chapters]),
    [Classical zero-free region for $zeta(s)$], [`Formalism/ZeroFreeRegion/Statement.lean`, `FinalZFR.lean`], [`Formalism.ZF.ZeroFreeRegion`, `LogDerivRegion`, `GzPNT` (Ch. 1, 5)],
    [Dirichlet zero-free region & Siegel zero uniqueness], [`Formalism/LandauZeroFreeBounds/Statement.lean`, `FinalSiegel.lean`, `NoZeroComplex.lean`], [`Formalism.ZeroFreeDirichlet.InRegion`, `IsLZero`, `ZFRDirichlet` (Ch. 2, 5)],
    [Siegel–Walfisz theorem in arithmetic progressions], [`Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean`, `SiegelWalfiszAPOfSiegelLower.lean`], [Prime-counting asymptotics in reduced residue classes modulo $q <= (log x)^A$ (Ch. 2, 5, 11)],
    [Smoothed von Mangoldt function $G(y)$ & $S_a(x)$], [`Formalism/LocalRingCardinality/DataParams₂.lean`, `Formalism/WindowSums/`], [`Formalism.BasicNotions.Gfun`, `dlogL`, `chiK`, smoothed Mellin-window estimates (Ch. 5, 11)],
    [Scale & rank parameter packages], [`Formalism/LocalRingCardinality/DataParams₂.lean`, `Params.lean`], [`Formalism.BasicNotions.Scale`, `Ranks`, `HCParam`, `SizeData₂` (Ch. 11, App. B)],
    [Character boxes & half-plane reduction], [`Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean`, `EveryCharacter.lean`, `Imprimitive.lean`], [`HalfPlane`, `Strip`, `Zeta`, `UpperTheory.EveryCharacter`, primitive reduction (Ch. 2, 11)],
    [Real-split & box-selection lemmas], [`Development/AutomorphicArithmetic/CharacterBoxes/RealBox.lean`, `RealSplit.lean`, `ThinChoice.lean`, `DesWin.lean`], [Window extraction, real-splitting control, and thin-box selection (Ch. 11)],
    [Smallest prime & polynomial bounds], [`Development/AutomorphicArithmetic/CharacterBoxes/SmallestPrimePolynomialBound.lean`, `PairGood.lean`, `PairHyp.lean`], [Linnik-type prime-pair supply for `WinPair` construction (Ch. 11, 15)],
    [Mean-square & $op("GL")_3$ analytic bounds], [`Formalism/GL3MeanSquares/`, `Formalism/WeightedDeltaMeans/`, `Development/AutomorphicArithmetic/MeanSquareBounds/`], [Second-moment estimates and weighted delta-method bounds (Ch. 5, 11)],
    [Size-window brackets & log-sum-exp bounds], [`Formalism/SizeWindowBrackets/`, `Formalism/LogSumExpBounds/`, `Formalism/LFunctionBounds/`], [Archimedean $L$-function convexity and log-sum-exp inequalities (Ch. 5, 11, 14)],
    [Dedekind $L$-functions & Dirichlet density], [`Development/AutomorphicArithmetic/DedekindLFunctions/`, `Formalism/DirichletDensity/`], [Euler products, analytic continuation, and density of degree-$1$ primes (Ch. 2, 5)],
    [Zero-free nonvanishing on $op("Re")(s) = 1$], [`Formalism/ZetaNonvanishing/`, `Formalism/RealPlaceAnalysis/`], [Mertens-type nonvanishing and real-place archimedean bounds (Ch. 1, 5)],
  )

  == Table 3: Automorphic Spectrum, Theta Correspondence, and Unitary Group Modules

  Chapters 6, 7, 12, and 13 carry the core discovery of Alpöge and Claude: replacing the Frobenius-power derivative $D^m$ of Stepanov's method with a chain of $m approx sqrt(X)$ theta lifts between totally definite unitary groups $U(X_0) -> U(Y_1) -> dots.c -> U(X_m)$, whose nonvanishing is certified by the Rallis inner product formula and the doubling method, and whose Hecke eigenvalues synthesize "automorphic multiplicity" over $bb(Z)$. The supporting representation theory spans `Development/AutomorphicSpectrum`, `Development/WeilBound`, `Development/AutomorphicArithmetic/ThetaCorrespondence`, `CompanionTheory`, and `PositivityTheory`.

  #map-table(
    columns: (22%, 40%, 38%),
    ([Mathematical Concept], [Lean 4 Module Path (under `src/`)], [Key Declarations & Chapters]),
    [Cuspidal spectrum of $op("GL")_n$ & rapid decay], [`Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspRapidDecaySiegelGL.lean`, `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CuspFormsRapidDecay.lean`], [`GlobalTheory.RapidDecay.cuspRapidDecay`, `UpperTheory.V.Af.cuspSpectrumGL`, `RfCs.cuspidalSpectrumGL` (Ch. 6)],
    [Bernstein–Zelevinsky theory & segments], [`Development/WeilBound/CoreStatements/TemperedRepresentationTheory/BernsteinZelevinskyGL/`, `Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/`], [`PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`, `PositivityTheory.RgGu.segmentRepresentation`, `PositivityTheory.Exh.langlandsExhaustionGL_of_seg` (Ch. 6)],
    [Generic unitary dual & Bernstein irreducibility], [`Development/WeilBound/CoreStatements/AutomorphicKernels/UnitaryDualGL/`, `Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/`], [`PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds`, `PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible` (Ch. 6)],
    [Jacquet–Shalika rigidity & multiplicity one], [`Development/WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaRigidity/`, `SmoothVectorEstimates/CuspidalMultiplicityOne.lean`], [`PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity`, `PositivityTheory.jumpWindows.cuspidalMultiplicityOne` (Ch. 6)],
    [Local converse theorem for $op("GL")_n$], [`Development/DiscreteGroups/GlobalIrreducibility/LConvFinal.lean`], [`DiscreteGroups.sglob.LConv.localConverseGL` (Ch. 6)],
    [Base change for definite unitary groups], [`Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/DefiniteNHolds.lean`], [`UpperTheory.BaseChangeIdentities.baseChangeN`, `definiteN_of` (Ch. 6, 12)],
    [Real discrete series & Casselman–Wallach], [`CompanionTheory/RealGroups/DiscreteSeries/`, `CompanionTheory/RealGroups/UnitaryAdmissibility/`, `Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/`], [`CompanionTheory.RgExh.discreteSeriesClassification`, `CompanionTheory.RgDs.B.discreteSeriesUpqExists`, `PositivityTheory.CWB.casselmanWallach` (Ch. 6, 7)],
    [Weil representation & Kudla splitting], [`Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation/WeilEx.lean`, `WeilTheta.lean`, `Development/AbelianVarietyTheory/Proofs/DivisorProofs/KudlaSplittingSplitUnitary.lean`], [`UpperTheory.Lit.weilRepresentationExists_pair`, `GlobalTheory.weilRepresentationUnitaryPair`, `GlobalTheory.kudlaSplittingSplitUnitary` (Ch. 7)],
    [Howe duality & Fock models], [`Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/FockAnisoFree.lean`, `Formalism/FockGram/`, `Development/AbelianVarietyTheory/Proofs/DivisorProofs/HoweDualityRealHolds.lean`], [`GlobalTheory.howeDualityReal_holds`, `PositivityTheory.Stage1.PM.gLHoweDuality`, Fock Gram-matrix calculations (Ch. 7, 12)],
    [Siegel–Weil formula & Siegel Eisenstein series], [`Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/`, `Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/`], [`UpperTheory.Lit.Sw47.convergent`, `PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd`, `PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation` (Ch. 7)],
    [Doubling method & Rallis inner product], [`Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean`, `Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean`], [`ResidueKilled.dm_of_two`, `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm`, `PositivityTheory.ThKR.theoremK_head2` (Ch. 7, 12)],
    [Theta lift independence & supremum bounds], [`Formalism/ThetaLiftIndependence/`, `Formalism/LatticeTheta/`, `Formalism/ThetaSupremumBounds/`, `Formalism/ThetaLogCoordinates/`], [Linear independence of iterated theta lifts and archimedean theta sup-norm estimates (Ch. 12, 13)],
    [Mirabolic Mackey theory & Satake/Weyl duality], [`Formalism/MirabolicMackeyTheory/StatementT.lean`, `Formalism/SatakeDualWeyl/`, `Formalism/FormalDegreeBessel/`, `Formalism/PeriodIntegrals/`], [Mirabolic restriction, Satake dual Weyl characters, formal degrees, and period nonvanishing (Ch. 7, 12, 13)],
  )

  == Table 4: Complex Multiplication, Formal Groups, and Local Divisibility Modules

  Chapters 8 and 13 construct the integral test data that force high-order local divisibility at inert primes—the $p$-adic analogue of vanishing to order $m$ at every $bb(F)_q$-point in Stepanov's method. This relies on Lubin–Tate and Honda formal groups, the Artin–Hasse exponential, Witt-vector coordinates, complex multiplication of elliptic curves, Weber's ray class field theory, and Wach-module / crystalline lattice twists.

  #map-table(
    columns: (22%, 40%, 38%),
    ([Mathematical Concept], [Lean 4 Module Path (under `src/`)], [Key Declarations & Chapters]),
    [Formal group logarithms & functional equation lemma], [`Formalism/FormalGroupLog/Statement.lean`, `LogDeterminesLaw.lean`], [`Formalism.G.IsHom`, `IsLog`, `LogExistsUnique`, `IsFunEqType`, `FunEqGroup`, `FunEqHom` (Ch. 8)],
    [Formal groups over Witt vectors & weight invariance], [`Formalism/FormalGroupWitt/Statement.lean`, `SubstInjectiveV.lean`, `WeightInvariance.lean`], [Honda/Witt formal group coordinates and $p$-adic valuation invariance (Ch. 8)],
    [Artin–Hasse exponential & $p$-adic integrality], [`Formalism/ArtinHasse/`], [Integrality of the Artin–Hasse series and local formal-group exponentials (Ch. 8)],
    [CM elliptic curves, good reduction, & main theorem of CM], [`Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmCurveGoodOutsidePrime.lean`, `HcfjHolds.lean`], [`PositivityTheory.Prw.ellipticMainTheoremCM_holds`, `GlobalTheory.Published.cmCurveGoodOutsidePrime`, `GlobalTheory.Laid.hcfj_holds`, `PositivityTheory.Prw.weberRayFieldSt_holds` (Ch. 8, 13)],
    [Elliptic torsion, CM types, & Galois action], [`Formalism/EllipticTorsion/`, `Formalism/CMTypeGalois/`, `Formalism/TorsionNormIteration/`], [Torsion-point norms, CM-type reflex fields, and iterated norm divisibility (Ch. 8, 13)],
    [Gauss jets, valuation bounds, & Möbius jet duality], [`Formalism/GaussJetBounds/`, `Formalism/GaussValuationBounds/`, `Formalism/GaussIdealIdentity/`, `Formalism/MoebiusJetDuality/`], [Taylor/jet valuations at inert primes and divisibility gain $F_0$ (Ch. 8, 13, 14)],
    [CM trace forms & trace embeddings], [`Development/AutomorphicArithmetic/CMTraceEmbeddings/`, `Development/AutomorphicArithmetic/CMTraceForms/`], [Hermitian trace pairings on CM orders and local lattice discriminants (Ch. 8, 13)],
    [Abelian schemes, duality, & Grothendieck–Messing], [`Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbelianSchemeHomLiftingNilpotentDividedPowers.lean`, `GrothendieckDeformationOfLifting.lean`, `DualAbelianSchemeExistsBiduality.lean`], [`GlobalTheory.dualAbelianScheme`, `GlobalTheory.Published.grothendieckDeformation_of_lifting`, `GrothendieckDeformation.grothendieckMessing` (Ch. 8, 9)],
    [Semistable reduction & abelian de Rham duality], [`Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemistableReductionPpavPadicField.lean`, `Development/WeilBound/CoreStatements/AutomorphicKernels/DualAbelianScheme/`], [`GlobalTheory.SS.semistableReductionSt`, `PositivityTheory.DualRT.abelianDeRham` (Ch. 8, 9)],
    [Wach modules & integral crystalline lattices], [`Formalism/WachLatticeTwists/`, `Formalism/WachModuleLifts/`, `GroundTheory/PAdicHodge/`, `Development/AutomorphicArithmetic/ThetaCorrespondence/PrismaticDieudonne/`], [`GlobalTheory.BSP.bhattScholzeIntegral`, `UpperTheory.Lit.prismaticDieudonneHodge`, Wach-lattice twist estimates (Ch. 8, 10)],
  )

  == Table 5: Arakelov Geometry, Harder–Narasimhan Slopes, and Divisor Inequality Modules

  Chapters 9 and 14 translate local divisibility at inert primes into a global contradiction via Arakelov geometry and Jean-Benoît Bost's slope inequality. In Lean 4, the Hermitian lattice engine lives in `Formalism/HarderNarasimhan/` and `Formalism/HermitianLattices/`, culminating in the master propositions `DivIneqObjU` and `HeightS` in `Formalism/DivisorInequality/DivIneqTopAnchorU.lean`. The higher-dimensional Arakelov covolume machinery—arithmetic Hilbert–Samuel, Moriwaki bigness, Poincaré–Lelong, Nadel vanishing, toroidal compactifications, and characteristic-zero resolution of singularities—is proved from scratch across `Development/WeilBound`, `Development/AbelianVarietyTheory`, and `Development/ResolutionOfSingularities`.

  #map-table(
    columns: (22%, 40%, 38%),
    ([Mathematical Concept], [Lean 4 Module Path (under `src/`)], [Key Declarations & Chapters]),
    [Hermitian lattices, Arakelov degree, & HN filtration], [`Formalism/HarderNarasimhan/Statement.lean`, `DegSupermodZ.lean`, `QuotRealize.lean`, `ShiftInvariance.lean`], [`Formalism.HN.deg`, `rk`, `slope`, `muMax`, `muMin`, `hnStep`, `slopeList`, `hnPoly`, `DegSupermod`, `MuChar`, `HNStep`, `HNSlopes` (Ch. 9)],
    [Master divisor–slope inequality & height bound], [`Formalism/DivisorInequality/DivIneqTopAnchorU.lean`], [`Formalism.DivisorInequality.DivIneqObjU`, `HeightS` (Ch. 14, App. B)],
    [Quotient metrics, branch-sandwich & pairing divisors], [`Formalism/QuotientMetricDivisors/RatHermLcvTwist.lean`, `Formalism/BranchSandwichDivisors/`, `Formalism/PairingDivisors/`], [Quotient Hermitian metrics `IsQuotMetric`, rational Hermitian twists, and divisor sandwiching (Ch. 9, 14)],
    [Log-factorial indices & Stirling function $op("ph")(nu)$], [`Formalism/LogFactorialIndices/StatementSize.lean`, `Formalism/LogFactorialBounds/`, `Formalism/LogVandermondeBounds/`], [`Formalism.LatticeIndexTer.ph`, Vandermonde/Stirling bounds on lattice indices (Ch. 14, App. B)],
    [Hermitian curvature, successive minima, & height descent], [`Formalism/HermitianCurvature/`, `Formalism/LatticeSlopes/`, `Formalism/SuccessiveMinima/`, `Formalism/MeanHeightDescent/`], [Bost slope-inequality estimates, Minkowski successive minima, and mean-height descent (Ch. 9, 14)],
    [Arakelov intersection theory & cycle heights], [`Development/WeilBound/CoreStatements/TemperedRepresentationTheory/ArakelovCycleHeights/`, `ChernDegreeComplex/`, `PoincareLelong/`], [`GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct`, `cycleHeights_direct`, `PositivityTheory.Tls2.Pl.poincareLelongInv` (Ch. 9)],
    [Arithmetic Hilbert–Samuel & Moriwaki bigness], [`Development/AbelianVarietyTheory/Proofs/DivisorProofs/ArithHilbertSamuelOfPrincipalisation.lean`, `VolGeOfHilbertSamuel.lean`, `Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/`], [`GlobalTheory.arithHilbertSamuel_of_principalisation`, `PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright` (Ch. 9, 14)],
    [Nadel vanishing, Kawamata–Viehweg, & $L^2$ extension], [`Development/WeilBound/CoreStatements/AutomorphicKernels/NadelVanishing/`, `Development/AbelianVarietyTheory/Proofs/DivisorProofs/KawamataViehwegOfNadelVanishingPair.lean`, `L2ExtensionLogCanonical.lean`], [`NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor`, `GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair`, `GlobalTheory.l2ExtensionLogCanonical'` (Ch. 9)],
    [Toroidal compactifications of Siegel varieties], [`Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToroidalCompactificationHolds.lean`, `SiegelToroidalIntegralHolds.lean`, `ToroidalCompactificationFanLogKodairaSpencerIso.lean`], [`GlobalTheory.toroidalCompactification_holds`, `GlobalTheory.siegelToroidalIntegral_holds`, `GlobalTheory.TorKSField.toroidalForFanKS` (Ch. 9, 13)],
    [Resolution of singularities & principalization], [`Development/ResolutionOfSingularities/`, `Development/WeilBound/CoreStatements/ResolutionCharZero/`], [`PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero`, `PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed` (Ch. 9)],
  )

  == Table 6: Galois Cohomology, Poitou–Tate Duality, and Iwasawa/Behrend Modules

  Chapters 10 and 15 establish the weakened Vandiver window `VWin`: on every cyclotomic-quadratic host field $E$ in a `WinPair` family, the weighted sum of $bb(Z)_ell$-lengths of the Tate–Shafarevich kernels $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ for $1 <= e < floor(x^401)$ is bounded by $sqrt(exp(x^epsilon))$. This combines profinite Galois cohomology, local and global Tate duality, the Poitou–Tate nine-term exact sequence, the Greenberg–Wiles Euler characteristic formula, Fontaine–Berger $p$-adic Hodge theory, and the Behrend sphere / modularity-threshold argument in `AutomorphicVarieties/ModularityArgument/`.

  #map-table(
    columns: (22%, 40%, 38%),
    ([Mathematical Concept], [Lean 4 Module Path (under `src/`)], [Key Declarations & Chapters]),
    [Tate–Shafarevich kernel `Sha` & length `shaLen`], [`Formalism/GaloisCohomology/Statement.lean`, `StatementLoc.lean`, `LocalTateDualityK.lean`], [`Formalism.GaloisCohomology.LData`, `QZ`, `qzTw`, `zlTw`, `Sha`, `shaLen` (Ch. 10, 15)],
    [Local Tate duality & local Euler characteristic], [`CompanionTheory/AutomorphicTheory/PadicCyclotomicFields/GcohTop.lean`, `GcohTopEuler.lean`, `Development/AbelianVarietyTheory/Proofs/DivisorProofs/LoceulerHolds.lean`], [`CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate`, `top_euler`, `top_locfin`, `GlobalTheory.LocalDualityAll.localTateDuality` (Ch. 10)],
    [Poitou–Tate nine-term exact sequence & global Euler char], [`Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/`, `GlobalEulerCharacteristic/`, `GlobalFiniteness/`], [`PositivityTheory.Lit1.PTN.poitouTateNormalised_holds`, `PositivityTheory.Lit1.GEN.globalEulerChar_full`, `PositivityTheory.Lit1.GF.globalFiniteness` (Ch. 10)],
    [Greenberg–Wiles formula & Bloch–Kato local conditions], [`Development/AutomorphicArithmetic/ThetaCorrespondence/GaloisRepresentations/GreenbergWiles.lean`, `BlochKatoLocal.lean`, `Development/AutomorphicArithmetic/BlochKatoExtensions/`], [`UpperTheory.Lit.greenbergWiles`, `UpperTheory.Lit.blochKatoLocal` (Ch. 10)],
    [Fontaine's $B_"cris"$ & Berger's de Rham $->$ pot. semistable], [`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineBcrisBasicTheoremsProof.lean`, `DeRhamPotentiallySemistable.lean`], [`GlobalTheory.MemLoc.fontaineBcris`, `GlobalTheory.deRham_potentiallySemistable` (Ch. 10)],
    [Hecke $ell$-adic characters (de Rham & crystalline)], [`Development/AutomorphicArithmetic/ThetaCorrespondence/GaloisRepresentations/HeckeDeRham.lean`, `AlgebraicCharacters/AlgebraicCharacterWD.lean`], [`UpperTheory.Lit.heckeLAdicCharacterDeRham`, `UpperTheory.Lit.CharWD.algebraicCharacterWD`, `UpperTheory.Lit.heckeLAdicCharacterCrystalline_of_deRham` (Ch. 10, 15)],
    [Cyclotomic norms, tame inertia, & tower valuations], [`Formalism/CyclotomicNorms/`, `Formalism/TameInertiaTowers/`, `Formalism/TowerValuationBounds/`, `Formalism/ConjugateSelfDual/`], [Cyclotomic-quadratic Iwasawa tower structure and tame ramification control (Ch. 10, 15)],
    [Sharp restriction & totient Galois classes], [`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean`, `TopDefs.lean`], [Frobenius-orbit separation and Behrend-type sphere bounds (Ch. 10, 15)],
    [Modularity threshold argument & `VWin` proof], [`Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, `TopMainZj.lean`], [`UpperTheory.One.vwin_of_row`, `UpperTheory.One.Join.automorphic_window_of_inputs` (Ch. 15)],
    [Profinite & Tate cohomology foundations], [`GroundTheory/ProfiniteCohomology/`, `GroundTheory/TateCohomology/`, `GroundTheory/Brauer/`, `ReciprocityTheory/GroupCohomology/`], [Continuous cochains, inflation-restriction, cup products, and Brauer invariants (Ch. 10)],
    [Global Artin reciprocity & ray class fields], [`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlobalArtinReciprocityHolds.lean`, `ReciprocityTheory/ClassFieldTheory/`, `ReciprocityTheory/Chebotarev/`], [`GlobalTheory.globalArtinReciprocity_holds`, `PositivityTheory.Stage1.PM.rayClassFieldSt`, `GlobalTheory.Published.chebotarevDegreeOne'` (Ch. 10)],
  )

  == Table 7: Published Classical Pillars Formalized from Scratch

  One of the most striking engineering achievements of `leanprover-community/riemann-hypothesis` is that it contains *zero* `sorry` statements and *zero* custom mathematical axioms: every classical theorem invoked by the proof—spanning sixty years of modern number theory, representation theory, complex geometry, and arithmetic geometry—is proved from scratch inside the repository.

  To keep the top-level proof modular, the file
  `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`
  defines a three-field structure `UpperTheory.LiteratureTheorems.OpenLiteratureStatements`:

  #lean-note(
    title: "The Three-Field Interface Record",
    module: "EveryCharacterOfLiteratureOfVWin.lean, lines 220–223",
  )[
    ```lean
    structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
      caraianiLocalGlobalDual     : UpperTheory.One.M.Row
      localLanglandsExists        : UpperTheory.Zero.LLC.RecTExists
      galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row
    ```
    In `MainConclusion.lean` (lines 48–54), all three fields are discharged unconditionally by `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (Caraiani / Shin / Harris–Taylor local-global compatibility for polarized regular algebraic cuspidal automorphic representations) and `UpperTheory.Zero.LLC.recTExists` (Harris–Taylor / Henniart Local Langlands Correspondence for $op("GL")_n$).
  ]

  From `OpenLiteratureStatements` together with standalone internal proofs, `EveryCharacterOfLiteratureOfVWin.lean` assembles over eighty named literature theorems into eight structured record bundles (`literature_local`, `literature_automorphy`, `literature_cohomology`, `published_results_analytic`, `published_results_local`, `published_results_eigen`, `published_results_first`, and `published_results_arithmetic`). Table 7 catalogs the sixty-plus principal pillars by mathematical domain.

  #map-table(
    columns: (24%, 38%, 38%),
    ([Domain & Classical Theorem], [Lean 4 Wrapper in `EveryCharacterOfLiteratureOfVWin.lean`], [Underlying Proof Declaration]),
    [*Local & Global $op("GL")_n$ Representation Theory*], [], [],
    [Bernstein–Zelevinsky finiteness], [`bernstein_zelevinsky_finiteness_of_literature`], [`PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds`],
    [Bernstein unitary product irreducibility], [`bernstein_unitary_product_irreducible_of_literature`], [`PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible`],
    [Zelevinsky polynomial ring structure], [`zelevinsky_polynomial_ring_of_literature`], [`PositivityTheory.Prw.zelevinskyPolynomialRing_of`],
    [Geometric lemma & filtration], [`geometric_restriction_of_literature`, `geometric_restriction_filtration_of_literature`], [`GlobalTheory.CompanionTheory.GeoLink.geometricLemma`, `GlobalTheory.geometricLemmaFiltration_holds`],
    [Langlands classification & exhaustion], [`langlands_exhaustion_gl_of_literature`, `langlands_multisegments_of_literature`, `standard_cosocle_gl_of_literature`], [`PositivityTheory.Exh.langlandsExhaustionGL_of_seg`, `langlandsMultisegments_of_seg`, `standardCosocleGL_of_seg`],
    [Generic unitary dual of $op("GL")_n$ (Tadić)], [`generic_unitary_dual_gl_of_literature`, `generic_unlinked_gl_of_literature`], [`PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds`, `GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2`],
    [Moy–Prasad Jacquet isomorphism & depth-zero theory], [`moy_prasad_jacquet_iso_of_literature`, `depth_zero_induction_of_literature`, `depth_zero_jacquet_injective_of_literature`], [`PositivityTheory.Prw.moyPrasadJacquetIso_holds`, `GlobalTheory.DepthZeroPass.depthZeroInduction`, `GlobalTheory.DepthZeroJac.depthZeroJacquetInjective`],
    [Green's characters of $op("GL")_n (bb(F)_q)$], [`green_cuspidal_of_literature`, `green_regular_characters_of_literature`, `green_series_st_of_literature`], [`PositivityTheory.Stage1.PM.greenCuspidal`, `greenRegularCharacters`, `PositivityTheory.Prw.greenSeriesSt_of`],
    [Local converse theorem (Henniart / Jacquet–Liu)], [`local_converse_gl_of_literature`], [`DiscreteGroups.sglob.LConv.localConverseGL`],
    [Jacquet–Shalika bounds & strong multiplicity one], [`jacquet_shalika_of_literature`, `jacquet_shalika_rigidity_of_literature`, `cuspidal_multiplicity_one_of_literature`], [`PositivityTheory.AdelicQuotientData.jacquetShalika`, `jacquetShalikaRigidity`, `PositivityTheory.jumpWindows.cuspidalMultiplicityOne`],
    [Gelfand–Kazhdan contragredient duality], [`gelfand_kazhdan_dual_of_literature`], [`PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity`],
    [Flath tensor-product factorization], [`flath_tensor_product_of_literature`, `flath_factorisation_of_literature`], [`CompanionTheory.Rg.Fl.B.flathTensorProduct`, `PositivityTheory.Prw.flathFactorisation_of`],
    [Borel–Casselman & Schur orthogonality], [`borel_casselman_of_literature`, `schur_orthogonality_square_integrable_of_literature`], [`PositivityTheory.Stage1.PM.borelCasselman`, `schurOrthogonalitySquareIntegrable`],
    [Clozel purity & cohomological automorphy], [`clozel_purity_of_literature`, `clozel_cohomological_of_literature`, `regular_algebraic_purity_of_literature`], [`PositivityTheory.Lit1.ClozelPurity.clozelPurity`, `PositivityTheory.Rg.Cz.clozelCohomological`, `GlobalTheory.regularAlgebraicPurity_of_clozel`],
    [Base change for definite unitary groups (Labesse)], [`base_change_isobaric`, `base_change_definite_unitary_group_of_literature`], [`UpperTheory.BaseChangeIdentities.baseChangeN`, `definiteN_of`],
    [*Real Groups, Theta Lifts, & Automorphic Forms*], [], [],
    [Harish-Chandra modules, finiteness, & analyticity], [`harish_chandra_modules_of_literature`, `harish_chandra_finite_of_literature`, `harish_chandra_analyticity_of_literature`], [`PositivityTheory.Stage1.PM.harishChandraModules`, `PositivityTheory.RgHf.harishChandraFinite`, `GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density`],
    [Casselman–Wallach globalization], [`casselman_wallach_of_literature`, `gk_globalisation_of_literature`], [`PositivityTheory.CWB.casselmanWallach`, `GlobalTheory.gkGlobalisation_holds`],
    [Discrete series classification & formal degrees], [`discrete_series_classification_of_literature`, `discrete_series_upq_exists_of_literature`, `holomorphic_discrete_series_of_literature`, `formal_degree_compact_dual_of_literature`], [`CompanionTheory.RgExh.discreteSeriesClassification`, `CompanionTheory.RgDs.B.discreteSeriesUpqExists`, `GlobalTheory.HolDS.holomorphicDiscreteSeries_holds`, `PositivityTheory.RgFd.B.formalDegreeCompactDual`],
    [Dixmier–Malliavin factorization & trace-class cusp operators], [`dixmier_malliavin_factorisation_of_literature`, `cusp_trace_class_of_literature`], [`GlobalTheory.dixmierMalliavinFactorisation_fromLibrary`, `PositivityTheory.Prw.cuspTraceClass_of`],
    [Rapid decay & Sobolev bounds on cusp forms], [`cusp_rapid_decay_of_literature`, `cusp_decay_sobolev_of_literature`, `cusp_bounded_of_literature`], [`GlobalTheory.RapidDecay.cuspRapidDecay`, `PositivityTheory.Stage1.PM.cuspDecaySobolev`, `cuspBounded`],
    [Stone–von Neumann & metaplectic / Weil representation], [`stone_von_neumann_of_literature`, `metaplectic_representation_of_literature`, `real_metaplectic_representation_of_literature`, `weil_representation_unitary_pair_of_literature`], [`PositivityTheory.Stage1.PM.stoneVonNeumann`, `GlobalTheory.metaplecticRepresentation_holds`, `PositivityTheory.Stage1.PM.realMetaplecticRepresentation`, `GlobalTheory.weilRepresentationUnitaryPair`],
    [Kudla splitting & Howe duality (real & $op("GL")$)], [`kudla_splitting_split_unitary_of_literature`, `howe_duality_real_of_literature`, `gl_howe_duality_of_literature`], [`GlobalTheory.kudlaSplittingSplitUnitary`, `GlobalTheory.howeDualityReal_holds`, `PositivityTheory.Stage1.PM.gLHoweDuality`],
    [Siegel–Weil formula (unitary convergent & Schrödinger)], [`siegel_weil_unitary_convergent_of_literature`, `weil_siegel_formula_unitary_of_literature`, `siegel_weil_unitary_schrodinger_of_literature`, `siegel_weil_std_of_literature`], [`UpperTheory.Lit.Sw47.convergent`, `Sw47.weilUnitary`, `PositivityTheory.SiegelWeilCoefficients.field`, `PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd`],
    [Siegel Eisenstein continuation, doubling, & Rallis inner product], [`siegel_eisenstein_continuation_of_literature`, `doubling_method`, `unramified_doubling_gl_of_literature`, `rallis_inner_product_convergent_of_literature`], [`PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation`, `ResidueKilled.dm_of_two`, `GlobalTheory.UnramDoublingProof.unramifiedDoublingGL`, `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm`],
    [Strong approximation for $op("SU")$ & Hermitian Hasse–Landherr], [`strong_approx_su_of_literature`, `hermitian_hasse_principle_of_literature`, `hasse_norm_st_of_literature`, `landherr_st_of_literature`], [`GlobalTheory.StrongApproxSUProof.strongApproxSU`, `PositivityTheory.Stage1.PM.hermitianHassePrinciple`, `GlobalTheory.QNorm.hasseNormSt`, `landherr_and_landherrSt`],
    [*Algebraic, Complex, & Arakelov Geometry*], [], [],
    [Hironaka resolution of singularities & principalization], [`resolution_char_zero_of_literature`, `principalisation_of_literature`, `principalisation_char_zero_of_literature`], [`PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero`, `PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed`],
    [Poincaré–Lelong, Chern–Weil, & Arakelov calculus], [`poincare_lelong_inv_of_literature`, `good_chern_weil_of_literature`, `ar_calc_of_literature`, `ar_degree_of_literature`, `cycle_heights_of_literature`], [`PositivityTheory.Tls2.Pl.poincareLelongInv`, `GlobalTheory.GoodMetric.goodChernWeil`, `ArakelovDirectHeights.arCalc_direct`, `cycleHeights_direct`],
    [Arithmetic Hilbert–Samuel & Moriwaki bigness], [`arith_hilbert_samuel_of_literature`, `vol_ge_of_literature`, `vol_nef_of_literature`, `nef_rr_of_literature`, `nef_numerics_of_literature`], [`GlobalTheory.arithHilbertSamuel_of_principalisation`, `GlobalTheory.VolBr.volGe_of_hilbertSamuel`, `PositivityTheory.Tls2.Nef.nefRR`, `GlobalTheory.nefNumerics_outright`],
    [Nadel vanishing, Kawamata–Viehweg, & Ohsawa–Takegoshi $L^2$], [`nadel_vanishing_and_non_klt_divisor_of_literature`, `kawamata_viehweg_of_literature`, `l2_extension_log_canonical_of_literature`, `point_separation_pair_of_literature`], [`NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor`, `GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair`, `GlobalTheory.l2ExtensionLogCanonical'`],
    [Toroidal compactification & Siegel integral models], [`toroidal_compactification_of_literature`, `siegel_toroidal_integral_of_literature`, `toroidal_for_fan_ks_of_literature`], [`GlobalTheory.toroidalCompactification_holds`, `GlobalTheory.siegelToroidalIntegral_holds`, `GlobalTheory.TorKSField.toroidalForFanKS`],
    [Abelian schemes, Grothendieck–Messing, semistable reduction, Zarhin, Fargues], [`dual_abelian_scheme_of_literature`, `grothendieck_messing_of_literature`, `semistable_reduction_st_of_literature`, `zarhin_statement`, `fargues_exact_of_literature`], [`GlobalTheory.dualAbelianScheme`, `GrothendieckDeformation.grothendieckMessing`, `GlobalTheory.SS.semistableReductionSt`, `PositivityTheory.HtPt.Narrow.zarhin`, `UpperTheory.Lit.farguesExact`],
    [Formal algebraization & Chow forms], [`formal_algebraisation_of_literature`, `chow_form_exists_of_literature`, `serre_holomorphic_sections_of_literature`], [`PositivityTheory.FormalThickening.formalAlgebraisation`, `GlobalTheory.Published.chowFormExists_holds`, `serreHolomorphicSections_holds`],
    [*Galois Cohomology, Class Field Theory, & $p$-adic Hodge*], [], [],
    [Global Artin reciprocity, ray class fields, Chebotarev, Linnik], [`global_artin_reciprocity_of_literature`, `ray_class_field_st_of_literature`, `chebotarev_degree_one_of_literature`, `linnik_of_literature`], [`GlobalTheory.globalArtinReciprocity_holds`, `PositivityTheory.Stage1.PM.rayClassFieldSt`, `GlobalTheory.Published.chebotarevDegreeOne'`, `UpperTheory.Lit.linnik`],
    [Hecke–Tate functional equation & Deligne–Ribet], [`heckeTateFunctionalEquation'`, `hecke_l_entire_and_nonzero_at_one_of_literature`, `deligne_ribet_of_literature`, `siegel_klingen_deligne_ribet_of_literature`], [`GlobalTheory.Top.heckeTateFE`, `PositivityTheory.Stage1.PM.heckeLEntireAndNonzeroAtOne`, `PositivityTheory.PfDR.deligneRibet_holds`],
    [Poitou–Tate duality, local Tate, & Greenberg–Wiles], [`poitou_tate_normalised_of_literature`, `local_tate_duality_of_literature`, `global_euler_char_of_literature`, `greenberg_wiles_of_literature`], [`PositivityTheory.Lit1.PTN.poitouTateNormalised_holds`, `GlobalTheory.LocalDualityAll.localTateDuality`, `PositivityTheory.Lit1.GEN.globalEulerChar_full`, `UpperTheory.Lit.greenbergWiles`],
    [Fontaine $B_"cris"$, Berger, Bloch–Kato, Bhatt–Scholze], [`fontaine_bcris_of_literature`, `de_rham_pot_semistable_of_literature`, `bloch_kato_local_of_literature`, `bhatt_scholze_integral_of_literature`, `prismatic_dieudonne_hodge_of_literature`], [`GlobalTheory.MemLoc.fontaineBcris`, `GlobalTheory.deRham_potentiallySemistable`, `UpperTheory.Lit.blochKatoLocal`, `GlobalTheory.BSP.bhattScholzeIntegral`, `UpperTheory.Lit.prismaticDieudonneHodge`],
    [Main theorem of CM & Hilbert class field via $j$-invariant], [`ellipticMainTheoremCM'`, `hilbertClassFieldJ'`, `weber_ray_field_st_of_literature`, `cm_curve_good_outside_prime_st_of_literature`], [`PositivityTheory.Prw.ellipticMainTheoremCM_holds`, `GlobalTheory.Laid.hcfj_holds`, `PositivityTheory.Prw.weberRayFieldSt_holds`, `GlobalTheory.Published.cmCurveGoodOutsidePrime`],
    [Weyl branching, lowest alcove, & Radford shuffle], [`weyl_branching_of_literature`, `induced_simple_lowest_alcove_of_literature`, `radford_shuffle_polynomial_of_literature`], [`PositivityTheory.Stage1.PM.weylBranching`, `GlobalTheory.Alc.inducedSimpleLowestAlcove`, `PositivityTheory.Stage1.PM.radfordShufflePolynomial`],
  )

  == Navigating and Auditing the Repository

  Readers who wish to inspect or independently verify any link in the formal proof can follow a four-step audit workflow directly against a local clone of `leanprover-community/riemann-hypothesis`:

  + *Fetch precompiled `.olean` artifacts*: run `lake exe cache get` (backed by the S3 cache configured in `lakefile.toml`) to download compiled binaries for all ten libraries without rebuilding 17 million lines of Lean from source.
  + *Verify the top-level axioms*: open a scratch file importing `Main` and evaluate
    `#print axioms riemannHypothesis` and `#print axioms LFunction_eq_zero_re`.
    Both print strictly `[propext, Classical.choice, Quot.sound]`.
  + *Cross-check the statement against Mathlib*: inspect `src/Statements.lean` (20 lines) and `src/Main.lean` (56 lines) to confirm that `RiemannHypothesis` is Mathlib's unmodified `RiemannHypothesis` definition from `Mathlib.NumberTheory.LSeries.DirichletContinuation`, and that `DirichletLZerosOnLine` quantifies over all $N >= 1$ and all Dirichlet characters $chi : (bb(Z) \/ N bb(Z))^times -> bb(C)^times$.
  + *Trace any chapter result via `Formalism/`*: because every major mathematical pillar has a clean, human-readable `Statement.lean` (or `DivIneqTopAnchorU.lean`, `ExistsPageN.lean`, `DataParams₂.lean`) inside `Formalism/` or `CharacterBoxes/`, one can verify the exact mathematical hypotheses and conclusions in minutes before descending into the machine-checked proofs in `Development/`.

  #insight-box(title: "Why the Ten-Library Split Matters for Human Readers")[
    Although the repository contains 149,217 files, fewer than 100 *interface files*—principally `Statements.lean`, `Main.lean`, `MainConclusion.lean`, `EveryCharacterOfLiteratureOfVWin.lean`, `ExistsPageN.lean`, `DataParams₂.lean`, `Params.lean`, and `DivIneqTopAnchorU.lean`—carry the entire conceptual architecture of the proof. The remaining 99.9% of the codebase consists of granular, parallelizable proof steps discharging those interfaces. Reading the interface files alongside Chapters 11–15 of this monograph gives complete command of the proof's logical skeleton.
  ]
]
