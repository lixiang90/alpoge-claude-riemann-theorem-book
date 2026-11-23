#import "style.typ": *
#let sub(body) = block(above: 9pt, below: 4pt, sticky: true)[#text(size: 13.2pt, weight: "bold")[#body]]
#front[Notation and source concordance]

#sub[Notation]

#table(columns: (1.1fr, 3fr), inset: (x: 3pt,y: 3.4pt), stroke: none,
  table.hline(stroke: 0.7pt), [*Symbol*], [*Meaning in the proof*], table.hline(stroke: 0.4pt),
  [$x, Y, X$], [Point of evaluation, start of a good interval, outer scale.],
  [$epsilon,theta$], [Allowed arithmetic loss and exponent in the zero-free test.],
  [$Lambda(n), S_chi$], [Von Mangoldt weight and the uncentered ramp sum.],
  [$G_z,g_chi,F_psi$], [Centered untwisted ramp, complex character ramp, fixed real family.],
  [$q,d$], [Auxiliary primes giving the two quadratic signs.],
  [$E slash F, Phi$], [CM extension and its chosen CM type.],
  [$H,A_0$], [Abelian factor of the host group and its averaging subgroup.],
  [$T,T_2$], [Top places with prescribed shares and the separated thick set.],
  [$n,f,d_E$], [$n=abs(H)$, $f=abs(Phi)=2n$, and $d_E=[E:ℚ]=4n$ for the arithmetic host.],
  [$k,m,t$], [Initial rank, number of lifts, and odd rank parameter.],
  [$a,b,w$], [Top scale $x b$, thick weight scale $exp(x^epsilon)$, and individual weight.],
  [$Sha_(ℓ)(E,j)$], [Degree-one localization kernel for $(ℚ_ℓ slash ℤ_ℓ)(-j)$.],
  [$mu(P)$], [Normalized Arakelov degree divided by rank.],
  table.hline(stroke: 0.7pt))

#sub[Concordance]

The links below open the individual files in the public source snapshot at commit #text(font: "DejaVu Sans Mono", size: 8.3pt)[40e56bab]. The identifiers are search terms within the linked files. Each entry identifies a definition or a hypothesis and the theorem that supplies it.

*The prime sum and the zero test.* The Mellin transform of the ramp is proved in #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp")[MellinRamp]. Residues and isolation of poles for a family are assembled by #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData")[poleData]. The real-versus-shifted-center alternative is in #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy")[landau_dichotomy]. The one-sided window conclusion is #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow")[zeroFree_of_rpow_window].

*The target family and its host.* The cyclic level, its weights and required coset accuracy are defined in #src("Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions")[Level.cyc, Shares, and EAtH]. Admissible hosts that meet the analytic and cohomological conditions at the same point are produced by #src("Development.AutomorphicArithmetic.CharacterBoxes.HostOfField")[supplyOfAdm] and #src("Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi")[supplyChi].

*The theta construction.* For the rank change and strict weight inequalities consult #src("Formalism.LocalRingCardinality.Params")[Ranks and HCParam]. The seven inputs at the top of this branch are collected by #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses")[every_character_of_theta_integrals_local_matching]. They concern the auxiliary Hecke place, local theta theory, integral agreement, local matching, covolumes, local parameters, and the cohomological window.

*From geometry to an explicit prime sum.* The local gain, overlap, division, and slope conditions are in #src("Formalism.SharpRestriction.GlobalTheoremInputs")[GlobalTheoremInputs]. The joint conclusion is #src("Formalism.SharpRestriction.GlobalSchurBounds.TieGlobal")[ChainTied]. The prime identity, upper estimate and final normalization are #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance")[ch_balance], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop")[ch_top], and #src("Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm")[core_gm].

*Galois parameters and the interval.* The theorem for regular algebraic polarized inputs is #src("Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis")[Row0b]. Its geometric and theta supply is #src("Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc")[galoisLocalGlobalStrong_recParameter]. #src("Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow")[vwin_of_row] supplies the cohomological assertion defined in #src("Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN")[VWinAt].

*Final implications.* #src("Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion")[everyCharacter_of_row] uses the Galois theorem both for the automorphic inputs and for the window. #src("Formalism.GammaFactorNonvanishing.RhOfRight")[rh_of_right] treats the ordinary zeta function outside the strip. #src("Main")[Main] collects the five public statements, including the primitive specialization.

#front[References and further reading]

*Primary source for Part II.* Levent Alpöge, announcement and formal development with Claude, November 2026. The announcement describes the inspiration for the method. The theorem statements, constants, and dependencies used in this book follow the released source. #link("https://alpo.ge/remark.pdf")[Announcement.] #link("https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005/src")[Source snapshot.]

*Euler and Riemann.* Leonhard Euler, _Variae observationes circa series infinitas_, Eneström 72. Bernhard Riemann, _Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse_, Berlin Academy, 1859. Enrico Bombieri's _Problems of the Millennium: the Riemann Hypothesis_ explains the modern statement and its history. #link("https://scholarlycommons.pacific.edu/euler-works/72/")[Euler.] #link("https://www.claymath.org/collections/riemanns-1859-manuscript/")[Riemann.] #link("https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf")[Bombieri.]

*Analytic milestones.* Jacques Hadamard, _Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques_, Bulletin de la Société Mathématique de France 24 (1896), 199–220. Helge von Koch, _Sur la distribution des nombres premiers_, Acta Mathematica 24 (1901), 159–182. Dave Platt and Tim Trudgian, _The Riemann hypothesis is true up to $3 dot 10^12$_, Bulletin of the London Mathematical Society 53 (2021), 792–797. #link("https://numdam.org/articles/10.24033/bsmf.545/")[Hadamard.] #link("https://zenodo.org/records/2347595")[von Koch.] #link("https://arxiv.org/abs/2004.09765")[Platt and Trudgian.]

*Finite-field geometry.* S. A. Stepanov, _On the number of points of a hyperelliptic curve over a finite prime field_, Mathematics of the USSR-Izvestiya 3 (1969), 1103–1114. Pierre Deligne, _La conjecture de Weil I_, Publications Mathématiques de l'IHÉS 43 (1974), 273–307. The first paper illustrates the multiplicity method. The second places the square-root phenomenon for curves in the general theory of weights. #link("https://doi.org/10.1070/IM1969v003n05ABEH000834")[Stepanov.] #link("https://numdam.org/articles/10.1007/BF02684373/")[Deligne.]

*Theta lifting and cyclotomic towers.* Stephen Rallis, _On the Howe duality conjecture_, Compositio Mathematica 51 (1984), 333–399. Bruce Ferrero and Lawrence C. Washington, _The Iwasawa invariant $mu_p$ vanishes for abelian number fields_, Annals of Mathematics 109 (1979), 377–395. These are background sources for two of the technologies entering the construction. #link("https://www.numdam.org/item/CM_1984__51_3_333_0/")[Rallis.] #link("https://doi.org/10.2307/1971116")[Ferrero and Washington.]
