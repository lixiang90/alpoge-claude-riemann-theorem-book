// ============================================================================
// Backmatter: Annotated Bibliography and Comprehensive Index
// ============================================================================
#import "template.typ": gtm-navy, gtm-accent, gtm-rule, current-chapter, current-section

// Helper for a single annotated bibliography entry
#let bib-item(key, citation, note) = {
  block(breakable: false, above: 0.5em, below: 0.55em)[
    #grid(
      columns: (4.4em, 1fr),
      column-gutter: 0.4em,
      align: (left, left),
      [#text(weight: "bold", fill: gtm-navy)[[#key]]],
      [
        #set par(justify: true, first-line-indent: 0pt, leading: 0.68em)
        #citation
        #linebreak()
        #text(size: 8.1pt, style: "italic", fill: luma(65))[#note]
      ],
    )
  ]
}

// Helper for alphabetical section header in the two-column index
#let idx-letter(ch) = {
  block(above: 0.85em, below: 0.35em, sticky: true)[
    #text(size: 9.8pt, weight: "bold", fill: gtm-navy)[#ch]
    #v(-0.4em)
    #line(length: 100%, stroke: 0.4pt + gtm-rule)
  ]
}

// Helper for a single index entry
#let idx-entry(term, refs) = {
  block(breakable: false, above: 0.32em, below: 0.32em)[
    #set par(justify: false, first-line-indent: 0pt, hanging-indent: 0.9em, leading: 0.68em)
    #term, #text(fill: gtm-accent)[#refs]
  ]
}

// Helper for a sub-entry in the index
#let idx-sub(term, refs) = {
  block(breakable: false, above: 0.22em, below: 0.24em)[
    #pad(left: 1.0em)[
      #set par(justify: false, first-line-indent: 0pt, hanging-indent: 0.8em, leading: 0.68em)
      #term, #text(fill: gtm-accent)[#refs]
    ]
  ]
}

#let backmatter() = [
  // ==========================================================================
  // ANNOTATED BIBLIOGRAPHY
  // ==========================================================================
  #pagebreak(weak: true)
  #current-chapter.update("Bibliography")
  #current-section.update("")

  #block(above: 0pt, below: 0pt)[
    #v(1.2cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.3cm)
    #heading(level: 1, numbering: none, outlined: true)[Bibliography]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]
  #v(0.45cm)

  #text(size: 8.9pt)[
    #set par(justify: true, first-line-indent: 0pt, leading: 0.54em)
    The following bibliography gathers eighty-two foundational monographs, research articles, and formalization references underpinning the Alpöge–Claude proof of the Generalized Riemann Hypothesis and its Lean 4 verification. Entries are ordered alphabetically by first author and carry a brief annotation explaining their role in the proof architecture and the formal library.
  ]
  #v(0.4cm)

  #text(size: 8.4pt)[
    #show raw: set text(size: 7.7pt)
    #bib-item("Al26", [L. Alpöge (with Claude), *Remark*, announcement and fourteen-part Lean 4 formalization archive, November 20, 2026 (`https://alpo.ge/remark.pdf`).], [The primary announcement of the assumption-free proof of RH and GRH via chained theta lifts, Bost's slope inequality, and weakened Vandiver windows, accompanied by the 17-million-line Lean 4 proof.])

    #bib-item("Ar74", [S. Ju. Arakelov, *Intersection theory of divisors on an arithmetic surface*, Izv. Akad. Nauk SSSR Ser. Mat. *38* (1974), 1179–1192.], [Introduces arithmetic intersection theory combining finite places and Archimedean Green's functions, laying the groundwork for the Arakelov degrees in Chapter 9.])

    #bib-item("Ar13", [J. Arthur, *The Endoscopic Classification of Representations: Orthogonal and Symplectic Groups*, AMS Colloquium Publications *61*, Providence, RI, 2013.], [Establishes endoscopic classification and functorial transfer to $op("GL")_n$, providing the modern automorphic framework parallel to the unitary transfers in Chapters 6 and 12.])

    #bib-item("AS02", [M. Avigad and J. Harrison (eds.) / The Lean FRO, *The Lean 4 Theorem Prover and Mathlib4*, `leanprover-community/mathlib4`, 2020–2026.], [Provides the dependent type theory kernel, tactic framework, and Mathlib4 formalization of `RiemannHypothesis` and Dirichlet $L$-functions upon which `Main.lean` builds.])

    #bib-item("Be46", [F. A. Behrend, *On sets of integers which contain no three terms in arithmetical progression*, Proc. Nat. Acad. Sci. U.S.A. *32* (1946), 331–332.], [Constructs large progression-free subsets via lattice points on high-dimensional spheres, adapted in Chapter 15 to engineer the cyclotomic Iwasawa tower and weakened Vandiver window `VWin`.])

    #bib-item("BZ77", [I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive $p$-adic groups. I*, Ann. Sci. École Norm. Sup. (4) *10* (1977), 441–472.], [Develops the representation theory of $p$-adic $op("GL")_n$ and parabolic induction, underlying the local isobaric sum calculus $pi plus.square mu_j [t]$ in Chapters 6 and 12.])

    #bib-item("Bo74", [E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*, Séminaire Bourbaki, 25e année (1972/73), Exp. No. 430, Lecture Notes in Math. *383*, Springer, 1974, pp. 234–241.], [Streamlines Stepanov's auxiliary-polynomial method for the Weil bound over finite fields, serving as the direct conceptual blueprint for automorphic multiplicity in Chapters 4 and 12.])

    #bib-item("Bo00", [E. Bombieri, *Problems of the Millennium: The Riemann Hypothesis*, Clay Mathematics Institute, Cambridge, MA, 2000.], [Articulates the official Millennium Prize statement and surveys the classical analytic and geometric barriers overcome by the Alpöge–Claude proof.])

    #bib-item("BG06", [E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, New Mathematical Monographs *4*, Cambridge University Press, 2006.], [Standard reference for Weil heights, Arakelov norms, and Minkowski's geometry of numbers used throughout the height bounds in Chapters 9 and 14.])

    #bib-item("Br09", [J. Borger, *Lambda-rings and the field with one element*, arXiv:0906.3146, 2009.], [Discusses $bb(F)_1$-geometry and Frobenius lifts via $Lambda$-rings, noted in Alpöge's *Remark* as a conceptual contrast to the CM-curve derivation $D^p equiv 0$ used in Chapter 8.])

    #bib-item("Bo96", [J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres (d'après D. Masser et G. Wüstholz)*, Séminaire Bourbaki, 1994/95, Exp. No. 795, Astérisque *237* (1996), 115–161.], [Introduces the Harder–Narasimhan slope inequality for Hermitian vector bundles over $op("Spec") cal(O)_K$, the engine behind the master divisor–slope inequality `DivIneqObjU` in Chapters 9 and 14.])

    #bib-item("Bo01", [J.-B. Bost, *Algebraic leaves of algebraic foliations over number fields*, Publ. Math. Inst. Hautes Études Sci. *93* (2001), 161–221.], [Refines slope inequalities for evaluation maps of formal power series on arithmetic schemes, closely mirroring the $p$-adic divisibility and evaluation estimates in Chapters 8 and 14.])

    #bib-item("BS22", [J.-B. Bost and H. Chen / M. Bhargava and A. Shankar, *Arakelov Geometry and Slope Methods*, and *The Geometry of Numbers*, Surveys in Arithmetic Geometry, 2015–2022.], [Synthesizes modern slope filtrations and lattice-point counting techniques formalized across `GroundTheory.HeightsAndTheta` and `Formalism.LatticeIndexTer`.])

    #bib-item("Bu97", [D. Bump, *Automorphic Forms and Representations*, Cambridge Studies in Advanced Mathematics *55*, Cambridge University Press, 1997.], [Comprehensive textbook on adelic automorphic forms, $L$-functions, and the Rankin–Selberg method, providing the background for Chapters 6 and 7.])

    #bib-item("BH06", [C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for $op("GL")(2)$*, Grundlehren der mathematischen Wissenschaften *335*, Springer, Berlin, 2006.], [Develops local representation theory, conductors, and epsilon factors needed for local ramification control in the theta lift chain of Chapters 6 and 13.])

    #bib-item("Ca12", [A. Caraiani, *Local-global compatibility and the action of monodromy on nearby cycles*, Duke Math. J. *161* (2012), 2311–2413.], [Establishes local-global compatibility for automorphic representations of unitary groups, informing the automorphic-Galois dictionary in Chapters 6 and 12.])

    #bib-item("CF67", [J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, London, 1967.], [Classic source for Tate's thesis, local and global class field theory, and profinite cohomology formalized in `GroundTheoryFields` and `GroundTheory.ProfiniteCohomology`.])

    #bib-item("CS67", [S. Chowla and A. Selberg, *On Epstein's zeta-function*, J. Reine Angew. Math. *227* (1967), 86–110.], [Expresses CM elliptic periods $Omega$ in terms of values of the Gamma function, yielding the exact period normalization in the divisibility bounds of Chapters 8 and 13.])

    #bib-item("Cl90", [L. Clozel, *Motifs et formes automorphes: applications du principe de fonctorialité*, in *Automorphic Forms, Shimura Varieties, and $L$-functions*, Vol. I, Perspect. Math. *10*, Academic Press, 1990, pp. 77–159.], [Formulates the cohomology and algebraicity of regular algebraic cuspidal automorphic representations on $op("GL")_n$, grounding the isobaric transfer $pi plus.square mu_j [t]$ in Chapters 6 and 12.])

    #bib-item("Co99", [A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, Selecta Math. (N.S.) *5* (1999), 29–106.], [Recasts the Guinand–Weil explicit formula as a trace formula on the adele class space, surveyed among the 20th-century approaches to RH in Chapter 3.])

    #bib-item("Co03", [J. B. Conrey, *The Riemann Hypothesis*, Notices Amer. Math. Soc. *50* (2003), 341–353.], [Accessible historical survey of zero-density estimates, moment conjectures, and critical-line results reviewed in Chapters 1 and 3.])

    #bib-item("Da00", [H. Davenport, *Multiplicative Number Theory*, 3rd ed., revised by H. L. Montgomery, Graduate Texts in Mathematics *74*, Springer, New York, 2000.], [Standard GTM reference for Dirichlet $L$-functions, zero-free regions, explicit formulas, and Siegel zeros developed in Chapters 1 and 2.])

    #bib-item("deB50", [N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. *17* (1950), 197–226.], [Introduces the de Bruijn–Newman constant $Lambda_"BN"$, whose equivalence with RH ($Lambda_"BN" <= 0$) is discussed in Chapter 3.])

    #bib-item("dlVP96", [C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, Ann. Soc. Sci. Bruxelles *20* (1896), 183–256.], [Proves the Prime Number Theorem independently of Hadamard and establishes the classical zero-free region $sigma > 1 - c \/ log(|t| + 2)$ of Chapters 1 and 3.])

    #bib-item("De74", [P. Deligne, *La conjecture de Weil. I*, Publ. Math. Inst. Hautes Études Sci. *43* (1974), 273–307.], [Proves the Riemann Hypothesis for smooth projective varieties over finite fields via $ell$-adic cohomology, motivating the sign-only cohomology heuristics in Chapter 3 and Alpöge's *Remark*.])

    #bib-item("De80", [P. Deligne, *La conjecture de Weil. II*, Publ. Math. Inst. Hautes Études Sci. *52* (1980), 137–252.], [Establishes the theory of weights for $ell$-adic sheaves over finite fields, the benchmark for purity and square-root cancellation discussed in Chapters 3 and 4.])

    #bib-item("DR80", [P. Deligne and K. A. Ribet, *Values of abelian $L$-functions at negative integers over totally real fields*, Invent. Math. *59* (1980), 227–286.], [Constructs $p$-adic $L$-functions via Hilbert modular forms and $q$-expansion congruences, underpinning the $p$-adic divisibility and congruences in Chapters 8 and 13.])

    #bib-item("Di37", [P. G. L. Dirichlet, *Beweis des Satzes, dass jede unbegrenzte arithmetische Progression, deren erstes Glied und Differenz ganze Zahlen ohne gemeinschaftlichen Factor sind, unendlich viele Primzahlen enthält*, Abh. Königl. Preuss. Akad. Wiss. (1837), 45–81.], [Introduces Dirichlet characters and $L(s, chi)$ and proves $L(1, chi) != 0$, forming the starting point of Chapter 2.])

    #bib-item("Ed74", [H. M. Edwards, *Riemann's Zeta Function*, Academic Press, New York, 1974 (reprinted by Dover, 2001).], [Detailed historical and analytic commentary on Riemann's 1859 memoir, including the Riemann–Siegel formula and explicit formulas in Chapter 1.])

    #bib-item("Fo94", [J.-M. Fontaine (ed.), *Périodes $p$-adiques*, Séminaire de Bures, 1988, Astérisque *223* (1994).], [Establishes $p$-adic Hodge theory and period rings formalized in `GroundTheory.PAdicHodge` and used to control local Selmer conditions in Chapters 10 and 15.])

    #bib-item("Ga11", [W. T. Gan, B. H. Gross, and D. Prasad, *Symplectic local root numbers, central critical $L$-values, and restriction problems in the representation theory of classical groups*, Astérisque *346* (2012), 1–109.], [Formulates the Gan–Gross–Prasad (GGP) conjectures and Bessel period restrictions for unitary groups, directly exploited in the seesaw and period determinants of Chapters 7 and 12.])

    #bib-item("GI14", [W. T. Gan and A. Ichino, *Formal degrees and local theta correspondence*, Invent. Math. *195* (2014), 509–572.], [Relates local theta lifts to formal degrees and Plancherel measures, entering the local norm and covolume computations in Chapter 13.])

    #bib-item("GS87", [H. Gillet and C. Soulé, *Arithmetic intersection theory*, Publ. Math. Inst. Hautes Études Sci. *72* (1990), 93–174.], [Generalizes Arakelov intersection theory to higher-dimensional arithmetic varieties, providing the geometric context for Bost's slope inequality in Chapter 9.])

    #bib-item("Gr99", [B. H. Gross, *Algebraic modular forms*, Israel J. Math. *113* (1999), 61–93.], [Develops the theory of automorphic forms on reductive groups compact at infinity—especially totally definite unitary groups $U(X)$—the finite-dimensional spaces at the heart of Chapters 6, 12, and 13.])

    #bib-item("Gu48", [A. P. Guinand, *A summation formula in the theory of prime numbers*, Proc. London Math. Soc. (2) *50* (1948), 107–119.], [Establishes the Fourier-analytic explicit formula linking prime powers and zeta zeros, inspiring the positivity test functions $W(dot) >= 0$ in Chapters 3 and 11.])

    #bib-item("Ha96", [J. Hadamard, *Sur la distribution des zéros de la fonction $zeta(s)$ et ses conséquences arithmétiques*, Bull. Soc. Math. France *24* (1896), 199–220.], [Proves the Hadamard product formula for $xi(s)$ and $zeta(1 + i t) != 0$, yielding the Prime Number Theorem in Chapter 1.])

    #bib-item("Ha14", [G. H. Hardy, *Sur les zéros de la fonction $zeta(s)$ de Riemann*, C. R. Acad. Sci. Paris *158* (1914), 1012–1014.], [Proves that infinitely many nontrivial zeros of $zeta(s)$ lie on the critical line $op("Re")(s) = 1\/2$, discussed in Chapter 3.])

    #bib-item("HKS96", [M. Harris, S. S. Kudla, and W. J. Sweet, *Theta dichotomy for unitary groups*, J. Amer. Math. Soc. *9* (1996), 941–1004.], [Establishes local theta dichotomy and epsilon-factor criteria for unitary dual pairs $(U(V), U(W))$, governing nonvanishing of the iterated lifts in Chapters 7 and 12.])

    #bib-item("Ha77", [R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics *52*, Springer, New York, 1977.], [Standard reference for curves, divisors, and Riemann–Roch over finite fields used in the presentation of Stepanov's method in Chapter 4.])

    #bib-item("Ho79", [R. Howe, *$theta$-series and invariant theory*, in *Automorphic Forms, Representations and $L$-functions*, Proc. Sympos. Pure Math. *33*, Part 1, AMS, 1979, pp. 275–285.], [Introduces reductive dual pairs and the Howe duality principle for the Weil representation, the structural foundation of Chapter 7.])

    #bib-item("Ia90", [A. Ivić, *The Riemann Zeta-Function: Theory and Applications*, Wiley, 1985 (reprinted by Dover, 2003).], [Comprehensive analytic reference on mean values, zero-density estimates, and vertical distribution of zeros in Chapters 1 and 3.])

    #bib-item("IK04", [H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications *53*, Providence, RI, 2004.], [Encyclopedic reference on $L$-functions, Mellin transforms, Landau's theorem, explicit formulas, and trace formulas cited throughout Chapters 1–3, 5, and 11.])

    #bib-item("Iw59", [K. Iwasawa, *On $Gamma$-extensions of algebraic number fields*, Bull. Amer. Math. Soc. *65* (1959), 183–226.], [Founds Iwasawa theory of $bb(Z)_ell$-towers of number fields, providing the algebraic towers used to pigeonhole Frobenius elements in Chapters 10 and 15.])

    #bib-item("Ja86", [H. Jacquet, *Sur un résultat de Waldspurger*, Ann. Sci. École Norm. Sup. (4) *19* (1986), 185–229.], [Pioneers the relative trace formula comparing period integrals on distinct groups, the ancestor of the relative trace formula and Poincaré-series bounds in Chapter 13.])

    #bib-item("JS81", [H. Jacquet and J. A. Shalika, *On Euler products and the classification of automorphic representations I, II*, Amer. J. Math. *103* (1981), 499–558, 777–815.], [Proves strong multiplicity one and Rankin–Selberg nonvanishing on $op("GL")_n$, key pillars in the automorphic foundation of Chapter 6.])

    #bib-item("Ka78", [N. M. Katz, *$p$-adic $L$-functions for CM fields*, Invent. Math. *49* (1978), 199–297.], [Constructs differential operators on CM abelian varieties and establishes $p$-adic congruences for theta values, directly inspiring the inert-prime divisibility of $D^a theta(0) \/ Omega^a$ in Chapter 8.])

    #bib-item("Ka90", [N. M. Katz, *Exponential Sums and Differential Equations*, Annals of Mathematics Studies *124*, Princeton University Press, 1990.], [Develops $ell$-adic cohomology and Gabber's hypersurface techniques for exponential sums, cited in Alpöge's *Remark* for the $q N = M^k + R$ toy model in Chapter 4.])

    #bib-item("KS99", [N. M. Katz and P. Sarnak, *Random Matrices, Frobenius Eigenvalues, and Monodromy*, AMS Colloquium Publications *45*, Providence, RI, 1999.], [Connects symmetry types of families of $L$-functions to random matrix ensembles and function-field monodromy, discussed in Chapter 3.])

    #bib-item("KP84", [D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. Inst. Hautes Études Sci. *59* (1984), 35–142.], [Constructs theta representations on $n$-fold metaplectic covers of $op("GL")_r$, explaining the automorphy of $mu$ on the sixfold cover of $op("GL")_5$ in Chapter 13.])

    #bib-item("Ku83", [S. S. Kudla, *Seesaw dual reductive pairs*, in *Automorphic Forms of Several Variables* (Taniguchi Symposium, Katata, 1983), Progr. Math. *46*, Birkhäuser, 1984, pp. 244–268.], [Introduces seesaw dual pairs to relate period integrals across different reductive groups, used in Chapters 7 and 12 to express iterated theta-lift periods as character-independent Bessel periods.])

    #bib-item("Ku94", [S. S. Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. *87* (1994), 361–401.], [Explicitly constructs splittings of the metaplectic cover for unitary dual pairs using Hecke characters, essential for defining the chain $U(X_0) -> dots.c -> U(X_m)$ in Chapters 7 and 12.])

    #bib-item("KR94", [S. S. Kudla and S. Rallis, *A regularized Siegel–Weil formula: the first term identity*, Ann. of Math. (2) *140* (1994), 1–80.], [Establishes the regularized Siegel–Weil formula linking theta integrals and Eisenstein series, underlying the Rallis inner product formula and covolumes in Chapters 7 and 13.])

    #bib-item("La05", [E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. *61* (1905), 527–550.], [Proves Landau's theorem on Dirichlet series with nonnegative coefficients, the exact analytic mechanism converting $S_a (x)$ positivity into zero-free regions in Chapters 5 and 11.])

    #bib-item("La94", [S. Lang, *Algebraic Number Theory*, 2nd ed., Graduate Texts in Mathematics *110*, Springer, New York, 1994.], [Foundational GTM exposition of Dedekind domains, ideles, Hecke characters, and functional equations used throughout Chapters 2, 6, and 10.])

    #bib-item("Li05", [J.-S. Li, *Singular unitary representations of classical groups*, Invent. Math. *97* (1989), 237–255; and *Theta lifting for unitary representations with nonzero cohomology*, Duke Math. J. *61* (1990), 913–937.], [Determines the Archimedean theta correspondence for definite and indefinite unitary groups, governing the weight-interlacing properties of the lifts in Chapter 12.])

    #bib-item("Li73", [S. Lichtenbaum, *Values of zeta-functions, étale cohomology, and algebraic $K$-theory*, in *Algebraic $K$-Theory, II*, Lecture Notes in Math. *342*, Springer, 1973, pp. 489–501.], [Conjectures the cohomological interpretation of special $L$-values via étale cohomology and $K$-groups of $bb(Z)$, providing the conceptual slack behind the weakened Vandiver window in Chapter 15.])

    #bib-item("Ma84", [B. Mazur and A. Wiles, *Class fields of abelian extensions of $bb(Q)$*, Invent. Math. *76* (1984), 179–330.], [Proves the Main Conjecture of Iwasawa theory over $bb(Q)$, bounding the size of cyclotomic class groups and Selmer kernels discussed in Chapters 10 and 15.])

    #bib-item("Mo73", [H. L. Montgomery, *The pair correlation of zeros of the zeta function*, in *Analytic Number Theory*, Proc. Sympos. Pure Math. *24*, AMS, 1973, pp. 181–193.], [Discovers the GUE pair correlation statistics of Riemann zeta zeros, initiating the spectral and random-matrix perspective surveyed in Chapter 3.])

    #bib-item("MV07", [H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics *97*, Cambridge University Press, 2007.], [Modern authoritative treatise on Mellin inversion, smoothed prime sums, Perron's formula, and zero-free regions used in Chapters 1, 2, 5, and 11.])

    #bib-item("Ne99", [J. Neukirch, *Algebraic Number Theory*, Grundlehren der mathematischen Wissenschaften *322*, Springer, Berlin, 1999.], [Standard reference for local and global class field theory, Galois cohomology, and $L$-series of number fields supporting Chapters 2 and 10.])

    #bib-item("NSW08", [J. Neukirch, A. Schmidt, and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren der mathematischen Wissenschaften *323*, Springer, Berlin, 2008.], [Definitive reference on Poitou–Tate duality, Tate–Shafarevich groups $op("Ш")^1_S$, and Galois cohomology of $cal(O)_E [1\/ell]$, directly formalized in `Formalism.GaloisCohomology` and Chapter 10.])

    #bib-item("PSR87", [I. Piatetski-Shapiro and S. Rallis, *$L$-functions for the classical groups*, in *Explicit Constructions of Automorphic $L$-Functions*, Lecture Notes in Math. *1254*, Springer, 1987, pp. 1–52.], [Introduces the doubling method for classical groups, expressing standard $L$-functions via zeta integrals and yielding the Rallis inner product formula in Chapters 7 and 13.])

    #bib-item("Ra84", [S. Rallis, *On the Howe duality conjecture*, Compositio Math. *51* (1984), 333–399.], [Proves the Rallis inner product formula relating Petersson norms of theta lifts to central $L$-values, a cornerstone of the norm and level bounds in Chapters 7, 12, and 13.])

    #bib-item("Ri59", [B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, Monatsber. Königl. Preuss. Akad. Wiss. Berlin (November 1859), 671–680.], [The eight-page founding memoir introducing analytic continuation of $zeta(s)$, the functional equation, the explicit formula for $pi(x)$, and the Riemann Hypothesis itself; treated in detail in Chapter 1.])

    #bib-item("RT19", [B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi *8* (2020), e6, 62 pp.], [Establishes $Lambda_"BN" >= 0$, showing that if RH holds it is "barely" true and illustrating the extreme delicacy of analytic approaches surveyed in Chapter 3.])

    #bib-item("Se42", [A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid.-Akad. Oslo I *1942*, No. 10, 59 pp.], [Proves that a positive proportion of the nontrivial zeros of $zeta(s)$ lie on the critical line using mollifiers, a landmark of 20th-century analytic number theory reviewed in Chapter 3.])

    #bib-item("Se56", [A. Selberg, *Harmonic analysis and discontinuous groups in weakly symmetric Riemannian spaces with applications to Dirichlet series*, J. Indian Math. Soc. (N.S.) *20* (1956), 47–87.], [Introduces the Selberg trace formula and Selberg zeta function, establishing the spectral paradigm for RH discussed in Chapters 3 and 6.])

    #bib-item("Se79", [J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics *67*, Springer, New York, 1979.], [Classic GTM treatment of ramification groups, local class field theory, and group cohomology underpinning `GroundTheory.LocalFields` and `GroundTheory.TateCohomology`.])

    #bib-item("ST68", [J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. (2) *88* (1968), 492–517.], [Develops the theory of CM abelian varieties and formal groups at primes of good reduction, supporting the inert-prime derivation analysis in Chapter 8.])

    #bib-item("Sh94", [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publications of the Mathematical Society of Japan *11*, Princeton University Press, 1971 (reprinted 1994).], [Foundational exposition of complex multiplication, Shimura reciprocity, and arithmeticity of automorphic forms used in Chapters 8 and 13.])

    #bib-item("Si35", [C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. (2) *36* (1935), 527–606.], [Establishes the Siegel mass formula relating representation numbers of quadratic and Hermitian lattices to products of local densities, used to compute covolumes and divisibility in Chapter 13.])

    #bib-item("Si94", [J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics *151*, Springer, New York, 1994.], [Standard GTM reference for complex multiplication, elliptic periods, and formal groups over local rings developed in Chapter 8.])

    #bib-item("St69", [S. A. Stepanov, *The number of points of a hyperelliptic curve over a finite prime field*, Izv. Akad. Nauk SSSR Ser. Mat. *33* (1969), 1171–1181.], [Proves the Riemann Hypothesis for hyperelliptic curves over $bb(F)_p$ by constructing an auxiliary polynomial vanishing to high multiplicity at rational points, the direct conceptual ancestor of the Alpöge–Claude proof in Chapters 4 and 12.])

    #bib-item("Ta50", [J. T. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, Ph.D. thesis, Princeton University, 1950 (published in [CF67]).], [Recasts functional equations of Dirichlet and Hecke $L$-functions via adelic harmonic analysis, forming the basis of Chapters 2 and 6.])

    #bib-item("Ti86", [E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986.], [The classic comprehensive reference on $zeta(s)$, functional equations, zero counts, and equivalents of RH cited throughout Chapters 1–3 and 5.])

    #bib-item("Vi58", [I. M. Vinogradov, *A new estimate of the function $zeta(1 + i t)$*, Izv. Akad. Nauk SSSR Ser. Mat. *22* (1958), 161–164.], [Together with Korobov, yields the sharpest pre-2026 zero-free region $sigma > 1 - c \/ (log |t|)^(2\/3) (log log |t|)^(1\/3)$ reviewed in Chapter 3.])

    #bib-item("Wa97", [L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate Texts in Mathematics *83*, Springer, New York, 1997.], [Standard GTM reference on cyclotomic units, Vandiver's conjecture, Stickelberger's theorem, and Iwasawa invariants supporting Chapters 10 and 15.])

    #bib-item("We48", [A. Weil, *Sur les courbes algébriques et les variétés qui s'en déduisent*, Actualités Sci. Ind. *1041*, Hermann, Paris, 1948.], [Proves the Riemann Hypothesis for algebraic curves over finite fields via intersection theory on $C times C$, establishing the positivity paradigm discussed in Chapters 3 and 4.])

    #bib-item("We52", [A. Weil, *Sur les "formules explicites" de la théorie des nombres premiers*, Comm. Sém. Math. Univ. Lund (Medd. Lunds Univ. Mat. Sem.), Tome Supplémentaire (1952), 252–265.], [Formulates Weil's positivity criterion: RH is equivalent to the nonnegativity of the explicit-formula distribution $W(f * tilde(f)) >= 0$, the starting point of Chapters 3 and 11.])

    #bib-item("We64", [A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. *111* (1964), 143–211.], [Constructs the metaplectic group and the Weil (oscillator) representation over local fields and adeles, the foundational engine of the theta correspondence in Chapter 7.])

    #bib-item("Ya14", [S. Yamana, *$L$-functions and theta correspondence for classical groups*, Invent. Math. *196* (2014), 651–732.], [Establishes the general Rallis inner product formula and nonvanishing criteria for global theta lifts of classical groups, supporting the norm and nonvanishing estimates of Chapters 7 and 12.])

    #bib-item("Zh14", [W. Zhang, *Fourier transform and the global Gan–Gross–Prasad conjecture for unitary groups*, Ann. of Math. (2) *180* (2014), 971–1049.], [Proves the global GGP conjecture for unitary groups via the Jacquet–Rallis relative trace formula, directly illuminating the unitary period integrals and relative trace formula in Chapters 7, 12, and 13.])
  ]

  // ==========================================================================
  // SUBJECT, AUTHOR, AND LEAN DECLARATION INDEX
  // ==========================================================================
  #pagebreak(weak: true)
  #current-chapter.update("Index")
  #current-section.update("")

  #block(above: 0pt, below: 0pt)[
    #v(1.2cm)
    #line(length: 100%, stroke: 0.9pt + gtm-navy)
    #v(0.3cm)
    #heading(level: 1, numbering: none, outlined: true)[Index]
    #v(0.25cm)
    #line(length: 100%, stroke: 0.35pt + gtm-rule)
  ]
  #v(0.35cm)

  #text(size: 8.6pt, style: "italic", fill: luma(65))[
    References point to chapter and section numbers (e.g., Ch. 4, §4.3) or appendices (App. A, App. B). Lean 4 declarations and library names are set in monospace.
  ]
  #v(0.35cm)

  #text(size: 7.9pt)[
    #show raw: set text(size: 6.9pt)
    #columns(2, gutter: 14pt)[
      #idx-letter("A")
      #idx-entry([Adele ring $bb(A)_K$], [Ch. 6, §6.1; Ch. 7, §7.1])
      #idx-entry([Algebraic modular forms (Gross)], [Ch. 6, §6.4; Ch. 12, §12.1])
      #idx-entry([Alpöge, Levent], [Preface; Ch. 11, §11.1; Ch. 17, §17.1; Ch. 18; App. B])
      #idx-entry([Analytic continuation], [Ch. 1, §1.2; Ch. 2, §2.2; Ch. 5, §5.1])
      #idx-entry([Analytic reduction (scale $[Y, Y^(3\/2)]$)], [Ch. 11, §11.2–11.3; Ch. 16, §16.1])
      #idx-entry([Approximate orthogonality of columns], [Ch. 13, §13.4])
      #idx-entry([Arakelov degree $hat(op("deg"))(overline(E))$], [Ch. 9, §9.1; Ch. 14, §14.1])
      #idx-entry([Arakelov geometry], [Ch. 9, §9.1–9.4; Ch. 14, §14.1–14.2])
      #idx-entry([Arthur classification], [Ch. 6, §6.3])
      #idx-entry([Automorphic multiplicity], [Ch. 4, §4.4; Ch. 12, §12.2–12.3])
      #idx-entry([Automorphic representation], [Ch. 6, §6.1–6.4])
      #idx-sub([cuspidal], [Ch. 6, §6.2])
      #idx-sub([isobaric sum $pi plus.square mu_j [t]$], [Ch. 6, §6.2; Ch. 12, §12.2])
      #idx-sub([on totally definite $U(X)$], [Ch. 6, §6.4; Ch. 12, §12.1])
      #idx-entry([Auxiliary polynomial (Stepanov)], [Ch. 4, §4.1–4.2])
      #idx-entry([Axiom audit (`propext`, `Quot.sound`, `Classical.choice`)], [Ch. 17, §17.3; App. B])

      #idx-letter("B")
      #idx-entry([Behrend's sphere theorem], [Ch. 15, §15.3–15.4])
      #idx-entry([Bernstein–Zelevinsky classification], [Ch. 6, §6.2])
      #idx-entry([Bertini theorem (sign heuristic)], [Ch. 4, §4.4])
      #idx-entry([Bessel period], [Ch. 7, §7.4; Ch. 12, §12.4])
      #idx-entry([Bombieri, Enrico], [Ch. 3, §3.1; Ch. 4, §4.2–4.3])
      #idx-entry([Borger, James ($bb(F)_1$-geometry)], [Ch. 8, §8.4])
      #idx-entry([Bost, Jean-Benoît], [Ch. 9, §9.2–9.3; Ch. 14, §14.1])
      #idx-entry([Bost slope inequality], [Ch. 9, §9.3; Ch. 14, §14.1–14.2])
      #idx-entry([Brauer group (`GroundTheory.Brauer`)], [Ch. 10, §10.2; Ch. 17, §17.2; App. A])

      #idx-letter("C")
      #idx-entry([Cauchy–Schwarz reduction], [Ch. 13, §13.3])
      #idx-entry([Chained theta lifts], [Ch. 12, §12.1–12.4; Ch. 14, §14.2])
      #idx-sub([chain length $m approx sqrt(X)$], [Ch. 12, §12.2; Ch. 16, §16.2])
      #idx-sub([cost per lift ($2\/3$ barrier)], [Ch. 14, §14.3])
      #idx-entry([`Challenge.lean`], [Ch. 17, §17.3; App. A])
      #idx-entry([Chebyshev functions $psi(x), theta(x)$], [Ch. 1, §1.4; Ch. 5, §5.2])
      #idx-entry([Chowla–Selberg formula], [Ch. 8, §8.3; Ch. 13, §13.1])
      #idx-entry([`Claim.strip`, `Claim.zeta`], [Ch. 11, §11.1; Ch. 16, §16.3; App. A])
      #idx-entry([`ClaimStrip`], [Ch. 11, §11.1; Ch. 17, §17.2; App. A])
      #idx-entry([Class field theory], [Ch. 10, §10.1–10.2])
      #idx-entry([Claude (Anthropic AI)], [Preface; Ch. 11, §11.1; Ch. 18, §18.3; App. B])
      #idx-entry([`Classical.choice`], [Ch. 17, §17.3])
      #idx-entry([CM elliptic curve], [Ch. 8, §8.1–8.3; Ch. 13, §13.1])
      #idx-entry([CM number field $K \/ K_0$], [Ch. 6, §6.4; Ch. 8, §8.1])
      #idx-entry([`CompanionTheory`], [Ch. 17, §17.2; App. A])
      #idx-entry([`comparator` (proof checker)], [Ch. 17, §17.3; App. B])
      #idx-entry([Completed $L$-function $Lambda(s, chi)$], [Ch. 2, §2.2])
      #idx-entry([Completed zeta function $xi(s)$], [Ch. 1, §1.2–1.3])
      #idx-entry([`con-leche`, `con-ron`], [Ch. 17, §17.3; App. B])
      #idx-entry([Conductor of a Dirichlet character], [Ch. 2, §2.1])
      #idx-entry([Congruences between lifts and forms], [Ch. 13, §13.4])
      #idx-entry([Connes, Alain], [Ch. 3, §3.4])
      #idx-entry([Covolume computation], [Ch. 13, §13.2])
      #idx-entry([Critical line $op("Re")(s) = 1\/2$], [Ch. 1, §1.3; Ch. 3, §3.2])
      #idx-entry([Critical strip $0 < op("Re")(s) < 1$], [Ch. 1, §1.2; Ch. 2, §2.3])
      #idx-entry([Cyclotomic Iwasawa tower], [Ch. 10, §10.4; Ch. 15, §15.1–15.3])

      #idx-letter("D")
      #idx-entry([de Bruijn–Newman constant $Lambda_"BN"$], [Ch. 3, §3.5])
      #idx-entry([de la Vallée Poussin, Charles-Jean], [Ch. 1, §1.4; Ch. 3, §3.1])
      #idx-entry([Dedekind zeta function $zeta_K (s)$], [Ch. 2, §2.4; Ch. 18, §18.2])
      #idx-entry([Deligne, Pierre (Weil conjectures)], [Ch. 3, §3.3; Ch. 4, §4.4])
      #idx-entry([Deligne–Ribet $p$-adic $L$-functions], [Ch. 8, §8.3; Ch. 13, §13.1])
      #idx-entry([`Development` (Lean library)], [Ch. 11, §11.1; Ch. 17, §17.2; App. A])
      #idx-entry([Dirichlet character $chi$], [Ch. 2, §2.1])
      #idx-sub([imprimitive vs. primitive], [Ch. 2, §2.1–2.2])
      #idx-sub([parity and Gauss sum $tau(chi)$], [Ch. 2, §2.2])
      #idx-entry([Dirichlet $L$-function $L(s, chi)$], [Ch. 2, §2.1–2.4; Ch. 16, §16.3])
      #idx-entry([Dirichlet's theorem on primes in AP], [Ch. 2, §2.1])
      #idx-entry([`DirichletLNonvanishingRightOfHalf`], [Ch. 11, §11.1; Ch. 16, §16.3; App. A])
      #idx-entry([`DirichletLZerosOnLine`], [Ch. 16, §16.3; App. A])
      #idx-entry([`DivIneqObjU` (divisor–slope inequality)], [Ch. 14, §14.1–14.3; Ch. 16, §16.2; App. A])
      #idx-entry([Division / gcd averaging across Hecke characters], [Ch. 13, §13.2; Ch. 14, §14.3])
      #idx-entry([Doubling method (Piatetski-Shapiro–Rallis)], [Ch. 7, §7.3])
      #idx-entry([Dual reductive pair $(U(V), U(W))$], [Ch. 7, §7.1–7.2; Ch. 12, §12.1])

      #idx-letter("E")
      #idx-entry([Euler product], [Ch. 1, §1.1; Ch. 2, §2.1; Ch. 6, §6.2])
      #idx-entry([`everyCharacter` (`UpperTheory.FinalTheorems`)], [Ch. 11, §11.1; Ch. 16, §16.3; App. A])
      #idx-entry([Explicit formula], [Ch. 1, §1.4; Ch. 2, §2.3; Ch. 3, §3.4; Ch. 5, §5.3])
      #idx-entry([Extended Riemann Hypothesis (ERH)], [Ch. 2, §2.4; Ch. 18, §18.2])

      #idx-letter("F")
      #idx-entry([Fontaine $p$-adic Hodge theory], [Ch. 10, §10.3; Ch. 17, §17.2])
      #idx-entry([Formal group of a CM elliptic curve], [Ch. 8, §8.2])
      #idx-entry([`Formalism` (Lean library)], [Ch. 11, §11.2; Ch. 14, §14.1; Ch. 17, §17.2; App. A])
      #idx-entry([`Formalism.GaloisCohomology.Sha`], [Ch. 10, §10.3; Ch. 15, §15.2; App. A])
      #idx-entry([`Formalism.LatticeIndexTer.ph`], [Ch. 14, §14.1; App. A])
      #idx-entry([`Formalism.Sa`], [Ch. 5, §5.2; Ch. 11, §11.2; App. A])
      #idx-entry([Frobenius endomorphism], [Ch. 4, §4.1; Ch. 8, §8.2])
      #idx-entry([Functional equation], [Ch. 1, §1.2; Ch. 2, §2.2])

      #idx-letter("G")
      #idx-entry([Gabber's hypersurface], [Ch. 4, §4.4])
      #idx-entry([Galois cohomology], [Ch. 10, §10.1–10.3; Ch. 15, §15.1–15.2])
      #idx-entry([Gan–Gross–Prasad (GGP) periods], [Ch. 7, §7.4; Ch. 12, §12.1, §12.4])
      #idx-entry([Gauss sum $tau(chi)$], [Ch. 2, §2.2; Ch. 4, §4.4])
      #idx-entry([Generalized Riemann Hypothesis (GRH)], [Ch. 2, §2.3; Ch. 16, §16.3])
      #idx-entry([Gross, Benedict H.], [Ch. 6, §6.4; Ch. 7, §7.4])
      #idx-entry([`GroundTheory`, `GroundTheoryFields`], [Ch. 17, §17.2; App. A])
      #idx-entry([GUE (Gaussian Unitary Ensemble)], [Ch. 3, §3.4])
      #idx-entry([Guinand–Weil explicit formula], [Ch. 3, §3.4; Ch. 11, §11.2])

      #idx-letter("H")
      #idx-entry([Hadamard, Jacques], [Ch. 1, §1.3–1.4; Ch. 3, §3.1])
      #idx-entry([Hadamard product formula], [Ch. 1, §1.3; Ch. 2, §2.2])
      #idx-entry([Harder–Narasimhan filtration and slopes $mu_max, mu_min$], [Ch. 9, §9.2; Ch. 14, §14.1])
      #idx-entry([Hardy, G. H.], [Ch. 3, §3.2])
      #idx-entry([Hecke character], [Ch. 6, §6.1; Ch. 7, §7.2; Ch. 12, §12.2])
      #idx-entry([`HeightS` (height bound)], [Ch. 14, §14.2; Ch. 16, §16.2; App. A])
      #idx-entry([Hermitian lattice], [Ch. 6, §6.4; Ch. 9, §9.1; Ch. 13, §13.1])
      #idx-entry([Hermitian vector bundle $overline(E)$], [Ch. 9, §9.1–9.3])
      #idx-entry([Hilbert–Pólya conjecture], [Ch. 3, §3.4])
      #idx-entry([Howe duality], [Ch. 7, §7.2])
      #idx-entry([Human–AI mathematical collaboration], [Ch. 18, §18.3])
      #idx-entry([Hyperelliptic curve over $bb(F)_q$], [Ch. 4, §4.1–4.2])

      #idx-letter("I")
      #idx-entry([Inert prime $p$ in a CM field], [Ch. 8, §8.2; Ch. 13, §13.1])
      #idx-entry([Integral structure across Hecke characters], [Ch. 13, §13.2])
      #idx-entry([Interlacing weights (GGP)], [Ch. 12, §12.1])
      #idx-entry([Invariant derivation $D$ ($D^p equiv 0$)], [Ch. 8, §8.2; Ch. 13, §13.1])
      #idx-entry([Isobaric transfer $pi |-> pi plus.square mu_j [t]$], [Ch. 12, §12.2–12.3])
      #idx-entry([Iwasawa theory and $bb(Z)_ell$-towers], [Ch. 10, §10.4; Ch. 15, §15.1–15.3])

      #idx-letter("J")
      #idx-entry([Jacquet–Rallis relative trace formula], [Ch. 13, §13.3])
      #idx-entry([Jacquet–Shalika theorem], [Ch. 6, §6.2])

      #idx-letter("K")
      #idx-entry([Katz, Nicholas M.], [Ch. 3, §3.4; Ch. 4, §4.4; Ch. 8, §8.3])
      #idx-entry([Kazhdan–Patterson metaplectic forms], [Ch. 13, §13.3])
      #idx-entry([Korobov–Vinogradov zero-free region], [Ch. 3, §3.1])
      #idx-entry([Kudla, Stephen S.], [Ch. 7, §7.2–7.4; Ch. 12, §12.4])
      #idx-entry([Kudla splitting of the metaplectic cover], [Ch. 7, §7.2; Ch. 12, §12.2])

      #idx-letter("L")
      #idx-entry([Landau's nonvanishing theorem], [Ch. 5, §5.3; Ch. 11, §11.2])
      #idx-entry([`Lemmata` (Lean library)], [Ch. 17, §17.2; App. A])
      #idx-entry([`LFunction_eq_zero_re`], [Ch. 11, §11.1; Ch. 16, §16.3; App. A])
      #idx-entry([`LFunction_eq_zero_re_of_isPrimitive`], [Ch. 16, §16.3; App. A])
      #idx-entry([`LFunction_ne_zero_of_half_lt_re`], [Ch. 11, §11.1; Ch. 16, §16.3; App. A])
      #idx-entry([Lichtenbaum conjecture], [Ch. 15, §15.2])
      #idx-entry([Local divisibility of $D^a theta(0) \/ Omega^a$], [Ch. 8, §8.2–8.3; Ch. 13, §13.1])
      #idx-entry([Logarithmic Stirling function $op("ph")(nu) = nu log nu - nu$], [Ch. 14, §14.1])

      #idx-letter("M")
      #idx-entry([`Main.lean`], [Ch. 11, §11.1; Ch. 16, §16.3; Ch. 17, §17.1; App. A])
      #idx-entry([Mathlib4], [Preface; Ch. 17, §17.1, §17.3])
      #idx-entry([Mazur–Wiles Main Conjecture], [Ch. 10, §10.4; Ch. 15, §15.2])
      #idx-entry([Mellin transform and inversion], [Ch. 5, §5.1–5.2; Ch. 11, §11.2])
      #idx-entry([Metaplectic cover (sixfold cover of $op("GL")_5$)], [Ch. 13, §13.3])
      #idx-entry([Minkowski's lattice point theorem], [Ch. 9, §9.1–9.2])
      #idx-entry([Mollifier method (Selberg, Levinson, Conrey)], [Ch. 3, §3.2])
      #idx-entry([Montgomery pair correlation conjecture], [Ch. 3, §3.4])
      #idx-entry([Multiplicity $m$ via iterated lifts], [Ch. 12, §12.2–12.3])

      #idx-letter("N")
      #idx-entry([`nanoda` (independent Lean checker)], [Ch. 17, §17.3; App. B])
      #idx-entry([Nonvanishing right of $1\/2$], [Ch. 11, §11.1; Ch. 16, §16.3])
      #idx-entry([Norms of theta lifts], [Ch. 7, §7.3; Ch. 13, §13.1])

      #idx-letter("O")
      #idx-entry([$O(2, n)$ multiplicity-2 prototype], [Ch. 12, §12.1; App. B])
      #idx-entry([Oscillator (Weil) representation], [Ch. 7, §7.1])

      #idx-letter("P")
      #idx-entry([$p$-adic Hodge theory (`GroundTheory.PAdicHodge`)], [Ch. 10, §10.3; Ch. 17, §17.2])
      #idx-entry([Period integral], [Ch. 7, §7.4; Ch. 12, §12.4; Ch. 13, §13.3])
      #idx-entry([Perron's formula], [Ch. 5, §5.2])
      #idx-entry([Poincaré bundle on CM curves], [Ch. 8, §8.3])
      #idx-entry([Poincaré series norm bound], [Ch. 13, §13.3])
      #idx-entry([Poitou–Tate duality], [Ch. 10, §10.2; Ch. 15, §15.2])
      #idx-entry([`PositivityTheory` (Lean library)], [Ch. 11, §11.2; Ch. 17, §17.2; App. A])
      #idx-entry([Prime Number Theorem], [Ch. 1, §1.4; Ch. 3, §3.1])
      #idx-entry([Prime-counting function $pi(x)$], [Ch. 1, §1.1, §1.4])
      #idx-entry([`propext`], [Ch. 17, §17.3])

      #idx-letter("Q")
      #idx-entry([$q N = M^k + R$ sign-only proof], [Ch. 4, §4.4; App. B])
      #idx-entry([`Quot.sound`], [Ch. 17, §17.3])

      #idx-letter("R")
      #idx-entry([Rallis inner product formula], [Ch. 7, §7.3; Ch. 12, §12.4; Ch. 13, §13.1])
      #idx-entry([Rankin–Selberg $L$-function], [Ch. 6, §6.2; Ch. 7, §7.3])
      #idx-entry([`ReciprocityTheory` (Lean library)], [Ch. 17, §17.2; App. A])
      #idx-entry([Relative trace formula], [Ch. 13, §13.3])
      #idx-entry([*Remark* (Alpöge, 2026)], [Preface; Ch. 11, §11.1; Ch. 18, §18.1; App. B])
      #idx-entry([Riemann, Bernhard (1859 memoir)], [Ch. 1, §1.1–1.4])
      #idx-entry([Riemann Hypothesis], [Ch. 1, §1.3; Ch. 16, §16.3])
      #idx-sub([equivalences], [Ch. 1, §1.4; Ch. 3, §3.4–3.5; Ch. 5, §5.3])
      #idx-sub([over finite fields], [Ch. 3, §3.3; Ch. 4, §4.1–4.4])
      #idx-entry([`RiemannHypothesis` (Mathlib4 statement)], [Ch. 11, §11.1; Ch. 16, §16.3; Ch. 17, §17.1])
      #idx-entry([`riemannHypothesis` (`Main.lean`)], [Ch. 16, §16.3; App. A])
      #idx-entry([Riemann–von Mangoldt formula], [Ch. 1, §1.3; Ch. 2, §2.3])
      #idx-entry([`riemannZeta_eq_zero_re`], [Ch. 16, §16.3; App. A])

      #idx-letter("S")
      #idx-entry([$S_a (x)$ smoothed sum], [Ch. 5, §5.2; Ch. 11, §11.2; Ch. 16, §16.1])
      #idx-entry([Sarnak, Peter], [Ch. 3, §3.4; Ch. 18, §18.1])
      #idx-entry([Scale parameters $(x, epsilon, L, b, a)$], [Ch. 11, §11.3; Ch. 14, §14.2; Ch. 16, §16.1])
      #idx-entry([Seesaw duality], [Ch. 7, §7.4; Ch. 12, §12.4])
      #idx-entry([Selberg, Atle], [Ch. 3, §3.2, §3.4; Ch. 8, §8.3])
      #idx-entry([Selmer group and $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$], [Ch. 10, §10.3; Ch. 15, §15.2])
      #idx-entry([Siegel mass formula], [Ch. 13, §13.1–13.2])
      #idx-entry([Siegel zero], [Ch. 2, §2.3; Ch. 3, §3.1])
      #idx-entry([Simplifications of the proof], [Ch. 18, §18.1])
      #idx-entry([Slope polygon (Harder–Narasimhan)], [Ch. 9, §9.2; Ch. 14, §14.1])
      #idx-entry([Smoothed von Mangoldt sum], [Ch. 5, §5.2; Ch. 11, §11.2])
      #idx-entry([Stepanov, S. A.], [Ch. 4, §4.1–4.4])
      #idx-entry([Stepanov determinant], [Ch. 4, §4.2; Ch. 12, §12.1; App. B])
      #idx-entry([`Supplements` (Lean library)], [Ch. 17, §17.2; App. A])

      #idx-letter("T")
      #idx-entry([Tate's thesis], [Ch. 2, §2.2; Ch. 6, §6.1])
      #idx-entry([Tate–Shafarevich kernel $op("Ш")^1_S$], [Ch. 10, §10.3; Ch. 15, §15.2])
      #idx-entry([Theta correspondence (unitary)], [Ch. 7, §7.1–7.4; Ch. 12, §12.1–12.4])
      #idx-entry([Theta kernel $theta_phi (g, h)$], [Ch. 7, §7.1])
      #idx-entry([Theta series index], [Ch. 13, §13.4; Ch. 14, §14.1])
      #idx-entry([Totally definite unitary group $U(X)$], [Ch. 6, §6.4; Ch. 12, §12.1–12.2])
      #idx-entry([Trivial zeros of $zeta(s)$ and $L(s, chi)$], [Ch. 1, §1.2; Ch. 2, §2.2])
      #idx-entry([Two-thirds ($2\/3$) barrier], [Ch. 14, §14.3])

      #idx-letter("U")
      #idx-entry([Unitary dual pair $(U(V), U(W))$], [Ch. 7, §7.2; Ch. 12, §12.1])
      #idx-entry([`UpperTheory.FinalTheorems`], [Ch. 16, §16.3; App. A])

      #idx-letter("V")
      #idx-entry([Vandiver's conjecture (weakened)], [Ch. 10, §10.4; Ch. 15, §15.1–15.4])
      #idx-entry([Verification pipeline (Lean FRO)], [Ch. 17, §17.3; App. B])
      #idx-entry([von Mangoldt function $Lambda(n)$], [Ch. 1, §1.4; Ch. 5, §5.2; Ch. 11, §11.2])
      #idx-entry([`VWin` (weakened Vandiver window)], [Ch. 15, §15.1–15.4; Ch. 16, §16.2; App. A])

      #idx-letter("W")
      #idx-entry([Weil, André], [Ch. 3, §3.3–3.4; Ch. 4, §4.1; Ch. 7, §7.1])
      #idx-entry([Weil conjectures], [Ch. 3, §3.3; Ch. 4, §4.1, §4.4])
      #idx-entry([Weil positivity criterion $W(dot) >= 0$], [Ch. 3, §3.4; Ch. 11, §11.2; Ch. 12, §12.1])
      #idx-entry([Weil representation], [Ch. 7, §7.1–7.2])
      #idx-entry([Weyl character formula / divisibility], [Ch. 13, §13.1])

      #idx-letter("Z")
      #idx-entry([Zero-density estimates], [Ch. 3, §3.2])
      #idx-entry([Zero-free region], [Ch. 1, §1.4; Ch. 2, §2.3; Ch. 3, §3.1; Ch. 5, §5.3])
      #idx-entry([Zeta function $zeta(s)$], [Ch. 1, §1.1–1.4])
      #idx-entry([Zhang, Wei], [Ch. 7, §7.4; Ch. 13, §13.3])
    ]
  ]
]
