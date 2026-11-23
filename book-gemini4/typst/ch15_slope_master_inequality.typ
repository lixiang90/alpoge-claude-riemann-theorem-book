// ============================================================================
// Chapter 15: The Divisor-Slope Master Inequality and Height Bounds
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch15() = [
  #chapter(
    "The Divisor-Slope Master Inequality and Height Bounds",
    short-title: "Divisor-Slope Master Inequality",
    epigraph: "The arithmetic slope of a Hermitian vector bundle is the bridge by which local integrality constraints at finite primes force global analytic inequalities at archimedean places.",
    epigraph-source: "After Jean-Benoît Bost, Périodes et isogénies des variétés abéliennes sur les corps de nombres (1996)",
    overview: [
      In Chapters 11 through 14 we assembled the geometric, representation-theoretic, and Arakelov-theoretic components of the Alpöge–Claude–Riemann architecture: Harder–Narasimhan filtrations of Hermitian lattices, local index estimates at finite places, quotient metrics on abelian-variety cohomology, and covolume bounds derived from arithmetic Hilbert–Samuel theory on Siegel toroidal compactifications. The present chapter synthesizes all of these ingredients into the two master inequalities that form the arithmetic pivot of the proof. First, we translate the complete lattice-comparison datum of `DivIneqObjU` into graduate mathematical language, glue the local lattices into a global Hermitian lattice $R$, and apply Bost's slope inequality together with a good/bad Harder–Narasimhan decomposition to prove the Divisor-Slope Master Inequality. Second, we prove the Height Sum Bound `HeightS`, combining archimedean embedding averages, period integrals, theta zero-values, and the Arakelov covolume bound `CovolumeBoundOfX`. Finally, we eliminate the intermediate height term $h_u$ between `DivIneqObjU` and `HeightS` to extract the exact one-sided upper bound on the smoothed prime sum required by `TopG`.
    ],
    label-name: "ch-slope-master-inequality",
  )

  == Setup of the Arithmetic Lattice Comparison Problem

  At the heart of the Arakelov-theoretic reduction of the Generalized Riemann Hypothesis lies a comparison between two fundamentally different ways of measuring the size of a global lattice over a CM number field. On one side stands a *glued* Hermitian lattice $R$, assembled place by place from local abelian-variety lattices carrying quotient metrics and twisted by rational matrices at a finite set of primes. On the other side stands a finite family of *reference* Hermitian lattices $M_j$ ($j in J$), whose slopes are controlled from below by automorphic and representation-theoretic input, together with a family of auxiliary lattices $op("Tl")_(j, t)$ encoding local division-value and eigenvalue data. When the archimedean determinant ratios of the glued data factor as a product of the determinant ratios of the reference data up to a scalar twist, the product formula of global number fields couples the global Arakelov slope of the dual lattice $R^or$ directly to the sum of the slopes of the $M_j$ and the weighted local indices at every finite place.

  We begin by recording the complete algebraic and Hermitian datum of this comparison problem, matching every object and hypothesis of the Lean 4 specification `DivIneqObjU` in `Formalism.DivisorInequality.DivIneqTopAnchorU`.

  === The CM Field, Archimedean Frames, and Local Comparison Types

  Let $K$ be a totally complex number field equipped with a star involution $alpha |-> alpha^*$ (complex conjugation) and a maximal totally real subfield $K_0 subset.eq K$ fixed by the involution, so that $K / K_0$ is a CM extension (`IsCMSub K0`). Let $Sigma_oo (K)$ denote the set of archimedean places of $K$, and fix a distinguished infinite place $v_0 in Sigma_oo (K)$ at which complex conjugation in $bb(C)$ agrees with the star involution on $K$ (`IsConjAt v0`), meaning that
  $ v_0 (alpha^*) = overline(v_0 (alpha)) quad (forall alpha in K). $
  Let $cal(O)_K$ be the ring of integers of $K$, and let $op("Spec")_1 (cal(O)_K)$ denote the set of nonzero prime ideals $y$ of $cal(O)_K$ (the height-one spectrum of $cal(O)_K$). The CM involution induces an involution $y |-> bar(y)$ on $op("Spec")_1 (cal(O)_K)$ (denoted `conjPl y` in the formalization). For each $y in op("Spec")_1 (cal(O)_K)$, let $v_y : K^times -> bb(Z)$ denote the normalized discrete valuation at $y$ (written `vw y`), let $op("plc")(y) in bb(N)$ denote the residue characteristic of $y$, let $op("ramw")(y) in bb(N)$ denote its ramification weight, and let $op("lw")(y) > 0$ denote the normalized logarithmic weight of the place $y$ in the Arakelov degree formula (proportional to $log N(y) / [K : bb(Q)]$).

  Fix a positive integer rank $D >= 1$ and consider the $D$-dimensional $K$-vector space $V = K^D$. Recall from Chapter 11 that an *archimedean frame* on $K^D$ is a family of invertible complex matrices
  $ X : Sigma_oo (K) -> op("GL")_D (bb(C)), $
  which equips $K^D times_(K, v) bb(C) approx bb(C)^D$ at each infinite place $v$ with the Hermitian inner product whose Gram matrix in the standard basis is $X(v)^* X(v)$ (or equivalently, the norm $norm(z)_v = norm(X(v) z)_2$). A full $cal(O)_K$-lattice $Lambda subset K^D$ paired with an archimedean frame $X$ defines a Hermitian vector bundle $(Lambda, X)$ over $op("Spec")(cal(O)_K)$.

  To compare lattices across all finite places simultaneously, we introduce a parameter set $op("Tup")$ of *local comparison types* equipped with a distinguished *base type* $mu_0 in op("Tup")$, together with a type assignment
  $ mu : op("Spec")_1 (cal(O)_K) -> op("Tup") $
  satisfying two structural axioms:
  1. *Conjugation invariance*: $mu(bar(y)) = mu(y)$ for every $y in op("Spec")_1 (cal(O)_K)$.
  2. *Finite support of twists*: the set ${ y in op("Spec")_1 (cal(O)_K) : mu(y) != mu_0 }$ is finite.

  Conceptually, $mu_0$ represents the unramified (generic) local configuration, while the finitely many places $y$ with $mu(y) != mu_0$ are the places where a nontrivial local twist—coming from the prime-power support of our analytic test function or from inert primes—alters the local lattice.

  #definition(title: "Arithmetic Lattice Comparison Datum")[
    Fix $(K / K_0, v_0, D)$ and $(op("Tup"), mu_0, mu)$ as above, together with a finite index set $J$ of cardinality $|J| = m >= 1$. An *arithmetic lattice comparison datum* consists of the following families of archimedean frames, full $cal(O)_K$-lattices in $K^D$, and invertible transition matrices:
    - An *ambient reference frame* $X_E : Sigma_oo (K) -> op("GL")_D (bb(C))$.
    - For each type $t in op("Tup")$, an *abelian quotient frame* $X_Q (t) : Sigma_oo (K) -> op("GL")_D (bb(C))$, a full $cal(O)_K$-lattice $cal(A)_2 (t) subset K^D$ (denoted `abelian₂ t` in Lean), and an invertible transition matrix $iota(t) in op("GL")_D (K)$.
    - For each index $j in J$, a *comparison frame* $X_W (j) : Sigma_oo (K) -> op("GL")_D (bb(C))$ and a full $cal(O)_K$-lattice $M_j subset K^D$.
    - For each $j in J$ and $t in op("Tup")$, a rational Hermitian matrix $H_T (j, t) in M_D (K)$, an archimedean frame $X_T (j, t) : Sigma_oo (K) -> op("GL")_D (bb(C))$, a full $cal(O)_K$-lattice $op("Tl")_(j, t) subset K^D$, and a transition matrix $theta_(j, t) in op("GL")_D (K)$.

    The pairs $(H_T (j, t), X_T (j, t))$ are required to satisfy two Hermitian compatibility conditions:
    1. *Global rational Hermitian compatibility at the base type*: for every $j in J$, the matrix $H_T (j, mu_0)$ is rationally Hermitian over $K_0$ with respect to $X_T (j, mu_0)$ (`IsRatHerm K0 (HT j μ0) (XT j μ0)`).
    2. *Distinguished-place Hermitian compatibility for all types*: for every $j in J$ and every $t in op("Tup")$, $H_T (j, t)$ is Hermitian with respect to $X_T (j, t)$ at the distinguished place $v_0$ (`IsHermAt v0 (HT j t) (XT j t)`).
  ]

  === The Determinant-Ratio Identities

  Given two archimedean frames $X_1, X_2 : Sigma_oo (K) -> op("GL")_D (bb(C))$ and a rational change-of-basis matrix $g in op("GL")_D (K)$, the *determinant ratio* at an infinite place $v in Sigma_oo (K)$ measures the local volume distortion induced by $g$ between the two Hermitian structures:
  $ op("detRatio")(X_1, X_2, g, v) = (|det(X_1 (v))| dot.c |v(det g)|) / |det(X_2 (v))| in bb(R)_(> 0) $
  (up to the fixed normalization convention of `Formalism.DivisionValues`—the crucial property is multiplicativity in $(X_1, X_2, g)$ and homogeneity of degree $D$ under scalar rescaling of the frame).

  In our comparison datum, the determinant ratios of the abelian frames $X_Q (t)$ relative to $X_E$ are locked to the product over $j in J$ of the determinant ratios of $X_T (j, t)$ relative to $X_W (j)$ via two scalar factors:
  - A positive archimedean weight function $kappa : Sigma_oo (K) -> bb(R)_(> 0)$ satisfying the vanishing mean-logarithm normalization
    $ op("meanLog")(kappa) = 1 / |Sigma_oo (K)| sum_(v in Sigma_oo (K)) log kappa(v) = 0. $
  - Rational and real twist scalars $rho_D : op("Tup") -> K$ and $rho_r : op("Tup") -> bb(R)_(> 0)$ normalized at the base type by $rho_D (mu_0) = 1$ and $rho_r (mu_0) = 1$, satisfying
    $ v_0 (rho_D (t)) = rho_r (t)^D quad (forall t in op("Tup")) $
    and the integrality-unit condition
    $ v_y (rho_D (mu(y))) = 0 quad (forall y in op("Spec")_1 (cal(O)_K)). $

  With these scalars in place, the determinant ratios satisfy the *global base-type identity* at every infinite place $v in Sigma_oo (K)$,
  $ & op("detRatio")(X_Q (mu_0), X_E, iota(mu_0), v) \
    & quad = kappa(v)^D product_(j in J) op("detRatio")(X_T (j, mu_0), X_W (j), theta_(j, mu_0), v), $
  and the *distinguished-place twisted identity* for every type $t in op("Tup")$,
  $ & op("detRatio")(X_Q (t), X_E, iota(t), v_0) \
    & quad = (kappa(v_0) rho_r (t))^D product_(j in J) op("detRatio")(X_T (j, t), X_W (j), theta_(j, t), v_0). $

  Notice the arithmetic force of these two equations. At the generic type $mu_0$, the determinant ratio factors at *every* infinite place $v in Sigma_oo (K)$. At a twisted type $t != mu_0$, we only require the factorization at the single distinguished place $v_0$, where the extra factor $rho_r (t)^D$ is the image under $v_0$ of a global element $rho_D (t) in K$ that is a unit at every finite place $y$ where $mu(y) = t$. When we pass to the Arakelov degree via the product formula, the factor $kappa(v)^D$ disappears because $op("meanLog")(kappa) = 0$, while $rho_D (mu(y))$ contributes zero finite valuation at $y$!

  === Quotient Metrics, Local Gram Determinants, and the Glued Lattice $R$

  To control the finite-place contribution of the abelian lattices $cal(A)_2 (t)$, we introduce local bases and Gram determinants. For each $t in op("Tup")$ and $y in op("Spec")_1 (cal(O)_K)$, let $e_b (t, y) : op("Fin") D -> K^D$ be a local $cal(O)_(K, y)$-basis of the localization $cal(A)_2 (t)_y$ (`IsLocBasis (abelian₂ t) y (eb t y)`), and let $G_m (t, y) in K$ be a rational representative of its archimedean Gram determinant at $v_0$:
  $ v_0 (G_m (t, y)) = det(op("gram")(X_Q (t), v_0, e_b (t, y))). $
  At the base type $mu_0$, the Hermitian structure $X_Q (mu_0)$ is not arbitrary: it arises as a *quotient Hermitian metric* from a larger positive-definite Hermitian lattice. Specifically, there exist an integer $n_H >= D$, a matrix $H_m in M_(n_H) (K_0)$ whose image under every archimedean embedding $v in Sigma_oo (K)$ is Hermitian positive definite, a surjective $K$-linear map $P_m : K^(n_H) -> K^D$, and a full $cal(O)_K$-lattice $M_t subset K^(n_H)$ such that:
  1. $cal(A)_2 (mu_0) = P_m (M_t)$ as $cal(O)_K$-submodules of $K^D$;
  2. $X_Q (mu_0)$ carries the quotient metric induced by $(P_m, H_m)$ (`IsQuotMetric Pm Hm (XQ μ0)`), meaning that the induced Hermitian form on $K^D approx K^(n_H) / ker(P_m)$ is given by the orthogonal projection with respect to $H_m$, whose Gram matrix in the standard basis is the rational quotient Gram matrix
     $ op("quotGram")(P_m, H_m) = (P_m H_m^(-1) P_m^*)^(-1); $
  3. for every finite place $y in op("Spec")_1 (cal(O)_K)$, the rational Gram determinant $G_m (mu_0, y)$ coincides identically with the algebraic Gram determinant of the local basis $e_b (mu_0, y)$ with respect to $op("quotGram")(P_m, H_m)$:
     $ G_m (mu_0, y) = op("gramR")(op("quotGram")(P_m, H_m), e_b (mu_0, y)). $

  Finally, we assemble the *glued lattice* $R subset K^D$. Because $mu(y) = mu_0$ for all but finitely many $y in op("Spec")_1 (cal(O)_K)$, the local-global correspondence for lattices over Dedekind domains guarantees that there exists a unique full $cal(O)_K$-lattice $R subset K^D$ whose localization at every finite place $y$ matches the shifted lattice $iota(mu(y)) (cal(A)_2 (mu(y)))$:
  $ R_y = (iota(mu(y)) cal(A)_2 (mu(y)))_y quad (forall y in op("Spec")_1 (cal(O)_K)). $
  In the Lean formalization, this gluing axiom is recorded verbatim as
  `localization₂ y.asIdeal R = localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))`.

  #insight-box(title: "Why Glue Locally and Dualize Globally?")[
    The glued lattice $R$ does not arise as a single global image $iota(t)(cal(A)_2 (t))$ for any fixed $t in op("Tup")$; rather, it stitches together the untwisted quotient lattice $iota(mu_0) P_m (M_t)$ at almost all places with the twisted lattices $iota(mu(y)) cal(A)_2 (mu(y))$ at the finitely many places $y$ in the support of the twist. By passing to the dual Hermitian lattice $(R^or, X_E^*)$, the local-global index of $R$ against the reference lattices $M_j$ converts multiplicative local divisibility into an additive upper bound on the Arakelov slope $mu_0 = hat(mu)(R^or, X_E^*)$. Meanwhile, the quotient-metric property at $mu_0$ ensures that the rational Gram determinants $G_m (mu_0, y)$ are controlled by the integral structure of $M_t$, preventing uncontrolled denominators outside the finite bad set $S_y$.
  ]

  === Finite-Place Support Sets $T_w subset.eq S_y$ and Local Index Bounds

  To organize the finite-place contributions in the Arakelov degree formula, we fix two finite sets of nonzero prime ideals
  $ T_w subset.eq S_y subset op("Spec")_1 (cal(O)_K). $
  Here $S_y$ is the *global bad-place support* (containing all places where either the Gram determinant valuation or the lattice indices are nonzero), while $T_w subset.eq S_y$ is the *twisted support* (the subset of places where the comparison lattices $M_j$ and $theta_(j, mu(y)) op("Tl")_(j, mu(y))$ actually differ).

  For any two full $cal(O)_K$-lattices $Lambda_1, Lambda_2 subset K^D$ and any $y in op("Spec")_1 (cal(O)_K)$, let $op("idx")_y (Lambda_1, Lambda_2) in bb(Z)$ denote the local $y$-adic lattice index (the $y$-adic valuation of the determinant of a local change-of-basis matrix taking $Lambda_(1, y)$ to $Lambda_(2, y)$), and let $op("jw")(H_T (j, t), y, op("Tl")_(j, t)) in bb(Z)$ denote the local Hermitian discriminant valuation of the lattice $op("Tl")_(j, t)$ with respect to the rational Hermitian form $H_T (j, t)$ at $y$. Define the combined $j$-indexed local discrepancy at $y$ by
  $ Delta_j (y) &= op("idx")_y (M_j, theta_(j, mu(y)) op("Tl")_(j, mu(y))) + op("idx")_(bar(y)) (M_j, theta_(j, mu(y)) op("Tl")_(j, mu(y))) \
    & quad + op("jw")(H_T (j, mu(y)), y, op("Tl")_(j, mu(y))). $
  The support sets $T_w subset.eq S_y$ satisfy two exact vanishing hypotheses:
  1. *Vanishing outside $S_y$*: for every $y in.not S_y$,
     $ op("lw")(y) (v_y (G_m (mu(y), y)) + sum_(j in J) Delta_j (y)) = 0. $
  2. *Vanishing of lattice discrepancies outside $T_w$*: for every $y in S_y without T_w$ and every $j in J$,
     $ Delta_j (y) = 0. $

  On $S_y$, the Gram determinant valuations are bounded by a local envelope $g_y : op("Spec")_1 (cal(O)_K) -> bb(R)$ with global weighted sum bounded by $L_G in bb(R)$:
  $ v_y (G_m (mu(y), y)) <= D dot.c g_y (y) quad (forall y in S_y), \
    sum_(y in S_y) op("lw")(y) g_y (y) <= L_G. $

  On the twisted support $T_w$, the local lattice indices and Hermitian discriminant valuations satisfy a fine system of local upper bounds parameterized by a threshold $delta_q > 0$, a dimension-scale $d_K : J -> bb(R)$ satisfying $d_K (j) / delta_q <= 3 D$, and local real-valued functions $e_0, r_0, epsilon_0, F_0, op("err")_ell, J_y, eta_y : op("Spec")_1 (cal(O)_K) times J -> bb(R)$ and $v_(U, 0), g_q : op("Spec")_1 (cal(O)_K) -> bb(R)$:
  - *Local index bounds at $y$ and $bar(y)$*: for every $y in T_w$ and $j in J$,
    $ & op("idx")_y (M_j, theta_(j, mu(y)) op("Tl")_(j, mu(y))) \
      & quad <= op("ramw")(y) ( (e_0 (y, j) + v_(U, 0) (y)) D \
      & quad + (r_0 (y, j) + d_K (j) v_(U, 0) (y)) / delta_q + epsilon_0 (y, j) ), $
    and the analogous bound holds with $y$ replaced by $bar(y)$ (and $op("ramw")(y)$ replaced by $op("ramw")(bar(y))$).
  - *Symmetry and domination of the unipotent valuation $v_(U, 0)$*: for every $y in T_w$,
    $ 0 <= v_(U, 0) (y), wide v_(U, 0) (bar(y)) = v_(U, 0) (y), wide 4 v_(U, 0) (y) <= g_q (y). $
  - *Decomposition into inert-prime main term $F_0$ and local error $op("err")_ell$*: $F_0 (y, j) = 0$ for $y in S_y without T_w$, and for every $y in T_w$ and $j in J$,
    $ e_0 (y, j) + e_0 (bar(y), j) - 2 F_0 (y, j) + 2 g_q (y) <= op("err")_ell (y, j). $
  - *Inverse-square residue-characteristic tail*: for every $y in T_w$,
    $ sum_(j in J) (epsilon_0 (y, j) + epsilon_0 (bar(y), j)) <= 2 / op("plc")(y)^2. $
  - *Hermitian discriminant valuation bound*: for every $y in T_w$ and $j in J$,
    $ op("jw")(H_T (j, mu(y)), y, op("Tl")_(j, mu(y))) <= J_y (y, j) D + eta_y (y, j). $

  These local estimates aggregate into five global error budgets $L_G$, $E_A (j)$, $R_b (j)$, $E_J (j)$, $E_2 (j)$ and one global inert-prime divisibility functional $F_0$ (written `Fo` in Lean):
  $ sum_(y in T_w) op("lw")(y) op("ramw")(y) op("err")_ell (y, j) <= E_A (j), \
    sum_(y in S') op("lw")(y) op("ramw")(y) r_0 (y, j) <= R_b (j) quad (forall S' subset.eq op("Spec")_1 (cal(O)_K)), $
  $ sum_(y in T_w) op("lw")(y) J_y (y, j) <= E_J (j), wide sum_(y in T_w) op("lw")(y) (eta_y (y, j) / D) <= E_2 (j), $
  $ F_0 = sum_(j in J) sum_(y in T_w) op("lw")(y) op("ramw")(y) F_0 (y, j). $
  Note that the second inequality holds for *every* finite subset $S'$ of $op("Spec")_1 (cal(O)_K)$, which allows us to bound both the sum of $r_0 (y, j)$ over $y in T_w$ and the sum of $r_0 (bar(y), j)$ over $y in T_w$ (by taking $S' = bar(T)_w$) by the same quantity $R_b (j)$.

  == Applying Bost's Slope Inequality to the Glued Lattice $R$

  With the arithmetic lattice comparison datum in hand, we now execute the three-stage slope comparison that links the comparison slope $mu_C$ to the reference lattices $M_j$ and the local index sums. In the formalization, the normalized Arakelov slope of a full Hermitian lattice $(Lambda, X)$ of rank $D$ over $K$ is defined by `Formalism.HN.muDef`, which satisfies the fundamental duality relation between log-covolume and slope:
  $ op("lcv")(X, Lambda) / D = -hat(mu)(Lambda, X). $
  For the glued lattice $R$ equipped with the reference frame $X_E$, we denote the slope of the dual Hermitian lattice $(R^or, X_E^*)$ by
  $ mu_0 = hat(mu)(R^or, X_E^*) = op("muDef")(cal(B)^or, X_E^*, R^or), $
  where $cal(B)^or$ is the dual basis to the standard basis of $K^D$.

  === Stage 1: Local-to-Global Covolume Bound for $mu_0$

  The first step applies the Arakelov product formula and the determinant-ratio identities to express $mu_0$ in terms of the slopes $hat(mu)(M_j, X_W (j))$ and the finite-place indices over $S_y$ and $T_w$.

  #proposition(title: "Global Slope Bound for the Dual Glued Lattice")[
    Under the hypotheses of Section 15.1, assume in addition that $op("meanLog")(kappa) = 0$. Then the dual slope $mu_0 = hat(mu)(R^or, X_E^*)$ satisfies
    $ mu_0 &<= -sum_(j in J) hat(mu)(M_j, X_W (j)) + 2 F_0 + L_G \
      & quad + sum_(j in J) (E_A (j) + (2 R_b (j)) / (delta_q D) + E_J (j) + E_2 (j)) + E_3, $
    where $E_3 = sum_(y in S_y) op("lw")(y) dot.c 2 / op("plc")(y)^2$ is the weighted inverse-square prime tail.
  ]

  #proof[
    By the covolume comparison theorem `BoundsMu` (formalized in `Formalism.DivisorInequality.StatementObj`), the determinant-ratio identities at $mu_0$ (for all $v in Sigma_oo (K)$) and at $v_0$ (for all $t in op("Tup")$), together with the quotient-metric identity $G_m (mu_0, y) = op("gramR")(op("quotGram")(P_m, H_m), e_b (mu_0, y))$, the unit condition $v_y (rho_D (mu(y))) = 0$, and the vanishing of local discrepancies outside $S_y$ and $T_w$, yield the general slope inequality
    $ mu_0 &<= op("meanLog")(kappa) + sum_(j in J) op("lcv")(X_W (j), M_j) / D + 2 sum_(j in J) sum_(y in T_w) op("lw")(y) F_y (y, j) \
      & quad + L_G + sum_(j in J) (E_1 (j) + E_2 (j)) + E_3, $
    whenever $F_y, op("err")_y, J_y, eta_y$ satisfy the aggregated local bounds
    $ & sum_(j in J) (op("idx")_y (M_j, theta_(j, mu(y)) op("Tl")_(j, mu(y))) + op("idx")_(bar(y)) (M_j, theta_(j, mu(y)) op("Tl")_(j, mu(y)))) \
      & quad <= (sum_(j in J) (2 F_y (y, j) + op("err")_y (y, j)) + 2 / op("plc")(y)^2) D $
    for all $y in T_w$, and $sum_(y in T_w) op("lw")(y) (op("err")_y (y, j) + J_y (y, j)) <= E_1 (j)$.

    Let us verify that our local hypotheses from Section 15.1 imply these bounds with $F_y (y, j) = op("ramw")(y) F_0 (y, j)$ and $E_1 (j) = E_A (j) + 2 R_b (j) / (delta_q D) + E_J (j)$. Fix $y in T_w$ and $j in J$. Since the CM involution preserves ramification degree, $op("ramw")(bar(y)) = op("ramw")(y)$, and by hypothesis $v_(U, 0) (bar(y)) = v_(U, 0) (y) >= 0$. Adding the local index bounds at $y$ and $bar(y)$ gives
    $ op("idx")_y + op("idx")_(bar(y)) &<= op("ramw")(y) ( (e_0 (y, j) + e_0 (bar(y), j) + 2 v_(U, 0) (y)) D \
      & quad + (r_0 (y, j) + r_0 (bar(y), j) + 2 d_K (j) v_(U, 0) (y)) / delta_q \
      & quad + epsilon_0 (y, j) + epsilon_0 (bar(y), j) ). $
    Using the dimension-scale bound $d_K (j) / delta_q <= 3 D$, the terms involving $v_(U, 0) (y)$ combine as
    $ & 2 v_(U, 0) (y) D + 2 (d_K (j) / delta_q) v_(U, 0) (y) \
      & quad <= 2 v_(U, 0) (y) D + 6 v_(U, 0) (y) D = 8 v_(U, 0) (y) D. $
    Because $4 v_(U, 0) (y) <= g_q (y)$, this is bounded above by $2 g_q (y) D$. Substituting the local decomposition $e_0 (y, j) + e_0 (bar(y), j) + 2 g_q (y) <= 2 F_0 (y, j) + op("err")_ell (y, j)$ yields
    $ op("idx")_y + op("idx")_(bar(y)) &<= op("ramw")(y) ( (2 F_0 (y, j) + op("err")_ell (y, j)) D \
      & quad + (r_0 (y, j) + r_0 (bar(y), j)) / delta_q + epsilon_0 (y, j) + epsilon_0 (bar(y), j) ). $
    Now sum over $j in J$. Since $D >= 1$ and $op("ramw")(y) >= 1$ (with the residue-characteristic bound $sum_j (epsilon_0 (y, j) + epsilon_0 (bar(y), j)) <= 2 / op("plc")(y)^2$ absorbed into the $E_3$ term after dividing by $D$), setting
    $ op("err")_y (y, j) = op("ramw")(y) (op("err")_ell (y, j) + (r_0 (y, j) + r_0 (bar(y), j)) / (delta_q D)) $
    gives the required local bound. Summing $op("lw")(y) op("err")_y (y, j)$ over $y in T_w$ and applying the $R_b (j)$ bound twice—once with $S' = T_w$ for $r_0 (y, j)$ and once with $S' = bar(T)_w$ for $r_0 (bar(y), j)$, using $op("lw")(bar(y)) = op("lw")(y)$ and $op("ramw")(bar(y)) = op("ramw")(y)$—produces
    $ sum_(y in T_w) op("lw")(y) op("err")_y (y, j) <= E_A (j) + (2 R_b (j)) / (delta_q D). $
    Adding $sum_(y in T_w) op("lw")(y) J_y (y, j) <= E_J (j)$, noting that $op("meanLog")(kappa) = 0$ and $op("lcv")(X_W (j), M_j) / D = -hat(mu)(M_j, X_W (j))$, and recalling $F_0 = sum_j sum_(y in T_w) op("lw")(y) op("ramw")(y) F_0 (y, j)$ completes the proof.
  ]

  === Stage 2: Comparing the Dual Slope $mu_0$ with the Comparison Slope $mu_C$

  In the global automorphic application, the slope that directly interfaces with the analytic side is not $mu_0 = hat(mu)(R^or, X_E^*)$ itself, but a closely related *comparison slope* $mu_C$ arising from a weighted sum over a finite set $op("Sg")$ of Harder–Narasimhan or representation-theoretic strata $s in op("Sg")$. Each stratum $s in op("Sg")$ carries a nonnegative rank $op("rk")(s) >= 0$ (with total rank $R_"tot" = sum_(s in op("Sg")) op("rk")(s) > 0$), an arithmetic degree $op("dg")(s) in bb(R)$, and a multiplicity $n_S (s) in bb(R)$.

  Let $bar(n) > 0$ be the average multiplicity, $lambda_0 >= 0$ a small perturbation tolerance, $H_0 in bb(R)$ a slope ceiling (written `HH0` in Lean), and $mu_(P, 0), mu_(P, s) in bb(R)$ auxiliary slopes approximating $-mu_0$ and $-mu_C$ respectively. Assume that for parameters $f, r, g$ with $r >= 0$, $g > 0$, and $24 f r <= g$, the following relations hold:
  1. *Uniformity of multiplicities*: for every $s in op("Sg")$,
     $ (1 - (8 f r) / g) bar(n) <= n_S (s) <= (1 + (8 f r) / g) bar(n). $
  2. *Approximation of dual and comparison slopes*:
     $ |(-mu_0) - mu_(P, 0)| <= lambda_0, wide |(-mu_C) - mu_(P, s)| <= lambda_0. $
  3. *Stratum-wise slope ceiling*: for every $s in op("Sg")$,
     $ op("dg")(s) <= op("rk")(s) (H_0 + lambda_0). $
  4. *Weighted and unweighted degree-slope comparisons*:
     $ & sum_(s in op("Sg")) n_S (s) op("dg")(s) - 17 / 2 lambda_0 sum_(s in op("Sg")) n_S (s) op("rk")(s) \
       & quad <= mu_(P, s) sum_(s in op("Sg")) n_S (s) op("rk")(s), $
     $ mu_(P, 0) sum_(s in op("Sg")) op("rk")(s) <= sum_(s in op("Sg")) op("dg")(s) + 2 lambda_0 sum_(s in op("Sg")) op("rk")(s). $

  The following lemma shows that whenever $n_S (s)$ is nearly constant across strata, the weighted slope $mu_(P, s)$ cannot lie far below the unweighted slope $mu_(P, 0)$, which translates immediately into an upper bound on $mu_C - mu_0$.

  #lemma(title: "Weighted-to-Unweighted Slope Comparison")[
    Under hypotheses (1)–(4) above, with $24 f r <= g$, we have
    $ mu_C - mu_0 <= 25 / 2 lambda_0 + (24 f r) / g (H_0 + 4 lambda_0 + mu_0). $
  ]

  #proof[
    Set $delta_S = 8 f r / g$. Since $24 f r <= g$, we have $0 <= delta_S <= 1 / 3$, and hence $1 - delta_S >= 2 / 3 > 0$. In particular,
    $ (1 + delta_S) / (1 - delta_S) = 1 + (2 delta_S) / (1 - delta_S) <= 1 + 3 delta_S = 1 + (24 f r) / g. $
    For each $s in op("Sg")$, define the *degree deficit* relative to the ceiling $H_0 + lambda_0$ by
    $ Delta(s) = op("rk")(s) (H_0 + lambda_0) - op("dg")(s). $
    By hypothesis (3), $Delta(s) >= 0$ for every $s in op("Sg")$. Let $R_"tot" = sum_s op("rk")(s) > 0$ and $N_"tot" = sum_s n_S (s) op("rk")(s)$. By hypothesis (1), $N_"tot" >= (1 - delta_S) bar(n) R_"tot" > 0$, and because $Delta(s) >= 0$,
    $ sum_(s in op("Sg")) n_S (s) Delta(s) <= (1 + delta_S) bar(n) sum_(s in op("Sg")) Delta(s). $
    Dividing the weighted degree identity $sum_s n_S (s) op("dg")(s) = (H_0 + lambda_0) N_"tot" - sum_s n_S (s) Delta(s)$ by $N_"tot" > 0$ and applying hypothesis (4) yields
    $ mu_(P, s) + 17 / 2 lambda_0 &>= (sum_s n_S (s) op("dg")(s)) / N_"tot" = (H_0 + lambda_0) - (sum_s n_S (s) Delta(s)) / N_"tot" \
      &>= (H_0 + lambda_0) - (1 + delta_S) / (1 - delta_S) (sum_s Delta(s)) / R_"tot". $
    Using $(1 + delta_S) / (1 - delta_S) <= 1 + 24 f r / g$ and $(sum_s Delta(s)) / R_"tot" >= 0$, we obtain
    $ mu_(P, s) + 17 / 2 lambda_0 >= (H_0 + lambda_0) - (sum_s Delta(s)) / R_"tot" - (24 f r) / g (sum_s Delta(s)) / R_"tot". $
    Now simplify $(sum_s Delta(s)) / R_"tot" = (H_0 + lambda_0) - (sum_s op("dg")(s)) / R_"tot"$. By the second inequality of hypothesis (4), $(sum_s op("dg")(s)) / R_"tot" >= mu_(P, 0) - 2 lambda_0$, which implies both
    $ (H_0 + lambda_0) - (sum_s Delta(s)) / R_"tot" = (sum_s op("dg")(s)) / R_"tot" >= mu_(P, 0) - 2 lambda_0 $
    and
    $ 0 <= (sum_s Delta(s)) / R_"tot" <= H_0 + 3 lambda_0 - mu_(P, 0). $
    Substituting these two bounds into the previous display gives
    $ mu_(P, s) + 17 / 2 lambda_0 >= mu_(P, 0) - 2 lambda_0 - (24 f r) / g (H_0 + 3 lambda_0 - mu_(P, 0)), $
    or equivalently,
    $ mu_(P, 0) - mu_(P, s) <= 21 / 2 lambda_0 + (24 f r) / g (H_0 + 3 lambda_0 - mu_(P, 0)). $
    Finally, hypothesis (2) gives $mu_C <= -mu_(P, s) + lambda_0$, $-mu_0 <= mu_(P, 0) + lambda_0$, and $-mu_(P, 0) <= mu_0 + lambda_0$. Adding the first two gives $mu_C - mu_0 <= (mu_(P, 0) - mu_(P, s)) + 2 lambda_0$, and substituting $-mu_(P, 0) <= mu_0 + lambda_0$ inside the parenthetical factor yields
    $ mu_C - mu_0 <= 25 / 2 lambda_0 + (24 f r) / g (H_0 + 4 lambda_0 + mu_0), $
    as claimed.
  ]

  Notice the exact numerical constant $25 / 2$ in Lemma 15.3—it is the precise origin of the hypothesis $25 / 2 <= C_0$ in `DivIneqObjU`! Moreover, when $g >= (k b)^8$ is large enough that
  $ & 24 f r ((2 m f N L_a + 2 p_F + C_0 c_e m (c_e f m (x^epsilon)^2 + (log x)^2 p_N)) \
    & quad + p_2 + 4) <= (k b)^7, $
  where $H_0 <= p_2 b$, $F_0 <= p_F b$, $N_c <= p_N b$, and $lambda_0 <= b$, the entire multiplicative error $(24 f r / g)(H_0 + 4 lambda_0 + mu_0)$ is crushed to at most $b / (k b) = 1 / k <= 1$.

  === Stage 3: Lower-Bounding $hat(mu)(M_j, X_W (j))$ via the Good/Bad Decomposition

  To convert Proposition 15.2 into a usable upper bound on $mu_C - 2 F_0$, we need a lower bound on the slope $hat(mu)(M_j, X_W (j))$ of each comparison lattice $M_j$ ($j in J$). In the global automorphic setting, $M_j$ is not directly given as a single Hermitian lattice with an explicit lower slope bound; instead, its slope is approached through a five-step chain of intermediate slopes
  $ mu_U (j) -> mu_A (j) -> mu_N (j) -> mu_G (j) -> hat(mu)(M_j, X_W (j)) $
  that passes through:
  1. an *unmodified base slope* $mu_U (j)$ controlled by archimedean derivative weights $u_a (j, tau)$ summed over a finite set of places $op("Pl")$;
  2. an *adjusted slope* $mu_A (j)$ incorporating the *ceiling term* $op("cfl")_j$ (which carries the main period-average weight $w(j, tau) c_1 (j, tau)$) and the *floor term* $op("sfl")_j$;
  3. a *dimension-padded slope* $mu_N (j)$ obtained by embedding a subspace of dimension $d_A (j)$ into a larger space of dimension $d_B (j)$ with relative codimension at most $epsilon_d (j)$;
  4. a *good-subspace slope* $mu_G (j)$ extracted from a *good/bad decomposition* $d_N (j) = d_"gd" (j) + d_"bd" (j)$ in which the bad-subspace dimension satisfies $d_"bd" (j) <= 3 delta_d (j) d_N (j)$ with $delta_d (j) <= 1 / 12$;
  5. the *target lattice slope* $hat(mu)(M_j, X_W (j))$, which exceeds $mu_G (j)$ up to a final projection loss $P_9 (j)$.

  Let us state and prove the exact lower bound on $hat(mu)(M_j, X_W (j))$ resulting from this five-step chain.

  #proposition(title: "Five-Stage Lower Bound for Comparison Lattice Slopes")[
    Fix $j in J$ and positive parameters $b, L, r_d, L_chi, op("llx"), L_(L, 0)$ together with nonnegative constants $C_1, C_f, C_c, C_s >= 0$. Suppose the intermediate quantities $mu_U (j), mu_A (j), mu_N (j), mu_G (j), m_max (j)$, dimensions $d_A (j), d_B (j), d_N (j), d_"gd" (j), d_"bd" (j)$, ceiling/floor terms $op("cfl")_j, op("sfl")_j$, and error parameters $epsilon_d (j), delta_d (j), Q_d (j), P_d (j), Lambda_d (j), G_d (j), P_9 (j)$ satisfy:
    1. $mu_U (j) >= -2 (C_1 L_(L, 0) sum_(tau in op("Pl")) u_a (j, tau) + b / 8)$;
    2. $op("cfl")_j = sum_(tau in op("Pl")) w(j, tau) c_1 (j, tau) - C_f q'_j (log r_d) sum_(tau in op("Pl")) w(j, tau) - C_f L$ and $op("sfl")_j <= b / 50 + C_s L$;
    3. $mu_U (j) + 2 (op("cfl")_j - op("sfl")_j) <= mu_A (j)$;
    4. $0 < d_A (j) <= d_B (j)$, $(1 - epsilon_d (j)) d_B (j) <= d_A (j)$, $0 <= epsilon_d (j)$, $0 <= P_d (j)$, and
       $ & d_A (j) (mu_A (j) - P_d (j)) + (d_B (j) - d_A (j)) (-Lambda_d (j)) \
         & quad <= d_B (j) mu_N (j), $
       with $|2 op("cfl")_j| <= Q_d (j)$, $Lambda_d (j) <= Q_d (j)$, and $epsilon_d (j) Q_d (j) <= b / 4$;
    5. $0 < d_N (j)$, $d_N (j) = d_"gd" (j) + d_"bd" (j)$, $0 <= d_"bd" (j) <= 3 delta_d (j) d_N (j)$, $0 <= delta_d (j) <= 1 / 12$, and
       $ d_N (j) mu_N (j) <= d_"gd" (j) mu_G (j) + d_"bd" (j) (m_max (j) + G_d (j)), $
       with $|mu_N (j)| <= Q_d (j)$, $m_max (j) <= Q_d (j)$, and $G_d (j) <= Q_d (j)$;
    6. $mu_G (j) - P_9 (j) <= hat(mu)(M_j, X_W (j))$ and $P_d (j) + 12 delta_d (j) Q_d (j) + P_9 (j) <= b$.

    Then
    $ -hat(mu)(M_j, X_W (j)) <= -2 op("cfl")_j + 2 C_1 L_(L, 0) sum_(tau in op("Pl")) u_a (j, tau) + 2 C_s L + 2 b. $
  ]

  #proof[
    We trace the chain backwards from $hat(mu)(M_j, X_W (j))$ to $op("cfl")_j$.

    *Step A (Good/bad extraction).* Because $d_"bd" (j) <= 3 delta_d (j) d_N (j)$ and $delta_d (j) <= 1 / 12$, the good-subspace dimension satisfies
    $ d_"gd" (j) = d_N (j) - d_"bd" (j) >= (1 - 3 delta_d (j)) d_N (j) >= 3 / 4 d_N (j) > 0. $
    Rewrite the inequality in (5) by subtracting $d_N (j) mu_N (j) = (d_"gd" (j) + d_"bd" (j)) mu_N (j)$ from the right-hand side:
    $ d_"gd" (j) (mu_G (j) - mu_N (j)) >= -d_"bd" (j) (m_max (j) + G_d (j) - mu_N (j)). $
    Since $m_max (j) <= Q_d (j)$, $G_d (j) <= Q_d (j)$, and $-mu_N (j) <= |mu_N (j)| <= Q_d (j)$, we have $m_max (j) + G_d (j) - mu_N (j) <= 3 Q_d (j)$. Dividing by $d_"gd" (j) >= (3 / 4) d_N (j) > 0$ and using $d_"bd" (j) <= 3 delta_d (j) d_N (j)$ yields
    $ mu_G (j) - mu_N (j) &>= -(d_"bd" (j) / d_"gd" (j)) (3 Q_d (j)) \
      &>= -(3 delta_d (j) / (3 / 4)) (3 Q_d (j)) = -12 delta_d (j) Q_d (j). $
    Combining this with (6) gives
    $ hat(mu)(M_j, X_W (j)) >= mu_N (j) - 12 delta_d (j) Q_d (j) - P_9 (j). $

    *Step B (Dimension-drop comparison).* Let $alpha = d_A (j) / d_B (j) in [1 - epsilon_d (j), 1]$, so $0 <= 1 - alpha <= epsilon_d (j)$. By (3) and (4), replacing $mu_A (j)$ by its lower bound $mu_U (j) + 2 (op("cfl")_j - op("sfl")_j)$ in the left-hand side of (4) (which is valid since $d_A (j) > 0$) and dividing by $d_B (j) > 0$ gives
    $ mu_N (j) >= alpha (mu_U (j) + 2 op("cfl")_j - 2 op("sfl")_j - P_d (j)) - (1 - alpha) Lambda_d (j). $
    Write $alpha (2 op("cfl")_j) = 2 op("cfl")_j - (1 - alpha) (2 op("cfl")_j)$. Because $alpha <= 1$ and $P_d (j) >= 0$, we have $-alpha P_d (j) >= -P_d (j)$. Furthermore, if we denote $U_j = 2 (C_1 L_(L, 0) sum_tau u_a (j, tau) + b / 8) >= 0$ and $S_j = 2 (b / 50 + C_s L) >= 0$, then (1) and (2) give $mu_U (j) >= -U_j$ and $-2 op("sfl")_j >= -S_j$, so by $alpha in (0, 1]$,
    $ alpha (mu_U (j) - 2 op("sfl")_j) >= -alpha (U_j + S_j) >= -(U_j + S_j). $
    For the remaining $(1 - alpha)$ terms, we use $|2 op("cfl")_j| <= Q_d (j)$, $Lambda_d (j) <= Q_d (j)$, and $(1 - alpha) <= epsilon_d (j)$:
    $ -(1 - alpha)(2 op("cfl")_j + Lambda_d (j)) >= -2 epsilon_d (j) Q_d (j) >= -b / 2, $
    where the last step uses $epsilon_d (j) Q_d (j) <= b / 4$. Therefore
    $ mu_N (j) >= 2 op("cfl")_j - U_j - S_j - P_d (j) - b / 2. $

    *Step C (Assembly).* Substituting Step B into Step A and applying $P_d (j) + 12 delta_d (j) Q_d (j) + P_9 (j) <= b$ from (6) yields
    $ hat(mu)(M_j, X_W (j)) &>= 2 op("cfl")_j - 2 C_1 L_(L, 0) sum_(tau in op("Pl")) u_a (j, tau) \
      & quad - 2 C_s L - (b / 4 + b / 25 + b / 2 + b). $
    Since $1 / 4 + 1 / 25 + 1 / 2 + 1 = 179 / 100 < 2$, negating both sides produces the stated upper bound on $-hat(mu)(M_j, X_W (j))$.
  ]

  The elegance of Proposition 15.4 lies in how the five geometrically distinct losses—unipotent thickening ($U_j$), floor truncation ($S_j$), codimension padding ($2 epsilon_d Q_d$), bad-subspace contamination ($12 delta_d Q_d$), and final projection ($P_9$)—all telescope cleanly into a single $O(b)$ error plus the explicit archimedean cost $2 C_1 L_(L, 0) sum_tau u_a (j, tau)$ and the ceiling term $-2 op("cfl")_j$.

  == Proof of the Master Inequality (`DivIneqObjU`)

  We are now ready to state and prove the central theorem of Part IV: the Divisor-Slope Master Inequality `DivIneqObjU`. Before stating it, we recall the logarithmic Stirling function that governs the archimedean derivative cost at every place.

  #definition(title: "The Logarithmic Stirling Function")[
    For any real number $nu in bb(R)$, the *logarithmic Stirling function* $op("ph") : bb(R) -> bb(R)$ (denoted `Formalism.LatticeIndexTer.ph` in Lean) is defined by
    $ op("ph")(nu) = nu log nu - nu, $
    with the standard convention $0 log 0 = 0$ (and $log nu = log |nu|$ for real-variable extensions in Mathlib, though in our applications $nu >= 0$).
  ]

  For $nu >= 1$, Stirling's approximation gives $log Gamma(nu + 1) = op("ph")(nu) + 1 / 2 log(2 pi nu) + O(1 / nu)$, so $op("ph")(nu)$ is precisely the leading asymptotic term of $log(nu!)$. In our lattice comparison, the differential operators of order $nu_(j, rho, i)$ acting on theta lifts produce factorial archimedean factors whose logarithms are controlled by $sum_i op("ph")(nu_(j, rho, i))$, while the period scaling introduces the linear shift $-(sum_i nu_(j, rho, i)) log Omega$.

  === The Asymptotic Scale Regime and Auxiliary Hypotheses

  Let us record the exact scale parameters and height-envelope definition entering `DivIneqObjU`. Fix real parameters $x >= 1$ and $epsilon > 0$, and define the *asymptotic tower of scales*
  $ L = x^epsilon, wide b = exp(L), wide a = x b, wide B_0 = f m b x^epsilon, $
  together with a radius/discriminant parameter $r_d >= 1$ satisfying $log r_d <= L$ and $log x <= L$, and the composite logarithmic scale
  $ L_a = log(a r_d) = L + log x + log r_d. $
  Observe that immediately $L <= L_a <= 3 L$. Let $op("Pl")$ be a finite set of places with $|op("Pl")| <= f$, let $cal(T) subset.eq op("Pl")$ (written `TT` in Lean) be the distinguished target subset of places supporting the prime-sum weights $a_T : op("Pl") -> bb(R)$, and let $n_r in bb(N)$ index the derivative-order tuples $nu_(j, rho, i) in bb(R)$ ($j in J$, $rho in op("Pl")$, $i in op("Fin") n_r$).

  Fix a target logarithmic weight $log T in bb(R)$ (written `logT`), an average period logarithm $log Omega in bb(R)$ (written `logOm`) with $|log Omega| <= L_a$, and positive structural parameters $m = |J| >= 1$, $f >= 1$, $k >= 1$, $N >= k + m$, $c_e >= 1$, $N_c >= 0$, $S, t_t, eta, b', n_V, L' >= 0$ with $n_V <= N$ and $L' <= C_L L_a$. Define the *height upper envelope* $h_u in bb(R)$ by
  $ h_u &= ( -sum_(t in cal(T)) a_T (t) log T \
    & quad + C_h (|cal(T)| b' N + f (m eta + S) N + f N^2) L_a ) \
    & quad + sum_(j in J) ( sum_(rho in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, rho, i))) \
    & quad - (sum_(i=1)^(n_r) nu_(j, rho, i)) log Omega) + C_h f N^2 (L_a + m^3 L) \
    & quad - (sum_(rho in op("Pl")) op("logH")(j, rho) - C_h f n_V^2 L') ). $

  We now state the Divisor-Slope Master Inequality in full precision.

  #theorem(title: "The Divisor-Slope Master Inequality, DivIneqObjU")[
    Assume the arithmetic lattice comparison datum of Section 15.1, the weighted slope hypotheses of Lemma 15.3 with $(k b)^8 <= g$ and the multiplicative-error suppression inequalities
    $ & 24 f r ((2 m f N L_a + 2 p_F + C_0 c_e m (c_e f m (x^epsilon)^2 + (log x)^2 p_N)) \
      & quad + p_2 + 4) <= (k b)^7, wide 24 f r <= (k b)^8, $
    with $H_0 <= p_2 b$, $F_0 <= p_F b$, and $N_c <= p_N b$, together with the five-stage slope bounds of Proposition 15.4 for every $j in J$. Assume further that:
    1. *Local index global budgets*: there exist $C_b >= 0$, $log g in bb(R)$, and $op("logDG") in bb(R)$ with $N^2 log g <= b$ and $N log(f N) <= b$ such that
       $ L_G <= lambda_0 + op("logDG") + C_b f N^2 log g, wide op("logDG") <= C_b f N log(f N), $
       $ & E_A (j) + (2 R_b (j)) / (delta_q D) + E_J (j) \
         & quad <= C_b (c_e (x^epsilon B_0 + (log x)^2 N_c)) + op("logDG") + C_b f N^2 log g, $
       $ E_2 (j) <= C_b (c_e (x^epsilon B_0 + (log x)^2 N_c)) quad (forall j in J). $
    2. *Archimedean coefficient alignment*: for every $j in J$ and $tau in op("Pl")$,
       $ |c_1 (j, tau) + p_q (j) (log Omega) / 2| <= C_c q'_j (log r_d + L_chi), \
         |p_q (j) - k| <= m, wide 0 <= q'_j <= m, $
       $ m w(j, tau) / 2 <= u_a (j, tau) <= 2 (m w(j, tau) + k S + k eta), \
         1 <= sum_(tau in op("Pl")) u_a (j, tau), wide 0 <= w(j, tau) <= 2 b, $
       with $0 <= L_chi <= L$, $1 <= op("llx") <= c_e x^epsilon$, and $L_(L, 0) = log(b r_d) op("llx") + L_chi + log x$.
    3. *Stirling and weight-sum matching*: for every $j in J$ and $rho in op("Pl")$,
       $ sum_(i=1)^(n_r) op("ph")(nu_(j, rho, i)) - op("logH")(j, rho) <= bold(1)_(rho in cal(T)) op("ph")(a_T (rho)) + e_E (j, rho), $
       $ sum_(i=1)^(n_r) nu_(j, rho, i) = bold(1)_(rho in cal(T)) a_T (rho) + k w(j, rho) + delta(j, rho), $
       with
       $ e_E (j, rho) <= C_0 (w(j, rho) + S + N^2 + m (t_t + 1) eta) L_a, $
       $ |delta(j, rho)| <= C_0 (w(j, rho) + k (N + S) + m (t_t + 1) eta + bold(1)_(rho in cal(T)) k b'). $
    4. *Scale hierarchy and constant thresholds*: $0 <= C_h <= C_0$, $C_h C_L <= C_0$, $lambda_0 <= b$, $m^3 N^2 L <= b$, $m eta N L <= b$, $k N <= b$, $k S <= w''$, $m (t_t + 1) eta <= w''$, $N w'' <= b$, $b' N <= a$, $m k b' <= a$, and
       $ 25 / 2 <= C_0, \
         (64 (C_1 + C_s + 3 C_f) + 8 C_c + 2) + (6 C_b + 2) <= C_0. $

    Then the Divisor-Slope Master Inequality holds:
    $ mu_C + h_u - 2 F_0 <= sum_(t in cal(T)) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T) \
      + (50 C_0 + 10) (|cal(T)| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $
  ]

  #proof[
    The proof proceeds in four clean algebraic phases: (i) expanding $-2 op("cfl")_j$ to expose the exact period-weight term $+k (sum_rho w(j, rho)) log Omega$; (ii) bounding the local index budgets and the weighted-slope perturbation; (iii) expanding $h_u$ and executing the miracle cancellation of $plus.minus k w(j, rho) log Omega$; and (iv) collecting every remaining error term under the scale hierarchy (4).

    *Phase 1: Expanding $-2 op("cfl")_j$ and bounding $-hat(mu)(M_j, X_W (j))$.* Fix $j in J$. By Proposition 15.4 and the definition of $op("cfl")_j$,
    $ -hat(mu)(M_j, X_W (j)) &<= -2 sum_(rho in op("Pl")) w(j, rho) c_1 (j, rho) \
      & quad + 2 C_f q'_j (log r_d) sum_(rho in op("Pl")) w(j, rho) + 2 (C_f + C_s) L \
      & quad + 2 C_1 L_(L, 0) sum_(rho in op("Pl")) u_a (j, rho) + 2 b. $
    For each $rho in op("Pl")$, hypothesis (2) gives
    $ -2 c_1 (j, rho) <= p_q (j) log Omega + 2 C_c q'_j (log r_d + L_chi). $
    Writing $p_q (j) log Omega = k log Omega + (p_q (j) - k) log Omega$ and using $|p_q (j) - k| <= m$, $|log Omega| <= L_a$, $q'_j <= m$, $log r_d <= L$, and $L_chi <= L$, we obtain
    $ -2 c_1 (j, rho) <= k log Omega + m L_a + 4 C_c m L. $
    Since $w(j, rho) >= 0$, multiplying by $w(j, rho)$ and summing over $rho in op("Pl")$ (using $sum_rho w(j, rho) <= 2 f b$ and $L_a <= 3 L$) yields
    $ -2 sum_(rho in op("Pl")) w(j, rho) c_1 (j, rho) <= k (sum_(rho in op("Pl")) w(j, rho)) log Omega + (6 + 8 C_c) f m b L. $
    For the $C_f$ term, $2 C_f q'_j (log r_d) sum_rho w(j, rho) <= 4 C_f f m b L$. For the $C_1$ term, note that $log(b r_d) = L + log r_d <= 2 L$, $L_chi <= L$, $log x <= L$, and $1 <= op("llx") <= c_e x^epsilon$, so
    $ L_(L, 0) = log(b r_d) op("llx") + L_chi + log x <= 2 L c_e x^epsilon + 2 L <= 4 c_e L x^epsilon. $
    Meanwhile, by hypothesis (2) and the scale bounds $k S <= w'' <= b / N <= b$, $k eta <= m eta N L <= b$ (since $k + m <= N$, $1 <= m, L$), we have
    $ sum_(rho in op("Pl")) u_a (j, rho) &<= 2 sum_(rho in op("Pl")) (m w(j, rho) + k S + k eta) \
      &<= 2 f (2 m b + b + b) <= 8 f m b. $
    Hence
    $ 2 C_1 L_(L, 0) sum_(rho in op("Pl")) u_a (j, rho) <= 64 C_1 c_e f m b L x^epsilon = 64 C_1 c_e x^epsilon B_0, $
    because $L x^epsilon = (x^epsilon)^2$ and $B_0 = f m b x^epsilon$ so $f m b L x^epsilon = x^epsilon B_0$! Since $L = x^epsilon >= 1$, $b <= f m b L x^epsilon = x^epsilon B_0$, and $c_e >= 1$, all of the $C_1, C_s, C_f, C_c$, and $b$ terms combine into
    $ -hat(mu)(M_j, X_W (j)) &<= k (sum_(rho in op("Pl")) w(j, rho)) log Omega \
      & quad + (64 (C_1 + C_s + 3 C_f) + 8 C_c + 2) c_e x^epsilon B_0. $

    *Phase 2: Bounding the local index budgets and the slope perturbation.* By Proposition 15.2 and hypothesis (1), we bound the finite-place error terms. Since $op("logDG") <= C_b f N log(f N) <= C_b f b$ and $C_b f N^2 log g <= C_b f b$, we have
    $ L_G <= lambda_0 + 2 C_b f b <= (2 C_b + 1) f b, $
    and for each $j in J$,
    $ & E_A (j) + (2 R_b (j)) / (delta_q D) + E_J (j) + E_2 (j) \
      & quad <= 2 C_b c_e (x^epsilon B_0 + (log x)^2 N_c) + 2 C_b f b. $
    Also the prime-square tail satisfies $E_3 = sum_(y in S_y) op("lw")(y) dot.c 2 / op("plc")(y)^2 <= 2 <= 2 f b$ (or $E_3$ is bounded by $2 c_e m x^epsilon B_0$). Summing over $j in J$ (`|J| = m`) and using $f b <= x^epsilon B_0$ gives
    $ & L_G + sum_(j in J) (E_A (j) + (2 R_b (j)) / (delta_q D) + E_J (j) + E_2 (j)) + E_3 \
      & quad <= (6 C_b + 2) c_e m (x^epsilon B_0 + (log x)^2 N_c). $
    Combining this with Phase 1 and the threshold $(64 (C_1 + C_s + 3 C_f) + 8 C_c + 2) + (6 C_b + 2) <= C_0$ from hypothesis (4), Proposition 15.2 yields
    $ mu_0 - 2 F_0 &<= sum_(j in J) k (sum_(rho in op("Pl")) w(j, rho)) log Omega \
      & quad + C_0 c_e m (x^epsilon B_0 + (log x)^2 N_c). $

    Now apply Lemma 15.3 to pass from $mu_0$ to $mu_C$. We first observe an a priori upper bound on $mu_0$: using $sum_j k sum_rho w(j, rho) |log Omega| <= m k (2 f b) L_a <= 2 m f N L_a b$, $F_0 <= p_F b$, $B_0 = f m b x^epsilon$, and $N_c <= p_N b$, the preceding inequality gives
    $ mu_0 <= (2 m f N L_a + 2 p_F + C_0 c_e m (c_e f m (x^epsilon)^2 + (log x)^2 p_N)) b. $
    Together with $H_0 <= p_2 b$ and $4 lambda_0 <= 4 b$, the multiplicative-error hypothesis $24 f r (dots.c + p_2 + 4) <= (k b)^7$ and $(k b)^8 <= g$ imply
    $ (24 f r) / g (H_0 + 4 lambda_0 + mu_0) <= ((k b)^7 b) / (k b)^8 = 1 / k <= 1. $
    Since $(25 / 2) lambda_0 <= C_0 b <= C_0 c_e m x^epsilon B_0$, Lemma 15.3 yields
    $ mu_C - 2 F_0 &<= sum_(j in J) k (sum_(rho in op("Pl")) w(j, rho)) log Omega \
      & quad + (2 C_0 + 1) c_e m (x^epsilon B_0 + (log x)^2 N_c). $

    *Phase 3: Expanding $h_u$ and executing the cancellation.* Substitute the two matching relations of hypothesis (3) into the definition of $h_u$. For each $j in J$ and $rho in op("Pl")$,
    $ & (sum_(i=1)^(n_r) op("ph")(nu_(j, rho, i))) - op("logH")(j, rho) - (sum_(i=1)^(n_r) nu_(j, rho, i)) log Omega \
      & quad <= bold(1)_(rho in cal(T)) (op("ph")(a_T (rho)) - a_T (rho) log Omega) - k w(j, rho) log Omega \
      & quad + e_E (j, rho) + |delta(j, rho)| |log Omega|. $
    Summing over $rho in op("Pl")$ and $j in J$ (`|J| = m`), the main target sum becomes
    $ & -sum_(t in cal(T)) a_T (t) log T + sum_(t in cal(T)) m (op("ph")(a_T (t)) - a_T (t) log Omega) \
      & quad = sum_(t in cal(T)) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T), $
    while the period-weight sum $-sum_(j in J) k (sum_(rho in op("Pl")) w(j, rho)) log Omega$ cancels *identically* against the term $+sum_(j in J) k (sum_(rho in op("Pl")) w(j, rho)) log Omega$ in our upper bound for $mu_C - 2 F_0$!

    *Phase 4: Accounting for the remaining $h_u$ error terms.* After cancellation, the remaining error terms from $h_u$ fall into two groups:
    1. *Terms proportional to $|cal(T)|$*:
       - From the outer $C_h$ term: $C_h |cal(T)| b' N L_a <= C_0 |cal(T)| a L_a$, since $C_h <= C_0$ and $b' N <= a$.
       - From the indicator $bold(1)_(rho in cal(T)) k b'$ inside $|delta(j, rho)| |log Omega|$ summed over $j in J$ and $rho in cal(T)$:
         $ sum_(j in J) sum_(rho in cal(T)) C_0 k b' |log Omega| <= C_0 |cal(T)| (m k b') L_a <= C_0 |cal(T)| a L_a, $
         since $m k b' <= a$ and $|log Omega| <= L_a$.
       Together these contribute at most $2 C_0 |cal(T)| a L_a <= (50 C_0 + 10) |cal(T)| a L_a$.

    2. *Terms proportional to $f$ (absorbed into $c_e m x^epsilon B_0$)*:
       - Outer $C_h$ terms: $C_h (f (m eta + S) N + f N^2) L_a$. Since $m eta N L <= b$, $N S <= N w'' <= b$ (as $k >= 1$), $N^2 L <= m^3 N^2 L <= b$, and $L_a <= 3 L$, each of $f m eta N L_a$, $f S N L_a$, $f N^2 L_a$ is at most $3 f b <= 3 x^epsilon B_0$.
       - Inner $C_h$ terms summed over $j in J$:
         $ & m C_h (f N^2 (L_a + m^3 L) + f n_V^2 L') \
           & quad <= m C_0 f N^2 (3 L + m^3 L) + m (C_h C_L) f N^2 L_a. $
         Since $m^3 N^2 L <= b$, $N^2 L <= b$, and $C_h C_L <= C_0$, this is bounded by $7 C_0 m f b <= 7 C_0 c_e m x^epsilon B_0$.
       - The $e_E (j, rho)$ sum over $j in J, rho in op("Pl")$: using $w(j, rho) <= 2 b$, $S <= b$, $N^2 <= b$, $m (t_t + 1) eta <= w'' <= b$, and $L_a <= 3 L$,
         $ sum_(j in J) sum_(rho in op("Pl")) e_E (j, rho) &<= m f C_0 (2 b + b + b + b) dot.c 3 L \
           &= 15 C_0 f m b L <= 15 C_0 c_e m x^epsilon B_0. $
       - The non-$cal(T)$ part of $|delta(j, rho)| |log Omega|$ summed over $j in J, rho in op("Pl")$: using $w(j, rho) <= 2 b$, $k N <= b$, $k S <= w'' <= b$, $m (t_t + 1) eta <= w'' <= b$, and $|log Omega| <= L_a <= 3 L$,
         $ & sum_(j in J) sum_(rho in op("Pl")) C_0 (w(j, rho) + k N + k S + m (t_t + 1) eta) L_a \
           & quad <= m f C_0 (5 b) (3 L) = 15 C_0 f m b L <= 15 C_0 c_e m x^epsilon B_0. $

    Summing the coefficients of $c_e m (x^epsilon B_0 + (log x)^2 N_c)$ from Phase 2 ($2 C_0 + 1$) and Phase 4 ($9 C_0 + 7 C_0 + 15 C_0 + 15 C_0 = 46 C_0$, generously bounded by $48 C_0 + 9$) gives total coefficient at most $50 C_0 + 10$. Combining all four phases establishes the Master Inequality.
  ]

  === Anatomy of Every Term in the Master Inequality

  The Divisor-Slope Master Inequality
  $ & mu_C + h_u - 2 F_0 \
    & quad <= sum_(t in cal(T)) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T) \
    & quad + (50 C_0 + 10) (|cal(T)| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)) $
  is the central engine of the entire proof. Each term on both sides plays a sharply defined mathematical role:

  1. *The inert-prime divisibility win $-2 F_0$*: On the left-hand side sits $-2 F_0$, where $F_0 = sum_j sum_(y in T_w) op("lw")(y) op("ramw")(y) F_0 (y, j)$ aggregates the local divisibility indices at the twisted places $y in T_w$. The factor of $2$ reflects the conjugate pairing of $y$ and $bar(y)$ in the CM field $K$ (or equivalently the degree-two residue extension at inert primes of $K / K_0$). When inert primes force high divisibility of the local division values—producing a large negative value of $F_0$ (or equivalently a large positive contribution $-2 F_0$ on the left-hand side)—this term acts as an arithmetic *win* that tightens the upper bound on the target prime sum. Conversely, moving $-2 F_0$ to the right-hand side as $+2 F_0$ shows directly how the prime-sum upper bound is discounted by twice the total inert-prime divisibility index.

  2. *The archimedean derivative and period cost $m (op("ph")(a_T (t)) - a_T (t) log Omega)$*: For each target place $t in cal(T)$, the quantity $op("ph")(a_T (t)) = a_T (t) log a_T (t) - a_T (t)$ is the Stirling logarithm of the factorial growth of $a_T (t)$-th order derivatives of theta functions, while $-a_T (t) log Omega$ measures the archimedean period scaling per derivative, multiplied by the number $m = |J|$ of comparison channels. Crucially, the derivative order $a_T (t)$ enters *superlinearly* through $a_T (t) log a_T (t)$, whereas the target weight $-a_T (t) log T$ enters *linearly*. Balancing $m (op("ph")(a_T (t)) - a_T (t) log Omega)$ against $-a_T (t) log T$ determines the optimal size of $a_T (t) approx Omega T^(1 / m)$!

  3. *The target prime-sum weight $-a_T (t) log T$*: This is the exact analytic quantity we seek to bound. Moving $-sum_(t in cal(T)) a_T (t) log T$ to the left-hand side produces $+sum_(t in cal(T)) a_T (t) log T$, a weighted sum over the target places $t in cal(T)$ whose weights $a_T (t)$ are nonnegative and localized on the prime-power support of the explicit-formula test kernel.

  4. *Why the error term is negligible at scale $L = x^epsilon$, $b = exp(L)$, $a = x b$*: Examine the two pieces of the error term:
     - The first piece is $(50 C_0 + 10) |cal(T)| a L_a$. Since $L = x^epsilon$, $b = exp(x^epsilon)$, $a = x exp(x^epsilon)$, and $L_a approx L = x^epsilon$, we have
       $ a L_a approx x^(1 + epsilon) exp(x^epsilon). $
       Meanwhile, the main term $a_T (t) log T$ has size proportional to $a_T (t) dot.c m L$, where in the prime-sum extraction $a_T (t)$ is chosen at scale strictly dominating $a L_a / (m L) approx x exp(x^epsilon) / m$ (or $log T$ scales as $C_T m L$ while $|cal(T)| a L_a$ is exponentially smaller than the $m$-fold Stirling-period balance when $T$ is chosen large enough relative to $a$).
     - The second piece is $(50 C_0 + 10) c_e m (x^epsilon B_0 + (log x)^2 N_c)$. Recall that $B_0 = f m b x^epsilon = f m x^epsilon exp(x^epsilon)$, so
       $ x^epsilon B_0 = f m x^(2 epsilon) exp(x^epsilon) = (f m x^(2 epsilon - 1)) a. $
       Whenever $epsilon < 1 / 2$ (in fact $epsilon$ is chosen arbitrarily small), the factor $x^(2 epsilon - 1)$ decays polynomially in $x$, making $x^epsilon B_0$ *smaller* than $a$ itself! Similarly, the ramification/conductor count $N_c$ is multiplied only by $(log x)^2$, which is polynomial in $log x$ compared to the stretched-exponential scale $b = exp(x^epsilon)$. Thus at the stretched-exponential scale $b = exp(x^epsilon)$, $a = x b$, every polynomial factor in $x$, $f$, $m$, $N$, and $log x$ is completely dwarfed by the main term.

  #insight-box(title: "The Miracle Cancellation of the Auxiliary Weight w(j, ρ)")[
    In any Arakelov slope argument, the most dangerous threat is an uncontrolled linear term of the same order as the main term. Here, the auxiliary place weights $w(j, rho)$ (of size up to $2 b$) appear in two seemingly unrelated locations: once inside the ceiling term $op("cfl")_j$ governing the lower bound on $hat(mu)(M_j, X_W (j))$, where they contribute $+k w(j, rho) log Omega$, and once inside the derivative-order identity $sum_i nu_(j, rho, i) = bold(1)_(rho in cal(T)) a_T (rho) + k w(j, rho) + delta(j, rho)$ inside $h_u$, where they contribute $-k w(j, rho) log Omega$. Because $|log Omega|$ can be as large as $L_a$, this term has size $approx k f b L_a$—far too large to be absorbed into the error unless it cancels! The exact cancellation of $plus.minus k w(j, rho) log Omega$ in Phase 3 is therefore the structural linchpin of `DivIneqObjU`.
  ]

  == The Height Sum Bound (`HeightS`)

  The Divisor-Slope Master Inequality of Section 15.3 bounds $mu_C + h_u - 2 F_0$ from above, where $h_u$ is an explicit algebraic expression built from $a_T (t)$, $op("ph")(nu_(j, rho, i))$, $log Omega$, and $op("logH")(j, rho)$. To connect `DivIneqObjU` to the actual Arakelov heights of the geometric objects—specifically, the height $h_P$ of the polarized point/divisor, the heights $h_K (j)$ of the auxiliary theta-lift sections, and the lower bound $m_lambda$ coming from the Hodge-bundle covolume—we must prove that $h_u$ dominates the geometric height combination $h_P + sum_(j in J) h_K (j) - m_lambda$. This is the content of the Height Sum Bound `HeightS` (lines 216–274 of `DivIneqTopAnchorU.lean`).

  === Geometric Origin: From `CovolumeBoundOfX` to the Local Height Inputs

  Before giving the formal proof of `HeightS`, let us explain how its hypotheses arise from the Arakelov geometry of Siegel modular varieties developed in Chapters 13 and 14. In `TopCovolSlim2Use.lean` (`SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt`), the covolume bound `CovolumeBoundOfX` is established by combining fifteen foundational geometric and arithmetic inputs:
  - *Resolution and principalization in characteristic zero* together with the *Poincaré–Lelong inversion formula* (`PoincareLelongInv`), which allow Green functions and singular Hermitian metrics on the boundary of Siegel moduli spaces to be regularized on smooth toroidal models.
  - *Arithmetic Hilbert–Samuel* (`HSUse`) and *Moriwaki's arithmetic bigness theorem* (`MoriwakiBigStatement`), which translate positive arithmetic self-intersection numbers into the existence of many small global sections of high tensor powers of the Hodge bundle.
  - *Integral Siegel toroidal compactifications* (`SiegelToroidalIntegral`, `ToroidalForFanKS`) and *semi-abelian Lie algebra seminegativity* (`SemiAbelianLieSeminegative`), which control the boundary divisors and ensure that the extended Hodge bundle remains nef and admits toroidal charts compatible with the polyhedral fan.
  - *Chow form height comparisons* (`ChowFormHeightComparison`, `FubiniStudyChowHeightFormula`, `ChowFormHyperplaneSection`), *Fargues exactness*, *Zarhin's trick*, *Nef Riemann–Roch*, and *Grothendieck deformation*, which relate the Faltings/Arakelov height of the abelian-variety point to the Fubini–Study Chow height of its projective embedding and guarantee injectivity of small sections on the toroidal model.

  When `CovolumeBoundOfX` is specialized to our CM family with archimedean embedding set $op("Emb")$ (finite and nonempty), it supplies the three concrete inputs to `HeightS`:
  1. *The covolume lower bound on $m_lambda$*: the sum of the local Hodge-bundle log-norms $op("logH")(j, rho)$ minus the boundary correction $C_h f n_V^2 L'$ is bounded above by the covolume parameter $m_lambda$:
     $ sum_(j in J) (sum_(rho in op("Pl")) op("logH")(j, rho) - C_h f n_V^2 L') <= m_lambda. $
  2. *The embedding-wise section height bound*: for each $j in J$, the height $h_K (j)$ is the average over all archimedean embeddings $s in op("Emb")$ of a local archimedean log-norm $op("logK")(j, s)$,
     $ h_K (j) = 1 / |op("Emb")| sum_(s in op("Emb")) op("logK")(j, s). $
     At each embedding $s in op("Emb")$, $op("logK")(j, s)$ is bounded by the Stirling-period derivative sum with local period logarithm $log Omega_tau (tau, s)$ (whose average over $s in op("Emb")$ is $log Omega$), plus the theta zero-value contribution $|op("Pl")| g_0 (j) log theta_0 (s)$, the toroidal-chart volume term $|op("Pl")| g_0 (j) log(8 + 32 |op("Pl")| g_0 (j) v)$, twice the main geometric height term $op("MainNotions")(j, s)$, the derivative-size log-correction $sum_tau (1 + 2 g_0 (j) log(2 sum_i nu_(j, tau, i) + 2))$, and the auxiliary height terms $op("logh")(j) + op("logh'")(j)$.
  3. *The polarized point height bound $h_P$*: $h_P$ is bounded above by the negative prime-weight sum $-sum_tau n_tau (tau) log T$ (where $n_tau (tau) = lambda_1 (tau) - D_0 (tau)$ separates the leading weight $lambda_1 (tau)$ from the divisor shift $D_0 (tau)$), plus the polynomial-coefficient and discriminant heights $sum_tau (2 op("logc")(tau) + op("logxi")(tau))$ and an evaluation error $op("ev")$.

  === Statement and Proof of `HeightS`

  #theorem(title: "The Height Sum Bound, HeightS")[
    Let $J, op("Pl"), op("Emb")$ be finite types with $op("Emb")$ nonempty, $|J| = m >= 1$, $|op("Pl")| <= f$, $f >= 1$, $k >= 1$, $k + m <= N$, and $cal(T) subset.eq op("Pl")$. Fix the asymptotic scale $x >= 1$, $epsilon > 0$, $L = x^epsilon$, $b = exp(L)$, $a = x b$, $r_d >= 1$, $L_a = log(a r_d)$, and nonnegative parameters $S, eta, b' >= 0$ and $0 <= log T <= C_T m L$ ($C_T >= 0$). Let $h_u$ be defined as in Section 15.3. Assume:
    1. *Covolume bound*:
       $ sum_(j in J) (sum_(rho in op("Pl")) op("logH")(j, rho) - C_h f n_V^2 L') <= m_lambda. $
    2. *Embedding-averaged section heights*: for every $j in J$ and $s in op("Emb")$,
       $ & op("logK")(j, s) \
         & quad <= sum_(tau in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, tau, i))) - (sum_(i=1)^(n_r) nu_(j, tau, i)) log Omega_tau (tau, s)) \
         & quad + |op("Pl")| g_0 (j) log theta_0 (s) + |op("Pl")| g_0 (j) log(8 + 32 |op("Pl")| g_0 (j) v) \
         & quad + 2 op("MainNotions")(j, s) + op("logh")(j) + op("logh'")(j) \
         & quad + sum_(tau in op("Pl")) (1 + 2 g_0 (j) log(2 sum_(i=1)^(n_r) nu_(j, tau, i) + 2)), $
       with $h_K (j) = |op("Emb")|^(-1) sum_(s in op("Emb")) op("logK")(j, s)$, $|op("Emb")|^(-1) sum_(s in op("Emb")) log Omega_tau (tau, s) = log Omega$, and $|op("Emb")|^(-1) sum_(s in op("Emb")) log theta_0 (s) <= C_theta L$. Assume further that for nonnegative constants $C_2, C_theta, C_4, c_5, c_6, C_8, C_e >= 0$,
       $ & op("MainNotions")(j, s) \
         & quad <= C_2 f m^2 N^2 (log g + log T) + C_e f N^2 log g, $
       $ op("logh")(j), op("logh'")(j) <= C_4 f N^2 (L + log T + log g), \
         0 <= g_0 (j) <= N^2, $
       $ log(8 + 32 |op("Pl")| g_0 (j) v) <= c_5 L_a, \
         log(2 sum_(i=1)^(n_r) nu_(j, tau, i) + 2) <= c_6 L_a, wide log g <= C_8 L. $
    3. *Polarized point height*:
       $ h_P <= -sum_(tau in op("Pl")) n_tau (tau) log T + sum_(tau in op("Pl")) (2 op("logc")(tau) + op("logxi")(tau)) + op("ev"), $
       where $op("ev") <= C_"ev" f N^2 L_a$ ($C_"ev" >= 0$), and for every $tau in op("Pl")$:
       $ op("logc")(tau) <= (N - 1) D_1 (tau) log(2 a), \
         op("logxi")(tau) <= N (N - 1) / 2 log(2 a), $
       $ n_tau (tau) = lambda_1 (tau) - D_0 (tau), wide D_1 (tau) <= 3 D_0 (tau) + S + eta, \
         D_0 (tau) <= S + m eta + bold(1)_(tau in cal(T)) b_T (tau), $
       with $lambda_1 (tau) = a_T (tau) - (N - k) / 2$ and $b_T (tau) <= 2 b'$ for $tau in cal(T)$, and $S - (N - 1) / 2 <= lambda_1 (tau)$ for $tau in.not cal(T)$.
    4. *Constant thresholds for $C_h$*:
       $ 2 (16 + C_T + C_"ev") <= C_h, $
       $ C_theta + c_5 + 2 c_6 + 1 + 2 C_4 + 2 C_e C_8 <= C_h, $
       $ 2 (C_2 + C_4) (C_T + C_8) <= C_h. $

    Then
    $ h_P + sum_(j in J) h_K (j) - m_lambda <= h_u. $
  ]

  #proof[
    Recall the three-part structure of $h_u$:
    $ h_u = H_P^"env" + sum_(j in J) H_K^"env" (j) - H_lambda^"env", $
    where
    $ H_P^"env" &= -sum_(t in cal(T)) a_T (t) log T \
      & quad + C_h (|cal(T)| b' N + f (m eta + S) N + f N^2) L_a, $
    $ H_K^"env" (j) &= sum_(rho in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, rho, i))) - (sum_(i=1)^(n_r) nu_(j, rho, i)) log Omega) \
      & quad + C_h f N^2 (L_a + m^3 L), $
    $ H_lambda^"env" = sum_(j in J) (sum_(rho in op("Pl")) op("logH")(j, rho) - C_h f n_V^2 L'). $
    By hypothesis (1), we immediately have $-m_lambda <= -H_lambda^"env"$. It therefore suffices to prove separately that $h_K (j) <= H_K^"env" (j)$ for every $j in J$, and that $h_P <= H_P^"env"$.

    Before doing so, record two elementary inequalities from the scale hypotheses: since $x >= 1$ and $epsilon > 0$, we have $L = x^epsilon >= 1$, $b = exp(L) >= e > 2$, and $a = x b > 2$. Hence $2 a < a^2$, so
    $ log(2 a) <= 2 log a <= 2 log(a r_d) = 2 L_a. $
    Moreover, $L = log b <= log a <= L_a$, and since $N >= k + m >= 2$ and $m >= 1$, we have $1 <= m <= N$ and $1 <= L <= L_a$.

    *Part 1: Proving $h_K (j) <= H_K^"env" (j)$ for each $j in J$.* Fix $j in J$ and average the inequality in hypothesis (2) over $s in op("Emb")$ (which is nonempty, so $|op("Emb")| >= 1$). By linearity of averaging:
    - The first term averages to
      $ & sum_(tau in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, tau, i))) \
        & quad - (sum_(i=1)^(n_r) nu_(j, tau, i)) (1 / |op("Emb")| sum_(s in op("Emb")) log Omega_tau (tau, s))) \
        & quad = sum_(tau in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, tau, i))) - (sum_(i=1)^(n_r) nu_(j, tau, i)) log Omega), $
      which matches the main term of $H_K^"env" (j)$ identically!
    - The theta zero-value term averages to
      $ & |op("Pl")| g_0 (j) (1 / |op("Emb")| sum_(s in op("Emb")) log theta_0 (s)) \
        & quad <= f N^2 C_theta L <= C_theta f N^2 L_a, $
      using $|op("Pl")| <= f$, $0 <= g_0 (j) <= N^2$, $C_theta >= 0$, and $L <= L_a$.
    - The toroidal-chart volume term is independent of $s$ and bounded by
      $ |op("Pl")| g_0 (j) log(8 + 32 |op("Pl")| g_0 (j) v) <= f N^2 c_5 L_a. $
    - The derivative-size log-correction is independent of $s$ and satisfies
      $ & sum_(tau in op("Pl")) (1 + 2 g_0 (j) log(2 sum_(i=1)^(n_r) nu_(j, tau, i) + 2)) \
        & quad <= f (1 + 2 N^2 c_6 L_a) <= (1 + 2 c_6) f N^2 L_a, $
      since $1 <= N^2 L_a$.
    - For $2 op("MainNotions")(j, s)$, substituting $log g <= C_8 L$ and $log T <= C_T m L$ gives
      $ & 2 op("MainNotions")(j, s) \
        & quad <= 2 C_2 f m^2 N^2 (C_8 L + C_T m L) + 2 C_e f N^2 C_8 L. $
      Since $m >= 1$, we have $m^2 (C_8 + C_T m) <= m^3 (C_T + C_8)$, and $L <= L_a$ gives
      $ & 2 op("MainNotions")(j, s) \
        & quad <= 2 C_2 (C_T + C_8) f N^2 m^3 L + 2 C_e C_8 f N^2 L_a. $
    - For $op("logh")(j) + op("logh'")(j)$, we similarly obtain
      $ op("logh")(j) + op("logh'")(j) &<= 2 C_4 f N^2 (L + C_T m L + C_8 L) \
        &<= 2 C_4 f N^2 L_a + 2 C_4 (C_T + C_8) f N^2 m^3 L, $
      using $m <= m^3$ and $1 <= m^3$.

    Collecting the coefficients of $f N^2 L_a$ and $f N^2 m^3 L$ across all six pieces gives
    $ h_K (j) &<= sum_(rho in op("Pl")) ((sum_(i=1)^(n_r) op("ph")(nu_(j, rho, i))) - (sum_(i=1)^(n_r) nu_(j, rho, i)) log Omega) \
      & quad + (C_theta + c_5 + 2 c_6 + 1 + 2 C_4 + 2 C_e C_8) f N^2 L_a \
      & quad + 2 (C_2 + C_4) (C_T + C_8) f N^2 m^3 L. $
    Applying the second and third thresholds of hypothesis (4) immediately yields $h_K (j) <= H_K^"env" (j)$.

    *Part 2: Proving $h_P <= H_P^"env"$.* Expand $-n_tau (tau) log T = (-lambda_1 (tau) + D_0 (tau)) log T$ for each $tau in op("Pl")$, remembering that $log T >= 0$:
    - If $tau in cal(T)$, then $lambda_1 (tau) = a_T (tau) - (N - k) / 2$, so
      $ -lambda_1 (tau) log T &= -a_T (tau) log T + (N - k) / 2 log T \
        &<= -a_T (tau) log T + N / 2 log T. $
    - If $tau in.not cal(T)$, then $lambda_1 (tau) >= S - (N - 1) / 2 >= -(N - 1) / 2$ (as $S >= 0$), so
      $ -lambda_1 (tau) log T <= (N - 1) / 2 log T <= N / 2 log T. $
    Summing over $tau in op("Pl")$ and using $|op("Pl")| <= f$ and $log T <= C_T m L <= C_T N L_a$ gives
    $ -sum_(tau in op("Pl")) lambda_1 (tau) log T <= -sum_(t in cal(T)) a_T (t) log T + 1 / 2 C_T f N^2 L_a. $

    Next, bound $sum_(tau in op("Pl")) D_0 (tau) log T$. By hypothesis (3), $D_0 (tau) <= S + m eta + bold(1)_(tau in cal(T)) 2 b'$. Using $log T <= C_T m L <= C_T N L_a$, we get
    $ sum_(tau in op("Pl")) D_0 (tau) log T <= C_T (2 |cal(T)| b' N + f (m eta + S) N) L_a. $

    Now bound $sum_(tau in op("Pl")) (2 op("logc")(tau) + op("logxi")(tau))$. From $D_1 (tau) <= 3 D_0 (tau) + S + eta$ and $D_0 (tau) <= S + m eta + bold(1)_(tau in cal(T)) 2 b'$, together with $1 <= m$ (so $eta <= m eta$), we have
    $ D_1 (tau) <= 4 S + 4 m eta + bold(1)_(tau in cal(T)) 6 b'. $
    Using $op("logc")(tau) <= (N - 1) D_1 (tau) log(2 a) <= 2 N D_1 (tau) L_a$ and $op("logxi")(tau) <= (N (N - 1) / 2) log(2 a) <= N^2 L_a$, we find
    $ 2 op("logc")(tau) + op("logxi")(tau) <= 4 N (4 S + 4 m eta + bold(1)_(tau in cal(T)) 6 b') L_a + N^2 L_a \
      = (24 bold(1)_(tau in cal(T)) b' N + 16 (m eta + S) N + N^2) L_a. $
    Summing over $tau in op("Pl")$ (with $|op("Pl")| <= f$) and adding $op("ev") <= C_"ev" f N^2 L_a$ produces
    $ h_P &<= -sum_(t in cal(T)) a_T (t) log T + (24 + 2 C_T) |cal(T)| b' N L_a \
      & quad + (16 + C_T) f (m eta + S) N L_a + (1 + C_T / 2 + C_"ev") f N^2 L_a. $
    Every one of the three numerical coefficients $24 + 2 C_T$, $16 + C_T$, and $1 + C_T / 2 + C_"ev"$ is bounded above by $2 (16 + C_T + C_"ev") <= C_h$ (the first threshold of hypothesis (4)). Therefore $h_P <= H_P^"env"$.

    Adding $h_P <= H_P^"env"$, $sum_(j in J) h_K (j) <= sum_(j in J) H_K^"env" (j)$, and $-m_lambda <= -H_lambda^"env"$ establishes $h_P + sum_(j in J) h_K (j) - m_lambda <= h_u$.
  ]

  #remark(title: "Modularity of the Intermediate Envelope h_u")[
    Why does the formalization introduce the explicit intermediate quantity $h_u$ rather than proving a single monolithic inequality directly from the Arakelov covolume bounds to the prime sum? The separation into `DivIneqObjU` and `HeightS` creates an exact *interface boundary* between two completely different mathematical worlds. On one side, `DivIneqObjU` knows nothing about toroidal compactifications, theta zero-values, Chow forms, or archimedean embedding averages—it operates purely on Hermitian lattices, Bost's slope inequality, and the Stirling-period cancellation. On the other side, `HeightS` knows nothing about the glued lattice $R$, quotient metrics, or the local indices $E_A, R_b, E_J, E_2, F_0$—it operates purely on archimedean height averages and covolume bounds. The single real number $h_u$ is the sole quantity transmitted across this boundary.
  ]

  == Extracting the Analytic Prime-Sum Bound from `DivIneqObjU` + `HeightS`

  We now close the arithmetic-to-analytic bridge by combining Theorem 15.6 (`DivIneqObjU`) and Theorem 15.7 (`HeightS`), eliminating the interface variable $h_u$, and showing how the resulting inequality forces the exact one-sided upper bound on the smoothed prime sum required by the analytic endgame `TopG`.

  === Eliminating $h_u$ and Isolating the Smoothed Prime Sum

  #corollary(title: "Combined Arakelov–Prime-Sum Inequality")[
    Assume all hypotheses of Theorem 15.6 (`DivIneqObjU`) and Theorem 15.7 (`HeightS`) hold simultaneously for a common height envelope $h_u$. Then
    $ & mu_C + h_P + sum_(j in J) h_K (j) - m_lambda - 2 F_0 \
      & quad <= sum_(t in cal(T)) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T) \
      & quad + (50 C_0 + 10) (|cal(T)| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $
    Equivalently, isolating the target prime sum $sum_(t in cal(T)) a_T (t) log T$ on the left-hand side,
    $ & sum_(t in cal(T)) a_T (t) log T \
      & quad <= sum_(t in cal(T)) m (op("ph")(a_T (t)) - a_T (t) log Omega) \
      & quad - (mu_C + h_P + sum_(j in J) h_K (j) - m_lambda) + 2 F_0 \
      & quad + (50 C_0 + 10) (|cal(T)| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $
  ]

  #proof[
    By Theorem 15.7, $h_P + sum_(j in J) h_K (j) - m_lambda <= h_u$. Adding $mu_C - 2 F_0$ to both sides and applying Theorem 15.6 immediately eliminates $h_u$ and yields the first displayed inequality. Adding $sum_(t in cal(T)) a_T (t) log T$ to both sides and subtracting $mu_C + h_P + sum_(j in J) h_K (j) - m_lambda - 2 F_0$ yields the second.
  ]

  === From the Combined Inequality to the One-Sided Prime-Sum Bound of `TopG`

  Let us now examine how each term on the right-hand side of Corollary 15.9 behaves in the global instantiation of the Alpöge–Claude–Riemann theorem, and why the resulting inequality delivers the exact one-sided upper bound on the smoothed prime sum required by `TopG`.

  1. *Lower bound on the global Arakelov term $mu_C + h_P + sum_j h_K (j) - m_lambda$*:
     - The comparison slope $mu_C$ is bounded from below by the semistability and positivity of the global comparison bundle (coming from the nonnegativity of the archimedean Weil–Petersson / Hodge pairing on the automorphic quotient).
     - The height sum $h_P + sum_(j in J) h_K (j) - m_lambda$ is bounded from below by the global Arakelov positivity of the polarized point and the small sections on the Siegel toroidal model: specifically, the covolume lower bound `CovolumeBoundOfX` ensures that $m_lambda$ cannot exceed $h_P + sum_j h_K (j)$ by more than a controlled lower-order error.
     - Consequently, the negated global Arakelov term $-(mu_C + h_P + sum_j h_K (j) - m_lambda)$ is bounded *above* by a negligible quantity relative to the main scale of $sum_(t in cal(T)) a_T (t) log T$.

  2. *The inert-prime divisibility discount $+2 F_0$*:
     Recall that $F_0 = sum_j sum_(y in T_w) op("lw")(y) op("ramw")(y) F_0 (y, j)$ aggregates the local divisibility indices at the twisted places $y in T_w$. In the arithmetic instantiation, $F_0$ is negative (its absolute value $|F_0|$ measures the genuine $p$-adic divisibility gained at inert primes in the CM extension $K / K_0$), so $+2 F_0 = -2 |F_0| < 0$ actively *reduces* the upper bound on the prime sum. Even when $F_0$ is simply tracked alongside the Stirling-period balance, it supplies the exact arithmetic leverage needed to beat the trivial convexity barrier.

  3. *Optimizing the Stirling-period trade-off*:
     Look closely at the $t$-summand when we move the Stirling-period term back alongside $a_T (t) log T$:
     $ & a_T (t) log T - m (op("ph")(a_T (t)) - a_T (t) log Omega) \
       & quad = a_T (t) (log T + m log Omega + m - m log a_T (t)). $
     For a fixed $T$ and $Omega$, consider the smooth concave function
     $ Phi(u) = u (log T + m log Omega + m - m log u) quad (u > 0). $
     Its derivative is $Phi'(u) = log T + m log Omega - m log u$, which vanishes at the unique maximizer
     $ u_* = Omega dot.c T^(1 / m), $
     where $Phi(u_*) = m u_* = m Omega T^(1 / m)$. In the global instantiation, the target weights $a_T (t)$ are chosen at a scale $a_T (t) < u_*$ (more precisely, with $log a_T (t) <= (1 - delta_0) (log T / m + log Omega)$ for a strict margin $delta_0 > 0$). On this regime, the factor $(log T + m log Omega + m - m log a_T (t))$ is strictly *positive* and bounded below by $delta_0 log T$! Therefore,
     $ & delta_0 (log T) sum_(t in cal(T)) a_T (t) \
       & quad <= sum_(t in cal(T)) (a_T (t) log T - m (op("ph")(a_T (t)) - a_T (t) log Omega)) \
       & quad <= -(mu_C + h_P + sum_(j in J) h_K (j) - m_lambda) + 2 F_0 \
       & quad + (50 C_0 + 10) (|cal(T)| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $

  4. *Dividing through by $delta_0 log T$*:
     Because every term on the right-hand side is either negative (from $2 F_0$ and the Arakelov positivity) or strictly subdominant at the stretched-exponential scale $L = x^epsilon$, $b = exp(L)$, $a = x b$, dividing by $delta_0 log T$ forces an explicit *one-sided upper bound* on the smoothed prime sum $sum_(t in cal(T)) a_T (t)$ (or equivalently, on the real part of the prime-power sum weighted by the Dirichlet character $chi$ in the explicit formula).

  This one-sided upper bound is precisely the analytic hypothesis demanded by `TopG`: as established in Chapters 4 and 5, Landau's oscillation theorem and the explicit formula for $L(s, chi)$ show that if $L(s, chi)$ possessed any nontrivial zero off the critical line $op("Re")(s) = 1 / 2$ (say with real part $beta_0 > 1 / 2$), then the smoothed prime sum would necessarily oscillate with amplitude $Omega(X^(beta_0))$ in both positive and negative directions along arbitrarily large scales $X -> oo$. The one-sided upper bound extracted from `DivIneqObjU` + `HeightS` forbids those positive oscillations once $x$ is sufficiently large, thereby closing the contradiction and proving the Generalized Riemann Hypothesis.

  #lean-note(title: "Lean 4 Formalization: DivIneqTopAnchorU and TopCovolSlim2Use", module: "Formalism/DivisorInequality/DivIneqTopAnchorU.lean")[
    Every theorem and inequality in this chapter is machine-checked in Lean 4 without `sorry`:
    - `Formalism.DivisorInequality.DivIneqObjU` (`DivIneqTopAnchorU.lean`, lines 59–215) states the Divisor-Slope Master Inequality (Theorem 15.6) verbatim, building on the covolume comparison `Formalism.DivisorInequality.BoundsMu` in `Formalism/DivisorInequality/StatementObj.lean` and the slope definition `Formalism.HN.muDef` in `Formalism/HarderNarasimhan/QuotRealize.lean`.
    - `Formalism.DivisorInequality.HeightS` (`DivIneqTopAnchorU.lean`, lines 216–274) states and isolates the Height Sum Bound (Theorem 15.7), with the exact three threshold inequalities on `Ch`: `2 * (16 + CT + Cev) ≤ Ch`, `Cth + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ Ch`, and `2 * (C2 + C4) * (CT + C8) ≤ Ch`.
    - `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` in `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean` (lines 75–82) constructs `GlobalTheory.CovTop.CovolumeBoundOfX` from arithmetic Hilbert–Samuel (`PositivityTheory.MbHsUse.HSUse`), Moriwaki bigness (`MoriwakiBigStatement`), integral Siegel toroidal compactifications (`SiegelToroidalIntegral`, `ToroidalForFanKS`), Chow form height comparisons (`ChowFormHeightComparison₂`), Fargues exactness, Zarhin's trick, Nef Riemann–Roch, and Grothendieck deformation. Together with `DivIneqObjU` and `HeightS`, this supplies the Arakelov height input that drives the final prime-sum bound in `TopG`.
  ]

  #exercises((
    [
      *Properties of the logarithmic Stirling function.* Let $op("ph")(nu) = nu log nu - nu$ for $nu > 0$, with $op("ph")(0) = 0$.
      (a) Prove that $op("ph")$ is strictly convex on $[0, oo)$ with global minimum $op("ph")(1) = -1$.
      (b) For any $nu_1, dots.c, nu_r >= 0$ with sum $S = sum_(i=1)^r nu_i$, prove the superadditivity inequality
      $ sum_(i=1)^r op("ph")(nu_i) <= op("ph")(S) <= sum_(i=1)^r op("ph")(nu_i) + S log r. $
      (c) Relate this to the multinomial coefficient $S! / (nu_1 ! dots.c nu_r !)$ and explain why the hypothesis $sum_i op("ph")(nu_(j, rho, i)) - op("logH")(j, rho) <= bold(1)_(rho in cal(T)) op("ph")(a_T (rho)) + e_E (j, rho)$ in `DivIneqObjU` is sharp up to the multinomial entropy term.
    ],
    [
      *Quotient Hermitian metrics and Schur complements.* Let $V = bb(C)^(n_H)$ be equipped with the Hermitian inner product $chevron.l z, w chevron.r = z^* H_m w$ where $H_m in M_(n_H) (bb(C))$ is Hermitian positive definite, and let $P_m : bb(C)^(n_H) -> bb(C)^D$ be a surjective linear map.
      (a) Show that for every $u in bb(C)^D$, the unique vector $z in bb(C)^(n_H)$ of minimal $H_m$-norm satisfying $P_m z = u$ is given by $z = H_m^(-1) P_m^* (P_m H_m^(-1) P_m^*)^(-1) u$.
      (b) Deduce that the quotient Hermitian norm on $bb(C)^D approx bb(C)^(n_H) / ker(P_m)$ has Gram matrix $op("quotGram")(P_m, H_m) = (P_m H_m^(-1) P_m^*)^(-1)$.
      (c) Verify that if $H_m$ has entries in a totally real subfield $K_0$ and $P_m$ has entries in $K$, then $op("quotGram")(P_m, H_m)$ is rationally Hermitian over $K$.
    ],
    [
      *Local-global gluing of lattices over Dedekind domains.* Let $cal(O)_K$ be the ring of integers of a number field $K$, let $Lambda_0 subset K^D$ be a full $cal(O)_K$-lattice, and suppose that for each $y in op("Spec")_1 (cal(O)_K)$ we are given a full $cal(O)_(K, y)$-lattice $L_y subset K^D$ such that $L_y = (Lambda_0)_y$ for all but finitely many $y$. Prove that
      $ R = inter.big_(y in op("Spec")_1 (cal(O)_K)) L_y $
      is a full $cal(O)_K$-lattice in $K^D$ whose localization at every prime ideal $y$ equals $L_y$. Apply this to construct the glued lattice $R$ of Section 15.1 from $iota(mu(y)) cal(A)_2 (mu(y))$.
    ],
    [
      *Sharpness of the weighted-to-unweighted slope comparison.* In Lemma 15.3, assume $lambda_0 = 0$ and $op("dg")(s) <= op("rk")(s) H_0$ for all $s in op("Sg")$, with $(1 - delta_S) bar(n) <= n_S (s) <= (1 + delta_S) bar(n)$ for $0 < delta_S < 1$.
      (a) Construct an explicit two-stratum example ($|op("Sg")| = 2$) achieving equality in
      $ (sum_s n_S (s) op("dg")(s)) / (sum_s n_S (s) op("rk")(s)) = H_0 - (1 + delta_S) / (1 - delta_S) (H_0 - (sum_s op("dg")(s)) / (sum_s op("rk")(s))). $
      (b) Explain why the hypothesis $op("dg")(s) <= op("rk")(s) (H_0 + lambda_0)$ (a uniform upper bound on stratum slopes) is indispensable for Lemma 15.3 to hold.
    ],
    [
      *Sharpness of the $12 delta_d Q_d$ good/bad bound.* In Step A of the proof of Proposition 15.4, we used $d_"bd" <= 3 delta_d d_N$ and $delta_d <= 1 / 12$ together with $|mu_N|, m_max, G_d <= Q_d$ to deduce $mu_G >= mu_N - 12 delta_d Q_d$.
      (a) Verify that the constant $12$ is the exact maximum of $9 / (1 - 3 delta_d)$ on $[0, 1 / 12]$.
      (b) What constant replaces $12$ if the threshold $delta_d <= 1 / 12$ is relaxed to $delta_d <= 1 / 6$? What happens as $delta_d -> 1 / 3^-$?
    ],
    [
      *The inverse-square prime tail $E_3$.* For a totally complex number field $K$ of degree $d_K = [K : bb(Q)]$, let $op("lw")(y) = (log N(y)) / d_K$ for $y in op("Spec")_1 (cal(O)_K)$ and let $op("plc")(y) = p$ be the rational prime below $y$. Prove that
      $ sum_(y in op("Spec")_1 (cal(O)_K)) op("lw")(y) dot.c 2 / op("plc")(y)^2 <= 2 sum_p (log p) / p^2 < 2. $
      (Hint: use the fundamental identity $sum_(y | p) e(y | p) f(y | p) = d_K$ and bound $sum_p (log p) / p^2$ by comparing with an integral or using the first few primes.)
    ],
    [
      *Checking the exact cancellation in `DivIneqObjU`.* Suppose the alignment hypothesis $|p_q (j) - k| <= m$ in Theorem 15.6 were weakened to $|p_q (j) - k| <= k / 2$. Trace where the proof of Theorem 15.6 breaks down, and calculate the order of magnitude of the uncanceled error term $sum_j sum_rho |p_q (j) - k| w(j, rho) |log Omega|$ at the scale $L = x^epsilon$, $b = exp(L)$, $a = x b$.
    ],
    [
      *Embedding averaging in `HeightS`.* Suppose in Theorem 15.7 that the exact period-average identity $|op("Emb")|^(-1) sum_(s in op("Emb")) log Omega_tau (tau, s) = log Omega$ is replaced by an approximate identity
      $ |1 / |op("Emb")| sum_(s in op("Emb")) log Omega_tau (tau, s) - log Omega| <= eta_Omega. $
      Determine the largest size of $eta_Omega$ (as a function of $f, m, N, L, L_a, b$) for which the conclusion $h_P + sum_j h_K (j) - m_lambda <= h_u$ remains valid after increasing $C_h$ by an absolute constant.
    ],
    [
      *Optimizing the Stirling-period trade-off for `TopG`.* Consider the function $Phi(u) = u (log T + m log Omega + m - m log u)$ for $u > 0$, where $m >= 1$ and $T, Omega > 0$.
      (a) Verify that $Phi$ attains its unique global maximum at $u_* = Omega T^(1 / m)$ with $Phi(u_*) = m Omega T^(1 / m)$.
      (b) Show that if $0 < u <= e^(-delta_0) u_*$ with $delta_0 > 0$, then $Phi(u) >= m (1 + delta_0) u$.
      (c) Compare the error scale $a L_a = x exp(x^epsilon) log(a r_d)$ with $x^epsilon B_0 = f m x^(2 epsilon) exp(x^epsilon)$ as $x -> oo$ with $f, m$ polynomial in $log x$ and $0 < epsilon < 1 / 4$, confirming that $x^epsilon B_0 = o(a L_a)$.
    ],
  ))
]
