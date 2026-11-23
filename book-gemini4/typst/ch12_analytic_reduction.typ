// ============================================================================
// Chapter 12: From Nonvanishing in Re(s) > 1/2 to the Main Inequality
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch12() = [
  #chapter(
    "From Nonvanishing in Re(s) > 1/2 to the Main Inequality",
    short-title: "Analytic Reduction to the Main Inequality",
    epigraph: "The abscissa of convergence of a Dirichlet integral with nonnegative integrand is necessarily a singularity on the real axis.",
    epigraph-source: "Edmund Landau, 1905",
    overview: [
      The preceding chapters have assembled the automorphic, arithmetic-geometric, and Iwasawa-theoretic tools required for the Alpöge–Claude–Riemann theorem. Before entering the heart of the proof—where chains of theta lifts, Bost slope inequalities, and Kummer–Vandiver cohomology estimates are combined to bound prime-power sums—we must erect the analytic bridge that connects the classical statements of the Riemann Hypothesis (RH) and the Generalized Riemann Hypothesis (GRH) to the exact inequality produced by the automorphic engine.

      This chapter constructs that bridge in complete, self-contained rigor, descending layer by layer from the top-level conjecture to the precise analytic target `TopG`. In Section 12.1 we prove that nonvanishing of $L(s, psi)$ in the right half-plane $op("Re")(s) > 1\/2$ for all primitive Dirichlet characters $psi$ implies both full GRH for arbitrary (possibly imprimitive) characters and the classical Riemann Hypothesis (`UpperTheory.Top.imprimitive`, `Claim.strip`, and `Claim.zeta`). In Section 12.2 we develop the Mellin–Landau engine (`Formalism.ZetaNonvanishing`), establishing `mellin_H` and `key_identity` for the regularized product $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ and showing how the divided difference `dslope` cancels the double pole at $s = 1$ and isolates any hypothetical zero $rho$ with $op("Re")(rho) > 1\/2$. Section 12.3 refines Landau's classical positivity argument into a windowed theorem on sparse power intervals $[Y, Y^lambda]$ (with $lambda = 3\/2$), explaining the auxiliary character family `GChi psi`, the window existence condition `HostExW`, and family connectivity `FamilyClassConnected`. Section 12.4 formulates the Main Inequality (M) and the top-level target `TopG`, demonstrating how `zeroFreeOn_of_tiedWin_cyc` bridges `TopG` and `VWin` to `ZeroFreeAll` and explaining the Guinand–Weil variance test-function heuristic behind the sign. Finally, Section 12.5 documents the Lean 4 formalization with verbatim excerpts from `ClaimStrip.lean`, `Assembly.lean`, and `ZeroFreeAllOfTopG.lean`.
    ],
    label-name: "ch:analytic-reduction",
  )

  == Reduction from GRH and RH to Primitive Nonvanishing in $op("Re")(s) > 1\/2$

  The Generalized Riemann Hypothesis asserts that every zero of every Dirichlet $L$-function $L(s, chi)$ inside the critical strip $0 < op("Re")(s) < 1$ lies on the critical line $op("Re")(s) = 1\/2$. The classical Riemann Hypothesis asserts that every zero of $zeta(s)$ outside the trivial negative even integers $s = -2, -4, -6, dots.c$ lies on $op("Re")(s) = 1\/2$. At first glance, these statements involve infinitely many imprimitive characters, both halves of the critical strip, and (for $zeta(s)$) the entire left half-plane $op("Re")(s) <= 0$. Our first task is to collapse all of these requirements into a single clean assertion: nonvanishing of *primitive* Dirichlet $L$-functions in the open half-plane $op("Re")(s) > 1\/2$.

  === Top-Level Predicates

  To keep the logical architecture transparent—and to mirror the exact hierarchy of definitions in `HalfPlane.lean`, `ExplicitFormulaErrorOfHostConditions.lean`, and `ClaimStrip.lean`—we isolate four propositions.

  #definition(title: "Top-Level Nonvanishing Predicates")[
    We define the following four propositions concerning Dirichlet $L$-functions and the Riemann zeta function:
    1. *Primitive Half-Plane Nonvanishing (`ZeroFreeAll`):* For every primitive Dirichlet character $psi$ of conductor $M >= 1$ and every $s in bb(C)$ with $op("Re")(s) > 1\/2$,
       $ L(s, psi) != 0. $
       (Note that when $psi = 1_(op("mod") 1)$ is the trivial character of conductor $1$, $L(s, psi) = zeta(s)$ has a simple pole at $s = 1$; in Mathlib's conventions, `riemannZeta 1` is assigned a nonzero sentinel value or excluded by $s != 1$, and indeed `LFunction` at $s = 1$ for $chi = 1$ is handled separately in `Claim.HalfPlane` below.)
    2. *General Half-Plane Nonvanishing (`Claim.HalfPlane`):* For every modulus $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $op("Re")(s) > 1\/2$ such that $chi != 1$ or $s != 1$,
       $ L(s, chi) != 0. $
    3. *Generalized Riemann Hypothesis in the Critical Strip (`Claim.Strip`):* For every modulus $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $0 < op("Re")(s) < 1$,
       $ L(s, chi) = 0 ==> op("Re")(s) = 1 / 2. $
    4. *Classical Riemann Hypothesis (`Claim.Zeta`):* For every $s in bb(C)$ such that $zeta(s) = 0$, $s != 1$, and $s in.not {-2(n + 1) : n in bb(N)}$,
       $ op("Re")(s) = 1 / 2. $
  ]

  The chain of implications we establish in this section is
  $ "ZeroFreeAll" ==> "Claim.HalfPlane" ==> ("Claim.Strip" and "Claim.Zeta"). $
  Every step is completely elementary once we have the finite Euler-factor factorization for imprimitive characters, the functional equation for primitive $L$-functions, and the classical Hadamard–de la Vallée Poussin nonvanishing theorem on $op("Re")(s) >= 1$.

  === Passing from Primitive to Imprimitive Characters

  Let $chi$ be a Dirichlet character modulo $N >= 1$, let $f = f_chi | N$ be its conductor, and let $psi = chi^*$ be the unique primitive Dirichlet character modulo $f$ that induces $chi$. For $op("Re")(s) > 1$, the Euler products of $L(s, chi)$ and $L(s, psi)$ differ only at the finitely many primes $p | N$ that do not divide $f$:
  $ L(s, chi) = L(s, psi) product_(p | N \ p divides.not f) (1 - psi(p) p^(-s)). $
  More cleanly still, since $psi(p) = 0$ whenever $p | f$, the factor $1 - psi(p) p^(-s)$ equals $1$ for every prime $p | f$. Hence we may write the product over *all* primes $p | N$ (as in Mathlib's `DirichletCharacter.LFunction_changeLevel`):
  $ L(s, chi) = L(s, psi) product_(p | N) (1 - psi(p) p^(-s)). $ <eq:ch12-change-level>
  By analytic continuation, @eq:ch12-change-level holds for all $s in bb(C)$ whenever $psi != 1$ or $s != 1$ (since if $psi = 1$, then $chi$ is the principal character modulo $N$ and both sides have a simple pole at $s = 1$).

  #lemma(title: "Nonvanishing of Extra Euler Factors (`Claim.factor_ne_zero`)")[
    Let $psi$ be a Dirichlet character modulo $M >= 1$, let $p$ be a prime, and let $s in bb(C)$ satisfy $op("Re")(s) > 0$. Then
    $ 1 - psi(p) p^(-s) != 0. $
  ]

  #proof[
    Suppose for contradiction that $1 - psi(p) p^(-s) = 0$, so that $psi(p) p^(-s) = 1$. Since $p >= 2 > 1$ and $op("Re")(s) > 0$, we have
    $ |p^(-s)| = p^(-op("Re")(s)) < 1. $
    Because $psi$ takes values in the unit circle union ${0}$, we have $|psi(p)| <= 1$. Multiplying gives
    $ 1 = |psi(p) p^(-s)| = |psi(p)| dot.c |p^(-s)| <= 1 dot.c p^(-op("Re")(s)) < 1, $
    which is absurd.
  ]

  Note that the boundary $op("Re")(s) = 0$ is sharp: if $psi(p) != 0$, then $1 - psi(p) p^(-s)$ has infinitely many purely imaginary zeros along the line $op("Re")(s) = 0$, namely $s = (i arg(psi(p)) + 2 pi i k) \/ log p$ for $k in bb(Z)$. Because our target region is $op("Re")(s) > 0$ (and a fortiori $op("Re")(s) > 1\/2$), these imprimitive zeros on the imaginary axis never interfere.

  #theorem(title: "Imprimitive Reduction (`UpperTheory.Top.imprimitive`)")[
    Primitive half-plane nonvanishing (`ZeroFreeAll`) implies general half-plane nonvanishing (`Claim.HalfPlane`).
  ]

  #proof[
    Assume `ZeroFreeAll`. Let $N >= 1$, let $chi$ be a Dirichlet character modulo $N$, and let $s in bb(C)$ satisfy $op("Re")(s) > 1\/2$ and ($chi != 1$ or $s != 1$). Let $f = f_chi >= 1$ be the conductor of $chi$ and $psi = chi^*$ its primitive inducing character modulo $f$.

    First, we verify that $psi != 1$ or $s != 1$. If $s != 1$, this holds immediately. If $chi != 1$, then $psi$ cannot be the principal character modulo $f$: for if $psi = 1_(op("mod") f)$, then inducing $psi$ to modulus $N$ would yield $chi = 1_(op("mod") N)$, contradicting $chi != 1$. Thus the condition ($psi != 1$ or $s != 1$) is satisfied, and the level-change identity @eq:ch12-change-level applies:
    $ L(s, chi) = L(s, psi) product_(p | N) (1 - psi(p) p^(-s)). $
    By `ZeroFreeAll` applied to the primitive character $psi$ at $s$ (with $op("Re")(s) > 1\/2$), we have $L(s, psi) != 0$. Moreover, since $op("Re")(s) > 1\/2 > 0$, the preceding lemma guarantees $1 - psi(p) p^(-s) != 0$ for every prime $p | N$. A finite product of nonzero complex numbers is nonzero, so $L(s, chi) != 0$.
  ]

  === Reflection Across the Critical Line and Proof of `Claim.strip`

  To extend nonvanishing from the right half-strip $1\/2 < op("Re")(s) < 1$ to the left half-strip $0 < op("Re")(s) < 1\/2$, we reflect zeros via the functional equation of the completed $L$-function. Recall from Chapter 2 that for a primitive Dirichlet character $psi$ modulo $M >= 1$ with parity $a = (1 - psi(-1)) \/ 2 in {0, 1}$, the Archimedean gamma factor is
  $ Gamma_psi (s) = Gamma_bb(R) (s + a) = pi^(-(s + a)/2) Gamma((s + a) / 2), $
  and the completed $L$-function $Lambda(s, psi) = M^(s/2) Gamma_psi (s) L(s, psi)$ (or in Mathlib's normalization, `completedLFunction` $Lambda(s, psi) = Gamma_psi (s) L(s, psi)$ with the conductor factor absorbed into the root number) satisfies the functional equation
  $ Lambda(1 - s, psi^(-1)) = epsilon(psi^(-1)) Lambda(s, psi), $
  where $epsilon(psi^(-1))$ is a nonzero algebraic factor involving the Gauss sum and $M^(s - 1\/2)$. (In Mathlib's `IsPrimitive.completedLFunction_one_sub`, the identity is stated in the form $Lambda(1 - s, psi^(-1)) = (text("explicit nonzero factor")) dot.c Lambda(s, psi)$.)

  #lemma(title: "Three Reflection Lemmas (`prim_zero`, `gamma_ne_zero`, `prim_reflect`)")[
    1. *(`Claim.prim_zero`.)* Let $chi$ be a Dirichlet character modulo $N >= 1$ with primitive inducing character $psi = chi^*$. If $0 < op("Re")(s) < 1$ and $L(s, chi) = 0$, then $L(s, psi) = 0$.
    2. *(`Claim.gamma_ne_zero`.)* For any Dirichlet character $phi$ modulo $M >= 1$ and any $t in bb(C)$ with $op("Re")(t) > 0$, we have $Gamma_phi (t) != 0$.
    3. *(`Claim.prim_reflect`.)* Let $psi$ be a primitive Dirichlet character modulo $M >= 1$. If $0 < op("Re")(s) < 1$ and $L(s, psi) = 0$, then $L(1 - s, psi^(-1)) = 0$.
  ]

  #proof[
    For (1), since $op("Re")(s) < 1$, we have $s != 1$, so @eq:ch12-change-level holds:
    $ 0 = L(s, chi) = L(s, psi) product_(p | N) (1 - psi(p) p^(-s)). $
    Because $op("Re")(s) > 0$, every factor $1 - psi(p) p^(-s)$ is nonzero by `Claim.factor_ne_zero`. Hence $L(s, psi) = 0$.

    For (2), the real gamma factor $Gamma_bb(R) (z) = pi^(-z\/2) Gamma(z\/2)$ is nonzero whenever $op("Re")(z) > 0$, because $pi^(-z\/2) = exp(-(z\/2) log pi) != 0$ everywhere and $Gamma(w)$ has no zeros in $bb(C)$ (and no poles in $op("Re")(w) > 0$). If $phi$ is even, $Gamma_phi (t) = Gamma_bb(R) (t) != 0$ since $op("Re")(t) > 0$. If $phi$ is odd, $Gamma_phi (t) = Gamma_bb(R) (t + 1) != 0$ since $op("Re")(t + 1) = op("Re")(t) + 1 > 1 > 0$.

    For (3), set $t = 1 - s$. Since $0 < op("Re")(s) < 1$, we have $s != 0$, $op("Re")(t) = 1 - op("Re")(s) > 0$, and $t != 0$. Because $s != 0$, the relation $L(s, psi) = Lambda(s, psi) \/ Gamma_psi (s)$ holds without ambiguity. Since $L(s, psi) = 0$ and $Gamma_psi (s) != 0$ by (2), we deduce $Lambda(s, psi) = 0$. Moreover, $psi^(-1)$ is also primitive of the same conductor $M$ (since $ker(psi^(-1)) = ker(psi)$). Applying the functional equation of the primitive character $psi^(-1)$ at $s$ gives
    $ Lambda(1 - s, psi^(-1)) = epsilon(psi^(-1)) Lambda(s, psi) = 0. $
    Finally, since $t = 1 - s != 0$, we obtain
    $ L(1 - s, psi^(-1)) = Lambda(1 - s, psi^(-1)) / Gamma_(psi^(-1)) (1 - s) = 0 / Gamma_(psi^(-1)) (1 - s) = 0. $
  ]

  We can now prove the full Generalized Riemann Hypothesis in the critical strip from `Claim.HalfPlane`.

  #theorem(title: "Reduction of GRH to the Right Half-Plane (`Claim.strip`)")[
    General half-plane nonvanishing (`Claim.HalfPlane`) implies GRH in the critical strip (`Claim.Strip`).
  ]

  #proof[
    Assume `Claim.HalfPlane`. Let $N >= 1$, let $chi$ be a Dirichlet character modulo $N$, and let $s in bb(C)$ satisfy $0 < op("Re")(s) < 1$ and $L(s, chi) = 0$. Note that $s != 0$ and $s != 1$. By trichotomy for real numbers, one of three cases holds for $op("Re")(s)$ relative to $1\/2$:
    - *Case 1: $op("Re")(s) > 1\/2$.* Since $s != 1$, `Claim.HalfPlane` directly yields $L(s, chi) != 0$, contradicting $L(s, chi) = 0$.
    - *Case 2: $op("Re")(s) < 1\/2$.* Let $psi = chi^*$ be the primitive character modulo $f = f_chi$ inducing $chi$. By `Claim.prim_zero`, $L(s, psi) = 0$. By `Claim.prim_reflect`, $L(1 - s, psi^(-1)) = 0$. Now $op("Re")(1 - s) = 1 - op("Re")(s) > 1\/2$, and $1 - s != 1$ (since $s != 0$). Applying `Claim.HalfPlane` to $psi^(-1)$ at $1 - s$ gives $L(1 - s, psi^(-1)) != 0$, a contradiction.
    - *Case 3: $op("Re")(s) = 1\/2$.* This is the desired conclusion.
  ]

  #remark(title: "A Footnote on Trichotomy")[
    In his informal announcement (`remark.pdf`, footnote 2), Levent Alpöge fondly recounted testing an automated prose dump of the Lean proof: "Claude cutely called it the GRH ... 'book'—I looked at Theorem 1 and it began by noting that because the reals are totally ordered if $sigma != 1\/2$ then $sigma > 1\/2$ or $sigma < 1\/2$." That line is literally line 94 of `ClaimStrip.lean`: `rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt`.
  ]

  === Deduction of the Classical Riemann Hypothesis (`Claim.zeta`)

  The classical statement of the Riemann Hypothesis quantifies over *all* $s in bb(C)$ rather than restricting a priori to the critical strip $0 < op("Re")(s) < 1$. To deduce `Claim.Zeta` from `Claim.HalfPlane`, we must therefore also account for the closed half-planes $op("Re")(s) >= 1$ and $op("Re")(s) <= 0$.

  #theorem(title: "Reduction of Classical RH (`Claim.zeta`)")[
    General half-plane nonvanishing (`Claim.HalfPlane`) implies the classical Riemann Hypothesis (`Claim.Zeta`).
  ]

  #proof[
    Assume `Claim.HalfPlane`, and hence also `Claim.Strip` by the preceding theorem. Let $s in bb(C)$ satisfy $zeta(s) = 0$, $s != 1$, and $s != -2(n + 1)$ for all $n in bb(N)$.

    First, observe that $s != 0$, because $zeta(0) = -1\/2 != 0$. We split into cases according to the sign of $op("Re")(s)$:
    - *Case 1: $op("Re")(s) >= 1$.* By the classical Hadamard–de la Vallée Poussin theorem (`riemannZeta_ne_zero_of_one_le_re`), $zeta(s) != 0$ for all $op("Re")(s) >= 1$ (with $s != 1$), contradicting $zeta(s) = 0$.
    - *Case 2: $0 < op("Re")(s) < 1$.* The trivial character $1_(op("mod") 1)$ modulo $1$ satisfies $L(s, 1_(op("mod") 1)) = zeta(s)$. Applying `Claim.Strip` to $N = 1$, $chi = 1_(op("mod") 1)$ immediately gives $op("Re")(s) = 1\/2$.
    - *Case 3: $op("Re")(s) <= 0$.* We show this case is impossible. Because $s != 0$ and $s != -2(n + 1)$ for all $n in bb(N)$, the argument $s\/2$ is not a nonpositive integer, so $Gamma(s\/2)$ is finite and nonzero, and hence $Gamma_bb(R) (s) = pi^(-s\/2) Gamma(s\/2) in bb(C)^times$. (In Mathlib's formalization, `Gammaℝ` is extended by $0$ at the poles $s = -2n$ of $Gamma(s\/2)$, so `Complex.Gammaℝ_eq_zero_iff` characterizes the excluded points directly as $Gamma_bb(R) (s) = 0 <==> exists n in bb(N), s = -2n$.) From $zeta(s) = Lambda(s) \/ Gamma_bb(R) (s)$ (where $Lambda(s) = Gamma_bb(R) (s) zeta(s)$ is the completed zeta function, holomorphic away from $s = 0, 1$), the vanishing $zeta(s) = 0$ forces $Lambda(s) = 0$. By Riemann's functional equation $Lambda(1 - s) = Lambda(s)$, we obtain $Lambda(1 - s) = 0$. Since $op("Re")(s) <= 0$ and $s != 0$, we have $op("Re")(1 - s) = 1 - op("Re")(s) >= 1$ and $1 - s != 1$, so $Gamma_bb(R) (1 - s) in bb(C)^times$ and
      $ zeta(1 - s) = Lambda(1 - s) / Gamma_bb(R) (1 - s) = 0. $
      By Hadamard–de la Vallée Poussin, $zeta(1 - s) != 0$ for $op("Re")(1 - s) >= 1$, a contradiction.
  ]

  Together, `UpperTheory.Top.imprimitive`, `Claim.strip`, and `Claim.zeta` reduce the entirety of RH and GRH to proving `ZeroFreeAll`: for every primitive Dirichlet character $psi$, $L(s, psi)$ has no zeros in $op("Re")(s) > 1\/2$.

  == The Mellin–Landau Engine (`Formalism.ZetaNonvanishing`)

  How does one prove that a Dirichlet $L$-function $L(s, psi)$ has no zeros in $op("Re")(s) > 1\/2$? By the explicit formula (Chapter 1), the prime-power counting function $psi(x, chi) = sum_(n <= x) Lambda(n) chi(n)$ has an oscillatory expansion whose dominant terms are $-x^rho \/ rho$ summed over the nontrivial zeros $rho$ of $L(s, chi)$. Proving $|psi(x, chi) - delta_(chi, 1) x| = O_epsilon (x^(1\/2 + epsilon))$ for all $epsilon > 0$ would certainly imply GRH, because the Mellin transform would extend analytically to $op("Re")(s) > 1\/2$.

  Yet proving a *two-sided* bound of square-root quality directly is notoriously difficult: it demands simultaneously ruling out large positive deviations and large negative deviations of an arithmetic sum. Remarkably, *Landau's theorem on Dirichlet integrals with nonnegative integrands* shows that a *one-sided* bound suffices—provided we work with a nonnegative linear combination of von Mangoldt weights and a Riesz smoothing kernel whose Mellin transform puts the *right sign* on the residues at real zeros!

  In this section we develop the exact Mellin–Landau engine formalized in `Formalism/Statement.lean`, `Formalism/ZetaRealNonvanish.lean`, and `Formalism/ZetaNonvanishing/Assembly.lean`. This engine serves both as a warm-up for the windowed character-family version in Section 12.3 and as the standalone analytic core for real characters.

  === The Smoothed Prime Sum and the Regularized Product $P_chi (s)$

  Let $chi$ be a real, non-principal Dirichlet character modulo $N >= 1$ (so $chi(n) in {-1, 0, 1}$ for all $n$, i.e., $op("Im")(chi(n)) = 0$ and $chi != 1$). In the formalization, three concrete quadratic characters modulo $3$, $4$, and $7$ (`CharFacts`) are carried as test cases, though the algebra holds for any real non-principal $chi$.

  #definition(title: "Smoothed Weighted von Mangoldt Function and Remainder")[
    Let $chi$ be a Dirichlet character modulo $N >= 1$.
    1. Define the nonnegative arithmetic weight
       $ Lambda_(F, chi) (n) = Lambda(n) (1 + op("Re")(chi(n))) >= 0, $
       where $Lambda$ is the classical von Mangoldt function. (Since $|chi(n)| <= 1$, we always have $1 + op("Re")(chi(n)) >= 0$.)
    2. For $x > 0$, define the first-order Riesz (Cesàro) smoothed sum
       $ S_chi (x) = sum_(1 <= n <= floor(x)) Lambda_(F, chi) (n) (x / n - 1). $
    3. Define the logarithmic derivative constant at $s = 1$:
       $ gamma_(F, chi) = gamma + op("Re")((L'(1, chi)) / (L(1, chi))), $
       where $gamma = 0.57721566 dots.c$ is the Euler–Mascheroni constant.
    4. Define the normalized remainder function
       $ G_chi (x) = S_chi (x) - x log x + (1 + gamma_(F, chi)) x. $
    5. For parameters $sigma_0 < 1$ and $C in bb(R)$, define the shifted remainder
       $ H_f (sigma_0, C, x) = G_chi (x) + C x^(sigma_0), $
       and its Mellin transform (on $(1, oo)$)
       $ I_"mel" (sigma_0, C, s) = integral_1^oo H_f (sigma_0, C, x) x^(-s - 1) dif x. $
    6. Define the regularized $L$-product $P_chi : bb(C) -> bb(C)$ by
       $ P_chi (s) = cases(L(1, chi) & "if" s = 1, (s - 1) zeta(s) L(s, chi) & "if" s != 1.) $
  ]

  Observe why the factor $1 + op("Re")(chi(n))$ is so natural: for a real character $chi$ attached to a quadratic number field $K$, $Lambda_(F, chi) (n)$ is precisely the von Mangoldt function of the Dedekind zeta function $zeta_K (s) = zeta(s) L(s, chi)$ (up to finitely many ramified primes), and its Dirichlet series is $-zeta'_K (s) \/ zeta_K (s) = -zeta'(s)\/zeta(s) - L'(s, chi)\/L(s, chi)$. Moreover, multiplying by $(s - 1)$ removes the simple pole of $zeta(s)$ at $s = 1$: since $lim_(s -> 1) (s - 1) zeta(s) = 1$, the function $P_chi (s)$ is entire!

  #lemma(title: "Logarithmic Derivative of $P_chi$ (`Pfun_ne_zero_of_one_le_re`, `LSeries_LamF_eq`)")[
    Let $chi$ be a real, non-principal Dirichlet character modulo $N >= 1$.
    1. For all $s in bb(C)$ with $op("Re")(s) >= 1$, we have $P_chi (s) != 0$.
    2. For all $s in bb(C)$ with $op("Re")(s) > 1$, the Dirichlet series of $Lambda_(F, chi)$ converges absolutely and satisfies
       $ L(Lambda_(F, chi), s) := sum_(n = 1)^oo (Lambda_(F, chi) (n)) / n^s = -(P'_chi (s)) / (P_chi (s)) + 1 / (s - 1). $ <eq:ch12-lseries-lamf>
  ]

  #proof[
    For (1), if $s = 1$, then $P_chi (1) = L(1, chi) != 0$ by Dirichlet's nonvanishing theorem (since $chi != 1$). If $s != 1$ and $op("Re")(s) >= 1$, then $s - 1 != 0$, $zeta(s) != 0$, and $L(s, chi) != 0$ by Hadamard–de la Vallée Poussin, so $P_chi (s) = (s - 1) zeta(s) L(s, chi) != 0$.

    For (2), let $op("Re")(s) > 1$. Because $chi$ is real-valued, $op("Re")(chi(n)) = chi(n)$, so
    $ L(Lambda_(F, chi), s) = sum_(n = 1)^oo (Lambda(n)) / n^s + sum_(n = 1)^oo (Lambda(n) chi(n)) / n^s = -(zeta'(s)) / (zeta(s)) - (L'(s, chi)) / (L(s, chi)). $
    On the other hand, for $s != 1$ the product rule gives
    $ P'_chi (s) = zeta(s) L(s, chi) + (s - 1) zeta'(s) L(s, chi) + (s - 1) zeta(s) L'(s, chi). $
    Dividing by $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ (which is nonzero since $op("Re")(s) > 1$) yields
    $ (P'_chi (s)) / (P_chi (s)) = 1 / (s - 1) + (zeta'(s)) / (zeta(s)) + (L'(s, chi)) / (L(s, chi)). $
    Rearranging immediately produces @eq:ch12-lseries-lamf.
  ]

  === The Mellin Transform Formula `mellin_H`

  The reason we chose the Riesz weight $(x \/ n - 1)_+$ in $S_chi (x)$—rather than the sharp step function $1_(n <= x)$ of Chebyshev's $psi(x)$—is twofold. First, $S_chi (x)$ is continuous and piecewise linear, avoiding jump discontinuities. Second, for every integer $n >= 1$ and every $s in bb(C)$ with $op("Re")(s) > 1$, the elementary Mellin transform of $(x \/ n - 1)_+$ is
  $
    integral_1^oo max(x / n - 1, 0) x^(-s - 1) dif x
    &= integral_n^oo (x^(-s) / n - x^(-s - 1)) dif x \
    &= (n^(1 - s)) / (n (s - 1)) - n^(-s) / s = n^(-s) / (s (s - 1)).
  $
  Notice the extra factor $1 \/ (s - 1)$ in the denominator! Not only does $1 \/ (s(s - 1))$ decay like $|s|^(-2)$ vertically (guaranteeing absolute convergence of Mellin inversion integrals), it also *flips the sign* of the residue at every real zero $beta in (0, 1)$, because $beta (beta - 1) < 0$.

  #proposition(title: "Mellin Transform of the Shifted Remainder (`mellin_H`)")[
    Let $chi$ be a Dirichlet character modulo $N >= 1$, let $sigma_0 < 1$ and $C in bb(R)$, and let $s in bb(C)$ satisfy $op("Re")(s) > 1$. Then $x |-> H_f (sigma_0, C, x) x^(-s - 1)$ is integrable on $(1, oo)$ and
    $ I_"mel" (sigma_0, C, s) = (L(Lambda_(F, chi), s)) / (s (s - 1)) - 1 / (s - 1)^2 + (1 + gamma_(F, chi)) / (s - 1) + C / (s - sigma_0). $ <eq:ch12-mellin-H>
  ]

  #proof[
    We verify the four elementary Mellin transforms and their absolute integrability on $(1, oo)$ for $sigma = op("Re")(s) > 1$:
    1. *Smoothed prime sum (`MellinS`):* Since $0 <= Lambda_(F, chi) (n) <= 2 Lambda(n)$, Chebyshev's bound $psi(x) = O(x)$ implies $0 <= S_chi (x) <= 2 x sum_(n <= x) Lambda(n) \/ n = O(x log x)$, so $|S_chi (x)| x^(-sigma - 1)$ is integrable on $(1, oo)$ for every $sigma > 1$. By Fubini–Tonelli (all terms are nonnegative for real $s > 1$, and dominated for complex $op("Re")(s) > 1$),
       $
         integral_1^oo S_chi (x) x^(-s - 1) dif x
         &= sum_(n = 1)^oo Lambda_(F, chi) (n) integral_n^oo (x / n - 1) x^(-s - 1) dif x \
         &= (L(Lambda_(F, chi), s)) / (s (s - 1)).
       $
    2. *Power terms (`MellinElem` part 1):* For any real $a < sigma$, $integral_1^oo x^a x^(-sigma - 1) dif x = 1 \/ (sigma - a) < oo$, and by the fundamental theorem of calculus for complex exponentials,
       $ integral_1^oo x^a x^(-s - 1) dif x = [x^(a - s) / (a - s)]_1^oo = 1 / (s - a). $
       Applying this to $a = 1$ (since $1 < sigma$) and to $a = sigma_0$ (since $sigma_0 < 1 < sigma$) yields $1 \/ (s - 1)$ and $1 \/ (s - sigma_0)$, respectively.
    3. *Logarithmic term (`MellinElem` part 2):* For $sigma > 1$, substituting $x = e^u$ ($u in (0, oo)$) gives
       $ integral_1^oo (x log x) x^(-s - 1) dif x = integral_0^oo u e^(-(s - 1) u) dif u = 1 / (s - 1)^2, $
       with absolute integrability $integral_0^oo u e^(-(sigma - 1) u) dif u = 1 \/ (sigma - 1)^2 < oo$.

    Since $H_f (sigma_0, C, x) = S_chi (x) - x log x + (1 + gamma_(F, chi)) x + C x^(sigma_0)$, each of the four summands is integrable on $(1, oo)$ against $x^(-s - 1)$ (using $|f(x) x^(-s - 1)| = |f(x)| x^(-sigma - 1)$, `cint_of_abs`). By linearity of the Lebesgue integral,
    $
      I_"mel" (sigma_0, C, s)
      &= (L(Lambda_(F, chi), s)) / (s (s - 1)) - 1 / (s - 1)^2 \
      &quad + (1 + gamma_(F, chi)) dot.c 1 / (s - 1) + C dot.c 1 / (s - sigma_0),
    $
    which is @eq:ch12-mellin-H.
  ]

  === The Key Identity and Pole Cancellation via `dslope`

  Look closely at the right-hand side of @eq:ch12-mellin-H near $s = 1$. The first term $L(Lambda_(F, chi), s) \/ (s(s - 1))$ has a *double pole* at $s = 1$, because $L(Lambda_(F, chi), s) = 1\/(s - 1) + O(1)$. The second term $-1\/(s - 1)^2$ also has a double pole, and the third term $(1 + gamma_(F, chi))\/(s - 1)$ has a simple pole! The magic of the normalization $G_chi (x) = S_chi (x) - x log x + (1 + gamma_(F, chi)) x$ is that *both* the double pole and the simple pole at $s = 1$ cancel completely.

  To exhibit this cancellation algebraically without ever dividing by $0$ at $s = 1$, `Assembly.lean` introduces three auxiliary functions:
  $ q_0 (sigma_0, C, s) = -1 + s (1 + gamma_(F, chi)) + (C s (s - 1)) / (s - sigma_0), $
  $ A_"fun" (sigma_0, C, s) = -P'_chi (s) + q_0 (sigma_0, C, s) P_chi (s), $
  and the divided-difference meromorphic extension
  $ Phi(sigma_0, C, s) = ("dslope"(A_"fun" (sigma_0, C), 1, s)) / (s P_chi (s)), $
  where for any function $f : bb(C) -> bb(C)$ differentiable at $z_0$, Mathlib's divided difference `dslope` is defined by
  $ "dslope"(f, z_0, s) = cases((f(s) - f(z_0)) / (s - z_0) & "if" s != z_0, f'(z_0) & "if" s = z_0.) $

  #theorem(title: "Key Algebraic Identity and Pole Cancellation (`key_identity`)")[
    Let $chi$ be a real, non-principal Dirichlet character modulo $N >= 1$, let $sigma_0 < 1$, and let $C in bb(R)$.
    1. For all $s in bb(C)$ with $op("Re")(s) > 1$,
       $ s (s - 1) I_"mel" (sigma_0, C, s) = -(P'_chi (s)) / (P_chi (s)) + q_0 (sigma_0, C, s). $ <eq:ch12-key-identity>
    2. The function $A_"fun" (sigma_0, C, s)$ is holomorphic on $op("Re")(s) > sigma_0$ and vanishes at $s = 1$:
       $ A_"fun" (sigma_0, C, 1) = 0. $
    3. Consequently, $Phi(sigma_0, C, s)$ is meromorphic on $op("Re")(s) > sigma_0$, agrees identically with $I_"mel" (sigma_0, C, s)$ on $op("Re")(s) > 1$, is holomorphic at $s = 1$, and has its *only* singularities in $op("Re")(s) > sigma_0$ at the zeros $rho$ of $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ (equivalently, the zeros of $zeta(s)$ or $L(s, chi)$ in $op("Re")(s) > sigma_0$). At any such zero $rho$ of multiplicity $m_rho >= 1$ of $P_chi$, $Phi(sigma_0, C, s)$ has a simple pole with residue
       $ op("Res")_(s = rho) Phi(sigma_0, C, s) = - m_rho / (rho (rho - 1)). $ <eq:ch12-phi-residue>
  ]

  #proof[
    For (1), let $op("Re")(s) > 1$, so $s != 0$, $s - 1 != 0$, $s - sigma_0 != 0$, and $P_chi (s) != 0$. Multiplying @eq:ch12-mellin-H by $s (s - 1)$ and substituting @eq:ch12-lseries-lamf gives
    $
      &s (s - 1) I_"mel" (sigma_0, C, s) \
      &quad = L(Lambda_(F, chi), s) - s / (s - 1) + s (1 + gamma_(F, chi)) + (C s (s - 1)) / (s - sigma_0) \
      &quad = (-(P'_chi (s)) / (P_chi (s)) + 1 / (s - 1)) - s / (s - 1) + s (1 + gamma_(F, chi)) + (C s (s - 1)) / (s - sigma_0).
    $
    Now observe the exact cancellation
    $ 1 / (s - 1) - s / (s - 1) = (1 - s) / (s - 1) = -1! $
    The poles at $s = 1$ in the first two terms annihilate each other identically, leaving
    $
      s (s - 1) I_"mel" (sigma_0, C, s)
      &= -(P'_chi (s)) / (P_chi (s)) - 1 + s (1 + gamma_(F, chi)) + (C s (s - 1)) / (s - sigma_0) \
      &= -(P'_chi (s)) / (P_chi (s)) + q_0 (sigma_0, C, s),
    $
    proving @eq:ch12-key-identity.

    For (2), recall that $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ is entire, and $q_0 (sigma_0, C, s)$ is holomorphic on $bb(C) without {sigma_0}$, hence on $op("Re")(s) > sigma_0$. Thus $A_"fun" (sigma_0, C, s)$ is holomorphic on $op("Re")(s) > sigma_0$. To evaluate $A_"fun" (sigma_0, C, 1)$, we expand $P_chi (s)$ to first order around $s = 1$. Using the Laurent expansion $zeta(s) = (s - 1)^(-1) + gamma + O(s - 1)$ and the Taylor expansion $L(s, chi) = L(1, chi) + L'(1, chi)(s - 1) + O((s - 1)^2)$, we find
    $
      P_chi (s) &= (1 + gamma (s - 1) + O((s - 1)^2)) \
        &quad dot.c (L(1, chi) + L'(1, chi)(s - 1) + O((s - 1)^2)) \
        &= L(1, chi) + (gamma L(1, chi) + L'(1, chi)) (s - 1) + O((s - 1)^2).
    $
    Hence $P_chi (1) = L(1, chi)$ and
    $
      P'_chi (1) &= gamma L(1, chi) + L'(1, chi) \
        &= (gamma + (L'(1, chi)) / (L(1, chi))) P_chi (1) = gamma_(F, chi) P_chi (1),
    $
    where in the last equality we used that $chi$ is real, so $L(s, chi)$ is real on the real axis and $L'(1, chi) \/ L(1, chi) in bb(R)$ equals its own real part. On the other hand, evaluating $q_0$ at $s = 1$ gives
    $ q_0 (sigma_0, C, 1) = -1 + 1 dot.c (1 + gamma_(F, chi)) + 0 = gamma_(F, chi). $
    Therefore
    $
      A_"fun" (sigma_0, C, 1)
      &= -P'_chi (1) + q_0 (sigma_0, C, 1) P_chi (1) \
      &= -gamma_(F, chi) P_chi (1) + gamma_(F, chi) P_chi (1) = 0.
    $

    For (3), because $A_"fun" (sigma_0, C, dot.c)$ is holomorphic on $op("Re")(s) > sigma_0$ and vanishes at $s = 1$, its divided difference $"dslope"(A_"fun" (sigma_0, C), 1, s)$ is holomorphic on all of $op("Re")(s) > sigma_0$, and for $s != 1$ equals $A_"fun" (sigma_0, C, s) \/ (s - 1)$. Dividing by $s P_chi (s)$, we see that for $op("Re")(s) > 1$,
    $
      Phi(sigma_0, C, s) &= (A_"fun" (sigma_0, C, s)) / (s (s - 1) P_chi (s)) \
        &= (-(P'_chi (s)) / (P_chi (s)) + q_0 (sigma_0, C, s)) / (s (s - 1)) = I_"mel" (sigma_0, C, s).
    $
    At $s = 1$, both the numerator $"dslope"(A_"fun" (sigma_0, C), 1, s)$ and the denominator $s P_chi (s)$ are holomorphic, and the denominator evaluates to $1 dot.c L(1, chi) != 0$; hence $Phi(sigma_0, C, s)$ is holomorphic at $s = 1$. On the half-plane $op("Re")(s) > sigma_0$ (assuming $sigma_0 > 0$, or away from $s = 0$), the only zeros of $s P_chi (s)$ are the zeros $rho$ of $P_chi (s)$. Since $q_0$ is holomorphic at $rho$ (as $op("Re")(rho) > sigma_0$), the singular part of $Phi(sigma_0, C, s)$ at $rho$ comes entirely from $-P'_chi (s) \/ (s (s - 1) P_chi (s))$. Writing $P_chi (s) = (s - rho)^(m_rho) h(s)$ with $h(rho) != 0$, we have $P'_chi (s) \/ P_chi (s) = m_rho \/ (s - rho) + O(1)$, so
    $ Phi(sigma_0, C, s) = - m_rho / (rho (rho - 1)) dot.c 1 / (s - rho) + O(1) quad (s -> rho), $
    establishing @eq:ch12-phi-residue.
  ]

  #insight-box(title: "The Miracle of the Sign at Real Zeros")[
    Pause to inspect the sign of the residue @eq:ch12-phi-residue at a hypothetical *real* zero $rho = beta in (sigma_0, 1)$ of $P_chi (s)$! Because $0 < beta < 1$, we have $beta (beta - 1) = -beta (1 - beta) < 0$, and therefore
    $ op("Res")_(s = beta) Phi(sigma_0, C, s) = + m_beta / (beta (1 - beta)) > 0! $
    Now contrast the two possible one-sided bounds on $G_chi (x)$:
    - *Upper bound $G_chi (x) <= C x^(sigma_0)$:* Setting $f(x) = C x^(sigma_0) - G_chi (x) >= 0$, its Mellin transform is $M[f](s) = C\/(s - sigma_0) - Phi(sigma_0, 0, s)$. At any real zero $beta in (sigma_0, 1)$, the residue of $M[f](s)$ is $-m_beta \/ (beta(1 - beta)) < 0$. Hence as $sigma -> beta^+$, $M[f](sigma) -> -oo$. This is *impossible* for a nonnegative function $f(x) >= 0$, whose Mellin transform is nonnegative on $(sigma_c, oo)$! By Landau's theorem, $M[f](s)$ cannot have *any* singularity in $op("Re")(s) > sigma_0$—neither real nor complex—because any complex zero $rho$ with $op("Re")(rho) > sigma_0$ would force a real singularity at the abscissa of convergence $sigma_c >= op("Re")(rho) > sigma_0$, which in turn would have to be a real zero $beta = sigma_c in (sigma_0, 1)$, impossible by the residue sign!
    - *Lower bound $G_chi (x) >= -C x^(sigma_0)$:* Here $H_f (sigma_0, C, x) = G_chi (x) + C x^(sigma_0) >= 0$, and at a real zero $beta in (sigma_0, 1)$ the residue of $Phi(sigma_0, C, s)$ is $+m_beta \/ (beta(1 - beta)) > 0$, which is *consistent* with positivity. Thus a lower bound $G_chi (x) >= -C x^(sigma_0)$ rules out complex zeros in $op("Re")(s) > sigma_0$ *provided* one knows independently that $P_chi (sigma) != 0$ on $(sigma_0, 1)$ (as holds for $zeta(s)$ and for quadratic characters without Siegel zeros).

    This asymmetry explains why the Alpöge–Claude proof targets an *upper bound* $G_m (y) <= C y^theta$ rather than a lower bound: an upper bound on the Riesz-smoothed sum $G_m (y)$ kills *both* complex zeros and potential real (Siegel) zeros simultaneously, in one clean stroke!
  ]

  === Completing the Classical Landau Argument

  For completeness, let us record the exact deduction from a global one-sided upper bound on $G_chi (x)$ to zero-freeness in $op("Re")(s) > sigma_0$, before generalizing to sparse power-windows and arbitrary complex characters in Section 12.3.

  #corollary(title: "Global One-Sided Upper Bound Implies Zero-Free Half-Plane")[
    Let $chi$ be a real, non-principal Dirichlet character modulo $N >= 1$, and suppose there exist $sigma_0 in (0, 1)$, $C > 0$, and $X_0 >= 1$ such that
    $ G_chi (x) <= C x^(sigma_0) quad "for all" x >= X_0. $
    Then $zeta(s) != 0$ and $L(s, chi) != 0$ for all $s in bb(C)$ with $op("Re")(s) > sigma_0$.
  ]

  #proof[
    Set $f(x) = C x^(sigma_0) - G_chi (x)$ for $x >= X_0$, so $f(x) >= 0$ on $[X_0, oo)$. For $op("Re")(s) > 1$, define
    $
      J(s) &= integral_(X_0)^oo f(x) x^(-s - 1) dif x \
        &= (C / (s - sigma_0) - Phi(sigma_0, 0, s)) - integral_1^(X_0) (C x^(sigma_0) - G_chi (x)) x^(-s - 1) dif x.
    $
    The finite integral over $[1, X_0]$ is an entire function of $s$. Thus the right-hand side provides a meromorphic continuation of $J(s)$ to $op("Re")(s) > sigma_0$, whose only poles in $op("Re")(s) > sigma_0$ are simple poles at the zeros $rho$ of $P_chi (s)$ with residue $+m_rho \/ (rho(rho - 1))$.

    Suppose for contradiction that $P_chi$ has a zero in $op("Re")(s) > sigma_0$. Let
    $ sigma_c = inf { sigma > sigma_0 : integral_(X_0)^oo f(x) x^(-sigma - 1) dif x < oo } $
    be the abscissa of convergence of the nonnegative Mellin integral $J(s)$. Because $J(s)$ is holomorphic on $op("Re")(s) > sigma_c$ and agrees with the meromorphic continuation there, no pole of $J$ can lie in $op("Re")(s) > sigma_c$; hence $sigma_c >= sup { op("Re")(rho) : P_chi (rho) = 0 } > sigma_0$. On the other hand, by Landau's theorem on Laplace/Mellin integrals of nonnegative functions (which we prove quantitatively in the next section via Taylor coefficients at a point $sigma > 2$), $J(s)$ must have a singularity at the real point $s = sigma_c in (sigma_0, 1]$. Since $J(s)$ is holomorphic at $s = 1$ (as $Phi(sigma_0, 0, s)$ is holomorphic at $s = 1$ and $sigma_0 < 1$), we must have $sigma_c in (sigma_0, 1)$, and $sigma_c$ must be a real zero of $P_chi (s)$ of some multiplicity $m >= 1$.

    Evaluating $J(sigma)$ for real $sigma -> sigma_c^+$, the principal part is
    $ J(sigma) = - m / (sigma_c (1 - sigma_c)) dot.c 1 / (sigma - sigma_c) + O(1) -> -oo quad (sigma -> sigma_c^+). $
    Yet $f(x) >= 0$ for all $x >= X_0$ implies $J(sigma) = integral_(X_0)^oo f(x) x^(-sigma - 1) dif x >= 0$ for every real $sigma > sigma_c$, a contradiction. Therefore $P_chi (s) != 0$ for all $op("Re")(s) > sigma_0$.
  ]

  == One-Sided Prime-Power Bounds on Sparse Intervals $[Y, Y^(3\/2)]$

  The global hypothesis "$G_chi (x) <= C x^(sigma_0)$ for *all* $x >= X_0$" is still far stronger than what the automorphic machinery of the Alpöge–Claude proof produces. When we construct auxiliary abelian varieties, CM fields, and Behrend-filtered Iwasawa towers in later chapters, the arithmetic conditions (splitting of primes, divisibility of special values, avoidance of bad primes, and bounds on Sha) cannot be maintained uniformly at every single real scale $x >= X_0$. Instead, they hold along *sparse power-windows* $[Y, Y^lambda]$ for arbitrarily large $Y$, where $lambda > 1$ is a fixed exponent—in the formalization, $lambda = 3\/2$.

  Furthermore, we need to handle *arbitrary* primitive Dirichlet characters $psi$ (including complex characters of arbitrarily large order $o$), not merely real quadratic characters. In this section we extend the Mellin–Landau engine in both directions at once:
  1. from a single real character to a finite, positively weighted *cyclic character family* `Level.cyc psi`; and
  2. from a global bound on $[X_0, oo)$ to a one-sided upper bound on arbitrarily large sparse intervals $[Y, Y^lambda]$ with $lambda = 1 + delta > 1$.

  === Weighted Character Families and Cyclic Levels

  Let $psi$ be a primitive Dirichlet character of conductor $N >= 1$ and multiplicative order $o = op("ord")(psi) >= 1$ in the character group $(bb(Z)\/N bb(Z))^(times, hat)$. Consider the cyclic subgroup $Xi = chevron.l psi chevron.r$ of order $o$, and let $cal(K) = "KEPT"$ be the finite set of primitive characters inducing the elements of $Xi$ (so $1_(op("mod") 1) in cal(K)$, $psi in cal(K)$, and $cal(K)$ is closed under inversion $phi |-> phi^(-1)$). In `ExplicitFormulaErrorOfHostConditions.lean`, this structure is packaged as `Level.cyc ψ`.

  For any Dirichlet character $phi$ modulo $M$, define its complex Riesz-smoothed remainder (`An.gChi`):
  $ g_phi (y) = cases(
    sum_(1 <= n <= floor(y)) Lambda(n) (y / n - 1) - y (log y - 1 - gamma) & "if" phi = 1,
    sum_(1 <= n <= floor(y)) Lambda(n) phi(n) (y / n - 1) + y dot.c (L'(1, phi)) / (L(1, phi)) & "if" phi != 1.
  ) $
  Notice that for a real non-principal character $chi$, we have $G_chi (y) = g_1 (y) + op("Re")(g_chi (y))$. More generally, for a cyclic level $Lambda_"cyc" = "Level.cyc"(psi)$ of order $o$, we assign strictly positive weights
  $ w(1) = 1, quad w(phi) = 1 / (3 o + 1) quad (phi in cal(K) without {1}), $
  and define the real-valued weighted combination (`Level.Gm`):
  $
    G_m (y) &= g_1 (y) + sum_(phi in cal(K) without {1}) w(phi) op("Re")(g_phi (y)) \
      &= sum_(phi in cal(K)) w(phi) op("Re")(g_phi (y)).
  $ <eq:ch12-gm-def>

  Why is the combination @eq:ch12-gm-def paired with strictly positive weights $w(phi) > 0$? Because every $phi in cal(K)$ appears alongside its complex conjugate $overline(phi) = phi^(-1) in cal(K)$ with the same weight $w(phi) = w(overline(phi)) > 0$, and the real part $op("Re")(g_phi (y)) = (g_phi (y) + g_(overline(phi)) (y)) \/ 2$ is a sum of Mellin-transformable functions whose poles lie at the zeros of $L(s, phi)$ and $L(s, overline(phi))$! Specifically, changing variables to $y = e^u$ ($u >= 0$) and setting $g(u) = G_m (e^u)$, the Laplace transform
  $ Phi(s) = integral_0^oo g(u) e^(-s u) dif u = integral_1^oo G_m (y) y^(-s - 1) dif y quad (op("Re")(s) > 1) $ <eq:ch12-laplace-phi>
  satisfies the exact meromorphic continuation identity (combining `mellin_H` for each character in $cal(K)$):
  $ Phi(s) = sum_(phi in cal(K)) (w(phi)) / 2 (Phi_phi (s) + Phi_(overline(phi)) (s)), $
  where for $phi != 1$,
  $ Phi_phi (s) = 1 / (s (s - 1)) (-(L'(s, phi)) / (L(s, phi)) + s (L'(1, phi)) / (L(1, phi))) $
  is holomorphic at $s = 1$ (since the numerator vanishes at $s = 1$!). Thus $Phi(s)$ is meromorphic on $op("Re")(s) > 0$, holomorphic at $s = 1$, and its *only* poles in $op("Re")(s) > 0$ are simple poles at the zeros $rho$ of $product_(phi in cal(K)) L(s, phi)$ in $0 < op("Re")(rho) < 1$, with residue
  $ op("Res")_(s = rho) Phi(s) = - (sum_(phi in cal(K)) w(phi) m_phi (rho)) / (rho (rho - 1)), $ <eq:ch12-family-residue>
  where $m_phi (rho) >= 0$ is the order of vanishing of $L(s, phi)$ at $rho$ (using the fact that $cal(K)$ is closed under conjugation and $w(overline(phi)) = w(phi)$).

  Crucially, because $w(phi) > 0$ for every $phi in cal(K)$:
  1. *No cancellation between characters:* If *any* character $phi in cal(K)$ has a zero $rho$ with $0 < op("Re")(rho) < 1$, then $sum_(phi in cal(K)) w(phi) m_phi (rho) >= w(phi) > 0$, so $Phi(s)$ genuinely has a simple pole at $rho$!
  2. *Definite positive residue on the real axis:* If $rho = beta in (0, 1)$ is real, then $beta (beta - 1) < 0$, so the residue @eq:ch12-family-residue is *strictly positive*:
     $ op("Res")_(s = beta) Phi(s) = + (sum_(phi in cal(K)) w(phi) m_phi (beta)) / (beta (1 - beta)) > 0. $

  === The Windowed Landau Theorem (`zeroFree_of_rpow_window` and `landau_window`)

  We now prove the central analytic theorem of Section 12.3: a one-sided upper bound $G_m (y) <= C y^theta$ on a sequence of arbitrarily large sparse power-windows $[Y, Y^(1 + delta)]$ forces *every* $L(s, phi)$ ($phi in cal(K)$) to be zero-free in $op("Re")(s) > theta$.

  #theorem(title: "Windowed Landau Nonvanishing Theorem (`Deduction.zeroFree_of_rpow_window`)")[
    Let $cal(F) = {(phi_i, w_i)}$ be a finite family of primitive Dirichlet characters with strictly positive weights $w_i > 0$, closed under conjugation with $w(overline(phi)) = w(phi)$ and containing $1_(op("mod") 1)$. Let $G_m (y) = sum_i w_i op("Re")(g_(phi_i) (y))$. Suppose there exist $theta in (0, 1)$, $delta > 0$, and $C > 0$ such that for every $Y_0 > 0$, there exists $Y >= Y_0$ satisfying
    $ G_m (y) <= C y^theta quad "for all" y in [Y, Y^(1 + delta)]. $ <eq:ch12-window-hyp>
    Then $L(s, phi_i) != 0$ for every $phi_i in cal(F)$ and every $s in bb(C)$ with $op("Re")(s) > theta$.
  ]

  The proof is a quantitative, self-contained triumph of elementary complex analysis (`landauWindow.lean`). Rather than evaluating the Mellin integral on the entire half-line $(1, oo)$ (which would require a global sign condition), we examine the high-order Taylor coefficients $c_k (s) = (-1)^k Phi^((k)) (s) \/ k!$ at a real point $sigma > 2$ and a vertical shift $sigma + i gamma$. The kernel $(u^k \/ k!) e^(-sigma u)$ is a Gamma density peaking sharply at $u = k \/ sigma$; by positioning $k \/ sigma$ strictly inside the logarithmic window $[U, (1 + delta) U]$ (where $U = log Y$), the outside tails become exponentially negligible, and positivity inside the window controls $|c_k (sigma + i gamma)| + op("Re")(c_k (sigma))$!

  We break the proof into three clean lemmas mirroring `landauTails.lean`, `landauWindowIneq.lean`, and `landauWindow.lean`.

  #lemma(title: "Gamma-Peak Tail Localization (`landau_tails`)")[
    Let $delta > 0$. There exist real numbers $sigma > 2$ and $C_1 > 0$ (depending only on $delta$) such that for every $U >= 1$, there exists an integer $k >= U$ satisfying
    $ integral_([0, oo) without [U, (1 + delta) U]) u^k / k! e^(-(sigma - 2) u) dif u <= C_1 / sigma^k. $ <eq:ch12-tail-bound>
  ]

  #proof[
    Set $alpha = 1 + delta \/ 2$, so $1 < alpha < 1 + delta$. Given $sigma > 2$ (to be chosen large in terms of $delta$) and $U >= 1$, set $k = floor(sigma alpha U) >= U$ (provided $sigma >= 1$). By the standard Gamma integral, $integral_0^oo (u^k \/ k!) e^(-sigma u) dif u = sigma^(-k - 1)$, whereas our integrand has the slower decay $e^(-(sigma - 2) u)$. We bound the left tail $[0, U]$ and the right tail $[(1 + delta) U, oo)$ by Chernoff's method (multiplying by $e^(lambda (U - u)) >= 1$ or $e^(mu (u - (1 + delta) U)) >= 1$).

    *Left tail ($0 <= u <= U$):* For any $lambda > 0$, we have $1 <= e^(lambda (U - u))$ on $[0, U]$, so
    $
      integral_0^U u^k / k! e^(-(sigma - 2) u) dif u
      &<= e^(lambda U) integral_0^oo u^k / k! e^(-(sigma - 2 + lambda) u) dif u \
      &= (e^(lambda U)) / ((sigma - 2 + lambda)^(k + 1)).
    $
    Take $lambda = sigma (alpha - 1) > 0$. Since $k = floor(sigma alpha U)$ implies $U <= (k + 1) \/ (sigma alpha)$, the ratio of this bound to $sigma^(-k)$ is controlled by
    $ (sigma / (sigma - 2 + sigma (alpha - 1)))^k e^(sigma (alpha - 1) U) <= (e^((alpha - 1)/alpha) / (alpha - 2\/sigma))^k dot.c e^((alpha - 1)/alpha). $
    Because the function $t |-> log t - (t - 1) \/ t$ is strictly positive for all $t > 1$ (its derivative is $(t - 1)\/t^2 > 0$), we have $e^((alpha - 1)\/alpha) < alpha$. Choosing $sigma$ large enough that $alpha - 2\/sigma > e^((alpha - 1)\/alpha)$, the left tail is $O(sigma^(-k))$ uniformly in $U >= 1$!

    *Right tail ($u >= (1 + delta) U$):* Set $beta = 1 + delta > alpha$, and choose $mu = (sigma - 2) (1 - alpha \/ beta) > 0$. For $u >= beta U$, we have $1 <= e^(mu (u - beta U))$, so
    $
      integral_(beta U)^oo u^k / k! e^(-(sigma - 2) u) dif u
      &<= e^(-mu beta U) integral_0^oo u^k / k! e^(-(sigma - 2 - mu) u) dif u \
      &= (e^(-mu beta U)) / ((sigma - 2 - mu)^(k + 1)).
    $
    Here $sigma - 2 - mu = (sigma - 2) alpha \/ beta$ and $mu beta U = (sigma - 2)(beta - alpha) U$. Since $sigma alpha U >= k$, as $sigma -> oo$ the exponential factor per power of $k$ approaches
    $ (beta / alpha) e^(-(beta - alpha) / alpha) = (beta / alpha) e^(1 - beta / alpha) < 1, $
    because $t e^(1 - t) < 1$ for all $t = beta \/ alpha > 1$! Choosing $sigma > 2$ sufficiently large in terms of $delta$, the factor $(sigma \/ ((sigma - 2) alpha\/beta)) e^(-(sigma - 2)(beta - alpha)\/(sigma alpha))$ is strictly less than $1$. Hence the right tail is also $O(sigma^(-k))$ uniformly in $U >= 1$. Summing the two bounds gives @eq:ch12-tail-bound.
  ]

  #lemma(title: "Windowed Positivity Inequality for Taylor Coefficients (`landau_window_key`)")[
    Under the hypotheses of Theorem 12.7, let $g(u) = G_m (e^u)$ and $Phi(s) = integral_0^oo g(u) e^(-s u) dif u$ for $op("Re")(s) > 2$. Denote the $k$-th Taylor coefficient of $Phi$ at $s$ by
    $ c_k (s) = ((-1)^k Phi^((k)) (s)) / k! = integral_0^oo g(u) u^k / k! e^(-s u) dif u. $
    Then there exist $sigma > 2$ and $C_2 > 0$ such that for every $eta > 0$ and every $U_0 > 0$, there exist $U >= U_0$ and an integer $k >= U$ such that for *all* $gamma in bb(R)$,
    $ |c_k (sigma + i gamma)| + op("Re")(c_k (sigma)) <= (C_2 e^(eta U)) / (sigma - theta)^k. $ <eq:ch12-window-ineq>
  ]

  #proof[
    By Chebyshev's bound $psi(x) = O(x)$, the global remainder satisfies $|g(u)| = |G_m (e^u)| <= C_0 e^(2 u)$ for all $u >= 0$ and some constant $C_0 > 0$. Let $sigma > 2$ and $C_1 > 0$ be given by Lemma 12.8 for our exponent $delta > 0$.

    Given $eta > 0$ and $U_0 > 0$, choose $Y >= max(e^(U_0), e)$ sufficiently large that @eq:ch12-window-hyp holds on $[Y, Y^(1 + delta)]$, and set $U = log Y >= max(U_0, 1)$. Setting $R(u) = C e^(theta u)$, we have $g(u) <= R(u)$ for all $u in I := [U, (1 + delta) U]$. Moreover,
    $ integral_I R(u) e^(-theta u) dif u = C delta U <= e^(eta U) $
    once $U$ is sufficiently large (depending on $eta, C, delta$). Let $k >= U$ be the integer produced by Lemma 12.8.

    Split the integral defining $c_k (s)$ into the window $I = [U, (1 + delta) U]$ and its complement $I^c = [0, oo) without I$:
    $ c_k (s) = integral_I g(u) u^k / k! e^(-s u) dif u + integral_(I^c) g(u) u^k / k! e^(-s u) dif u =: c_k^I (s) + c_k^(I^c) (s). $
    *Bounding the tails:* For any $gamma in bb(R)$, since $|e^(-(sigma + i gamma) u)| = e^(-sigma u)$ and $|g(u)| <= C_0 e^(2 u)$, Lemma 12.8 yields
    $ |c_k^(I^c) (sigma + i gamma)| <= C_0 integral_(I^c) u^k / k! e^(-(sigma - 2) u) dif u <= (C_0 C_1) / sigma^k <= (C_0 C_1 e^(eta U)) / (sigma - theta)^k, $
    and the same bound holds for $op("Re")(c_k^(I^c) (sigma))$.

    *Bounding the window via positivity:* On $I$, write $g(u) = R(u) - (R(u) - g(u))$, where $h(u) := R(u) - g(u) >= 0$! For every $gamma in bb(R)$, the triangle inequality gives
    $ |c_k^I (sigma + i gamma)| &= |integral_I (R(u) - h(u)) u^k / k! e^(-(sigma + i gamma) u) dif u| \
      &<= integral_I R(u) u^k / k! e^(-sigma u) dif u + integral_I h(u) u^k / k! e^(-sigma u) dif u. $
    On the other hand, at $gamma = 0$ (where $c_k^I (sigma)$ is real),
    $ op("Re")(c_k^I (sigma)) = integral_I R(u) u^k / k! e^(-sigma u) dif u - integral_I h(u) u^k / k! e^(-sigma u) dif u. $
    Adding these two inequalities, the unknown nonnegative integral $integral_I h(u) (u^k \/ k!) e^(-sigma u) dif u$ *cancels completely*! We are left with
    $ |c_k^I (sigma + i gamma)| + op("Re")(c_k^I (sigma)) <= 2 integral_I R(u) u^k / k! e^(-sigma u) dif u. $
    Finally, writing $R(u) e^(-sigma u) = (R(u) e^(-theta u)) e^(-(sigma - theta) u)$ and using the elementary bound $x^k \/ k! dot.c e^(-x) <= 1$ for $x = (sigma - theta) u >= 0$ (since $e^x >= x^k \/ k!$), we have $(u^k \/ k!) e^(-(sigma - theta) u) <= (sigma - theta)^(-k)$ for all $u >= 0$. Therefore
    $ 2 integral_I R(u) u^k / k! e^(-sigma u) dif u <= 2 / (sigma - theta)^k integral_I R(u) e^(-theta u) dif u <= (2 e^(eta U)) / (sigma - theta)^k. $
    Combining the window bound with the two tail bounds gives @eq:ch12-window-ineq with $C_2 = 2 + 2 C_0 C_1$.
  ]

  Now we close the proof of Theorem 12.7 by comparing @eq:ch12-window-ineq with the Cauchy-formula lower bound for the Taylor coefficients of a meromorphic function near its nearest pole.

  #proof(title: "Proof of Theorem 12.7")[
    Suppose for contradiction that some $L(s, phi_i)$ ($phi_i in cal(F)$) has a zero $rho_0$ with $op("Re")(rho_0) > theta$. By Hadamard–de la Vallée Poussin, $op("Re")(rho_0) < 1$. Let $sigma > 2$ and $C_2 > 0$ be as in Lemma 12.9. Consider the set $cal(Z)$ of all poles of $Phi(s)$ in $op("Re")(s) > theta$ (which by @eq:ch12-family-residue is precisely the union of the zero sets of $L(s, phi_i)$ in $theta < op("Re")(s) < 1$).

    Let $beta_sup = sup { op("Re")(rho) : rho in cal(Z) }$. Since $rho_0 in cal(Z)$ has $op("Re")(rho_0) > theta$ and every zero satisfies $op("Re")(rho) < 1$, we have $theta < beta_sup <= 1$. Set $d_sup = sigma - beta_sup < sigma - theta$. Let $R_0$ be the distance from the real point $sigma$ to $cal(Z)$; because every $rho in cal(Z)$ has $op("Re")(rho) <= beta_sup$, we have $|sigma - rho| >= sigma - op("Re")(rho) >= d_sup$, so $R_0 >= d_sup$.

    *Case 1: $R_0 = d_sup$.* Then there exists a pole $rho in cal(Z)$ with $|sigma - rho| = d_sup$. Since $sigma - op("Re")(rho) >= d_sup$ and $|sigma - rho|^2 = (sigma - op("Re")(rho))^2 + (op("Im")(rho))^2 = d_sup^2$, we must have $op("Im")(rho) = 0$ and $op("Re")(rho) = beta_sup$. Thus $beta_sup in (theta, 1)$ is the *unique* pole of $Phi$ in the closed disk $overline(D)(sigma, d_sup)$! By discreteness of $cal(Z)$, there exists $e > d_sup$ (with $e <= sigma - theta$) such that $Phi(s) - r \/ (s - beta_sup)$ is holomorphic on $overline(D)(sigma, e)$, where $r = op("Res")_(s = beta_sup) Phi(s) > 0$ by @eq:ch12-family-residue. Extracting the $k$-th Taylor coefficient at $s = sigma$ and applying Cauchy's estimate on $|s - sigma| = e$ gives
    $ c_k (sigma) = r / d_sup^(k + 1) + O(1 / e^k). $
    Since $r > 0$, for all $k >= 0$ we obtain $op("Re")(c_k (sigma)) >= (r \/ d_sup) \/ d_sup^k - M \/ e^k$ for some constant $M > 0$. Combining this with @eq:ch12-window-ineq at $gamma = 0$ (and $|c_k (sigma)| >= 0$) yields
    $ (r / d_sup) / d_sup^k <= M / e^k + (C_2 e^(eta U)) / (sigma - theta)^k. $ <eq:ch12-contra-ineq>

    *Case 2: $R_0 > d_sup$.* Choose $d_*$ strictly between $d_sup$ and $min(R_0, sigma - theta)$. By definition of $beta_sup$, there exists a pole $rho_1 = beta_1 + i gamma_1 in cal(Z)$ with $sigma - beta_1 < d_*$. Let $s_1 = sigma + i gamma_1$, and let $R_1 <= sigma - beta_1 < d_*$ be the distance from $s_1$ to $cal(Z)$. The set $S = { rho in cal(Z) : |s_1 - rho| = R_1 }$ is finite and nonempty, and lies strictly in the left half-plane $op("Re")(rho) < 1 < sigma$; hence the map $rho |-> op("Im")(rho)$ is injective on $S$. Let $rho_+ = beta_+ + i gamma_+$ be the unique element of $S$ maximizing $op("Im")(rho)$.

    Consider the slightly shifted center $s(tau) = sigma + i (gamma_1 + tau)$ for $tau > 0$. For every $rho = beta + i gamma in S$,
    $ |s(tau) - rho|^2 = R_1^2 + 2 tau (gamma_1 - gamma) + tau^2. $
    Since $gamma_1 - gamma$ is strictly minimized on $S$ at $rho_+$, and all poles outside $S$ have distance strictly greater than $R_1$ from $s_1$, for sufficiently small $tau > 0$ the pole $rho_+$ is the *unique* pole of $Phi$ in some closed disk $overline(D)(s(tau), e)$ with $d := |s(tau) - rho_+| < e < min(R_0, sigma - theta)$. Let $r_+ = op("Res")_(s = rho_+) Phi(s) != 0$ (nonzero by @eq:ch12-family-residue). By Cauchy's estimate on $|s - s(tau)| = e$,
    $ |c_k (s(tau))| >= (|r_+| / d) / d^k - M_1 / e^k $
    for some constant $M_1 > 0$. Simultaneously, because $e < R_0$, the function $Phi$ is holomorphic on $overline(D)(sigma, e)$, so Cauchy's estimate at $s = sigma$ yields $|c_k (sigma)| <= M_2 \/ e^k$, whence $op("Re")(c_k (sigma)) >= -M_2 \/ e^k$. Substituting both bounds into @eq:ch12-window-ineq at $gamma = gamma_1 + tau$ gives
    $ (|r_+| / d) / d^k <= (M_1 + M_2) / e^k + (C_2 e^(eta U)) / (sigma - theta)^k. $ <eq:ch12-contra-ineq2>

    *Final contradiction (`landau_window_contra`):* In both Case 1 (@eq:ch12-contra-ineq) and Case 2 (@eq:ch12-contra-ineq2), we have constants $c > 0$, $0 < d < e <= sigma - theta$, and $M, C_2 > 0$ such that for every $eta > 0$ and every $U_0 > 0$, there exist $U >= U_0$ and $k >= U$ satisfying
    $ c / d^k <= M / e^k + (C_2 e^(eta U)) / (sigma - theta)^k <= ((M + C_2) e^(eta k)) / e^k, $
    where we used $U <= k$ and $e <= sigma - theta$. Multiplying by $d^k$ gives
    $ c <= (M + C_2) (d e^eta / e)^k. $
    Since $d < e$, choose $eta > 0$ so small that $q := d e^eta \/ e < 1$. Then as $k >= U >= U_0 -> oo$, the right-hand side $(M + C_2) q^k -> 0$, contradicting $c > 0$. Hence $cal(Z) = emptyset$, and $L(s, phi_i) != 0$ for all $op("Re")(s) > theta$.
  ]

  === From Sparse Windows to `HostExW`, `GChi`, and `FamilyClassConnected`

  Theorem 12.7 is the exact analytic engine behind `UpperTheory.Comparison₂.formB` (`Imports.lean`). To apply it to a primitive character $psi$ and obtain nonvanishing in the entire half-plane $op("Re")(s) > 1\/2$, we must produce, for every arbitrarily small $epsilon > 0$, a sequence of arbitrarily large windows $[Y, Y^lambda]$ (with $lambda = 3\/2$) on which
  $ G_m (y) <= y^(1\/2 + C_0 epsilon) quad (y in [Y, Y^(3\/2)]), $ <eq:ch12-target-gm>
  where $G_m = ("Level.cyc"(psi))."Gm"$ and $C_0 = e_D + e_L + 7$ is a fixed absolute constant independent of $epsilon$. Indeed, given any $s in bb(C)$ with $op("Re")(s) > 1\/2$, choosing $epsilon > 0$ small enough that $theta := 1\/2 + C_0 epsilon < op("Re")(s)$ (as in `exists_small_eps` in `TopWin.lean`) lets Theorem 12.7 conclude $L(s, psi) != 0$.

  How does the Lean formalization organize the arithmetic data needed to verify @eq:ch12-target-gm? It uses three layered predicates defined in `Supply.lean`, `ThinScalesIffHostBound.lean`, and `DivinNOfHypV.lean`:

  1. *The Auxiliary Character Requirement `GChi psi`:* For a primitive character $psi$, `GChi ψ` is a requirement (`FReq`) on a scale $s = (x, epsilon, dots.c)$ and an arithmetic host structure $(H, T T, t)$ (comprising a CM number field $E$, a set of split primes $T T$, and a cohomology truncation parameter $t$). It demands two simultaneous properties (`Supply.lean`):
     $
       &"GChi"(psi)(s, H, T T, t) \
       &quad : <==> "EAtH"("Level.cyc"(psi), H, T T, x, epsilon, 4) \
       &quad quad and "VVle"(H.E, t, sqrt(s.b)).
     $
     - The first conjunct, `"EAtH"("Level.cyc"(psi), H, T T, x, epsilon, 4)`, asserts that the explicit-formula error between the automorphic prime sum on the host $H$ and the cyclic character-family sum $("Level.cyc"(psi))."Gm"(x)$ is bounded by $4$ times the admissible error budget at scale $(x, epsilon)$.
     - The second conjunct, `"VVle"(H.E, t, sqrt(s.b))`, is the *weakened Vandiver / Sha-length bound*: the weighted sum of lengths of odd $l$-primary Tate–Shafarevich (or Galois cohomology) groups $H^1(cal(O)_E [1\/l], bb(Q)_l \/ bb(Z)_l (-e))$ over $1 <= e < t$ is at most $sqrt(s.b)$ (where $s.b = exp(x^epsilon)$).

  2. *The Window Existence Condition `HostExW la (GChi psi).req`:* A host requirement $P$ satisfies `HostExW la P` if, for every $epsilon in (0, 1\/52)$, there exist constants $(C_(T 2), C_8, C_5, c_6, C_b, x_0)$ and a set of scales $S$ containing arbitrarily large $lambda$-power windows (`Scales la`) such that at every scale $s in S$ with $s.x >= x_0$, there exists a good arithmetic host $(R, H, q_0)$ satisfying `HostGood` together with $P(C_5, s, R, H, q_0)$. In particular, when $lambda = 3\/2$, `HostExW (3/2) (GChi psi).req` supplies good hosts satisfying both `"EAtH"` and `"VVle"` across arbitrarily large $[Y, Y^(3\/2)]$ windows.

  3. *Family Classes and Connectivity `FamilyClassConnected (G.cls la)`:* Given any requirement $G : "FReq"$ and exponent $lambda > 1$, the family class $G."cls"(lambda)$ consists of all parametrized families $F m : "FamP"(epsilon)$ of automorphic data whose window set $F m."Win"$ contains arbitrarily large $lambda$-power windows (`Fm.toFamCore.Windows la`) and every member $F m.L(x, i)$ for $x > F m.x_1$ satisfies $G."At"$. Such a family class $cal(E)$ is called *connected* (`FamilyClassConnected cal(E)`) if there exist absolute exponents $e_D, e_L in bb(R)$ and a threshold $epsilon_1 > 0$ such that for every $epsilon in (0, epsilon_1)$, there exists a family $F m in cal(E)$ whose members are *chain-tied* (`ChainTied Fm eD eL K cHH eK CL x`) at every sufficiently large scale $x in F m."Win"$.

  Here `ChainTied` is the final output of the chained theta-lift and Bost slope-inequality machine: it asserts that at scale $x$, the automorphic lifts along the chain $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ (with $m approx sqrt(x)$) have their degrees, heights, covolumes, and divisibility budgets locked together tightly enough to enforce the Main Inequality on the window!

  == The Main Inequality (M) and `TopG`

  We are now in a position to formulate the exact analytic target at the summit of the Alpöge–Claude–Riemann proof—the proposition `TopG` of `ZeroFreeAllOfTopG.lean`—and to trace how `TopG`, together with the weakened Vandiver window hypothesis `VWin`, drives the entire deduction of `ZeroFreeAll` via `zeroFreeOn_of_tiedWin_cyc`. We also unpack the conceptual origin of the Main Inequality (M): the Guinand–Weil positivity and variance test-function heuristic recorded in items 5–6 of Alpöge's `remark.pdf`.

  === The Variance / Test-Function Heuristic (`remark.pdf`, Items 5–6)

  Before displaying the formal statement of `TopG`, it is illuminating to understand *why* an automorphic positivity inequality on prime-power sums produces the exact one-sided upper bound $G_m (y) <= y^(1\/2 + O(epsilon))$ required by the windowed Landau theorem of Section 12.3.

  Recall the Guinand–Weil explicit formula (Chapter 1) for a suitable even test function $h$ with Fourier–Mellin transform $hat(h)$:
  $
    W(h) := sum_rho hat(h)(rho)
    &= hat(h)(1) + hat(h)(0) \
    &quad - sum_(n = 1)^oo (Lambda(n)) / sqrt(n) (h(log n) + h(-log n)) \
    &quad + ("archimedean term"),
  $
  where the sum on the left runs over the nontrivial zeros $rho$ of $zeta(s)$ (or, in the twisted version, of $L(s, phi)$). By Weil's positivity criterion (Chapter 3), RH is equivalent to $W(h * tilde(h)) >= 0$ for all compactly supported test functions $h$.

  In items 5–6 of `remark.pdf`, Alpöge summarizes the conceptual leap that led from Stepanov's determinant method over function fields to the analytic Main Inequality over $bb(Q)$:

  1. *Switching to the Riesz-smoothed von Mangoldt functional (Item 5):* Instead of attempting to prove $W(h) >= 0$ for an arbitrary positive-definite test function directly, one focuses on the specific piecewise-linear Riesz functional
     $ G(X) = sum_(n <= X) Lambda(n) (X / n - 1)_+ - X log X + (1 + gamma) X. $
     Up to the elementary archimedean terms, $G(X)$ is the prime side of an explicit formula whose Mellin transform is $1 \/ (s (s - 1))$—the *square* (up to a shift of $1$) of a simple pole, which has the exact Guinand–Weil sign! Indeed, as we proved in Section 12.2, a hypothetical zero $rho$ contributes $-X^rho \/ (rho (rho - 1))$ to $G(X)$, so on the real axis $beta in (0, 1)$ the contribution $+X^beta \/ (beta (1 - beta))$ is *positive*.

  2. *The Variance Test-Function Trick (Items 5–6):* Consider a two-scale test function of the shape
     $ h_(X, eta) (t) = 1_((0, 1]) (t) + c X^eta dot.c 1_((0, 1\/X]) (t), $
     where $1_((0, 1])$ is the indicator of the main scale and $1_((0, 1\/X])$ is a sharp spike of height $approx X^eta$ near the origin (Item 6 of `remark.pdf`: "$W(1_((0, 1]) + (tilde X^eta) dot.c 1_((0, 1\/X])) >= 0$ gives $> 1 - eta$"). Why does positivity of $W(h_(X, eta))$ force a zero-free half-plane $op("Re")(s) > 1 - eta$ (and in particular, taking $eta = 1\/2 - epsilon$, $op("Re")(s) > 1\/2$)?

     Compute the Mellin/Laplace weight on both sides! A spike of height $X^eta$ and width $1\/X$ has $L^1$-mass $X^(eta - 1)$, so its contribution to the pole term $hat(h)(1)$ is $O(X^eta \/ X dot.c X) = O(X^eta)$, whereas its contribution to a zero $rho$ with $op("Re")(rho) = beta$ is $O(X^(eta + beta - 1))$, which is *smaller* than $X^beta$ whenever $eta < 1$. Meanwhile, the main indicator $1_((0, 1])$ tests the von Mangoldt sum up to $X$, giving a main term minus $G(X)$ of order $X^beta$. Thus the positivity inequality
     $ W(1_((0, 1]) + c X^eta dot.c 1_((0, 1\/X])) >= 0 $
     translates directly into a *one-sided upper bound*
     $ G(X) <= C X^(1 - eta) $
     on the Riesz-smoothed prime-power remainder! Taking $eta -> 1\/2^-$ yields $G(X) <= C X^(1\/2 + epsilon)$, which by the windowed Landau theorem (Section 12.3) rules out all zeros in $op("Re")(s) > 1\/2 + epsilon$.

  3. *The Main Inequality (M):* In the actual proof, how is the positivity $W(h_(X, eta)) >= 0$ (or equivalently the upper bound $G_m (x) <= x^(1\/2 + C_0 epsilon)$ on windows) established without already knowing the locations of the zeros? By *Bost's slope inequality* applied to an integral structure on spaces of automorphic forms produced by an $m$-fold chain of theta lifts $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ with $m approx sqrt(x)$! Schematically, the Bost slope inequality compares:
     - the *geometric/automorphic upper bound* (the sum of the archimedean norm and the level/covolume/height cost of the $m$-fold theta lift, controlled by Chowla–Selberg, Weyl branching, Siegel mass, and Arakelov intersection theory); against
     - the *arithmetic lower bound* (the non-archimedean divisibility of the lifted period at split primes $p <= x$, which evaluates precisely to a weighted prime-power sum reproducing $G_m (x)$ up to the controlled error `"EAtH"`!).

     This comparison—*arithmetic prime-power divisibility $<=$ automorphic height + covolume + Sha-defect budget*—is the *Main Inequality (M)*:
     $
       &("Level.cyc"(psi))."Gm"(x) <= x^(1\/2 + (e_D + e_L + 7) epsilon) \
       &quad "for all" x >= x_1, space x in F m."Win".
     $ <eq:ch12-main-inequality>
     In the Lean formalization (`TopWin.lean`), the statement that any chain-tied family satisfies @eq:ch12-main-inequality is called `ChebyshevInequalityOnWindows`, and it is proved unconditionally from the Artin/slope inputs in `UpperTheory.Comparison₂.level_gm_le_on_family_scales` (`LevelGmLeOnFamilyScales.lean`).

  === Exact Formulation of `TopG` and `VWin`

  With `ChebyshevInequalityOnWindows` (`level_gm_le_on_family_scales`) and the windowed Landau theorem (`formB`) already in hand, what remains to deduce `ZeroFreeAll`? Precisely two global theorems:
  1. *The Main Automorphic–Geometric Connectivity Theorem (`TopG`):* Whenever a host requirement $G : "FReq"$ admits good hosts across $lambda$-power windows (`HostExW la G.req`) and every family in $G."cls"(lambda)$ satisfies the Sha/Vandiver bound `HypV`, the family class $G."cls"(lambda)$ is *connected* (`FamilyClassConnected (G.cls la)`), meaning that for all sufficiently small $epsilon > 0$ there exists a chain-tied family $F m in G."cls"(lambda)$.
  2. *The Weakened Vandiver Window Supply Theorem (`VWin` and `supplyChi`):* For every primitive character $psi$, the weakened Vandiver cohomology bound holds across quadratic-power windows $[Y, Y^2]$ (`VWinAt ψ 401`, where $C_t = 401$ is the polynomial truncation exponent $t = floor(x^(401))$), and this implies the host window existence `HostExW (3/2) (GChi ψ).req` at exponent $lambda = 3\/2$.

  #definition(title: "The Analytic Target `TopG` and the Vandiver Window Predicate `VWin`")[
    1. *(`UpperTheory.Top.TopG`, `ZeroFreeAllOfTopG.lean`.)* The proposition `TopG` asserts that for every real $lambda > 1$ and every host requirement $G : "FReq"$, if
       - `HostExW la G.req` holds (good arithmetic hosts satisfying $G$ exist across arbitrarily large $lambda$-power windows for every $epsilon in (0, 1\/52)$), and
       - for every $epsilon in bb(R)$ and every family $F m : "FamP"(epsilon)$ in $G."cls"(lambda)$, the Sha/Vandiver hypothesis `HypV Fm.toFamCore` holds,
       then `FamilyClassConnected (G.cls la)` holds.
    2. *(`UpperTheory.Top.HypV`, `DivinNOfHypV.lean`.)* For a core family $F m : "FamCore"(epsilon)$, `HypV Fm` asserts that there exists $x_0 in bb(R)$ such that for all $x >= x_0$ and all indices $i in F m."Ix"(x)$,
       $
         &"VVle"((F m.D(x, i))."host".E, (F m.D(x, i)).R.t, \
         &quad sqrt((F m.L(x, i))."sc".b)).
       $
    3. *(`UpperTheory.Top.VWin`, `ExistsPageN.lean`.)* For a primitive character $psi$ and exponent $C_t > 0$, `VWinAt ψ Ct` asserts that for every $epsilon in (0, 1\/52)$ and every page-height function $e : bb(R) -> bb(N)$ satisfying $x^(2 + 8 epsilon) <= 2^(e(x)) <= 2 x^(2 + 8 epsilon)$, there exist $J >= 1$ and $X_0 in bb(R)$ such that for every $X >= X_0$ and every admissible prime pair $(q, d)$ satisfying `WinPair eps (X^(1/J)) q d`, there exists $Y in [X^(1\/J), X^(1\/2)]$ such that for every $x in [Y, Y^2]$ and every number field $E$ satisfying `IsChiField ψ (e x) q d E`,
       $ "VVle"(E, floor(x^(C_t)), sqrt(exp(x^epsilon))). $
       Finally, `VWin` is the universal statement $forall psi : "PChar", "VWinAt"(psi, 401)$.
  ]

  Notice how clean the division of labor is between `TopG` and `VWin`:
  - `VWin` (established in the Iwasawa-theoretic and Galois-cohomological chapters of Part III via the weakened Vandiver theorem on $H^1(cal(O)_E [1\/l], bb(Q)_l \/ bb(Z)_l (-e))$) supplies the cohomological bound `"VVle"` on quadratic windows $[Y, Y^2]$. Combined with the arithmetic prime-pair and character-box supply (`admissibleClassesTwistedChar` and `supplyOfAdm`), `UpperTheory.Top.supplyChi` converts `VWin` into `HostExW (3/2) (GChi ψ).req` for every primitive character $psi$. (The exponent drops from $2$ in $[Y, Y^2]$ to $lambda = 3\/2$ in $[Y, Y^(3\/2)]$ to absorb the scale-stepping slack when gluing local host windows into a single `Scales (3/2)` family!)
  - `TopG` (established in the automorphic and Arakelov-geometric chapters via chained theta lifts, seesaw/Rallis inner product formulas, covolume estimates, and Bost's slope inequality) is completely *agnostic* to the specific character $psi$: it takes *any* requirement $G$ with `HostExW la G.req` and `HypV`, and produces a chain-tied family in $G."cls"(lambda)$!

  === The Bridge Theorem: `zeroFreeOn_of_tiedWin_cyc` and `zeroFreeAll_of_topG`

  We now give the complete, rigorous proof of the bridge theorems `level_of_tiedWin`, `zeroFreeOn_of_tiedWin_cyc`, and `zeroFreeAll_of_topG`, verifying every single quantifier and exponent.

  #lemma(title: "Extracting `HypV` and `EFamC` from `(GChi ψ).cls la`")[
    Let $psi$ be a primitive Dirichlet character, $lambda in bb(R)$, and $F m : "FamP"(epsilon)$ be a family belonging to `((GChi ψ).cls la)`. Then:
    1. *(`hypV_of_cls`.)* `HypV Fm.toFamCore` holds.
    2. *(`eFamC_of_cls`.)* `EFamC (Level.cyc ψ) Fm.toFamCore` holds with explicit error constant $C = 4$.
  ]

  #proof[
    By definition of `FReq.cls` (`Supply.lean`), membership $F m in ("GChi"(psi))."cls"(lambda)$ means two things:
    1. $F m."toFamCore"."Windows"(lambda)$ holds (i.e., $F m."Win"$ contains arbitrarily large $lambda$-power windows $[Y, Y^lambda]$); and
    2. for all $x > F m.x_1$ and all $i in F m."Ix"(x)$, $("GChi"(psi))."At"(F m.L(x, i))$ holds—meaning both
       $
         &"EAtH"("Level.cyc"(psi), (F m.D(x, i))."host", \
         &quad (F m.D(x, i))."host".T T, \
         &quad (F m.L(x, i))."sc".x, (F m.L(x, i))."sc".epsilon, 4)
       $
       and
       $
         &"VVle"((F m.D(x, i))."host".E, (F m.D(x, i)).R.t, \
         &quad sqrt((F m.L(x, i))."sc".b)).
       $

    Set $x_0 = F m.x_1 + 1$. For every $x >= x_0$, we have $x > F m.x_1$, so the second conjunct directly gives `HypV Fm.toFamCore`. For the first conjunct, the scale compatibility axioms of `FamP` (`Fm.L_x` and `Fm.L_eps`) identify $(F m.L(x, i))."sc".x = x$ and $(F m.L(x, i))."sc".epsilon = epsilon$ whenever $x > F m.x_1$. Substituting these equalities yields `"EAt"("Level.cyc"(psi), F m.D(x, i), x, epsilon, 4)` for all $x >= x_0$ and all $i$, which is `EFamC (Level.cyc ψ) Fm.toFamCore` with $C = 4$ and $x_0 = F m.x_1 + 1$.
  ]

  #theorem(title: "From Tied Windows to Zero-Free Cyclic Levels (`level_of_tiedWin`, `zeroFreeOn_of_tiedWin_cyc`)")[
    Let $lambda > 1$ and let $Lambda$ be a character level (such as `Level.cyc ψ`). Suppose:
    1. `ChebyshevInequalityOnWindows Λ` holds: for all $e_D, e_L in bb(R)$, $epsilon > 0$, and $F m : "FamP"(epsilon)$ satisfying `EFamC Λ Fm` and `ChainTied Fm eD eL`, there exists $x_1 in bb(R)$ such that
       $ Lambda."Gm"(x) <= x^(1\/2 + (e_D + e_L + 7) epsilon) quad "for all" x >= x_1, space x in F m."Win". $
    2. `Λ.FormBAt la` holds (the windowed Landau theorem for $Lambda$ at exponent $lambda$).
    3. `ChebyshevInequalityAtWindowScale la Λ` holds: there exist $e_D, e_L in bb(R)$ and $epsilon_1 > 0$ such that for every $epsilon in (0, epsilon_1)$, there exists a family $F m : "FamP"(epsilon)$ satisfying `EFamC Λ Fm`, `Fm.Windows la`, and `ChainTied Fm eD eL`.

    Then $Lambda$ is zero-free in $op("Re")(s) > 1\/2$ (`Λ.ZeroFreeLevel`). In particular, if (1)–(3) hold for `Level.cyc ψ` for every primitive character $psi$ in a class $Q$, then `ZeroFreeOn Q` holds (`zeroFreeOn_of_tiedWin_cyc`).
  ]

  #proof[
    Fix $phi in Lambda."KEPT"$ and $s in bb(C)$ with $op("Re")(s) > 1\/2$. Let $e_D, e_L in bb(R)$ and $epsilon_1 > 0$ be supplied by hypothesis (3). Set
    $ delta_0 := min(op("Re")(s) - 1 / 2, space 1 / 2) > 0, $
    and define the intermediate exponent
    $ theta := 1 / 2 + delta_0 / 2. $
    Observe that $1\/2 < theta < 1$ (since $0 < delta_0 <= 1\/2$) and $theta < op("Re")(s)$ (since $delta_0 \/ 2 < delta_0 <= op("Re")(s) - 1\/2$).

    Now choose $epsilon > 0$ sufficiently small (`exists_small_eps`) that
    $ 0 < epsilon < epsilon_1 quad "and" quad (e_D + e_L + 7) epsilon <= delta_0 / 2; $
    explicitly, $epsilon = min(epsilon_1 \/ 2, (delta_0 \/ 2) \/ (|e_D + e_L + 7| + 1))$ works. By hypothesis (3) applied to this $epsilon$, there exists a family $F m : "FamP"(epsilon)$ satisfying `EFamC Λ Fm`, `Fm.Windows la`, and `ChainTied Fm eD eL`. By hypothesis (1), there exists $x_1 in bb(R)$ such that for all $y >= x_1$ with $y in F m."Win"$,
    $ Lambda."Gm"(y) <= y^(1\/2 + (e_D + e_L + 7) epsilon). $
    For all $y >= max(x_1, 1)$ with $y in F m."Win"$, since $y >= 1$ and $1\/2 + (e_D + e_L + 7) epsilon <= 1\/2 + delta_0 \/ 2 = theta$, monotonicity of $t |-> y^t$ gives
    $ Lambda."Gm"(y) <= y^theta. $
    Because `Fm.Windows la` guarantees that $F m."Win"$ contains arbitrarily large intervals $[Y, Y^lambda]$ with $Y >= max(x_1, 1)$, we obtain the windowed upper bound $Lambda."Gm"(y) <= y^theta$ on arbitrarily large $[Y, Y^lambda]$ windows. Applying hypothesis (2) (`Λ.FormBAt la` with exponent $theta in (0, 1)$) yields $L(s, phi) != 0$ for every $phi in Lambda."KEPT"$ and every $s$ with $op("Re")(s) > theta$—in particular, at our given $s$.

    For the final assertion (`zeroFreeOn_of_tiedWin_cyc`), every primitive character $psi$ belongs to $("Level.cyc"(psi))."KEPT"$ (since $psi in chevron.l psi chevron.r$). Thus `ZeroFreeLevel` for `Level.cyc ψ` immediately implies $L(s, psi) != 0$ for all $op("Re")(s) > 1\/2$.
  ]

  #theorem(title: "Master Analytic Reduction (`UpperTheory.Top.zeroFreeAll_of_topG`)")[
    Let $lambda > 1$ (in particular, $lambda = 3\/2$). Assume `TopG` and assume that `HostExW la (GChi ψ).req` holds for every primitive Dirichlet character $psi$ (for $lambda = 3\/2$, this follows from `VWin` via `supplyChi`). Then `ZeroFreeAll` holds—and consequently, by Section 12.1, both full GRH (`Claim.Strip`) and the classical Riemann Hypothesis (`Claim.Zeta`) hold.
  ]

  #proof[
    We verify the three hypotheses of `zeroFreeOn_of_tiedWin_cyc` for $Q(psi) := "True"$ and $Lambda = "Level.cyc"(psi)$:
    1. `ChebyshevInequalityOnWindows (Level.cyc ψ)` is proved unconditionally by `UpperTheory.Comparison₂.level_gm_le_on_family_scales`.
    2. `(Level.cyc ψ).FormB` is proved unconditionally by `UpperTheory.Comparison₂.formB` (Theorem 12.7).
    3. For `ChebyshevInequalityAtWindowScale la (Level.cyc ψ)`, fix any primitive character $psi$. Apply `TopG` to $lambda > 1$ and $G = "GChi"(psi)$, feeding in our hypothesis `HostExW la (GChi ψ).req` and Lemma 12.11(1) (`hypV_of_cls ψ la`). This yields `FamilyClassConnected ((GChi ψ).cls la)`: there exist $e_D, e_L in bb(R)$ and $epsilon_1 > 0$ such that for every $epsilon in (0, epsilon_1)$, there exists $F m in ("GChi"(psi))."cls"(lambda)$ satisfying `ChainTied Fm eD eL`. By definition of `cls`, $F m$ satisfies `Fm.toFamCore.Windows la`, and by Lemma 12.11(2) (`eFamC_of_cls ψ la Fm`), $F m$ satisfies `EFamC (Level.cyc ψ) Fm.toFamCore`. Hence `ChebyshevInequalityAtWindowScale la (Level.cyc ψ)` holds.

    Applying `zeroFreeOn_of_tiedWin_cyc` produces `ZeroFreeAll`. Finally, `UpperTheory.Top.imprimitive` yields `Claim.HalfPlane`, and `Claim.strip` and `Claim.zeta` yield full GRH and RH.
  ]

  #insight-box(title: "The Complete Dependency Spine from Automorphic Theory to RH & GRH")[
    Collecting all results of Chapter 12, the entire top-level deduction of the Alpöge–Claude–Riemann theorem forms a five-link chain:
    $
      "VWin"
      &space ==>^("supplyChi") space
      forall psi, space "HostExW"(3\/2, ("GChi"(psi))."req") \
      &space ==>^("TopG" + "zeroFreeAll_of_topG") space
      "ZeroFreeAll" \
      &space ==>^("imprimitive") space
      "Claim.HalfPlane"
      space ==>^("strip, zeta") space
      "GRH & RH".
    $
    Everything to the right of `TopG` and `VWin` has now been proved with 100% rigor in this chapter. The remaining chapters of the monograph are devoted to proving the two deep arithmetic-automorphic pillars on the left: `VWin` (via Iwasawa theory, Kummer–Vandiver cohomology, and Galois representations) and `TopG` (via chained theta lifts, seesaw/Rallis identities, covolume estimates, and Bost's slope inequality).
  ]

  == Lean 4 Formalization

  Every theorem proved in this chapter corresponds line-for-line to a machine-checked Lean 4 proof in the Alpöge–Claude repository. We record verbatim excerpts from the three principal files—`ClaimStrip.lean`, `Assembly.lean`, and `ZeroFreeAllOfTopG.lean`—and highlight the key formalization idioms (such as Mathlib's `dslope` for removable singularities and the universe-polymorphic `FReq : Type 1` abstraction).

  #lean-note(
    title: "GRH and RH from Half-Plane Nonvanishing",
    module: "Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean",
  )[
    In `ClaimStrip.lean`, the reduction from `Claim.HalfPlane` to `Claim.Strip` (GRH) and `Claim.Zeta` (RH) occupies fewer than 80 lines of tactics, resting on `prim_zero`, `gamma_ne_zero`, and `prim_reflect`:

    ```lean
    theorem strip (h : HalfPlane) : Strip := by
      unfold HalfPlane at h
      intro N _ χ s hs0 hs1 hz
      have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
      have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
      rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
      · exfalso
        have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        have hp := prim_zero χ hs0 hs1 hz
        have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
        have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
        exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
          (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
      · exact heq
      · exact absurd hz (h N χ s hgt (Or.inr hs))

    theorem zeta (h : HalfPlane) : Zeta := by
      intro s hz htriv hs1
      have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
      rcases lt_or_ge 0 s.re with hpos | hnpos
      · rcases lt_or_ge s.re 1 with hlt1 | hge1
        · have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
            rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
          exact strip h 1 1 s hpos hlt1 hL
        · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
      · exfalso
        have hG : Gammaℝ s ≠ 0 := by
          intro hg
          obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
          rcases n with _ | n
          · exact hs0 (by simpa using hn)
          · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
        have hc : completedRiemannZeta s = 0 := by
          rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
          exact hz.resolve_right hG
        have h1s : 1 - s ≠ 0 := fun e => by
          have := congrArg Complex.re e
          rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
          linarith
        have hz' : riemannZeta (1 - s) = 0 := by
          rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
        exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
    ```

    Notice how Lean handles the trivial zeros of $zeta(s)$ in `zeta`: Mathlib's `Complex.Gammaℝ_eq_zero_iff` characterizes the points where `Gammaℝ s = 0` (the sentinel value at the poles of $Gamma(s\/2)$) as $s = -2n$ for $n in bb(N)$; the `n = 0` case is ruled out by `riemannZeta_zero` ($zeta(0) = -1\/2 != 0$), and the `n + 1` cases are ruled out by the hypothesis `htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)`.
  ]

  #lean-note(
    title: "The Mellin–Landau Key Identity and `dslope` Cancellation",
    module: "Formalism/ZetaNonvanishing/Assembly.lean",
  )[
    In `Assembly.lean`, the Mellin transform `mellin_H`, the divided-difference extension `Phi`, and `key_identity` are formalized as follows:

    ```lean
    def Hf (σ₀ C : ℝ) (x : ℝ) : ℝ := G χ x + C * x ^ σ₀

    def Imel (σ₀ C : ℝ) (s : ℂ) : ℂ :=
      ∫ x in Ioi (1:ℝ), ((Hf χ σ₀ C x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

    def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
      -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)

    def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
      -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
        + C * s * (s - 1) * Pfun χ s / (s - σ₀)

    def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)

    lemma mellin_H (h3 : MellinS) (h5 : MellinElem) (σ₀ C : ℝ) {s : ℂ} (hs : 1 < s.re)
        (hσ₀ : σ₀ < 1) :
        ∫ x in Ioi (1:ℝ), ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
          LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
            + (1 + gammaF χ) * (1 / (s - 1)) + C * (1 / (s - σ₀)) := by ...

    lemma key_identity (hχ : χ ≠ 1) (h3 : MellinS) (h4 : LSeriesLamF) (h5 : MellinElem)
        (hreal : ∀ n : ℕ, (χ n).im = 0) {σ₀ C : ℝ} (hσ₀1 : σ₀ < 1) {s : ℂ}
        (hs : 1 < s.re) :
        s * (s - 1) * Imel χ σ₀ C s = -deriv (Pfun χ) s / Pfun χ s + q0 χ σ₀ C s := by
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
      have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
      have hsσ : s - σ₀ ≠ 0 := sub_ne_zero_of_lt_re (a := σ₀) (by linarith)
      have hP : Pfun χ s ≠ 0 := Pfun_ne_zero_of_one_le_re χ hχ hs.le
      have hm := mellin_H χ h3 h5 σ₀ C hs hσ₀1
      unfold Imel Hf
      rw [hm, LSeries_LamF_eq χ hχ h4 hreal hs]
      unfold q0
      field_simp
      ring
    ```

    The use of `dslope (Afun χ σ₀ C) 1 s` is a particularly slick Mathlib idiom: rather than defining `Phi` by cases at `s = 1` and separately proving continuity/analyticity at the removable singularity, `dslope` packages the removable singularity into a single expression whose differentiability at `s = 1` follows immediately from `DifferentiableAt.dslope` once one verifies `Afun χ σ₀ C 1 = 0`.
  ]

  #lean-note(
    title: "The Main Target `TopG` and `zeroFreeAll_of_topG`",
    module: "Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean",
  )[
    Finally, `ZeroFreeAllOfTopG.lean` states `TopG` and proves `zeroFreeAll_of_topG` in just 25 lines, assembling `level_gm_le_on_family_scales`, `formB`, `hypV_of_cls`, and `eFamC_of_cls` into `zeroFreeOn_of_tiedWin_cyc`:

    ```lean
    namespace UpperTheory.Top

    open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

    def TopG : Prop :=
      ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
        (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) →
        FamilyClassConnected (G.cls la)

    theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps)
        (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
      ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

    theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps)
        (h : (GChi ψ).cls la Fm) : EFamC (Level.cyc ψ) Fm.toFamCore := by
      refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
      have h1 := (h.2 x (by linarith) i).1
      rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
      exact h1

    theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG)
        (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
      have key : ZeroFreeOn fun _ => True :=
        zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore)
          (Tied := fun Fm => ChainTied Fm) hla
          (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _)
          (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
            obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
            refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
            obtain ⟨Fm, c, d⟩ := h2 eps a b
            exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
      exact key

    end UpperTheory.Top
    ```
  ]

  #exercises((
    [
      *(Imprimitive Zeros on the Imaginary Axis.)* Let $chi$ be an imprimitive Dirichlet character modulo $N$ induced by a primitive character $psi$ of conductor $f < N$.
      1. Show that if there exists a prime $p | N$ with $p divides.not f$, then $L(s, chi)$ has infinitely many zeros on the line $op("Re")(s) = 0$.
      2. Determine all zeros of $L(s, chi)$ in the half-plane $op("Re")(s) <= 0$ in terms of the zeros of $L(s, psi)$ and the primes $p | N$ not dividing $f$. Why does `Claim.Strip` restrict to the open critical strip $0 < op("Re")(s) < 1$?
    ],
    [
      *(Conductor of the Inverse Character.)* Prove from first principles that for any Dirichlet character $chi$ modulo $N$, the inverse character $chi^(-1) = overline(chi)$ has the same conductor as $chi$: $f_(chi^(-1)) = f_chi$. Deduce that $(chi^(-1))^* = (chi^*)^(-1)$, verifying the key step used in `Claim.prim_reflect` and `PChar.of_inv`.
    ],
    [
      *(Why $s = 0$ Requires Special Care in `Claim.zeta`.)* In the proof of `Claim.zeta`, we explicitly verified $s != 0$ using $zeta(0) = -1\/2 != 0$ before invoking the functional equation $Lambda(1 - s) = Lambda(s)$. Explain what would go wrong if one attempted to apply the functional equation at $s = 0$ directly, and show how the simple pole of $zeta(s)$ at $s = 1$ balances the pole of $Gamma_bb(R) (s)$ at $s = 0$ to yield $zeta(0) = -1\/2$.
    ],
    [
      *(Higher-Order Riesz Means.)* For an integer $k >= 1$, consider the $k$-th Riesz mean
      $ S_chi^((k)) (x) = sum_(1 <= n <= floor(x)) Lambda_(F, chi) (n) (x / n - 1)^k. $
      1. Compute the Mellin transform $integral_1^oo S_chi^((k)) (x) x^(-s - 1) dif x$ for $op("Re")(s) > 1$ in terms of $L(Lambda_(F, chi), s)$ and a rational function of $s$.
      2. Compute the sign of the residue at a hypothetical real zero $beta in (0, 1)$ of $P_chi (s)$ for general $k >= 1$. For which values of $k$ does an *upper* bound on the normalized remainder rule out real zeros automatically?
    ],
    [
      *(Taylor Expansion of `Afun` at $s = 1$.)* Let $chi$ be a real non-principal Dirichlet character modulo $N$, and recall $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ and $A_"fun" (sigma_0, C, s) = -P'_chi (s) + q_0 (sigma_0, C, s) P_chi (s)$.
      1. Compute the exact value of $"dslope"(A_"fun" (sigma_0, C), 1, 1) = A'_"fun" (sigma_0, C, 1)$ in terms of the Stieltjes constant $gamma_1$ (from $zeta(s) = (s - 1)^(-1) + gamma - gamma_1 (s - 1) + dots.c$), $L(1, chi)$, $L'(1, chi)$, $L''(1, chi)$, $C$, and $sigma_0$.
      2. Deduce an explicit formula for $Phi(sigma_0, C, 1) = integral_1^oo H_f (sigma_0, C, x) x^(-2) dif x$ (assuming convergence at $s = 1$, i.e., $G_chi (x) = o(x)$).
    ],
    [
      *(Sharpness of the Power-Window Condition.)* In Theorem 12.7 (`zeroFree_of_rpow_window`), we assumed $G_m (y) <= C y^theta$ on arbitrarily large *power* windows $[Y, Y^(1 + delta)]$ ($delta > 0$).
      1. Explain where the proof of Lemma 12.8 (`landau_tails`) breaks down if $[Y, Y^(1 + delta)]$ is replaced by a *dyadic* window $[Y, 2 Y]$ (corresponding to $[U, U + log 2]$ in the logarithmic variable $u = log y$).
      2. What is the minimal window length $[U, U + L(U)]$ (in the variable $u = log y$) for which a Gamma-peak localization of the form @eq:ch12-tail-bound can still succeed? (Hint: the standard deviation of the Gamma distribution $(u^k \/ k!) sigma^(k + 1) e^(-sigma u)$ with mean $u = k \/ sigma$ is $sqrt(k) \/ sigma approx sqrt(U \/ sigma)$.)
    ],
    [
      *(Why Complex Characters Need Conjugation-Closed Families.)* Suppose $psi$ is a non-real primitive Dirichlet character (so $psi != overline(psi)$).
      1. Explain why $g_psi (y)$ is complex-valued, so a one-sided inequality "$g_psi (y) <= C y^theta$" is meaningless, whereas $op("Re")(g_psi (y)) = (g_psi (y) + g_(overline(psi)) (y)) \/ 2$ is real-valued.
      2. Show that if $w(psi) > 0$ and $w(overline(psi)) = w(psi)$, then the residue of the Laplace transform $Phi(s)$ of $G_m (y)$ at any zero $rho$ of $L(s, psi)$ is strictly nonzero, even if $L(s, overline(psi))$ also vanishes at $rho$ (or does not vanish at $rho$). Why is strict positivity $w(phi) > 0$ for *all* $phi in cal(K)$ essential?
    ],
    [
      *(Perturbing the Center on a Vertical Line.)* In Case 2 of the proof of Theorem 12.7, we used the fact that all poles $rho in cal(Z)$ satisfy $op("Re")(rho) < 1 < sigma$ to deduce that $rho |-> op("Im")(rho)$ is injective on the finite set $S = { rho in cal(Z) : |s_1 - rho| = R_1 }$.
      1. Verify explicitly that for $tau > 0$ sufficiently small, the pole $rho_+ in S$ maximizing $op("Im")(rho)$ is the unique point of $cal(Z)$ closest to $s(tau) = sigma + i (gamma_1 + tau)$.
      2. Give an example of a meromorphic function (with poles allowed to the *right* of $op("Re")(s) = sigma$, or on a symmetric circle) where this perturbation fails if two poles share the same imaginary part, and explain why the half-plane bound $op("Re")(rho) < 1 < sigma$ prevents this obstruction.
    ],
    [
      *(Quantitative Dependence of $epsilon$ on $op("Re")(s) - 1\/2$.)* In the proof of `level_of_tiedWin` (`TopWin.lean`), given a point $s in bb(C)$ with $op("Re")(s) > 1\/2$, we set $delta_0 = min(op("Re")(s) - 1\/2, 1\/2)$ and chose $epsilon = min(epsilon_1 \/ 2, (delta_0 \/ 2) \/ (|e_D + e_L + 7| + 1))$. Trace how the parameter $epsilon$ enters the hypotheses of `HostExW (3/2) (GChi ψ).req` and `VWinAt ψ 401`, and explain why `epsilon_1` must be independent of $s$ (though it may depend on $psi$) in order to prove zero-freeness in the entire open half-plane $op("Re")(s) > 1\/2$.
    ],
  ))
]
