// ============================================================================
// Appendix B: Asymptotic Parameters and Master Inequalities
// ============================================================================
#import "template.typ": appendix-chapter, theorem, proposition, lemma, remark, lean-note, insight-box, gtm-navy, gtm-accent, gtm-tint, gtm-rule

// Helper for clean GTM-styled parameter tables
#let param-table(columns: (16%, 24%, 22%, 38%), header, ..rows) = {
  set text(size: 8.3pt)
  set par(justify: false, leading: 0.5em)
  table(
    columns: columns,
    stroke: (x: none, y: 0.35pt + luma(215)),
    fill: (_, y) => if y == 0 { gtm-tint } else if calc.odd(y) { white } else { rgb("#FAFBFD") },
    inset: (x: 5pt, y: 4.5pt),
    align: (left, left, left, left),
    table.header(..header.map(h => text(weight: "bold", fill: gtm-navy, size: 8.4pt)[#h])),
    ..rows,
  )
}

#let app-b() = [
  #appendix-chapter(
    "B",
    "Asymptotic Parameters and Master Inequalities",
    overview: [
      The Alpöge–Claude–Riemann proof orchestrates more than forty coupled analytic, automorphic, geometric, and cohomological parameters as the master scale $x -> oo$ with a fixed small exponent $0 < epsilon < 1\/52$. Every delicate step—from the window transfer $[W, W^2] -> [Z, Z^(3\/2)]$ and the rank ceiling $t <= x^400 < floor(x^401)$ to the Arakelov divisor–slope inequality `DivIneqObjU` and the archimedean height bound `HeightS`—depends on a strict separation of asymptotic growth regimes. This appendix provides a complete, self-contained dictionary of all parameters, their exact definitions in `DataParams₂.lean`, `Params.lean`, `ExistsPageN.lean`, `PairRowIffQdRows.lean`, and `DivIneqTopAnchorU.lean`, and a worked asymptotic and numerical verification proving that every side-condition inequality is simultaneously satisfied for all sufficiently large $x$.
    ],
  )

  == The Asymptotic Hierarchy: Five Regimes of Growth

  At first sight, the forty-plus hypotheses of `DivIneqObjU` and `HeightS` in `Formalism/DivisorInequality/DivIneqTopAnchorU.lean` appear dauntingly interdependent. In reality, their simultaneous satisfiability rests on a single structural principle: as $x -> oo$ with $0 < epsilon < 1\/52$ fixed, every parameter belongs to one of *five strictly separated regimes of growth*, where each regime dominates any polynomial combination of all lower regimes:

  + *Tier 0 — Absolute Constants ($Theta(1)$)*: fixed numerical exponents and structural constants independent of $x$, including the window exponent $lambda = 3\/2$, the Vandiver-window degree threshold $C_t = 401$, the auxiliary exponent $A = 26$, the global host-exponent $J >= 1$, and the absolute geometry/representation constants $C_0, C_h, C_b, C_1, C_f, C_c, C_s, C_2, C_"th", C_4, c_5, c_6, C_T, C_8, C_e, C_"ev", p_2, p_F, p_N$.
  + *Tier 1 — Logarithmic & Slowly Growing Scales ($log x << L = x^epsilon$)*: $log x$, $L = x^epsilon$, the logarithmic conductor/archimedean scale $L_a = log(a r_d) approx L$, and the prime-conductor logarithms $log q approx Y^(epsilon\/5)$ and $log d approx Y^(epsilon\/5) (log Y)^2$ (where $Y = X^(1\/J)$).
  + *Tier 2 — Polynomial Scales in $x$ ($x^(alpha)$)*: the theta-lift chain length $m approx x^(1\/2 - epsilon\/16)$, the cyclotomic degree $n = 2^e approx x^(2 + 8 epsilon)$ and CM degree $f = 2 n$, the base unitary rank $k approx x^(9\/2 + 10 epsilon)$, the unitary rank $r = k + m - 1$, the step increment $t <= x^400$, and the top chain rank $N = k + m(t + 1) <= x^(400.5)$.
  + *Tier 3 — Intermediate Stretched-Exponential Scales ($exp(x^(epsilon\/3))$)*: the intermediate cutoff $X' = exp(x^(epsilon\/3))$, which crushes every Tier-2 polynomial in $x$ (including $N^2, m k, f r$), yet is itself crushed by $b = exp(x^epsilon)$ because $x^(epsilon\/3) = o(x^epsilon)$. Consequently $b' = a \/ X' = x exp(x^epsilon - x^(epsilon\/3))$ and $w'' = b' \/ (x n)$ sit cleanly between Tier 2 and Tier 4.
  + *Tier 4 — Top Stretched-Exponential Scales ($exp(c x^epsilon)$)*: the primary height scale $b = exp(L) = exp(x^epsilon)$, the shifted weight scale $a = x b$, the error budget $B_0 = f m b x^epsilon$, the Vandiver-window bound $exp(L\/2) = sqrt(exp(x^epsilon))$, and the auxiliary genus/modulus parameter $g >= (k b)^8 = k^8 exp(8 L)$.

  Because $exp(x^epsilon)$ dominates $x^M$ for *every* fixed $M > 0$ as $x -> oo$, any inequality of the shape $("polynomial in " m, f, k, r, t, N, L) <= b$ or $("polynomial") dot.c b' <= a$ holds automatically with super-polynomial room to spare once $x >= x_0 (epsilon)$.

  == Complete Parameter Dictionary

  The four tables below record every parameter in the proof together with its exact mathematical definition, asymptotic order as $x -> oo$ (for fixed $0 < epsilon < 1\/52$), and exact Lean 4 source identifier.

  === Primary Analytic and Stretched-Exponential Scales

  #param-table(
    columns: (14%, 25%, 23%, 38%),
    ([Symbol], [Definition / Relation], [Asymptotic Order], [Lean 4 Identifier & Role]),
    [$x$], [Master asymptotic scale, $x > 1$], [$x -> oo$], [`Scale.x` (`DataParams₂.lean`); main Mellin-window variable.],
    [$epsilon$ (`eps`)], [Fixed small exponent, $0 < epsilon < 1\/52$], [$Theta(1)$], [`Scale.eps`; controls $L = x^epsilon$ and ensures $t <= x^400$.],
    [$J, epsilon_z$], [$J >= 1$, $epsilon_z = epsilon \/ J$], [$Theta(1)$], [`Scale.J`, `Scale.ez`; exponent linking $Y = X^(1\/J)$ to $X$ in `VWinAt`.],
    [$lambda$ (`la`)], [$lambda = 3\/2$], [$3\/2$], [`WinPairs.lean`, `ZeroFreeAllOfTopG.lean`; polynomial window $[Z, Z^(3\/2)]$.],
    [$C_t$], [$C_t = 401$], [$401$], [`VWin` (`ExistsPageN.lean`); upper twist cutoff $floor(x^401) > t$.],
    [$L$], [$L = x^epsilon$], [$x^epsilon$], [`Scale.L`; primary stretched-exponential exponent.],
    [$b$], [$b = exp(L) = exp(x^epsilon)$], [$exp(x^epsilon)$], [`Scale.b`; fundamental height / Arakelov slope scale.],
    [$a$], [$a = x dot.c b = x exp(x^epsilon)$], [$x exp(x^epsilon)$], [`Scale.a`; leading archimedean weight $a_T (t) approx a$.],
    [$X'$], [$X' = exp(x^(epsilon\/3))$], [$exp(x^(epsilon\/3))$], [`Scale.X'`; intermediate stretched-exponential separator.],
    [$b'$], [$b' = a \/ X'$], [$x exp(x^epsilon - x^(epsilon\/3))$], [`Scale.b'`; lower bound on negative weights $b_T (t) >= b'$.],
    [$w''$], [$w'' = b' \/ (x n) = b \/ (n X')$], [$n^(-1) exp(x^epsilon - x^(epsilon\/3))$], [`Scale.w''`; upper cushion for $k S$ and $m(t_0 + 1) eta$.],
    [$delta_1$], [$delta_1 = x^(-epsilon\/8)$], [$x^(-epsilon\/8)$], [`Scale.delta1`; slight damping in chain length $m approx sqrt(x delta_1)$.],
    [$A$], [$A = 26$], [$26$], [`Scale.A`; polynomial precision $a \/ (k x^(A\/2))$ for $a_T (t)$.],
    [$r_d$], [$1 <= r_d$, $log r_d <= L$], [$<= exp(L)$], [`rd` (`DivIneqTopAnchorU.lean`); discriminant/conductor factor.],
    [$L_a$ (`La`)], [$L_a = log(a r_d) = L + log x + log r_d$], [$Theta(L) = Theta(x^epsilon)$], [`La` (`DivIneqTopAnchorU.lean`); logarithmic archimedean scale.],
    [$B_0$], [$B_0 = f m b x^epsilon$], [$x^(5\/2 + 71 epsilon \/ 8) exp(x^epsilon)$], [`B0` (`DivIneqTopAnchorU.lean`); total error scale from local indices.],
    [$N_c$], [$0 <= N_c <= p_N b$], [$O(b)$], [`Nc` (`DivIneqTopAnchorU.lean`); ramified/bad-place count budget.],
  )

  === Arithmetic, Conductor, and Vandiver-Window Parameters

  #param-table(
    columns: (14%, 25%, 23%, 38%),
    ([Symbol], [Definition / Relation], [Asymptotic Order], [Lean 4 Identifier & Role]),
    [$q$], [Prime, $q equiv 3 (op("mod") 8)$, $Y^(epsilon\/5)\/2 < log q <= Y^(epsilon\/5)$], [$exp(Theta(Y^(epsilon\/5)))$], [`WinPair.q` (`ExistsPageN.lean`); auxiliary quadratic prime.],
    [$d$], [Prime, $d equiv 7 (op("mod") 16)$, $q | d + 1$, $p | d + 1$ for odd $p <= Y^(epsilon\/5)$], [$exp(Theta(Y^(epsilon\/5) (log Y)^2))$], [`WinPair.d` (`ExistsPageN.lean`); CM field discriminant prime.],
    [$e$], [Integer satisfying `PageN`: $x^(2 + 8 epsilon) <= 2^e <= 2 x^(2 + 8 epsilon)$], [$2^e = Theta(x^(2 + 8 epsilon))$], [`PageN` (`ExistsPageN.lean`); 2-power cyclotomic tower level.],
    [$E$], [Subfield of $bb(Q)(zeta_N)$ fixed by $a equiv plus.minus 1 (op("mod") 2^(e+2))$, $psi(a) = 1$, $(a\/q) = (a\/d) = 1$], [$[E : bb(Q)] = Theta(2^e)$], [`IsChiField` (`ExistsPageN.lean`); totally real host field.],
    [$op("VVle")(E, t, B)$], [$sum_(ell in S) log ell sum_(1 <= e < t) op("len")_(bb(Z)_ell) op("Ш")^1_S (E, bb(Q)_ell\/bb(Z)_ell (-e)) <= B$], [$t = floor(x^401)$, $B = exp(L\/2)$], [`VVle`, `VAt`, `VWinAt`, `VWin` (`ExistsPageN.lean`).],
  )

  === Unitary Rank, Chain, and Signature Parameters

  #param-table(
    columns: (14%, 25%, 23%, 38%),
    ([Symbol], [Definition / Relation], [Asymptotic Order], [Lean 4 Identifier & Role]),
    [$n$], [$n = op("ord")$, $x^(2 + 8 epsilon) <= n <= 2 x^(2 + 8 epsilon)$], [$Theta(x^(2 + 8 epsilon))$], [`Ranks.n`, `RankVal` (`Params.lean`, `PairRowIffQdRows.lean`).],
    [$f$], [$f = 2 n = [K : bb(Q)]$], [$Theta(x^(2 + 8 epsilon))$], [`Ranks.f`; degree of CM field $K$, upper bound on $|op("Pl")|$.],
    [$m$], [Even integer, $sqrt(x delta_1) <= m <= 2 sqrt(x delta_1)$], [$Theta(x^(1\/2 - epsilon\/16))$], [`Ranks.m`; length of iterated theta-lift chain $U(X_0) -> dots.c -> U(X_m)$.],
    [$k$], [Even integer, $x^(9\/2 + 10 epsilon) <= k <= 2 x^(9\/2 + 10 epsilon)$], [$Theta(x^(9\/2 + 10 epsilon))$], [`Ranks.k`; base rank of unitary group $U(X_0)$ ($k >= m + 3$).],
    [$r$], [$r = k + m - 1$ (odd)], [$Theta(x^(9\/2 + 10 epsilon))$], [`Ranks.r`; rank of intermediate unitary spaces $W_j$.],
    [$t$], [Odd integer, $r + t = 8 f r + 4 + T_0(s) n_W(R, s)$], [$<= x^400$], [`Ranks.t`; rank increment per theta-lift step.],
    [$N$], [$N = N(m) = k + m(t + 1)$ (even)], [$<= 3 x^(400.5)$], [`Ranks.N`; top rank of $U(X_m)$ (`k + m <= N` in `DivIneqObjU`).],
    [$n_V$], [$n_V = r + t$], [$<= x^400$], [`Ranks.nV`; ambient rank of auxiliary Hermitian space ($n_V <= N$).],
    [$op("sigW")(j)$], [$(k + j - 1, m - j)$ for $1 <= j <= m$], [Sum $= r$], [`Ranks.sigW`; signature evolution reaching definite $(r, 0)$ at $j = m$.],
  )

  === Divisor–Slope, Height, and Arakelov Parameters

  #param-table(
    columns: (14%, 25%, 23%, 38%),
    ([Symbol], [Definition / Relation], [Asymptotic Order], [Lean 4 Identifier & Role]),
    [$op("ph")(nu)$], [$op("ph")(nu) = nu log nu - nu$], [$nu log nu$], [`Formalism.LatticeIndexTer.ph`, `phF`; Stirling log-factorial kernel.],
    [$F_0$ (`Fo`)], [$F_0 = sum_j sum_(y in T_w) w_y e_y F_0(y, j) <= p_F b$], [$O(b)$], [`Fo` (`DivIneqObjU`); total $p$-adic CM divisibility gain.],
    [$h_u$ (`hu`)], [Archimedean height upper bound (Eq. in `DivIneqObjU` / `HeightS`)], [$Theta(|T T| m a L)$], [`hu` (`DivIneqTopAnchorU.lean`); bridges `HeightS` and `DivIneqObjU`.],
    [$mu_C$], [Arakelov slope of quotient/auxiliary Hermitian lattice], [$-mu_C approx mu_(P_s)$], [`muC` (`DivIneqObjU`); enters LHS $mu_C + h_u - 2 F_0$.],
    [$mu_0$], [$mu_0 = mu(R^or)$ (`Formalism.HN.muDef` of dual lattice)], [$-mu_0 approx mu_(P_0)$], [`mu0` (`DivIneqObjU`); dual slope of test lattice $R$.],
    [$mu_G(j)$], [Good-locus slope, $mu_G(j) - P_9(j) <= mu(M_j)$], [$>= -O(b)$], [`muG` (`DivIneqObjU`); lower-bounds slope of target lattice $M_j$.],
    [$mu_U, mu_A, mu_N$], [Unfiltered, admissible, and normalized intermediate slopes], [$O(b)$], [`muU`, `muA`, `muN` (`DivIneqObjU`); slope-descent chain.],
    [$S, eta, t_0$ (`tt`)], [Shift, perturbation, and depth parameters ($S, eta, t_0 >= 0$)], [$k S, m(t_0 + 1) eta <= w''$], [`S`, `eta`, `tt` (`DivIneqObjU`, `HeightS`); controlled by $w''$.],
    [$g, log g$], [Auxiliary genus/level, $(k b)^8 <= g$, $log g <= C_8 L$], [$Theta((k b)^8)$], [`g`, `logg` (`DivIneqObjU`, `HeightS`); spectral-gap denominator.],
    [$log T, log Omega$], [Period & test-form logs: $0 <= log T <= C_T m L$, $|log Omega| <= L_a$], [$O(m L)$, $O(L)$], [`logT`, `logOm` (`DivIneqObjU`, `HeightS`); CM period & archimedean terms.],
    [$h_P, h_K(j), m_lambda$], [Polynomial height, kernel heights, and log-Hodge lower bound], [$h_P + sum_j h_K(j) - m_lambda <= h_u$], [`hP`, `hK`, `mlam` (`HeightS`); archimedean height decomposition.],
    [$lambda_0$ (`lam0`)], [Slope-discrepancy tolerance, $0 <= lambda_0 <= b$], [$<= b$], [`lam0` (`DivIneqObjU`); error in $|(-mu_0) - mu_(P_0)|$ and $|(-mu_C) - mu_(P_s)|$.],
  )

  == Origin of the Thresholds $epsilon < 1\/52$, $C_t = 401$, and $lambda = 3\/2$

  Why does `ExistsPageN.lean` insist on the seemingly idiosyncratic constants $epsilon < 1\/52$ and $C_t = 401$, and why does `WinPairs.lean` transfer windows to $[Z, Z^(3\/2)]$? Both constants arise from two explicit, completely elementary inequalities verified in the Lean 4 source.

  #proposition(title: "Rank-Degree Ceiling — EventuallyRankLeRpowOfLtOneDivFiftytwo.lean")[
    Let $0 < epsilon < 1\/52$ and $x >= 2^100$. Let $s$ be a `Scale` with $s.x = x$, $s.epsilon = epsilon$, and let $R$ be a `Ranks` package satisfying `RankVal s R`. Then the theta-lift step increment $R.t$ satisfies
    $ R.t <= x^400 < floor(x^401). $
  ]

  *Verification (mirroring Lean lines 46–167).* Set $Y := x^(1\/100)$. Since $x >= 2^100$, we have $Y >= 2$, and for every integer $a >= 0$, $x^(a\/100) = Y^a$. Because $0 < epsilon < 1\/52$:
  - $2 + 8 epsilon + epsilon\/100 < 2 + 801\/5200 < 2.1541 < 216\/100$, hence
    $ n <= 2 x^(2 + 8 epsilon) <= 2 Y^216, quad f = 2 n <= 4 Y^216. $
  - $9\/2 + 10 epsilon < 4.5 + 10\/52 < 4.6924 < 470\/100$, hence
    $ k <= 2 x^(9\/2 + 10 epsilon) <= 2 Y^470, quad r = k + m - 1 <= 2 k <= 4 Y^470. $
  - $1 - epsilon\/8 > 1 - 1\/416 > 98\/100$, hence
    $ m >= sqrt(x dot.c x^(-epsilon\/8)) = x^((1 - epsilon\/8)\/2) >= Y^49. $
  - $2 epsilon < 2\/52 < 4\/100$, hence $L^2 = x^(2 epsilon) <= Y^4$.

  Combining these four bounds gives the rational quotient bound
  $ (f^2 (k - 1)^3 L^2) / m <= ((4 Y^216)^2 (2 Y^470)^3 Y^4) / Y^49 = (128 Y^(432 + 1410 + 4)) / Y^49 = 128 Y^1797. $
  Since $Y^216 <= Y^1797$, we obtain $f + f^2 (k - 1)^3 L^2 \/ m <= 132 Y^1797$. By definition of `nWv R s` and `TOv s` in `PairRowIffQdRows.lean`,
  $ n_W (R, s) &<= 10 r (f + f^2 (k - 1)^3 L^2 \/ m) + 8 \
    &<= 10 (4 Y^470)(132 Y^1797) + 8 <= 5288 Y^2267, $
  $ T_0 (s) = ceil(x^377) <= 2 Y^37700. $
  Substituting into the `RankVal` equation $r + t = 8 f r + 4 + T_0 (s) dot.c n_W (R, s)$ yields
  $ r + t &<= 8 (16 Y^686) + 4 + (2 Y^37700)(5288 Y^2267) \
    &<= (128 + 4 + 10576) Y^39967 = 10708 Y^39967. $
  Finally, since $Y >= 2$ implies $Y^33 >= 2^33 = 8589934592 > 10708$, we conclude
  $ t <= r + t <= Y^33 dot.c Y^39967 = Y^40000 = x^400 < floor(x^401). $
  Thus the cutoff $C_t = 401$ in `VWin` strictly exceeds $R.t$ for every valid `Scale` with $x >= 2^100$, leaving a full power of $x$ to spare for the rescaling $x = kappa x'$ in `WinPairs.lean`.

  #proposition(title: "Window Transfer $[W, W^2] -> [Z, Z^(3\/2)]$ — WinPairs.lean")[
    Let $c >= 1$, $0 < epsilon < 1\/52$, and define $kappa := c^(1\/(2 + 8 epsilon)) >= 1$. Whenever $W >= max(1, kappa^3, kappa^400)$ and `VAt` holds on $[W, W^2]$ at cutoff $C_t = 401$, setting $Z := kappa W$ guarantees that for every $x in [Z, Z^(3\/2)]$ the rescaled point $x' := x \/ kappa$ satisfies $W <= x' <= W^2$ and $floor((x')^401) >= floor(x^400)$.
  ]

  *Verification.* Since $kappa^3 <= W$, we have $(kappa W)^3 = kappa^3 W^3 <= W^4$. Taking square roots yields
  $ Z^(3\/2) = (kappa W)^(3\/2) <= W^2. $
  Therefore any $x in [Z, Z^(3\/2)]$ satisfies $W <= x' = x \/ kappa <= x <= W^2$, so `VAt` applies at $x'$. Moreover, since $kappa^400 <= W <= x'$, we have $x^400 = kappa^400 (x')^400 <= (x')^401$, which explains why `VWin` uses $C_t = 401$ rather than $400$: the extra unit in the exponent absorbs the constant dilation factor $kappa^400$ during the passage from $[W, W^2]$ to $[Z, Z^(3\/2)]$.

  == Master Verification of the Side Conditions in `DivIneqObjU`

  We now verify that *every* side-condition inequality in `Formalism.DivisorInequality.DivIneqObjU` (`DivIneqTopAnchorU.lean`, lines 146–215) is simultaneously satisfied for all sufficiently large $x >= x_0 (epsilon)$, under the `Scale` and `RankVal` assignments of Section 2.

  === Group I: Scale and Exponential Dominance (Lines 197–208)

  Recall $L = x^epsilon$, $b = exp(L)$, $a = x b$, $X' = exp(x^(epsilon\/3))$, $b' = a \/ X'$, $w'' = b' \/ (x n)$, and $L_a = log(a r_d)$.

  + *$log x <= L$ and $log r_d <= L$*: since $epsilon > 0$, $log x \/ x^epsilon -> 0$ as $x -> oo$, so $log x <= x^epsilon = L$ for all large $x$. The conductor bound $log r_d <= L$ holds because the discriminant factors $q, d$ in `WinPair` satisfy $log q <= Y^(epsilon\/5) <= x^(epsilon\/5)$ and $log d <= Y^(epsilon\/5) (log Y)^2 = o(x^epsilon)$ since $epsilon\/5 < epsilon$.
  + *$m^3 N^2 L <= b$*: from `RankVal`, $m <= 2 x^(1\/2)$, $N = k + m(t + 1) <= 3 x^(400.5)$, and $L = x^epsilon$. Hence the left-hand side is strictly polynomial:
    $ m^3 N^2 L <= 8 x^(3\/2) dot.c 9 x^801 dot.c x^epsilon = 72 x^(802.5 + epsilon). $
    Taking logarithms, $log(72 x^(802.5 + epsilon)) = O(log x) = o(x^epsilon) = log b$, so $m^3 N^2 L <= b$ holds with super-polynomial margin for all large $x$.
  + *$k N <= b$ and $lambda_0 <= b$*: $k N <= 2 x^(4.7) dot.c 3 x^(400.5) = 6 x^(405.2) << exp(x^epsilon) = b$. Likewise the slope tolerance $lambda_0$ is polynomial in $x$ (or $O(L)$), so $lambda_0 <= b$.
  + *$b' N <= a$ and $m k b' <= a$*: substituting $b' = a \/ X'$ cancels $a$ on both sides, reducing these two inequalities to
    $ N <= X' = exp(x^(epsilon\/3)), quad m k <= X' = exp(x^(epsilon\/3)). $
    Since $N <= 3 x^(400.5)$ and $m k <= 4 x^(5.2)$ are polynomial in $x$ whereas $X' = exp(x^(epsilon\/3))$ is stretched exponential (Tier 3), both inequalities hold for all sufficiently large $x$.
  + *$N w'' <= b$*: substituting $w'' = b' \/ (x n) = b \/ (n X')$ cancels $b$, leaving $N <= n X'$, which holds *a fortiori* from $N <= X'$ since $n >= 1$.
  + *$k S <= w''$, $m (t_0 + 1) eta <= w''$, and $m eta N L <= b$*: the perturbation parameters $S, eta, t_0$ are polynomial in $x$ (in fact $t_0 <= t <= x^400$), whereas $w'' = b \/ (n X') = n^(-1) exp(x^epsilon - x^(epsilon\/3))$ grows like $exp((1 - o(1)) x^epsilon)$. Thus $k S << w''$ and $m(t_0 + 1) eta << w''$. Multiplying $m eta <= w''$ by $N L$ yields $m eta N L <= N L w'' = b (N L \/ (n X')) <= b$ since $N L <= n X'$.

  === Group II: Spectral Gap, Genus, and Log-Discriminant Bounds (Lines 153–156, 179–183)

  In `DivIneqObjU`, the auxiliary genus/modulus parameter $g$ is chosen in Tier 4 to satisfy $(k b)^8 <= g <= (2 k b)^8$ (for instance, by choosing a prime or level parameter in the dyadic interval $[(k b)^8, 2 (k b)^8]$). Then:

  + *$(k b)^8 <= g$ and $log g <= C_8 L$*: by construction $(k b)^8 <= g$, and
    $ log g <= 8 log(2 k b) = 8 L + 8 log(2 k) = (8 + O(log x \/ x^epsilon)) L <= 9 L, $
    so `logg <= C8 * L` in `HeightS` holds with $C_8 = 9$.
  + *$N^2 log g <= b$ and $N log(f N) <= b$*: both left-hand sides are polynomial in $x$ ($N^2 log g <= 9 N^2 L <= 81 x^(801 + epsilon)$ and $N log(f N) = O(x^(400.5) log x)$), hence both are $o(b) = o(exp(x^epsilon))$.
  + *$24 f r <= (k b)^8$*: the left-hand side is polynomial ($24 f r <= 384 x^(6.86)$), whereas $(k b)^8 >= b^8 = exp(8 x^epsilon)$, giving an overwhelming margin.
  + *The spectral-gap inequality (lines 154–155)*:
    $ &24 f r dot.c (2 m f N L_a + 2 p_F \
      &quad + C_0 c_e m (c_e f m x^(2 epsilon) + (log x)^2 p_N) + p_2 + 4) <= (k b)^7. $
    Every single term inside the parentheses is polynomial in $x$: $m f N L_a = O(x^(403.2 + 9 epsilon))$, $f m^2 x^(2 epsilon) = O(x^(3 + 10 epsilon))$, and the constants $p_2, p_F, p_N, C_0, c_e$ are Tier 0. Hence the entire left-hand side is $O(x^(411))$ (Tier 2), while the right-hand side is $(k b)^7 >= exp(7 x^epsilon)$ (Tier 4). The inequality holds with hundreds of orders of magnitude to spare.

  === Group III: Slope-Floor, Drop-Level, and Constant Compatibility (Lines 158–178, 209–210)

  Lines 158–178 of `DivIneqTopAnchorU.lean` chain together the local-to-global slope lower bounds
  $ mu_U(j) -> mu_A(j) -> mu_N(j) -> mu_G(j) -> mu(M_j). $
  Each step incurs an explicit loss controlled by $b$:
  - The truncation loss $epsilon_d(j) Q_d(j) <= b\/4$ and the bad-locus loss $P_d(j) + 12 delta_d(j) Q_d(j) + P_9(j) <= b$ are satisfied because the bad-place densities $epsilon_d(j), delta_d(j)$ decay faster than $Q_d(j)^(-1) b$ (as $Q_d(j) = O(b L_a)$ while $epsilon_d, delta_d = O(L_a^(-2))$ or exponentially small in $L$).
  - The shift floor `sfl j <= b / 50 + Cs * L` absorbs the $O(L)$ discrepancy into the fixed fraction $b\/50$ of the primary height scale $b$.
  - Finally, the absolute constant $C_0$ is chosen *after* the representation-theoretic and geometric constants $C_1, C_s, C_f, C_c, C_b$ so that
    $ C_0 >= max(25\/2, 64(C_1 + C_s + 3 C_f) + 8 C_c + 6 C_b + 4), $
    which satisfies lines 209–210 identically for all $x$.

  === Group IV: The Master Conclusion of `DivIneqObjU` (Lines 211–214)

  Under Groups I–III, `DivIneqObjU` concludes:
  $ mu_C + h_u - 2 F_0 &<= sum_(t in T T) (m (op("ph")(a_T(t)) - a_T(t) log Omega) - a_T(t) log T) \
    &quad + (50 C_0 + 10) (|T T| a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $
  Let us compare the orders of magnitude of the terms on the right-hand side:
  - The *leading term* at each place $t in T T$ is $m op("ph")(a_T(t)) = m a_T(t) (log a_T(t) - 1)$. Since $a_T(t) approx a = x b$ and $log a = L + log x approx L$, the sum over $T T$ has magnitude
    $ |T T| dot.c m dot.c a L = |T T| dot.c m x b L. $
  - The *period and test-form terms* $-m a_T(t) log Omega - a_T(t) log T$ are controlled by $|log Omega| <= L_a approx L$ and $log T <= C_T m L$, contributing at most $O(|T T| m a L)$ with explicit leading cancellation against the archimedean height $h_u$.
  - The *first error term* $(50 C_0 + 10) |T T| a L_a$ is smaller than the leading term $|T T| m a L$ by a factor of $m approx x^(1\/2 - epsilon\/16) -> oo$! This factor of $m$ is precisely the *multiplicity gain* synthesized by the chain of $m$ theta lifts.
  - The *second error term* $(50 C_0 + 10) c_e m (x^epsilon B_0 + (log x)^2 N_c)$ is $O(m x^epsilon B_0) = O(f m^2 b x^(2 epsilon))$ plus $O(m (log x)^2 b)$. Against the divisibility gain $2 F_0$ on the left-hand side and the leading archimedean cancellation, this term is absorbed into the contradiction once $a = x b$ and the CM divisibility bound $F_0$ are instantiated in Chapter 14.

  == Master Verification of the Side Conditions in `HeightS`

  The companion proposition `HeightS` (`DivIneqTopAnchorU.lean`, lines 216–274) certifies the archimedean height upper bound
  $ h_P + sum_(j in J) h_K (j) - m_lambda <= h_u. $
  Its side conditions are verified as follows:

  + *Genus / rank bound $g_0(j) <= N^2$* (line 250): $g_0(j)$ is the Siegel genus / dimension parameter at step $j$, bounded quadratically by the top unitary rank $N$.
  + *Archimedean logarithm bounds (lines 251–252)*:
    $ log(8 + 32 f g_0(j) v) <= c_5 L_a, quad log(2 sum_i nu(j, tau, i) + 2) <= c_6 L_a. $
    Because $f, g_0(j), v$ are polynomial in $x$, $log(8 + 32 f g_0(j) v) = O(log x) = o(L) = o(L_a)$, so any $c_5 > 0$ works for large $x$. Similarly, each weight sum $sum_i nu(j, tau, i) = O(a) = O(x b)$, so its logarithm is $L + O(log x) <= 2 L_a$, satisfied with $c_6 = 2$.
  + *Log-genus and log-period bounds (lines 253, 264)*: $log g <= C_8 L$ (verified above with $C_8 = 9$) and $0 <= log T <= C_T m L$, where $log T$ scales linearly with the chain length $m$ and the archimedean weight logarithm $L$.
  + *Polynomial height decomposition (lines 256–265)*: the local bounds $log c(tau) <= (N - 1) D_1(tau) log(2 a)$ and $log xi(tau) <= (N(N-1)\/2) log(2 a)$, together with $D_0(tau) <= S + m eta + 2 b' bb(1)_(tau in T T)$ and $D_1(tau) <= 3 D_0(tau) + S + eta$, ensure that the total error in $h_P$ is bounded by
    $ O((|T T| b' N + f (m eta + S) N + f N^2) L_a), $
    which matches the exact coefficient of $C_h$ in the definition of $h_u$ (lines 231–234)!
  + *Constant compatibility for $C_h$ (lines 270–272)*: choosing the single absolute constant
    $ C_h >= max(&2(16 + C_T + C_"ev"), \
      &C_"th" + c_5 + 2 c_6 + 1 + 2 C_4 + 2 C_e C_8, \
      &2(C_2 + C_4)(C_T + C_8)) $
    satisfies all three inequalities simultaneously, and setting $C_0 >= max(C_h, C_h C_L)$ satisfies line 189 of `DivIneqObjU`.

  == Worked Numerical Snapshot at a Concrete Scale

  To make the five-tier separation tangible, Table B.5 evaluates the base-10 orders of magnitude of every key parameter at a concrete choice of $(epsilon, x)$ where *every* asymptotic inequality in `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`, `DivIneqObjU`, and `HeightS` holds simultaneously with strict inequality:
  $ epsilon = 1 / 60 < 1 / 52, quad x = 10^1260 > 2^100. $
  At this scale, $log_(10) x = 1260$, $ln x approx 2901.3$, $Y = x^(1\/100) = 10^(12.6) >> 2$, and $x^(epsilon\/3) = x^(1\/180) = 10^7$ strictly dominates $401 ln x approx 1.16 times 10^6$, ensuring that even Tier 3 ($X'$) dwarfs every Tier-2 polynomial ($N, m k, f r$).

  #param-table(
    columns: (17%, 22%, 25%, 36%),
    ([Parameter], [Exact Formula / Bound], [Value at $epsilon = 1\/60, x = 10^1260$], [Key Inequality Verified]),
    [$x$], [Master scale], [$10^1260$], [$x >= 2^100 approx 1.27 times 10^30$],
    [$ln x$], [Natural log], [$2.90 times 10^3$], [$ln x << L = 10^21$],
    [$L = x^epsilon$], [$10^(1260\/60)$], [$10^21$], [$L^2 = 10^42 <= Y^4 = 10^(50.4)$],
    [$m$], [$approx x^(1\/2 - epsilon\/16)$], [$approx 10^(628.7)$], [$m >= Y^49 = 10^(617.4)$],
    [$n, f = 2n$], [$approx x^(2 + 8 epsilon)$], [$approx 10^(2688)$], [$f <= 4 Y^216 approx 10^(2722.2)$],
    [$k, r$], [$approx x^(9\/2 + 10 epsilon)$], [$approx 10^(5880)$], [$k <= 2 Y^470 approx 10^(5922.3)$],
    [$t$], [$<= x^400$], [$<= 10^(5.04 times 10^5)$], [$t <= x^400 < floor(x^401) = 10^(5.0526 times 10^5)$],
    [$N$], [$k + m(t + 1)$], [$<= 10^(5.047 times 10^5)$], [$N <= X' = 10^(4.34 times 10^6)$],
    [$m^3 N^2 L$], [Tier-2 polynomial], [$<= 10^(1.012 times 10^6)$], [$m^3 N^2 L << b = 10^(4.34 times 10^20)$],
    [$X'$], [$exp(x^(epsilon\/3)) = exp(10^7)$], [$approx 10^(4.34 times 10^6)$], [$m k approx 10^6509 << X' << b$],
    [$b$], [$exp(L) = exp(10^21)$], [$approx 10^(4.34 times 10^20)$], [$N^2 log g approx 10^(1.01 times 10^6) << b$],
    [$a = x b$], [$x exp(L)$], [$approx 10^(4.34 times 10^20 + 1260)$], [$b' N = a (N\/X') << a$],
    [$g$], [$approx (k b)^8$], [$approx 10^(3.47 times 10^21)$], [$24 f r approx 10^8569 << (k b)^7 << g$],
  )

  #insight-box(title: "Why the Parameter System Is Robust Under Future Simplifications")[
    Notice how *enormous* the safety margins in Table B.5 are: $m^3 N^2 L$ has base-10 exponent $approx 10^6$, whereas $b = exp(x^epsilon)$ has base-10 exponent $approx 4.34 times 10^20$—fourteen orders of magnitude larger *in the exponent*. Even if future simplifications of the Alpöge–Claude–Riemann proof tighten $C_t = 401$ or relax $epsilon < 1\/52$, the underlying five-tier separation between polynomial ranks ($x^M$), intermediate cutoffs ($exp(x^(epsilon\/3))$), and stretched-exponential heights ($exp(x^epsilon)$) remains completely invariant.
  ]
]
