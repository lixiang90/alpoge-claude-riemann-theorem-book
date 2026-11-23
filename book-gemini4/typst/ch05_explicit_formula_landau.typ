#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch05() = [
#chapter(
  "Smoothed Prime Sums, Mellin Transforms, and Landau's Criterion",
  short-title: "Mellin Transforms and Landau's Criterion",
  epigraph: "If the coefficients of a Dirichlet series are eventually nonnegative, the real point on the line of convergence is always a singularity.",
  epigraph-source: "Edmund Landau, Über einen Satz von Tschebyschef (1905)",
  overview: [
    The analytic bridge between prime-counting estimates and zero-free regions for $L$-functions rests on two classical pillars: the Mellin transform (and its contour-integral inverse, Perron's formula) and Landau's theorem on Dirichlet integrals with nonnegative tails. In this chapter we construct the exact analytic interface used in the Alpöge–Claude–Riemann proof. We replace Chebyshev's discontinuous function $psi(x)$ by the continuous, piecewise-linear smoothed prime-power sum $S_a (x) = sum_(1 <= n <= x) a(n)(x/n - 1)$, whose Mellin transform gains a quadratic vertical decay factor $1 / (s(s-1))$. Subtracting the canonical main term $x log x - (1 + gamma_chi) x$ cancels the double and simple poles at $s = 1$, leaving a function $G_chi (x)$ whose Mellin transform is meromorphic with poles in $op("Re")(s) > 0$ exclusively at the nontrivial zeros of $zeta(s) L(s, chi)$. We then prove both Landau's classical nonvanishing theorem and a quantitative localized version on long intervals $[Y, Y^lambda]$ ($lambda = 3/2$), derive the Guinand–Weil explicit formula and its positivity functionals $W(f)$, and explain why a one-sided bound on sparse intervals $[Y, Y^(3/2)]$ suffices to establish the Generalized Riemann Hypothesis.
  ],
)

// ============================================================================
// Section 5.1
// ============================================================================
== The Smoothed Prime-Power Sum $S_a (x)$ and Its Mellin Transform

In classical analytic number theory, the distribution of prime numbers is encoded first by Chebyshev's summatory function
$ psi(x) = sum_(1 <= n <= x) Lambda(n), $
where $Lambda(n)$ is the von Mangoldt function ($Lambda(p^k) = log p$ for prime powers $p^k$ with $k >= 1$, and $Lambda(n) = 0$ otherwise). For $op("Re")(s) > 1$, the Dirichlet series of $Lambda$ is the negative logarithmic derivative of the Riemann zeta function,
$ L(Lambda, s) = sum_(n=1)^oo (Lambda(n))/(n^s) = -(zeta'(s))/(zeta(s)). $
Via integration by parts (or Abel summation), the Mellin transform of $psi(x)$ is
$ integral_1^oo psi(x) x^(-s-1) dif x = 1/s (-(zeta'(s))/(zeta(s))) wide (op("Re")(s) > 1). $
Although this identity is algebraically simple, it suffers from a well-known analytic defect when one attempts to invert it by Perron's formula: along a vertical line $s = sigma_0 + i t$ with $sigma_0 > 1$, the integrand $(-(zeta'(s))/(zeta(s))) x^s / s$ decays only like $|t|^(-1)$ as $|t| -> oo$. Consequently, the Perron integral for $psi(x)$ is only conditionally convergent, requires delicate truncation at height $T$, and exhibits Gibbs-like jump discontinuities at every prime power $x = p^k$.

To obtain an _absolutely_ convergent inversion integral and a continuous summatory function, one applies a Riesz or Cesàro smoothing. Two closely related smoothings appear throughout the literature: the first antiderivative
$ psi_1 (x) = integral_1^x psi(t) dif t = sum_(1 <= n <= x) Lambda(n) (x - n), $
and the multiplicatively scaled, linearly smoothed prime-power sum $S_a (x)$ defined below. It is the latter that serves as the primary analytic object throughout the Alpöge–Claude–Riemann formalization.

#definition(title: "Smoothed Prime-Power Sum")[
  Let $a : bb(N) -> bb(R)$ be an arithmetic function. For every real number $x in bb(R)$, we define the _smoothed summatory function_ $S_a (x)$ by
  $ S_a (x) := sum_(1 <= n <= floor(x)) a(n) (x/n - 1). $
  Here the sum is empty (and hence equal to $0$) whenever $x < 1$. When $a(n) = Lambda(n)$, we write $S_Lambda (x)$ (denoted `Formalism.Sz` in the Lean 4 codebase); when $a(n) = Lambda_F (chi, n) := Lambda(n)(1 + op("Re")(chi(n)))$ for a Dirichlet character $chi$, we write $S_chi (x)$ (denoted `Formalism.S χ`).
]

Writing $u_+ := max(u, 0)$ for the positive part of a real number $u$, we may rewrite $S_a (x)$ as a globally defined series with no $x$-dependent upper limit of summation:
$ S_a (x) = sum_(n=1)^oo a(n) (x/n - 1)_+ wide (x in bb(R)). $
For any fixed $x in bb(R)$, only the finitely many indices $1 <= n <= floor(x)$ contribute nonzero terms, so the series terminates locally uniformly on bounded subsets of $bb(R)$. From this representation we read off the basic regularity properties of $S_a (x)$ immediately:

+ *Vanishing on $(-oo, 1]$:* If $x <= 1$, then $x/n - 1 <= 0$ for every integer $n >= 1$, so $(x/n - 1)_+ = 0$ for all $n >= 1$ and hence $S_a (x) = 0$.
+ *Continuity and piecewise linearity:* On every interval $( -oo, N )$ with $N in bb(N)$, $S_a (x)$ coincides with the finite sum $sum_(n=1)^(N-1) a(n) (x/n - 1)_+$ of continuous piecewise-linear functions. Hence $S_a : bb(R) -> bb(R)$ is continuous everywhere on $bb(R)$, affine on each interval $[m, m+1]$ ($m in bb(N)$), and has right-derivative
  $ (S_a)_+' (x) = sum_(1 <= n <= x) (a(n))/n wide (x > 0). $
+ *Integral representation via $A(t) = sum_(1 <= n <= t) a(n)$:* For every $x >= 1$,
  $ S_a (x) = sum_(1 <= n <= x) a(n) integral_n^x x/(t^2) dif t = x integral_1^x (A(t))/(t^2) dif t. $
  Equivalently, dividing by $x$ and differentiating on $(0, oo) without bb(N)$ yields
  $ dif/(dif x) ((S_a (x))/x) = (A(x))/(x^2). $

Let us compare $S_Lambda (x)$ systematically with Chebyshev's $psi(x)$ and its first integral $psi_1 (x) = integral_1^x psi(t) dif t$.

#proposition(title: "Comparison of " + $psi(x)$ + ", " + $psi_1 (x)$ + ", and " + $S_Lambda (x)$)[
  For all $x >= 1$, the functions $psi(x)$, $psi_1 (x)$, and $S_Lambda (x)$ satisfy the exact integral relations
  $ psi_1 (x) &= integral_1^x psi(t) dif t = sum_(1 <= n <= x) Lambda(n)(x - n), \
    S_Lambda (x) &= x integral_1^x (psi(t))/(t^2) dif t = sum_(1 <= n <= x) Lambda(n)(x/n - 1), $
  and for $op("Re")(s) > 1$ their Mellin transforms are
  $ integral_1^oo psi(x) x^(-s-1) dif x &= 1/s (-(zeta'(s))/(zeta(s))), \
    integral_1^oo psi_1 (x) x^(-s-2) dif x &= 1/(s(s+1)) (-(zeta'(s))/(zeta(s))), \
    integral_1^oo S_Lambda (x) x^(-s-1) dif x &= 1/(s(s-1)) (-(zeta'(s))/(zeta(s))). $
  Moreover, $psi_1 (x) = 1/2 x^2 + O(x^2 exp(-c sqrt(log x)))$, whereas $S_Lambda (x) = x log x - (1 + gamma) x + O(x exp(-c sqrt(log x)))$, where $gamma = 0.5772156649 dots.c$ is the Euler–Mascheroni constant.
]

#proof[
  For $psi_1 (x)$, Fubini's theorem on the finite sum gives
  $ psi_1 (x) &= integral_1^x (sum_(1 <= n <= t) Lambda(n)) dif t \
    &= sum_(1 <= n <= x) Lambda(n) integral_n^x dif t = sum_(1 <= n <= x) Lambda(n)(x - n). $
  For $op("Re")(s) > 1$, substituting this finite sum into the Mellin integral with weight $x^(-s-2)$ and interchanging sum and integral (justified by Tonelli's theorem since $Lambda(n) >= 0$ and $x - n >= 0$) yields
  $ integral_1^oo psi_1 (x) x^(-s-2) dif x &= sum_(n=1)^oo Lambda(n) integral_n^oo (x - n) x^(-s-2) dif x \
    &= sum_(n=1)^oo Lambda(n) (n^(-s))/(s(s+1)) = 1/(s(s+1)) (-(zeta'(s))/(zeta(s))), $
  where we used the elementary evaluation
  $ integral_n^oo (x - n) x^(-s-2) dif x &= [-(x^(-s))/s + n (x^(-s-1))/(s+1)]_n^oo \
    &= (n^(-s))/s - (n^(-s))/(s+1) = (n^(-s))/(s(s+1)). $
  The corresponding identity for $S_Lambda (x)$ is a special case of Theorem 5.3 below, and its asymptotic main term $x log x - (1 + gamma) x$ is derived in Section 5.2.
]

The structural advantage of $S_Lambda (x)$ over $psi_1 (x)$ is immediate from this proposition. Both $psi_1 (x)$ and $S_Lambda (x)$ gain the quadratic vertical decay $|t|^(-2)$ required for absolute convergence of Perron's formula. However, $psi_1 (x)$ inflates the natural scale from $x$ to $x^2$, which shifts the Mellin weight from $x^(-s-1)$ to $x^(-s-2)$ and introduces a factor $1/(s+1)$ rather than $1/(s-1)$. By contrast, $S_Lambda (x)$ remains at the natural linear scale $x$ (up to a logarithmic factor), pairs with the canonical Mellin measure $x^(-s-1) dif x$, and places the extra factor $(s-1)^(-1)$ directly at the pole $s = 1$ of $zeta(s)$. As we will see in Section 5.2, this also means that $S_Lambda (x)$ has a direct interpretation in the Guinand–Weil explicit formula as the convolution of the indicator function with itself, and its nonnegativity properties interact cleanly with the regularized product $P_chi (s) = (s-1) zeta(s) L(s, chi)$.

We now prove the general Mellin transform theorem for $S_a (x)$ under the von Mangoldt domination hypothesis used in the Lean 4 formalization (`Formalism.MellinSgen`).

#theorem(title: "Mellin Transform of " + $S_a (x)$)[
  Let $a : bb(N) -> bb(R)$ be an arithmetic function for which there exists a constant $K >= 0$ such that
  $ |a(n)| <= K Lambda(n) wide "for all" n in bb(N). $
  Then:
  + $S_a : bb(R) -> bb(R)$ is Borel measurable (in fact continuous on $bb(R)$).
  + For every real $sigma > 1$, the function $x |-> |S_a (x)| x^(-sigma - 1)$ is Lebesgue integrable on $(1, oo)$.
  + For every complex number $s in bb(C)$ with $op("Re")(s) > 1$,
    $ integral_1^oo S_a (x) x^(-s-1) dif x = (L(a, s))/(s(s-1)), $
    where $L(a, s) = sum_(n=1)^oo a(n) n^(-s)$ converges absolutely for $op("Re")(s) > 1$.
]

#proof[
  First note that $Lambda(0) = 0$, so $|a(0)| <= K Lambda(0) = 0$ and hence $a(0) = 0$. Continuity (and therefore Borel measurability) of $S_a$ follows from the local finite-sum representation $S_a (x) = sum_(n=1)^(N-1) a(n)(x/n - 1)_+$ on $(-oo, N)$.

  For each integer $n >= 1$ and each complex $s in bb(C)$ with $sigma := op("Re")(s) > 1$, we compute the elementary Mellin transform of the single ramp function $m_n (x) := (x/n - 1)_+$ on $(1, oo)$. Since $m_n (x) = 0$ for $1 < x <= n$ and $m_n (x) = x/n - 1$ for $x >= n$, the integral splits at $x = n$:
  $ integral_1^oo m_n (x) x^(-s-1) dif x &= integral_n^oo (x/n - 1) x^(-s-1) dif x \
    &= 1/n integral_n^oo x^(-s) dif x - integral_n^oo x^(-s-1) dif x. $
  Because $op("Re")(s) > 1$, both integrals converge absolutely:
  $ 1/n integral_n^oo x^(-s) dif x = 1/n dot.c (n^(1-s))/(s-1) = (n^(-s))/(s-1), wide integral_n^oo x^(-s-1) dif x = (n^(-s))/s. $
  Subtracting the second from the first gives the exact identity
  $ integral_1^oo m_n (x) x^(-s-1) dif x = n^(-s) (1/(s-1) - 1/s) = (n^(-s))/(s(s-1)). $
  In particular, taking $s = sigma > 1$ real and noting $m_n (x) >= 0$, we obtain
  $ integral_1^oo |a(n)| m_n (x) x^(-sigma - 1) dif x = (|a(n)| n^(-sigma))/(sigma (sigma - 1)). $
  By the domination hypothesis $|a(n)| <= K Lambda(n)$ and the absolute convergence of $sum_(n=1)^oo Lambda(n) n^(-sigma) = -zeta'(sigma)/zeta(sigma) < oo$ for $sigma > 1$, the series of integrals converges:
  $ sum_(n=1)^oo integral_1^oo |a(n)| m_n (x) x^(-sigma - 1) dif x &= 1/(sigma (sigma - 1)) sum_(n=1)^oo |a(n)| n^(-sigma) \
    &<= K/(sigma (sigma - 1)) (-(zeta'(sigma))/(zeta(sigma))) < oo. $
  For every $x > 1$, the triangle inequality gives
  $ |S_a (x)| x^(-sigma - 1) <= sum_(n=1)^oo |a(n)| m_n (x) x^(-sigma - 1). $
  By Tonelli's theorem for nonnegative measurable functions, the right-hand side is integrable on $(1, oo)$, and hence so is $|S_a (x)| x^(-sigma - 1)$. This proves (2).

  Finally, for any $s in bb(C)$ with $sigma = op("Re")(s) > 1$, set $F_n (x) := a(n) m_n (x) x^(-s-1)$. Then $|F_n (x)| = |a(n)| m_n (x) x^(-sigma - 1)$, so $sum_(n=1)^oo integral_1^oo |F_n (x)| dif x < oo$. Since $S_a (x) x^(-s-1) = sum_(n=1)^oo F_n (x)$ pointwise on $(1, oo)$ (indeed, as a finite sum for each fixed $x$), Fubini's theorem for $L^1$ series permits interchanging the integral and the sum:
  $ integral_1^oo S_a (x) x^(-s-1) dif x &= sum_(n=1)^oo integral_1^oo a(n) m_n (x) x^(-s-1) dif x \
    &= sum_(n=1)^oo (a(n) n^(-s))/(s(s-1)) = (L(a, s))/(s(s-1)). $
  This completes the proof.
]

#remark[
  The hypothesis $|a(n)| <= K Lambda(n)$ is far stronger than necessary for Theorem 5.3: the exact same proof applies to any arithmetic function $a : bb(N) -> bb(C)$ whose Dirichlet series $sum_(n=1)^oo a(n) n^(-s)$ converges absolutely for $op("Re")(s) > 1$ (or for $op("Re")(s) > sigma_a$, yielding the Mellin identity in the half-plane $op("Re")(s) > max(sigma_a, 1)$). The domination bound $|a(n)| <= K Lambda(n)$ is adopted in `Formalism.MellinSgen` because every arithmetic weight arising in the proof — notably $Lambda(n)$ itself (with $K = 1$) and $Lambda_F (chi, n) = Lambda(n)(1 + op("Re")(chi(n)))$ (with $K = 2$) — satisfies it immediately, allowing Mathlib's `LSeriesSummable_vonMangoldt` to discharge all convergence obligations in a single stroke.
]

We conclude this section by establishing the exact Mellin inversion formula (Perron's formula) for $S_Lambda (y)$, which recovers $S_Lambda (y)$ from a single absolutely convergent vertical contour integral.

#theorem(title: "Perron's Formula for " + $S_Lambda (y)$)[
  For every real $y >= 1$ and every real $sigma_0 > 1$, the function
  $ t |-> (-(zeta'(sigma_0 + i t))/(zeta(sigma_0 + i t))) (y^(sigma_0 + i t))/((sigma_0 + i t)(sigma_0 + i t - 1)) $
  is Lebesgue integrable on $bb(R)$, and
  $ S_Lambda (y) &= 1/(2 pi i) integral_(sigma_0 - i oo)^(sigma_0 + i oo) (-(zeta'(w))/(zeta(w))) (y^w)/(w(w-1)) dif w \
    &= 1/(2 pi) integral_(-oo)^oo (-(zeta'(sigma_0 + i t))/(zeta(sigma_0 + i t))) (y^(sigma_0 + i t))/((sigma_0 + i t)(sigma_0 + i t - 1)) dif t. $
]

#proof[
  Write $w = sigma_0 + i t$ with $sigma_0 > 1$ and $t in bb(R)$. Since $sigma_0 > 1$, the Dirichlet series $L(Lambda, w) = -zeta'(w)/zeta(w)$ converges absolutely and satisfies the uniform bound
  $ |-(zeta'(sigma_0 + i t))/(zeta(sigma_0 + i t))| <= sum_(n=1)^oo (Lambda(n))/(n^(sigma_0)) = -(zeta'(sigma_0))/(zeta(sigma_0)) < oo. $
  To bound the denominator from below, set $m := min((sigma_0 - 1)^2, 1) > 0$. Then $m <= 1$ and $m <= (sigma_0 - 1)^2 < sigma_0^2$, so
  $ |w|^2 &= sigma_0^2 + t^2 >= m(1 + t^2), \
    |w - 1|^2 &= (sigma_0 - 1)^2 + t^2 >= m(1 + t^2). $
  Multiplying these two inequalities and taking square roots yields
  $ |w(w - 1)| >= m(1 + t^2) wide "for all" t in bb(R). $
  Since $|y^(sigma_0 + i t)| = y^(sigma_0)$ for $y > 0$, the integrand is bounded in modulus by
  $ ((-(zeta'(sigma_0))/(zeta(sigma_0))) y^(sigma_0))/m dot.c 1/(1 + t^2), $
  which is integrable on $bb(R)$ (with integral $pi$ for $(1+t^2)^(-1)$). Since $t |-> -zeta'(sigma_0 + i t)/zeta(sigma_0 + i t)$ is continuous on $bb(R)$ (as $zeta$ is holomorphic and nonvanishing on $op("Re")(w) > 1$), the integrand is continuous and $L^1$ on $bb(R)$.

  To evaluate the integral, recall the standard Mellin transform convention on $(0, oo)$:
  $ cal(M)[f](z) := integral_0^oo f(x) x^(z - 1) dif x. $
  Since $S_Lambda (x) = 0$ for $0 < x <= 1$, Theorem 5.3 with $s = -z$ gives, for every $z in bb(C)$ with $op("Re")(z) < -1$,
  $ cal(M)[S_Lambda](z) = integral_1^oo S_Lambda (x) x^(z - 1) dif x = (-(zeta'(-z))/(zeta(-z)))/((-z)(-z - 1)) = (-(zeta'(-z))/(zeta(-z)))/(z(z + 1)). $
  By Theorem 5.3(2), $x |-> S_Lambda (x) x^(-sigma_0 - 1)$ is in $L^1 (0, oo)$ (so $cal(M)[S_Lambda]$ converges absolutely at $-sigma_0$). By the integrability bound proved above with $y = 1$, the vertical slice $t |-> cal(M)[S_Lambda](-sigma_0 + i t)$ belongs to $L^1 (bb(R))$. Finally, $S_Lambda$ is continuous at every $y > 0$. By the Mellin inversion theorem (Fourier inversion in logarithmic coordinates $x = e^u$), we conclude that for every $y >= 1$,
  $ S_Lambda (y) &= 1/(2 pi i) integral_(-sigma_0 - i oo)^(-sigma_0 + i oo) cal(M)[S_Lambda](z) y^(-z) dif z \
    &= 1/(2 pi) integral_(-oo)^oo cal(M)[S_Lambda](-sigma_0 + i t) y^(sigma_0 - i t) dif t. $
  Substituting $t |-> -t$ (so $-z = sigma_0 + i t$) and using the formula for $cal(M)[S_Lambda](-w)$ yields the desired identity.
]

The same proof applies verbatim to $S_a (y)$ for any $a$ satisfying $|a(n)| <= K Lambda(n)$, replacing $-zeta'(w)/zeta(w)$ by $L(a, w)$. In particular, for $S_chi (y)$ we obtain an absolutely convergent vertical integral whose integrand is meromorphic on $bb(C)$, setting the stage for both the residue analysis of Section 5.2 and the explicit formula of Section 5.4.

// ============================================================================
// Section 5.2
// ============================================================================
== Cancellation of the Double Pole at $s = 1$

By Theorem 5.3, the Mellin transform of $S_Lambda (x)$ is
$ integral_1^oo S_Lambda (x) x^(-s-1) dif x = 1/(s(s-1)) (-(zeta'(s))/(zeta(s))) wide (op("Re")(s) > 1). $
Because $zeta(s)$ has a simple pole at $s = 1$, its logarithmic derivative $-zeta'(s)/zeta(s)$ also has a simple pole at $s = 1$ with residue $1$. Multiplying by $1/(s(s-1))$ therefore creates a _double pole_ at $s = 1$. If we wish to apply Landau's theorem (Section 5.3) to detect zeros of $zeta(s)$ or $L(s, chi)$ to the left of $op("Re")(s) = 1$, this singularity at $s = 1$ is an obstruction: it forces the abscissa of convergence of the Mellin integral to be at least $1$, completely masking any zeros in the critical strip $0 < op("Re")(s) < 1$. We must therefore subtract from $S_Lambda (x)$ (and from $S_chi (x)$) an explicit elementary function of $x$ whose Mellin transform cancels _both_ the double pole $(s-1)^(-2)$ and the simple pole $(s-1)^(-1)$ at $s = 1$.

We begin by recording the elementary Mellin transforms that generate poles at $s = a$ and double poles at $s = 1$ (`Formalism.MellinElem` in Lean 4).

#lemma(title: "Elementary Mellin Transforms")[
  + For every real $a in bb(R)$ and every $s in bb(C)$ with $op("Re")(s) > a$, the function $x |-> x^a dot.c x^(-s-1)$ is integrable on $(1, oo)$ and
    $ integral_1^oo x^a dot.c x^(-s-1) dif x = 1/(s - a). $
  + For every $s in bb(C)$ with $op("Re")(s) > 1$, the function $x |-> (x log x) x^(-s-1)$ is integrable on $(1, oo)$ and
    $ integral_1^oo (x log x) x^(-s-1) dif x = 1/((s - 1)^2). $
]

#proof[
  For (1), write $sigma = op("Re")(s) > a$. Then $|x^a x^(-s-1)| = x^(a - sigma - 1)$, which is integrable on $(1, oo)$ because $a - sigma < 0$. An antiderivative of $x^(a - s - 1)$ is $x^(a - s)/(a - s)$, which vanishes as $x -> oo$ since $op("Re")(a - s) = a - sigma < 0$, so
  $ integral_1^oo x^(a - s - 1) dif x = [ (x^(a - s))/(a - s) ]_1^oo = - 1/(a - s) = 1/(s - a). $
  For (2), let $sigma = op("Re")(s) > 1$. Substituting $x = e^u$ ($u in (0, oo)$, $dif x = e^u dif u$) gives
  $ integral_1^oo (x log x) x^(-s-1) dif x = integral_0^oo u e^(-(s-1) u) dif u. $
  Since $|u e^(-(s-1) u)| = u e^(-(sigma - 1) u)$ is integrable on $(0, oo)$, integration by parts yields
  $ integral_0^oo u e^(-(s-1) u) dif u &= [ - u/(s - 1) e^(-(s-1) u) ]_0^oo + 1/(s - 1) integral_0^oo e^(-(s-1) u) dif u \
    &= 1/((s - 1)^2). $
]

We now compute the exact Laurent principal part of $(s(s-1))^(-1) (-zeta'(s)/zeta(s))$ at $s = 1$. Recall that the Riemann zeta function has the Laurent expansion
$ zeta(s) = 1/(s - 1) + gamma + O(s - 1) wide (s -> 1), $
where $gamma = lim_(N -> oo) (sum_(n=1)^N 1/n - log N)$ is the Euler–Mascheroni constant. Writing $u = s - 1$, we have $(s-1) zeta(s) = 1 + gamma u + O(u^2)$, so taking logarithmic derivatives gives
$ 1/(s - 1) + (zeta'(s))/(zeta(s)) = dif/(dif s) log((s - 1) zeta(s)) = (gamma + O(u))/(1 + gamma u + O(u^2)) = gamma + O(u). $
Rearranging, we obtain the classical Laurent expansion
$ -(zeta'(s))/(zeta(s)) = 1/u - gamma + O(u) wide (u = s - 1 -> 0). $
On the other hand, near $u = 0$ we have $1/s = 1/(1 + u) = 1 - u + O(u^2)$, and hence
$ 1/(s(s - 1)) = 1/(u(1 + u)) = 1/u - 1 + O(u). $
Multiplying the two expansions gives the exact principal part at $s = 1$:
$ 1/(s(s - 1)) (-(zeta'(s))/(zeta(s))) &= (1/u - 1 + O(u))(1/u - gamma + O(u)) \
  &= 1/(u^2) - (1 + gamma)/u + O(1). $
Comparing this with Lemma 5.6, we see that
$ integral_1^oo (x log x - (1 + gamma) x) x^(-s-1) dif x = 1/((s - 1)^2) - (1 + gamma)/(s - 1). $
Therefore, defining the centered smoothed sum
$ G_Lambda (x) := S_Lambda (x) - x log x + (1 + gamma) x, $
the Mellin transform $integral_1^oo G_Lambda (x) x^(-s-1) dif x$ has a _removable singularity_ at $s = 1$!

We now carry out the exact same cancellation in the character-twisted setting required for the Generalized Riemann Hypothesis, following `Formalism.Statement` and `Formalism.ZetaNonvanishing.Assembly`.

Let $N >= 1$ be a modulus and let $chi : (bb(Z) / N bb(Z))^times -> bb(C)^times$ be a _real, non-principal_ Dirichlet character modulo $N$ (so $chi != 1$ and $op("Im")(chi(n)) = 0$ for all $n in bb(N)$, meaning $chi(n) in {-1, 0, 1}$). We define the twisted von Mangoldt weight
$ Lambda_F (chi, n) := Lambda(n)(1 + op("Re")(chi(n))) = Lambda(n)(1 + chi(n)). $
Observe two fundamental features of $Lambda_F (chi, n)$:
+ *Nonnegativity and domination:* Since $chi(n) in {-1, 0, 1}$, we have $0 <= 1 + chi(n) <= 2$ for every $n in bb(N)$, so $0 <= Lambda_F (chi, n) <= 2 Lambda(n)$. In particular, Theorem 5.3 applies with $K = 2$.
+ *Arithmetic meaning:* When $chi$ is a primitive quadratic character associated with a quadratic number field $K / bb(Q)$, the Dedekind zeta function factors as $zeta_K (s) = zeta(s) L(s, chi)$, and $Lambda_F (chi, n)$ is (up to ramified primes) the von Mangoldt function of $zeta_K (s)$, counting prime ideals of $cal(O)_K$ weighted by the logarithm of their norm.

For $op("Re")(s) > 1$, the Dirichlet series of $Lambda_F (chi, dot.c)$ is
$ L(Lambda_F (chi, dot.c), s) = sum_(n=1)^oo (Lambda(n)(1 + chi(n)))/(n^s) = -(zeta'(s))/(zeta(s)) - (L'(s, chi))/(L(s, chi)). $
Because $chi$ is non-principal, Dirichlet's theorem tells us that $L(s, chi)$ extends to an entire function on $bb(C)$ with $L(1, chi) != 0$. Moreover, since $chi$ is real-valued, $L(s, chi)$ takes real values on the real axis, so $L(1, chi) in bb(R) without {0}$ and $L'(1, chi) in bb(R)$. This motivates defining the _regularized product_ $P_chi (s)$ (`Formalism.Pfun`) and the _generalized Euler constant_ $gamma_chi$ (`Formalism.gammaF`) by
$ P_chi (s) := cases(L(1, chi) & "if" s = 1, (s - 1) zeta(s) L(s, chi) & "if" s != 1,) $
and
$ gamma_chi := gamma + op("Re")((L'(1, chi))/(L(1, chi))). $
(For real $chi$, the real-part operator in $gamma_chi$ is redundant, though keeping it in the definition ensures $gamma_chi in bb(R)$ cleanly in type theory.) Because $(s-1) zeta(s)$ is entire with value $1$ at $s = 1$ and $L(s, chi)$ is entire, $P_chi (s)$ is an _entire_ function of $s in bb(C)$. Moreover, by Hadamard and de la Vallée Poussin's classical nonvanishing theorem on the line $op("Re")(s) = 1$, $P_chi (s) != 0$ for every $s in bb(C)$ with $op("Re")(s) >= 1$ (including $s = 1$, where $P_chi (1) = L(1, chi) != 0$).

#proposition(title: "Logarithmic Derivative Identity for " + $P_chi (s)$)[
  Let $chi$ be a real, non-principal Dirichlet character modulo $N$. Then:
  + For every $s in bb(C)$ with $op("Re")(s) > 1$,
    $ L(Lambda_F (chi, dot.c), s) = -(P_chi' (s))/(P_chi (s)) + 1/(s - 1). $
  + At $s = 1$, the logarithmic derivative of $P_chi$ equals $gamma_chi$:
    $ (P_chi' (1))/(P_chi (1)) = gamma + (L'(1, chi))/(L(1, chi)) = gamma_chi. $
]

#proof[
  For $s != 1$, differentiating $P_chi (s) = (s - 1) zeta(s) L(s, chi)$ by the product rule gives
  $ P_chi' (s) = zeta(s) L(s, chi) + (s - 1) zeta'(s) L(s, chi) + (s - 1) zeta(s) L'(s, chi). $
  When $op("Re")(s) > 1$, both $zeta(s)$ and $L(s, chi)$ are nonzero, so dividing by $P_chi (s) = (s-1) zeta(s) L(s, chi)$ yields
  $ (P_chi' (s))/(P_chi (s)) = 1/(s - 1) + (zeta'(s))/(zeta(s)) + (L'(s, chi))/(L(s, chi)). $
  Negating and adding $1/(s-1)$ gives
  $ -(P_chi' (s))/(P_chi (s)) + 1/(s - 1) = -(zeta'(s))/(zeta(s)) - (L'(s, chi))/(L(s, chi)) = L(Lambda_F (chi, dot.c), s). $
  For (2), since $P_chi (s) = ((s-1) zeta(s)) dot.c L(s, chi)$ is a product of two entire functions that are nonzero at $s = 1$, with $((s-1) zeta(s))|_(s=1) = 1$ and $((s-1) zeta(s))'|_(s=1) = gamma$, we obtain
  $ (P_chi' (1))/(P_chi (1)) = gamma/1 + (L'(1, chi))/(L(1, chi)) = gamma_chi. $
]

Now define the centered character-twisted sum $G_chi (x)$ and, for any parameters $sigma_0 < 1$ and $C in bb(R)$, the shifted tail function $H_(chi, sigma_0, C) (x)$ (`Formalism.G` and `Formalism.Hf`):
$ G_chi (x) &:= S_chi (x) - x log x + (1 + gamma_chi) x, \
  H_(chi, sigma_0, C) (x) &:= G_chi (x) + C x^(sigma_0). $
Let $I_(chi, sigma_0, C) (s)$ (`Formalism.Imel`) denote the Mellin transform of $H_(chi, sigma_0, C)$:
$ I_(chi, sigma_0, C) (s) := integral_1^oo H_(chi, sigma_0, C) (x) x^(-s-1) dif x wide (op("Re")(s) > 1). $

#theorem(title: "Double-Pole Cancellation and the Key Identity")[
  Let $chi$ be a real, non-principal Dirichlet character modulo $N$, let $sigma_0 < 1$, and let $C in bb(R)$. Define the auxiliary rational function $q_0 (s)$ and the meromorphic numerator $A_(chi, sigma_0, C) (s)$ by
  $ q_0 (s) &:= -1 + s(1 + gamma_chi) + (C s (s - 1))/(s - sigma_0), \
    A_(chi, sigma_0, C) (s) &:= -P_chi' (s) + q_0 (s) P_chi (s) \
    &= -P_chi' (s) - P_chi (s) + s(1 + gamma_chi) P_chi (s) + (C s (s - 1))/(s - sigma_0) P_chi (s). $
  Then:
  + *(Key Identity)* For every $s in bb(C)$ with $op("Re")(s) > 1$,
    $ s(s - 1) I_(chi, sigma_0, C) (s) = -(P_chi' (s))/(P_chi (s)) + q_0 (s) = (A_(chi, sigma_0, C) (s))/(P_chi (s)). $
  + *(Exact Cancellation at $s = 1$)* The function $A_(chi, sigma_0, C) (s)$ is holomorphic on $bb(C) without {sigma_0}$ and vanishes at $s = 1$:
    $ A_(chi, sigma_0, C) (1) = 0. $
  + *(Meromorphic Continuation)* The quotient
    $ Phi_(chi, sigma_0, C) (s) := (A_(chi, sigma_0, C) (s) / (s - 1))/(s P_chi (s)) $
    (understood at $s = 1$ via its removable limit $A_(chi, sigma_0, C)' (1) / P_chi (1)$) agrees with $I_(chi, sigma_0, C) (s)$ on $op("Re")(s) > 1$, is holomorphic at $s = 1$, and is meromorphic on $bb(C)$ with poles in the half-plane $op("Re")(s) > max(sigma_0, 0)$ occurring _solely_ at the zeros of $P_chi (s)$ (i.e., the nontrivial zeros of $zeta(s) L(s, chi)$).
]

#proof[
  By linearity of the integral, Theorem 5.3 (applied to $a(n) = Lambda_F (chi, n)$ with $K = 2$), and Lemma 5.6 (using $sigma_0 < 1 < op("Re")(s)$), we have for all $op("Re")(s) > 1$:
  $ I_(chi, sigma_0, C) (s) = (L(Lambda_F (chi, dot.c), s))/(s(s - 1)) - 1/((s - 1)^2) + (1 + gamma_chi)/(s - 1) + C/(s - sigma_0). $
  Substituting Proposition 5.7(1) for $L(Lambda_F (chi, dot.c), s)$ yields
  $ I_(chi, sigma_0, C) (s) &= 1/(s(s - 1)) (-(P_chi' (s))/(P_chi (s)) + 1/(s - 1)) \
    & quad - 1/((s - 1)^2) + (1 + gamma_chi)/(s - 1) + C/(s - sigma_0). $
  Observe the exact algebraic cancellation of the double pole $(s - 1)^(-2)$:
  $ 1/(s(s - 1)^2) - 1/((s - 1)^2) = (1 - s)/(s(s - 1)^2) = - 1/(s(s - 1)). $
  Multiplying the entire identity by $s(s - 1)$ now produces
  $ s(s - 1) I_(chi, sigma_0, C) (s) &= -(P_chi' (s))/(P_chi (s)) - 1 + s(1 + gamma_chi) + (C s(s - 1))/(s - sigma_0) \
    &= -(P_chi' (s))/(P_chi (s)) + q_0 (s), $
  which proves (1).

  For (2), since $P_chi$ is entire and $sigma_0 < 1$, $A_(chi, sigma_0, C)$ is holomorphic on $bb(C) without {sigma_0}$. Evaluating at $s = 1$, the term $C s(s-1) P_chi (s)/(s - sigma_0)$ vanishes because of the factor $s - 1$, leaving
  $ A_(chi, sigma_0, C) (1) &= -P_chi' (1) - P_chi (1) + (1 + gamma_chi) P_chi (1) \
    &= -P_chi' (1) + gamma_chi P_chi (1) = 0, $
  by Proposition 5.7(2).

  For (3), because $A_(chi, sigma_0, C)$ is holomorphic at $s = 1$ and $A_(chi, sigma_0, C) (1) = 0$, the divided difference
  $ d_1 (s) := cases((A_(chi, sigma_0, C) (s))/(s - 1) & "if" s != 1, A_(chi, sigma_0, C)' (1) & "if" s = 1) $
  is holomorphic on $bb(C) without {sigma_0}$. Since $s P_chi (s)$ is entire and nonzero at $s = 1$ (where its value is $L(1, chi) != 0$), the quotient $Phi_(chi, sigma_0, C) (s) = d_1 (s) / (s P_chi (s))$ is holomorphic at $s = 1$, equals $I_(chi, sigma_0, C) (s)$ for $op("Re")(s) > 1$ by (1), and can have poles in $op("Re")(s) > max(sigma_0, 0)$ only where $P_chi (s) = 0$.
]

#insight-box(title: "Why the Divided Difference Works So Cleanly")[
  Notice the remarkable elegance of Theorem 5.8(3), which mirrors the `dslope` construction in `Formalism.ZetaNonvanishing.Assembly`. Rather than expanding $I_(chi, sigma_0, C) (s)$ into a Laurent series and checking that both the $(s-1)^(-2)$ and $(s-1)^(-1)$ coefficients vanish, we clear the denominator $s(s-1) P_chi (s)$ first: the double pole cancels _identically_ in $s(s-1) I_(chi, sigma_0, C) (s)$, reducing the cancellation of the remaining simple pole to a _single pointwise equation_ $A_(chi, sigma_0, C) (1) = 0$. Dividing by $s - 1$ via the slope operator `dslope` then produces a function manifestly holomorphic at $s = 1$.
]

// ============================================================================
// Section 5.3
// ============================================================================
== Landau's Theorem for Dirichlet Integrals with Nonnegative Tails

We now arrive at the centerpiece of the analytic reduction: Edmund Landau's 1905 theorem on Dirichlet integrals with nonnegative tails, together with its quantitative localized refinement on long intervals $[Y, Y^lambda]$. The conceptual miracle of Landau's theorem is that _one-sided_ positivity on the real axis rules out _complex_ oscillations (and hence off-line zeros) in an entire half-plane.

#theorem(title: "Landau's Theorem for Mellin Integrals")[
  Let $f : [1, oo) -> bb(R)$ be a locally Lebesgue integrable function such that there exists $x_0 >= 1$ with
  $ f(x) >= 0 wide "for almost every" x >= x_0. $
  Suppose the Mellin integral
  $ F(s) := integral_1^oo f(x) x^(-s-1) dif x $
  converges absolutely for $op("Re")(s) > sigma_1$ (for some real $sigma_1$). Define the abscissa of convergence
  $ sigma_c := inf { sigma in bb(R) : integral_1^oo |f(x)| x^(-sigma - 1) dif x < oo }. $
  If $-oo < sigma_c < oo$, then $F(s)$ _cannot_ be analytically continued to an open neighborhood of the real point $s = sigma_c$. In other words, if $F(s)$ extends holomorphically to a neighborhood of the real ray $(sigma_0, oo)$ for some $sigma_0 < sigma_1$, then $sigma_c <= sigma_0$, and consequently $F(s)$ extends holomorphically to the entire open half-plane $op("Re")(s) > sigma_0$.
]

#proof[
  Replacing $f(x)$ by $tilde(f)(x) := f(x) dot.c bb(1)_([x_0, oo)) (x)$ changes $F(s)$ by the finite-interval integral
  $ integral_1^(x_0) f(x) x^(-s-1) dif x, $
  which is an _entire_ function of $s in bb(C)$ (by Morera's theorem and dominated convergence, since $|f(x) x^(-s-1)| <= |f(x)| max(1, x_0^(-op("Re")(s) - 1))$ is integrable on $[1, x_0]$). Moreover, subtracting a compactly supported function does not alter the abscissa of convergence $sigma_c$. We may therefore assume without loss of generality that $f(x) >= 0$ for almost every $x >= 1$.

  Suppose for the sake of contradiction that $-oo < sigma_c < oo$ and that $F(s)$ admits an analytic continuation (still denoted $F$) to an open disk $D(sigma_c, r)$ centered at $sigma_c$ with radius $r > 0$. Set $delta := r / 4$, let $sigma_2 := sigma_c + delta$, and consider the open disk $D(sigma_2, 2 delta)$ of radius $2 delta = r / 2$. For any $s in D(sigma_2, 2 delta)$:
  - if $op("Re")(s) > sigma_c$, then $s$ lies in the half-plane of convergence;
  - if $op("Re")(s) <= sigma_c$, then $|s - sigma_c| <= |s - sigma_2| + |sigma_2 - sigma_c| < 2 delta + delta = 3 delta < r$, so $s in D(sigma_c, r)$.

  Thus $F$ is holomorphic on the entire disk $D(sigma_2, 2 delta)$. In particular, its Taylor series centered at $sigma_2$ converges at the real point $s_* := sigma_c - delta / 2 = sigma_2 - 3 delta / 2 in D(sigma_2, 2 delta)$:
  $ F(s_*) = sum_(k=0)^oo (F^((k)) (sigma_2))/(k!) (s_* - sigma_2)^k = sum_(k=0)^oo ((-1)^k F^((k)) (sigma_2))/(k!) (sigma_2 - s_*)^k. $
  Now, for $op("Re")(s) > sigma_c$, differentiating under the integral sign $k$ times (justified by dominated convergence since $(log x)^k x^(-sigma_2 - 1) <= C_(k, epsilon) x^(-(sigma_2 - epsilon) - 1)$ for any $epsilon in (0, sigma_2 - sigma_c)$) gives
  $ (-1)^k F^((k)) (sigma_2) = integral_1^oo f(x) (log x)^k x^(-sigma_2 - 1) dif x. $
  Because $f(x) >= 0$, $log x >= 0$, and $sigma_2 - s_* > 0$, every term in the Taylor series is nonnegative! Substituting the integral representation into the convergent Taylor series and applying Tonelli's theorem for nonnegative measurable functions yields
  $ F(s_*) &= sum_(k=0)^oo 1/(k!) (sigma_2 - s_*)^k integral_1^oo f(x) (log x)^k x^(-sigma_2 - 1) dif x \
           &= integral_1^oo f(x) (sum_(k=0)^oo ((sigma_2 - s_*) log x)^k / (k!)) x^(-sigma_2 - 1) dif x \
           &= integral_1^oo f(x) e^((sigma_2 - s_*) log x) x^(-sigma_2 - 1) dif x \
           &= integral_1^oo f(x) x^(-s_* - 1) dif x. $
  Since $F(s_*) < oo$ and $f(x) >= 0$, this shows that $integral_1^oo |f(x)| x^(-s_* - 1) dif x < oo$ with $s_* = sigma_c - delta / 2 < sigma_c$, contradicting the definition of $sigma_c$ as the infimum of all such real numbers.

  The second assertion follows immediately: if $F$ continues holomorphically to a neighborhood of $(sigma_0, oo)$, then $sigma_c$ cannot lie in $(sigma_0, oo)$, so $sigma_c <= sigma_0$. By definition of $sigma_c$, the Mellin integral then converges absolutely on the entire open half-plane $op("Re")(s) > sigma_0$ and defines a holomorphic continuation of $F$ there.
]

#example(title: "Necessity of the Nonnegativity Hypothesis")[
  The positivity condition $f(x) >= 0$ for $x >= x_0$ is completely indispensable. Consider the oscillatory function $f(x) := x^(sigma_0) cos(gamma_0 log x)$ with $sigma_0 in bb(R)$ and $gamma_0 != 0$. For $op("Re")(s) > sigma_0$, its Mellin transform is
  $ integral_1^oo x^(sigma_0) cos(gamma_0 log x) x^(-s-1) dif x &= 1/2 (1/(s - sigma_0 - i gamma_0) + 1/(s - sigma_0 + i gamma_0)) \
    &= (s - sigma_0)/((s - sigma_0)^2 + gamma_0^2). $
  The abscissa of absolute convergence is $sigma_c = sigma_0$, yet the meromorphic continuation is completely holomorphic at the real point $s = sigma_0$ (its only singularities are the complex conjugate poles $sigma_0 plus.minus i gamma_0$). Similarly, for the alternating Dirichlet eta series $eta(s) = sum_(n=1)^oo (-1)^(n-1) n^(-s) = (1 - 2^(1-s)) zeta(s)$, the abscissa of absolute convergence is $sigma_a = 1$, yet $eta(s)$ is entire! Landau's theorem rules out precisely this phenomenon of "hidden complex singularities" whenever the tail has a definite sign.
]

Combining Theorem 5.8 (double-pole cancellation) with Theorem 5.9 (Landau's theorem) yields our first major nonvanishing criterion.

#corollary(title: "Global One-Sided Nonvanishing Criterion")[
  Let $chi$ be a real, non-principal Dirichlet character modulo $N$, let $sigma_0 in [1/2, 1)$, and suppose that $P_chi (sigma) != 0$ for all real $sigma in (sigma_0, 1)$ (equivalently, $L(sigma, chi) != 0$ on $(sigma_0, 1)$). If there exist constants $C > 0$ and $x_0 >= 1$ such that _either_
  $ G_chi (x) + C x^(sigma_0) >= 0 wide "for all" x >= x_0, $
  _or_
  $ G_chi (x) - C x^(sigma_0) <= 0 wide "for all" x >= x_0, $
  then $zeta(s) L(s, chi) != 0$ for every complex number $s in bb(C)$ with $op("Re")(s) > sigma_0$.
]

#proof[
  Assume first that $H_(chi, sigma_0, C) (x) = G_chi (x) + C x^(sigma_0) >= 0$ for all $x >= x_0$. By Theorem 5.8(3), the Mellin transform $I_(chi, sigma_0, C) (s)$ admits a meromorphic continuation $Phi_(chi, sigma_0, C) (s)$ to $bb(C)$ whose only possible poles in $op("Re")(s) > sigma_0$ are the zeros of $P_chi (s)$. Since $P_chi (s) != 0$ for $op("Re")(s) >= 1$ and, by hypothesis, $P_chi (sigma) != 0$ for all real $sigma in (sigma_0, 1)$, the function $Phi_(chi, sigma_0, C) (s)$ is holomorphic on an open neighborhood of the entire real ray $(sigma_0, oo)$.

  By Theorem 5.9 (Landau's theorem), the abscissa of convergence $sigma_c$ of $I_(chi, sigma_0, C) (s)$ satisfies $sigma_c <= sigma_0$. Consequently, $I_(chi, sigma_0, C) (s)$ converges absolutely and defines a _holomorphic_ function on the entire open half-plane $op("Re")(s) > sigma_0$. By the identity theorem, $Phi_(chi, sigma_0, C) (s)$ has no poles anywhere in $op("Re")(s) > sigma_0$.

  Suppose for contradiction that $rho in bb(C)$ is a zero of $P_chi (s)$ with $op("Re")(rho) > sigma_0$ (hence $op("Re")(rho) in (sigma_0, 1)$), of multiplicity $m >= 1$. Then near $s = rho$,
  $ -(P_chi' (s))/(P_chi (s)) = - m/(s - rho) + O(1), $
  while $q_0 (s)$ is holomorphic at $s = rho$ (as $rho != sigma_0$). Since $rho(rho - 1) != 0$, Theorem 5.8(1) implies that $Phi_(chi, sigma_0, C) (s)$ has a simple pole at $s = rho$ with residue $-m / (rho(rho - 1)) != 0$, contradicting the holomorphy of $Phi_(chi, sigma_0, C)$ in $op("Re")(s) > sigma_0$. Thus $P_chi (s) != 0$, and hence $zeta(s) L(s, chi) != 0$, for all $op("Re")(s) > sigma_0$.

  In the opposite case $G_chi (x) - C x^(sigma_0) <= 0$, we apply the exact same argument to the nonnegative function $-H_(chi, sigma_0, -C) (x) = C x^(sigma_0) - G_chi (x) >= 0$, whose Mellin transform is $-Phi_(chi, sigma_0, -C) (s)$ and has simple poles of residue $+m / (rho(rho - 1)) != 0$ at every zero $rho$ of $P_chi$.
]

#remark(title: "Real Zeros on " + $(0, 1)$)[
  For the Riemann zeta function alone (working with $G_Lambda (x)$ instead of $G_chi (x)$), the hypothesis of no real zeros on $(0, 1)$ is automatic and elementary: for real $sigma in (0, 1)$, the alternating Dirichlet eta series
  $ (1 - 2^(1 - sigma)) zeta(sigma) = sum_(n=1)^oo ((-1)^(n-1))/(n^sigma) = (1 - 1/(2^sigma)) + (1/(3^sigma) - 1/(4^sigma)) + dots.c > 0 $
  is strictly positive while $1 - 2^(1 - sigma) < 0$, forcing $zeta(sigma) < 0$ for all $sigma in (0, 1)$. For Dirichlet $L$-functions $L(s, chi)$, the absence of real zeros in $(0, 1)$ is a famous open problem in full generality (the exclusion of Landau–Siegel zeros), though for fixed small conductors such as $N in {3, 4, 7}$ — the three auxiliary characters `quadraticCharThree`, `quadraticCharFour`, and `quadraticCharacterMod7` appearing in `Formalism.Statement` — nonvanishing on $(0, 1)$ is verified directly by elementary series rearrangements (indeed, $L(sigma, chi_4) = 1 - 3^(-sigma) + 5^(-sigma) - dots.c > 0$ on $(0, oo)$).
]

=== Quantitative Localization on Long Intervals $[Y, Y^lambda]$

Corollary 5.11 is remarkably powerful, but it requires a one-sided bound $G_chi (x) + C x^(sigma_0) >= 0$ for _all_ sufficiently large $x >= x_0$. In the Alpöge–Claude–Riemann proof, however, the automorphic theta-lift and Iwasawa-tower machinery does not produce a uniform bound for all $x$ simultaneously; instead, it yields one-sided bounds on _long intervals_ $[Y, Y^lambda]$ (specifically with $lambda = 3/2$) for arbitrarily large $Y$. To bridge this gap, we need a _quantitative localized_ version of Landau's theorem: if $zeta(s) L(s, chi)$ has a zero off the line $op("Re")(s) = sigma_0$, then $G_chi (x) + C x^(sigma_0)$ must take strictly negative values inside $[Y, Y^lambda]$ once $Y$ is sufficiently large.

The mechanism behind localization is harmonic analysis in the logarithmic variable $u = log x$. As we will prove in Section 5.4 via Perron's formula and contour shifting, the centered prime sum $G_chi (x)$ obeys the explicit formula
$ G_chi (e^u) = - sum_(rho) (e^(rho u))/(rho(rho - 1)) + O_chi (u + 1) wide (u >= 0), $
where the sum runs over all nontrivial zeros $rho = beta + i gamma$ of $zeta(s) L(s, chi)$, counted with multiplicity, and converges absolutely because $sum_rho |rho|^(-2) < oo$. Each non-real conjugate pair $rho = beta + i gamma$, $overline(rho) = beta - i gamma$ contributes a sinusoidal wave
$ -2 op("Re")((e^(rho u))/(rho(rho - 1))) = - (2 e^(beta u))/(|rho(rho - 1)|) cos(gamma u - theta_rho), $
whose period in $u = log x$ is $2 pi / |gamma|$. On the interval $x in [Y, Y^lambda]$, the logarithmic variable $u$ ranges over $[U, lambda U]$ where $U = log Y$, an interval of length $(lambda - 1) U$. As $Y -> oo$, this length tends to infinity and accommodates arbitrarily many oscillations of frequency $gamma$.

To isolate a single frequency $gamma_0$ while preserving nonnegativity in physical space $u in [U, lambda U]$, we construct a compactly supported, nonnegative kernel whose Fourier transform is both nonnegative and rapidly decaying.

#lemma(title: "The Quartic B-Spline Kernel")[
  For any $L > 0$, let $b_L := (4/L) bb(1)_([-L/8, L/8])$ and define the four-fold convolution
  $ w_L := b_L * b_L * b_L * b_L. $
  Then:
  + $w_L$ is continuous, nonnegative, even, supported in $[-L/2, L/2] subset.eq [-L, L]$, and normalized so that $integral_(-L)^L w_L (v) dif v = 1$.
  + Its Fourier transform $hat(w)_L (xi) := integral_(-L)^L w_L (v) e^(-i xi v) dif v$ satisfies
    $ hat(w)_L (xi) = ((sin(xi L / 8))/(xi L / 8))^4 wide (xi in bb(R)), $
    with the convention $hat(w)_L (0) = 1$. In particular, $0 <= hat(w)_L (xi) <= 1$ for all $xi in bb(R)$, and
    $ hat(w)_L (xi) <= min(1, (8/(L |xi|))^4) wide "for all" xi != 0. $
]

#proof[
  Since $b_L >= 0$ is even, supported in $[-L/8, L/8]$, and satisfies $integral_bb(R) b_L (v) dif v = (4/L)(L/4) = 1$, its four-fold convolution $w_L$ is continuous (in fact $C^2$), nonnegative, even, supported in $4 dot.c [-L/8, L/8] = [-L/2, L/2]$, and has total integral $1^4 = 1$. The Fourier transform of $b_L$ is
  $ hat(b)_L (xi) = 4/L integral_(-L/8)^(L/8) e^(-i xi v) dif v = (sin(xi L / 8))/(xi L / 8). $
  Because convolution becomes pointwise multiplication under the Fourier transform, $hat(w)_L (xi) = (hat(b)_L (xi))^4$, which is nonnegative, bounded above by $1$, and bounded by $(8 / (L |xi|))^4$ whenever $xi != 0$ (using $|sin theta| <= 1$).
]

Using $w_L$, we can now prove the quantitative localized Landau criterion.

#theorem(title: "Quantitative Localized Landau Criterion on " + $[Y, Y^lambda]$)[
  Let $chi$ be a real, non-principal Dirichlet character modulo $N$, let $sigma_0 in [1/2, 1)$, let $lambda > 1$ (for instance $lambda = 3/2$), and let $C > 0$. Assume $P_chi (sigma) != 0$ for all real $sigma in (sigma_0, 1)$, and suppose that
  $ Theta := sup { op("Re")(rho) : P_chi (rho) = 0 } > sigma_0 $
  is attained by at least one nontrivial zero $rho_0 = Theta + i gamma_0$ ($gamma_0 > 0$). Then there exists an effective threshold $Y_0 = Y_0 (chi, rho_0, sigma_0, C, lambda) >= 2$ such that for every $Y >= Y_0$:
  + there exists $x_(-) in [Y, Y^lambda]$ with $G_chi (x_(-)) + C x_(-)^(sigma_0) < 0$, and
  + there exists $x_(+) in [Y, Y^lambda]$ with $G_chi (x_(+)) - C x_(+)^(sigma_0) > 0$.
  In particular, neither $G_chi (x) + C x^(sigma_0) >= 0$ nor $G_chi (x) - C x^(sigma_0) <= 0$ can hold throughout $[Y, Y^lambda]$ for any $Y >= Y_0$.
]

#proof[
  We prove (1); the proof of (2) is identical upon reversing the sign of $G_chi$ and shifting the phase by $pi$. Assume for contradiction that $H(x) := G_chi (x) + C x^(sigma_0) >= 0$ for all $x in [Y, Y^lambda]$.

  Set $U := log Y$, $u_0 := ((lambda + 1)/2) U$, and $L := ((lambda - 1)/2) U > 0$, so that $[u_0 - L, u_0 + L] = [U, lambda U]$. For any real phase $phi in bb(R)$, consider the nonnegative test function
  $ K_(L, phi) (v) := w_L (v) (1 + cos(gamma_0 v + phi)) >= 0, $
  supported in $[-L/2, L/2] subset.eq [-L, L]$. Since $H(e^u) >= 0$ on $[u_0 - L, u_0 + L]$ and $e^(-Theta u) > 0$, the integral
  $ J(phi) := integral_(-L)^L H(e^(u_0 + v)) e^(-Theta (u_0 + v)) K_(L, phi) (v) dif v $
  must satisfy $J(phi) >= 0$ for every $phi in bb(R)$.

  We now evaluate $J(phi)$ using the explicit formula $G_chi (e^u) = - sum_rho e^(rho u) / (rho(rho - 1)) + O_chi (u + 1)$. First, observe that the $C x^(sigma_0)$ term and the $O_chi (u + 1)$ error term are negligible as $Y -> oo$: since $u_0 + v >= U = log Y$ for $v in [-L, L]$ and $integral_(-L)^L K_(L, phi) (v) dif v <= 2$, we have
  $ & integral_(-L)^L (C e^(sigma_0 (u_0 + v)) + O_chi (u_0 + v + 1)) e^(-Theta (u_0 + v)) K_(L, phi) (v) dif v \
    & quad <= 2 C Y^(-(Theta - sigma_0)) + O_chi (lambda (log Y + 1) Y^(-Theta)), $
  which tends to $0$ as $Y -> oo$ because $Theta > sigma_0 > 0$.

  Next, substitute the zero sum into the integral. Because $sum_rho |rho(rho - 1)|^(-1) < oo$ and $op("Re")(rho) <= Theta$ for _every_ nontrivial zero $rho$ (by definition of $Theta$), we have $|e^((rho - Theta)(u_0 + v))| <= 1$ uniformly for all $rho$ and all $v in [-L, L]$, so Fubini's theorem justifies interchanging the sum over $rho$ with the integral over $v$:
  $ J(phi) = - sum_rho (e^((rho - Theta) u_0))/(rho(rho - 1)) integral_(-L)^L e^((rho - Theta) v) K_(L, phi) (v) dif v + o_(Y -> oo) (1). $
  We split the sum into the set $cal(Z)_Theta := { rho : P_chi (rho) = 0 "and" op("Re")(rho) = Theta }$ of extremal zeros on the line $op("Re")(s) = Theta$, and the remaining set $cal(Z)_(< Theta)$ of zeros with $beta := op("Re")(rho) < Theta$. For any zero $rho = beta + i gamma in cal(Z)_(< Theta)$, taking absolute values inside the integral directly yields
  $ |integral_(-L)^L e^((beta - Theta)(u_0 + v) + i gamma (u_0 + v)) K_(L, phi) (v) dif v| <= 2 e^((beta - Theta) U) = 2 Y^(-(Theta - beta)). $
  For every $rho in cal(Z)_(< Theta)$, the factor $Y^(-(Theta - beta))$ tends to $0$ as $Y -> oo$, while $|rho(rho - 1)|^(-1)$ is summable over all zeros. By the dominated convergence theorem for series,
  $ sum_(rho in cal(Z)_(< Theta)) (2 Y^(-(Theta - beta)))/(|rho(rho - 1)|) -> 0 wide "as" Y -> oo. $

  It remains to evaluate the contribution of the extremal zeros $rho = Theta + i gamma in cal(Z)_Theta$. For these zeros, $rho - Theta = i gamma$ is purely imaginary, so the $v$-integral evaluates _exactly_ in terms of $hat(w)_L$:
  $ integral_(-L)^L e^(i gamma v) K_(L, phi) (v) dif v &= hat(w)_L (-gamma) + 1/2 e^(i phi) hat(w)_L (-gamma - gamma_0) \
    & quad + 1/2 e^(-i phi) hat(w)_L (-gamma + gamma_0). $
  Since $hat(w)_L$ is even, we may write $hat(w)_L (gamma)$, $hat(w)_L (gamma + gamma_0)$, and $hat(w)_L (gamma - gamma_0)$. Let $m_0 >= 1$ be the multiplicity of $rho_0 = Theta + i gamma_0$ (which equals the multiplicity of $overline(rho)_0 = Theta - i gamma_0$ because $chi$ is real).
  - The pair $rho = rho_0$ and $rho = overline(rho)_0$ contributes:
    - from $hat(w)_L (gamma - gamma_0)$ at $rho = rho_0$: $- 1/2 m_0 e^(-i phi) e^(i gamma_0 u_0) / (rho_0 (rho_0 - 1)) dot.c 1$;
    - from $hat(w)_L (gamma + gamma_0)$ at $rho = overline(rho)_0$: $- 1/2 m_0 e^(i phi) e^(-i gamma_0 u_0) / (overline(rho)_0 (overline(rho)_0 - 1)) dot.c 1$, which is the complex conjugate of the previous term!
    - Together, these two resonant terms sum to
      $ & - m_0 op("Re")((e^(i(gamma_0 u_0 - phi)))/(rho_0 (rho_0 - 1))) \
        & quad = - (m_0)/(|rho_0 (rho_0 - 1)|) cos(gamma_0 u_0 - phi - arg(rho_0 (rho_0 - 1))). $
    - The remaining terms from $rho_0, overline(rho)_0$ involve $hat(w)_L (gamma_0)$ and $hat(w)_L (2 gamma_0)$, both of which are $O((L gamma_0)^(-4)) -> 0$ as $L -> oo$.
  - Every other extremal zero $rho = Theta + i gamma in cal(Z)_Theta without {rho_0, overline(rho)_0}$ has $gamma != 0$ (since $P_chi (Theta) != 0$ by hypothesis) and $gamma != plus.minus gamma_0$. Because the zeros of $P_chi$ are discrete, for each such $rho$ all three frequencies $|gamma|$, $|gamma + gamma_0|$, and $|gamma - gamma_0|$ are strictly positive, so $hat(w)_L (gamma) + hat(w)_L (gamma + gamma_0) + hat(w)_L (gamma - gamma_0) -> 0$ as $L -> oo$ by Lemma 5.13(2). Since each term is bounded by $3$ and $|rho(rho - 1)|^(-1)$ is summable, dominated convergence again implies that the sum over all $rho in cal(Z)_Theta without {rho_0, overline(rho)_0}$ tends to $0$ as $Y -> oo$.

  Putting all pieces together, we have shown that uniformly in $phi in bb(R)$,
  $ J(phi) = - (m_0)/(|rho_0 (rho_0 - 1)|) cos(gamma_0 u_0 - phi - arg(rho_0 (rho_0 - 1))) + o_(Y -> oo) (1). $
  Now choose the phase $phi := gamma_0 u_0 - arg(rho_0 (rho_0 - 1))$ so that the cosine equals $+1$. Then
  $ J(phi) = - (m_0)/(|rho_0 (rho_0 - 1)|) + o_(Y -> oo) (1) < 0 $
  for all sufficiently large $Y >= Y_0$, contradicting $J(phi) >= 0$. Hence $H(x)$ must take strictly negative values on $[Y, Y^lambda]$ for every $Y >= Y_0$.
]

#remark(title: "The Unattained Supremum Case and Turán's Power-Sum Method")[
  What if $Theta = sup { op("Re")(rho) : P_chi (rho) = 0 } > sigma_0$ is _not_ attained — that is, what if there exists a sequence of zeros $rho_n = beta_n + i gamma_n$ with $beta_n arrow.t Theta$ and $|gamma_n| -> oo$, while no zero lies directly on $op("Re")(s) = Theta$? In that setting, the naive domination $|e^((beta - beta_0)(u_0 + v))| <= 1$ fails for zeros with $beta > beta_0$. Nevertheless, the localized oscillation phenomenon remains true: using Turán's power-sum method (as developed by Knapowski, Pintz, and Kaczorowski–Pintz) together with Gaussian kernels truncated to $[Y, Y^lambda]$, one shows that for _any_ nontrivial zero $rho_0 = beta_0 + i gamma_0$ with $beta_0 > sigma_0$ (without assuming $beta_0 = Theta$), the function $G_chi (x)$ still exhibits one-sided oscillations of size $>> x^(beta_0) / |rho_0|^2$ on intervals of the form $[Y, Y^lambda]$ for arbitrarily large $Y$. In fact, in the Alpöge–Claude–Riemann proof, one does not even need to invoke Turán's power-sum theorem when working directly with the global or Iwasawa-averaged positivity functional $W(f)$, to which we now turn.
]

// ============================================================================
// Section 5.4
// ============================================================================
== The Guinand–Weil Explicit Formula and Positivity Functionals $W(f)$

We now derive the Guinand–Weil explicit formula, which simultaneously supplies the exact zero expansion for $G_chi (x)$ used in Section 5.3 and recasts the Riemann Hypothesis as a positivity statement for a linear functional $W(f)$ on test functions.

Recall the completed Riemann zeta function
$ xi(s) := 1/2 s(s - 1) pi^(-s/2) Gamma(s/2) zeta(s), $
which is entire of order $1$, satisfies the functional equation $xi(s) = xi(1 - s)$, and whose zeros are precisely the nontrivial zeros $rho$ of $zeta(s)$ (with the same multiplicities). By Hadamard's factorization theorem,
$ (xi'(s))/(xi(s)) = B + sum_rho (1/(s - rho) + 1/rho), $
where the sum converges absolutely when grouped by conjugate pairs (or with the $1/rho$ renormalization), and $B = -gamma/2 - 1 + 1/2 log(4 pi)$. On the other hand, taking the logarithmic derivative of the definition of $xi(s)$ gives
$ (xi'(s))/(xi(s)) = 1/s + 1/(s - 1) - 1/2 log pi + 1/2 (Gamma'(s/2))/(Gamma(s/2)) + (zeta'(s))/(zeta(s)). $

#theorem(title: "Guinand–Weil Explicit Formula for " + $zeta(s)$)[
  Let $F : bb(R) -> bb(C)$ be an even (or general) function of bounded variation such that $F(u) e^((1/2 + delta)|u|) in L^1 (bb(R))$ and $F'(u) e^((1/2 + delta)|u|) in L^1 (bb(R))$ for some $delta > 0$ (in particular, any Schwartz function or compactly supported piecewise-$C^2$ function $F$). Define its Laplace–Mellin transform
  $ Phi(s) := integral_(-oo)^oo F(u) e^((s - 1/2) u) dif u, $
  which is holomorphic in the strip $-delta < op("Re")(s) < 1 + delta$. Then
  $ sum_rho Phi(rho) &= Phi(1) + Phi(0) \
    & quad - sum_(n=1)^oo (Lambda(n))/sqrt(n) (F(log n) + F(-log n)) + J_oo (F), $
  where the sum on the left runs over all nontrivial zeros $rho$ of $zeta(s)$ (ordered by $|op("Im")(rho)| <= T$ as $T -> oo$), and the archimedean contribution is
  $ J_oo (F) &:= - F(0) log pi \
    & quad + 1/(2 pi) integral_(-oo)^oo Phi(1/2 + i t) op("Re")((Gamma'(1/4 + i t / 2))/(Gamma(1/4 + i t / 2))) dif t. $
]

#proof[
  Fix $sigma_1 := 1 + delta / 2$ and consider a sequence of horizontal heights $T_k -> oo$ chosen so that the distance from $T_k$ to the imaginary part of every nontrivial zero $rho$ is at least $c / log T_k$ (which is possible because the number of zeros in $[T, T + 1]$ is $O(log T)$). Let $cal(R)_k$ be the positively oriented rectangle with vertices $sigma_1 plus.minus i T_k$ and $1 - sigma_1 plus.minus i T_k$. By Cauchy's residue theorem, since $Phi(s)$ is holomorphic inside and on $cal(R)_k$ and $xi'(s)/xi(s)$ has simple poles of residue $m(rho)$ at each nontrivial zero $rho$ of $zeta(s)$,
  $ sum_(|op("Im")(rho)| < T_k) Phi(rho) = 1/(2 pi i) integral_(cal(R)_k) Phi(s) (xi'(s))/(xi(s)) dif s. $
  On the horizontal edges $op("Im")(s) = plus.minus T_k$, integration by parts in the definition of $Phi(s)$ gives $|Phi(sigma plus.minus i T_k)| = O(T_k^(-1))$ uniformly for $sigma in [1 - sigma_1, sigma_1]$, while standard Hadamard product estimates give $|xi'(sigma plus.minus i T_k) / xi(sigma plus.minus i T_k)| = O((log T_k)^2)$ on the avoided heights $T_k$. Thus the horizontal integrals are $O((log T_k)^2 / T_k) -> 0$ as $k -> oo$.

  We are left with the two vertical edges at $op("Re")(s) = sigma_1$ (oriented upward) and $op("Re")(s) = 1 - sigma_1$ (oriented downward). On the left edge, substitute $s |-> 1 - s$ and use the functional equation $xi'(1 - s)/xi(1 - s) = -xi'(s)/xi(s)$:
  $ 1/(2 pi i) integral_(1 - sigma_1 + i T_k)^(1 - sigma_1 - i T_k) Phi(s) (xi'(s))/(xi(s)) dif s = 1/(2 pi i) integral_(sigma_1 - i T_k)^(sigma_1 + i T_k) Phi(1 - s) (xi'(s))/(xi(s)) dif s. $
  Now substitute the decomposition of $xi'(s)/xi(s)$ into both vertical integrals:
  $ (xi'(s))/(xi(s)) = (1/s + 1/(s - 1)) + (-1/2 log pi + 1/2 (Gamma'(s/2))/(Gamma(s/2))) + (zeta'(s))/(zeta(s)). $
  We evaluate the three pieces separately as $k -> oo$:
  + *The prime-power piece $zeta'(s)/zeta(s)$:* On $op("Re")(s) = sigma_1 > 1$, the Dirichlet series $zeta'(s)/zeta(s) = - sum_(n=1)^oo Lambda(n) n^(-s)$ converges uniformly and absolutely. Interchanging sum and integral and applying Fourier inversion to $Phi(sigma_1 + i t) = integral_bb(R) (F(u) e^((sigma_1 - 1/2) u)) e^(i t u) dif u$ yields
    $ & 1/(2 pi i) integral_(sigma_1 - i oo)^(sigma_1 + i oo) Phi(s) (-(zeta'(s))/(zeta(s))) dif s \
      & quad = sum_(n=1)^oo Lambda(n) dot.c 1/(2 pi) integral_(-oo)^oo Phi(sigma_1 + i t) n^(-sigma_1 - i t) dif t \
      & quad = sum_(n=1)^oo (Lambda(n))/sqrt(n) F(log n). $
    Similarly, replacing $Phi(s)$ by $Phi(1 - s)$ (which is the transform of $u |-> F(-u)$) yields $sum_(n=1)^oo (Lambda(n) / sqrt(n)) F(-log n)$. Together, the $zeta'/zeta$ terms contribute $- sum_(n=1)^oo (Lambda(n)/sqrt(n)) (F(log n) + F(-log n))$.
  + *The polar piece $1/s + 1/(s-1)$:* Shifting the contour of $(Phi(s) + Phi(1 - s))(1/s + 1/(s-1))$ from $op("Re")(s) = sigma_1$ to $op("Re")(s) = 1/2$ crosses the simple pole at $s = 1$ with residue $Phi(1) + Phi(0)$. On the critical line $s = 1/2 + i t$, the factor $1/s + 1/(s-1) = (2 s - 1)/(s(s-1)) = (2 i t)/(-1/4 - t^2)$ is purely imaginary and odd in $t$, while $Phi(1/2 + i t) + Phi(1/2 - i t)$ is even in $t$, so the remaining principal-value integral on $op("Re")(s) = 1/2$ vanishes identically! Thus the polar piece contributes exactly $Phi(1) + Phi(0)$.
  + *The archimedean piece:* Shifting $-1/2 log pi + 1/2 Gamma'(s/2)/Gamma(s/2)$ to the critical line $s = 1/2 + i t$ crosses no poles (as $Gamma(s/2)$ is holomorphic and nonvanishing for $op("Re")(s) > 0$). By Fourier inversion, $1/(2 pi) integral_(-oo)^oo (Phi(1/2 + i t) + Phi(1/2 - i t)) dif t = 2 F(0)$, giving $-F(0) log pi$, while the Gamma term simplifies via $Phi(1/2 - i t) = Phi(1/2 + i(-t))$ to $1/(2 pi) integral_(-oo)^oo Phi(1/2 + i t) op("Re")(Gamma'(1/4 + i t / 2) / Gamma(1/4 + i t / 2)) dif t$.

  Combining all three pieces yields the Guinand–Weil explicit formula.
]

For a primitive real Dirichlet character $chi$ modulo $N$, the exact same contour argument applied to the completed $L$-function $xi(s, chi) = (N / pi)^((s + frak(a))/2) Gamma((s + frak(a))/2) L(s, chi)$ (where $frak(a) in {0, 1}$ satisfies $chi(-1) = (-1)^(frak(a))$) gives the twisted explicit formula
$ sum_(rho_chi) Phi(rho_chi) = - sum_(n=1)^oo (Lambda(n) chi(n))/sqrt(n) (F(log n) + F(-log n)) + J_(oo, chi) (F), $
with _no_ polar terms $Phi(1) + Phi(0)$ because $L(s, chi)$ is entire. Adding this to Theorem 5.16 gives the explicit formula for $zeta(s) L(s, chi)$ with prime-power weight $Lambda_F (chi, n) = Lambda(n)(1 + chi(n))$.

=== Multiplicative Form and the Explicit Formula for $G_chi (x)$

It is illuminating to rewrite Theorem 5.16 in multiplicative coordinates $x = e^u in (0, oo)$. Setting $h(x) := x^(-1/2) F(log x)$, we have
$ tilde(h)(s) := integral_0^oo h(x) x^(s - 1) dif x = integral_(-oo)^oo F(u) e^((s - 1/2) u) dif u = Phi(s), $
while $F(log n)/sqrt(n) = h(n)$ and $F(-log n)/sqrt(n) = n^(-1) h(1/n)$. The Guinand–Weil explicit formula therefore takes the compact multiplicative form
$ sum_rho tilde(h)(rho) = tilde(h)(1) + tilde(h)(0) - sum_(n=1)^oo Lambda(n) (h(n) + 1/n h(1/n)) + J_oo (h). $
Notice how directly this recovers the explicit formula for $G_Lambda (X)$ (and $G_chi (X)$) used in Section 5.3! Choosing the continuous, compactly supported ramp function
$ h_X (x) := (X/x - 1) bb(1)_([1, X]) (x) $
(supported on $[1, X]$, so $h_X (1/n) = 0$ for all $n >= 2$, and $h_X (1) = X - 1$), we compute its Mellin transform for $s != 0, 1$:
$ tilde(h)_X (s) &= integral_1^X (X/x - 1) x^(s - 1) dif x = X (X^(s - 1) - 1)/(s - 1) - (X^s - 1)/s \
  &= (X^s)/(s(s - 1)) - X/(s - 1) + 1/s. $
At $s = 1$, taking the limit gives $tilde(h)_X (1) = X log X - X + 1$. Substituting $h_X$ into the explicit formula (or equivalently shifting the Perron contour of Theorem 5.5 left past the double pole at $s = 1$, the nontrivial zeros $rho$, and the simple pole at $s = 0$ to $op("Re")(s) = -1/2$) gives
$ S_Lambda (X) = X log X - (1 + gamma) X - sum_rho (X^rho)/(rho(rho - 1)) + O(log X + 1), $
and hence
$ G_Lambda (X) = - sum_rho (X^rho)/(rho(rho - 1)) + O(log X + 1), $
with the exact analogue for $G_chi (X)$ summing over the nontrivial zeros of $zeta(s) L(s, chi)$.

=== Positivity Functionals $W(f)$ and the Spike-Plus-Indicator Criterion

In Weil's 1952 reformulation of the Riemann Hypothesis, the explicit formula is viewed as a linear distribution $W$ — the _Weil functional_ — acting on test functions. On the geometric (prime) side, $W$ combines the main term at $s = 1$ with the prime-power sum; on the spectral (zero) side, $W$ is the sum over nontrivial zeros $rho$. Weil's celebrated positivity criterion states that RH holds if and only if $W(F * tilde(F)) >= 0$ for every admissible $F$, where $tilde(F)(u) = overline(F(-u))$ so that the spectral side is $sum_rho |Phi(rho)|^2$ on the critical line.

A key strategic insight in the Alpöge–Claude–Riemann proof (recorded in item 6 of Alpöge's timeline notes) is that one does _not_ need to prove Weil positivity for arbitrary convolutions $F * tilde(F)$ in order to rule out zeros in a half-plane $op("Re")(rho) > 1 - eta$. A much simpler one-parameter family of test functions — an indicator function augmented by a tall, narrow positive spike near the origin — already suffices!

Let us make this precise. For a scale parameter $X >= 2$, define the scale-$X$ Weil functional $W_X$ on piecewise-continuous functions $f : (0, oo) -> bb(R)$ supported on $(0, 1]$ by
$ W_X (f) := integral_0^1 f(t) dif t - 1/X sum_(n=1)^oo Lambda(n) f(n/X). $
(Equivalently, $X dot.c W_X (f)$ is the difference between the main term $X integral_0^1 f(t) dif t$ and the weighted prime sum $sum_(n <= X) Lambda(n) f(n/X)$; replacing $Lambda(n)$ by $Lambda_F (chi, n)$ defines the character-twisted functional $W_(X, chi) (f)$.)

Let us test $W_X$ on the two building-block indicators $bb(1)_((0, 1])$ and $bb(1)_((0, 1/X])$:
+ For $f_1 (t) = bb(1)_((0, 1]) (t)$:
  $ W_X (bb(1)_((0, 1])) = 1 - (psi(X))/X. $
+ For $f_2 (t) = bb(1)_((0, 1/X]) (t)$: since $n / X <= 1 / X$ holds only for $n = 1$ (where $Lambda(1) = 0$), the prime sum vanishes identically, leaving
  $ W_X (bb(1)_((0, 1/X])) = 1/X. $

Now form the linear combination of the unit indicator with a spike of width $1/X$ and height $c X^(1 - eta)$ (where $c > 0$ and $eta in (0, 1/2]$):
$ f_(X, eta) (t) := bb(1)_((0, 1]) (t) + c X^(1 - eta) bb(1)_((0, 1/X]) (t). $
(In the dual Mellin normalization where $W$ is paired against $t^(-rho)$ via the functional equation $rho <-> 1 - rho$, the same test function appears as $bb(1)_((0, 1]) + c X^eta bb(1)_((0, 1/X])$, whose Mellin transform at $1 - rho$ is $(1 + c X^(rho - (1 - eta)))/(1 - rho)$ — the exact form noted in item 6 of Alpöge's timeline: $W(bb(1)_((0, 1]) + (tilde.op X^eta) dot.c bb(1)_((0, 1/X])) >= 0$ gives $op("Re")(rho) <= 1 - eta$.)

#proposition(title: "Spike-Plus-Indicator Positivity Criterion")[
  Let $eta in (0, 1/2]$ and $c > 0$.
  + For every $X >= 2$, the positivity inequality
    $ W_X (bb(1)_((0, 1]) + c X^(1 - eta) bb(1)_((0, 1/X])) >= 0 $
    is _algebraically equivalent_ to the one-sided Chebyshev bound
    $ psi(X) - X <= c X^(1 - eta). $
  + More generally, replacing the sharp indicator $bb(1)_((0, 1])$ by the smoothed ramp $r(t) := (1/t - 1) bb(1)_((0, 1]) (t)$ (and including the exact main-term correction $log X - (1 + gamma)$ in $W_X$), the smoothed positivity inequality
    $ W_X^("sm") (r + c X^(1 - eta) bb(1)_((0, 1/X])) >= 0 $
    is equivalent to the one-sided bound $G_Lambda (X) <= c X^(1 - eta)$ (or, with opposite sign, $G_Lambda (X) + c X^(1 - eta) >= 0$).
  + Consequently, if this positivity inequality holds for all $X >= X_0$ (or, by Theorem 5.14, on a sequence of intervals $[Y_k, Y_k^(3/2)]$ with $Y_k -> oo$ in the attained-supremum case), then $zeta(s)$ has _no zeros_ in the half-plane $op("Re")(s) > 1 - eta$. In particular, establishing it for every $eta < 1/2$ implies the Riemann Hypothesis (and the analogous statement for $W_(X, chi)$ implies GRH for $L(s, chi)$).
]

#proof[
  For (1), by linearity of $W_X$ and the two evaluations above,
  $ W_X (bb(1)_((0, 1]) + c X^(1 - eta) bb(1)_((0, 1/X])) &= (1 - (psi(X))/X) + c X^(1 - eta) dot.c 1/X \
    &= (X - psi(X) + c X^(1 - eta))/X. $
  Since $X > 0$, this quantity is nonnegative if and only if $psi(X) - X <= c X^(1 - eta)$.

  To see the same threshold directly on the spectral side in the dual Mellin normalization, compute the Mellin transform of $g_(X, eta) (t) := bb(1)_((0, 1]) (t) + c X^eta bb(1)_((0, 1/X]) (t)$ at $1 - s$:
  $ integral_0^oo g_(X, eta) (t) t^(-s) dif t = 1/(1 - s) + c X^eta dot.c (X^(s - 1))/(1 - s) = (1 + c X^(s - (1 - eta)))/(1 - s). $
  Here the spike contributes a term of magnitude $c |X^(rho - (1 - eta))| / |1 - rho|$ at each zero $rho$: this term decays to $0$ when $op("Re")(rho) < 1 - eta$ and grows like $X^(op("Re")(rho) - (1 - eta))$ when $op("Re")(rho) > 1 - eta$.

  For (2) and (3), once $psi(X) - X <= c X^(1 - eta)$ holds for all $X >= X_0$, integrating against $X / t^2 dif t$ (or working directly with the smoothed ramp $r(t)$) yields the corresponding one-sided bound on $G_Lambda (X)$:
  $ S_Lambda (X) - X log X + (1 + gamma) X &= X integral_1^X (psi(t) - t)/(t^2) dif t + O(log X) \
    &<= c' X^(1 - eta) $
  for a constant $c' = c'(c, eta, X_0) > 0$. Applying Corollary 5.11 (with $sigma_0 = 1 - eta$ and using $zeta(sigma) < 0$ on $(0, 1)$) rules out all zeros of $zeta(s)$ with $op("Re")(s) > 1 - eta$.
]

#insight-box(title: "Why One-Sided Bounds on Sparse Intervals " + $[Y, Y^(3/2)]$ + " Suffice for GRH")[
  Step back and appreciate how dramatically Sections 5.1–5.4 simplify the target for the rest of this monograph. A priori, proving the Generalized Riemann Hypothesis looks like a _two-sided_ cancellation problem at _every_ scale $X$: one expects to have to prove $|psi(X, chi) - delta_chi X| <= C_epsilon X^(1/2 + epsilon)$ for all $X >= 2$.

  Landau's criterion and its localized refinement shatter both of those apparent requirements:
  + *One-sidedness suffices:* We never need both an upper and a lower bound on $G_chi (x)$. Any single-sided inequality $G_chi (x) + C x^(sigma_0) >= 0$ (or $G_chi (x) - C x^(sigma_0) <= 0$) already forbids complex zeros in $op("Re")(s) > sigma_0$, because every non-real zero $rho = beta + i gamma$ forces $G_chi (x)$ to swing in _both_ directions with amplitude $asymp x^beta$. In the automorphic chapters to come, one-sidedness is essential: positivity comes from a Gram determinant or an inner product $chevron.l v, v chevron.r >= 0$, which naturally produces a _lower_ bound (never a two-sided cancellation).
  + *Sparse intervals $[Y, Y^(3/2)]$ suffice:* In logarithmic coordinates $u = log x$, an interval $[Y, Y^(3/2)]$ has length $1/2 log Y$, which grows without bound as $Y -> oo$. Any fixed non-real zero $rho_0 = beta_0 + i gamma_0$ oscillates with fixed period $2 pi / |gamma_0|$ in $u$, so once $log Y >> 1 / |gamma_0|$ the interval $[Y, Y^(3/2)]$ contains arbitrarily many full cycles of the wave. Thus we do not need the automorphic positivity machine to operate at every scale $X$; it suffices to find an infinite sequence of scales $Y_k -> oo$ (constructed via an Iwasawa tower and a Behrend-set / pigeonhole selection) on which the one-sided bound holds across $[Y_k, Y_k^(3/2)]$.
]

// ============================================================================
// Section 5.5
// ============================================================================
== Lean 4 Formalization

Every analytic ingredient developed in Sections 5.1–5.3 has a direct, machine-checked counterpart in the `lean-rh` repository. Rather than working with ad hoc contour shifts at every step, the formalization cleanly separates four modular layers: the definition and Mellin transform of $S_a$, the pole-cancellation assembly for $P_chi$, the Perron inversion formula for $S_Lambda$, and Landau's nonvanishing deduction.

#lean-note(
  title: "Smoothed Sums, Mellin Transforms, Pole Cancellation, and Perron Inversion",
  module: "Formalism.DefsOC, Formalism.ZetaNonvanishing.Assembly, Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron",
)[
  *1. Definition of `Sa` and `MellinSgen` (`Formalism/DefsOC.lean` and `Formalism/ZetaNonvanishing/MellinSgen.lean`).*
  The general smoothed prime-power sum and its Mellin transform specification are defined in `DefsOC.lean` exactly as in Section 5.1:
  ```lean
  def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ :=
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)

  def MellinSgen : Prop :=
    ∀ (a : ℕ → ℝ) (K : ℝ),
      (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
      Measurable (Sa a) ∧
      (∀ σ : ℝ, 1 < σ →
        IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
      ∀ s : ℂ, 1 < s.re →
        ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
          LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))
  ```
  The proof `Formalism.mellinSgen : MellinSgen` in `ZetaNonvanishing/MellinSgen.lean` rewrites `Sa a x` as `∑' n, a n * mxS n x` (where `mxS n x = max (x / n - 1) 0`), proves measurability via `measurable_from_prod_countable` and `Nat.measurable_floor`, establishes `L¹` integrability via `integrable_tsum_of_nonneg` and `LSeriesSummable_vonMangoldt`, and interchanges integral and sum via `integral_tsum_of_summable_integral_norm`.

  *2. Double-pole cancellation and `key_identity` (`Formalism/Statement.lean`, `Formalism/ZetaRealNonvanish.lean`, `Formalism/ZetaNonvanishing/Assembly.lean`).*
  For a Dirichlet character `χ : DirichletCharacter ℂ N`, `Statement.lean` defines:
  - `LamF χ n := Λ n * (1 + (χ n).re)`,
  - `S χ x := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)`,
  - `gammaF χ := Real.eulerMascheroniConstant + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re`,
  - `G χ x := S χ x - x * Real.log x + (1 + gammaF χ) * x`.

  In `ZetaRealNonvanish.lean`, `Pfun χ s` is defined piecewise as `LFunction χ 1` at `s = 1` and `(s - 1) * riemannZeta s * LFunction χ s` otherwise. In `ZetaNonvanishing/Assembly.lean`, the shifted tail `Hf χ σ₀ C x := G χ x + C * x ^ σ₀` and its Mellin transform `Imel χ σ₀ C s` are paired with
  ```lean
  def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
    -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)

  def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
    -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
      + C * s * (s - 1) * Pfun χ s / (s - σ₀)

  def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)
  ```
  The central algebraic lemma `Formalism.key_identity` proves that for `χ ≠ 1`, real `χ`, `σ₀ < 1`, and `1 < s.re`:
  ```lean
  lemma key_identity (hχ : χ ≠ 1) (h3 : MellinS) (h4 : LSeriesLamF) (h5 : MellinElem)
      (hreal : ∀ n : ℕ, (χ n).im = 0) {σ₀ C : ℝ} (hσ₀1 : σ₀ < 1) {s : ℂ}
      (hs : 1 < s.re) :
      s * (s - 1) * Imel χ σ₀ C s = -deriv (Pfun χ) s / Pfun χ s + q0 χ σ₀ C s
  ```
  Notice how `Phi` uses Mathlib's `dslope` (the removable-singularity divided difference) so that holomorphy at `s = 1` reduces directly to `Afun χ σ₀ C 1 = 0`, avoiding any manual Laurent-series arithmetic.

  *3. Perron inversion (`Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean`).*
  The file `Perron.lean` proves `Formalism.ZF.perron_formula : Perron`, establishing the exact contour integral of Theorem 5.5 for `Sz = Sa Λ`. Its key sub-lemmas mirror our proof step by step:
  - `perron_Sz_continuousAt`: continuity of `Sz` at every `y : ℝ` via local finite sums of `Λ n * max (x / n - 1) 0`;
  - `perron_denom_bound`: the explicit lower bound `min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖(σ₀ + t * I) * (σ₀ + t * I - 1)‖`;
  - `perron_integrable_Fy`: vertical $L^1$ integrability of the Perron integrand `Fy y (σ₀ + t * I)` via comparison with `(1 + t ^ 2)⁻¹`;
  - `perron_mellin_Sz`: identification of Mathlib's `mellin (fun x => (Sz x : ℂ)) (-w)` with `-(deriv riemannZeta w / riemannZeta w) / (w * (w - 1))` using `Formalism.mellinSgen`;
  - `perron_formula`: invocation of Mathlib's `mellinInv_mellin_eq` (combining `perron_mellinConvergent`, `perron_verticalIntegrable`, and `perron_Sz_continuousAt`) to conclude the exact inversion identity for all `y ≥ 1` and `σ₀ > 1`.
]

// ============================================================================
// Exercises
// ============================================================================
#exercises((
  [
    *(Higher-order smoothed prime sums).* For an integer $k >= 1$ and an arithmetic function $a : bb(N) -> bb(R)$ satisfying $|a(n)| <= K Lambda(n)$, define the $k$-fold smoothed sum
    $ S_a^((k)) (x) := 1/(k!) sum_(1 <= n <= x) a(n) (x/n - 1)^k. $
    Prove that for every $s in bb(C)$ with $op("Re")(s) > 1$,
    $ integral_1^oo S_a^((k)) (x) x^(-s-1) dif x = (L(a, s))/(s(s - 1) dots.c (s - k)) ? $
    Careful! Compute $integral_n^oo (x/n - 1)^k x^(-s-1) dif x$ explicitly by substituting $x = n t$ (or $u = 1/t$) and show that the correct denominator is $s(s-1) dots.c (s-k)$ only when $op("Re")(s) > k$, with an additional $k!$ factor that cancels $1/k!$. What is the order of the pole at $s = 1$ for $k = 1$ versus $k = 2$?
  ],
  [
    *(Relating $S_Lambda (x)$ and $psi(x)$).* Using the integral representation $S_Lambda (x) = x integral_1^x psi(t) t^(-2) dif t$, prove that if the Prime Number Theorem holds in the form $psi(x) = x + O(x (log x)^(-A))$ for some $A > 1$, then
    $ S_Lambda (x) = x log x - (1 + gamma) x + O(x (log x)^(-(A - 1))). $
    *(Hint: use Mertens's constant or write $S_Lambda (x) - x log x = x integral_1^x (psi(t) - t) t^(-2) dif t$ and evaluate $integral_1^oo (psi(t) - t) t^(-2) dif t$ by letting $s -> 1^+$ in Theorem 5.3.)*
  ],
  [
    *(Exact evaluation of $A'_(chi, sigma_0, C) (1) / P_chi (1)$).* In Theorem 5.8, the value of the meromorphic continuation $Phi_(chi, sigma_0, C) (s)$ at $s = 1$ is $A'_(chi, sigma_0, C) (1) / P_chi (1)$. Express this value explicitly in terms of the Stieltjes constant $gamma_1$ (defined by $zeta(s) = (s-1)^(-1) + gamma - gamma_1 (s-1) + dots.c$), $L(1, chi)$, $L'(1, chi)$, $L''(1, chi)$, $C$, and $sigma_0$.
  ],
  [
    *(Dirichlet series version of Landau's theorem).* Deduce from Theorem 5.9 (or prove directly by the same Taylor-series method) Landau's original 1905 theorem for Dirichlet series: if $a(n) >= 0$ for all $n >= n_0$ and the Dirichlet series $D(s) = sum_(n=1)^oo a(n) n^(-s)$ has finite abscissa of convergence $sigma_c$, then $D(s)$ cannot be analytically continued to a neighborhood of $s = sigma_c$.
  ],
  [
    *(Elementary real nonvanishing for $chi_3$, $chi_4$, and $chi_7$).* Let $chi_4$ be the non-principal Dirichlet character modulo $4$, $chi_3$ the non-principal character modulo $3$, and $chi_7$ the quadratic character modulo $7$ (the Legendre symbol $(dot.c / 7)$).
    (a) Prove directly from the alternating series $L(sigma, chi_4) = sum_(k=0)^oo (-1)^k (2k+1)^(-sigma)$ that $L(sigma, chi_4) > 0$ for all real $sigma > 0$.
    (b) Prove similarly that $L(sigma, chi_3) > 0$ for all real $sigma > 0$.
    (c) By grouping terms in blocks of length $7$ (or using the partial-sum positivity $sum_(n=1)^m chi_7 (n) >= 0$ for all $m >= 1$ together with Abel summation), prove that $L(sigma, chi_7) > 0$ for all real $sigma > 0$.
  ],
  [
    *(Sharpness of the interval length in Theorem 5.14).* Suppose $zeta(s)$ had a simple pair of extremal zeros $rho_0 = Theta + i gamma_0$ and $overline(rho)_0 = Theta - i gamma_0$ ($Theta > 1/2$, $gamma_0 > 0$) and no other zeros on $op("Re")(s) = Theta$. Show that in Theorem 5.14 one can replace the interval $[Y, Y^lambda]$ (which has growing logarithmic length $(lambda - 1) log Y$) by the multiplicative interval $[Y, c Y]$ for any constant $c > exp(pi / gamma_0)$, provided $Y$ is sufficiently large. Why does $[Y, Y^lambda]$ (with any fixed $lambda > 1$) remain necessary when there may be _multiple_ zeros on the line $op("Re")(s) = Theta$?
  ],
  [
    *(Explicit formula for the Gaussian test function).* Apply Theorem 5.16 to the Gaussian test function $F_t (u) := (4 pi t)^(-1/2) exp(-u^2 / (4 t))$ ($t > 0$). Compute $Phi_t (s)$ explicitly, show that the spectral side is $sum_rho exp(t(rho - 1/2)^2)$, and verify that as $t -> 0^+$ the main term $Phi_t (1) + Phi_t (0)$ grows like $2 exp(t/4)$ while the archimedean term exhibits a logarithmic singularity.
  ],
  [
    *(Nonnegativity of $W$ on convolutions and Weil's criterion).* For an admissible function $F : bb(R) -> bb(C)$, define $tilde(F)(u) := overline(F(-u))$ and $(F * tilde(F))(u) := integral_bb(R) F(u + v) overline(F(v)) dif v$.
    (a) Show that the Laplace–Mellin transform of $F * tilde(F)$ satisfies $Phi_(F * tilde(F)) (s) = Phi_F (s) overline(Phi_F (1 - overline(s)))$.
    (b) Deduce that if the Riemann Hypothesis holds, then $sum_rho Phi_(F * tilde(F)) (rho) >= 0$ for every admissible $F$.
    (c) Conversely, assuming that $sum_rho Phi_(F * tilde(F)) (rho) >= 0$ for every $F in C_c^oo (bb(R))$, prove that every nontrivial zero $rho$ of $zeta(s)$ satisfies $op("Re")(rho) = 1/2$. *(Hint: if $rho_0 = beta_0 + i gamma_0$ had $beta_0 > 1/2$, construct $Phi_F$ concentrated near $rho_0$ and $1 - overline(rho)_0$ with opposite signs, or use a meromorphic approximation.)*
  ],
  [
    *(Removing a pole of order $2$ via iterated `dslope`).* Let $U subset.eq bb(C)$ be an open set containing $s = 1$, and let $f : U -> bb(C)$ be holomorphic. Define the slope operator $op("dslope")(f, 1)(s) := (f(s) - f(1))/(s - 1)$ for $s != 1$ and $f'(1)$ for $s = 1$.
    (a) Prove that $op("dslope")(f, 1)$ is holomorphic on $U$.
    (b) Suppose $g(s)$ has a pole of order at most $2$ at $s = 1$, so that $h(s) := (s - 1)^2 g(s)$ is holomorphic on $U$. Show that $g(s)$ has a removable singularity at $s = 1$ if and only if $h(1) = 0$ and $op("dslope")(h, 1)(1) = 0$, in which case $g(s) = op("dslope")(op("dslope")(h, 1), 1)(s)$ on $U without {1}$. Compare this with how `Formalism.ZetaNonvanishing.Assembly` avoids iterating `dslope` twice by canceling the $(s-1)^(-2)$ term algebraically in `key_identity`.
  ],
))
]
