// ============================================================================
// Chapter 1: Riemann's 1859 Memoir and the Zeta Function
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch01() = [
  #chapter(
    "Riemann's 1859 Memoir and the Zeta Function",
    short-title: "Riemann's 1859 Memoir",
    epigraph: "Man findet nun in der That etwa so viel reelle Wurzeln innerhalb dieser Grenzen, und es ist sehr wahrscheinlich, dass alle Wurzeln reell sind. Hiervon wäre allerdings ein strenger Beweis zu wünschen; ich habe indess die Aufsuchung desselben nach einigen flüchtigen vergeblichen Versuchen vorläufig bei Seite gelassen, da er für den nächsten Zweck meiner Untersuchung entbehrlich schien.",
    epigraph-source: "Bernhard Riemann, Über die Anzahl der Primzahlen unter einer gegebenen Grösse (1859)",
    overview: [
      In November 1859, on the occasion of his election to the Berlin Academy of Sciences, Bernhard Riemann submitted an eight-page memoir that permanently transformed number theory. By extending Euler's real-variable series $zeta(s) = sum_(n=1)^oo n^(-s)$ into the complex plane, Riemann revealed that the distribution of prime numbers is governed by the complex zeros of a meromorphic function satisfying a striking reflection symmetry. This chapter develops the classical analytic theory of $zeta(s)$ from first principles: Euler's product and the logarithmic derivative, Jacobi's theta function and the functional equation, the trivial zeros and Mertens' nonvanishing theorem on the line $op("Re")(s) = 1$, the Hadamard factorization and Riemann–von Mangoldt zero-counting formula, Perron's integral and the explicit formula for Chebyshev's function $psi(x)$, and finally the precise formalization of the Riemann Hypothesis in Lean 4.
    ],
    label-name: "ch-riemann-memoir",
  )

  == From Euler's Product to Complex Analysis

  The study of prime numbers entered the domain of analysis in 1737, when Leonhard Euler published *Variae observationes circa series infinitas*. For a real parameter $s > 1$, Euler considered the $p$-series
  $ zeta(s) = sum_(n=1)^oo 1 / n^s, $
  which converges by comparison with the improper integral $integral_1^oo x^(-s) dif x = 1 / (s - 1)$. Using the unique factorization of every positive integer into prime powers, Euler discovered that this sum factors into an infinite product indexed exclusively by the prime numbers $p in cal(P) = {2, 3, 5, 7, dots.c}$. Earlier, in 1734, he had already startled the mathematical world by solving the Basel problem, proving $zeta(2) = pi^2 / 6$, and more generally expressing $zeta(2k)$ as a rational multiple of $pi^(2k)$ involving Bernoulli numbers. Yet for more than a century after Euler, $zeta(s)$ was viewed primarily as a function of a real variable $s > 1$ (and occasionally as a formal or real-analytic object at $s = 1$).

  Riemann's decisive conceptual leap in 1859 was to replace the real variable $s > 1$ by a complex variable $s = sigma + i t in bb(C)$, where $sigma = op("Re")(s)$ and $t = op("Im")(s)$ are real numbers, and to interpret $n^(-s) = exp(-s log n)$. In the open half-plane $op("Re")(s) > 1$, the complex series behaves with complete regularity, and its analytic properties encode multiplicative arithmetic.

  #definition(title: "The Riemann Zeta Function on the Half-Plane of Convergence")[
    For $s = sigma + i t in bb(C)$ with $sigma > 1$, the *Riemann zeta function* is defined by the Dirichlet series
    $ zeta(s) = sum_(n=1)^oo n^(-s) = sum_(n=1)^oo exp(-s log n). $
  ]

  #proposition(title: "Absolute Convergence and Holomorphicity")[
    The series $sum_(n=1)^oo n^(-s)$ converges absolutely for every $s in bb(C)$ with $op("Re")(s) > 1$, and converges uniformly on every closed half-plane ${s in bb(C) : op("Re")(s) >= 1 + delta}$ with $delta > 0$. Consequently, $zeta(s)$ is holomorphic on the open half-plane ${s in bb(C) : op("Re")(s) > 1}$, and its derivatives are obtained by termwise differentiation:
    $ zeta^((k))(s) = (-1)^k sum_(n=1)^oo (log n)^k n^(-s) quad (op("Re")(s) > 1, space k >= 0). $
  ]

  #proof[
    For $s = sigma + i t$ with $sigma >= 1 + delta > 1$, we have
    $ |n^(-s)| = |exp(-(sigma + i t) log n)| = n^(-sigma) <= n^(-1 - delta). $
    Since the majorant series $sum_(n=1)^oo n^(-1 - delta)$ converges (as $sum_(n=2)^oo n^(-1-delta) <= integral_1^oo x^(-1-delta) dif x = 1 / delta$), the Weierstrass $M$-test guarantees uniform and absolute convergence on ${op("Re")(s) >= 1 + delta}$. Each term $s |-> n^(-s)$ is entire, so by Weierstrass's theorem on uniform limits of holomorphic functions on compact subsets, $zeta(s)$ is holomorphic on ${op("Re")(s) > 1}$ and may be differentiated term by term arbitrarily many times.
  ]

  Before passing to the global analytic continuation in Section 1.2, it is already instructive to see how elementary summation by parts extends $zeta(s)$ across the line $op("Re")(s) = 1$ to the half-plane $op("Re")(s) > 0$, exposing the pole at $s = 1$.

  #proposition(title: "Elementary Continuation to Re(s) > 0")[
    For $op("Re")(s) > 1$, let ${x} = x - floor(x)$ denote the fractional part of $x >= 1$. Then
    $ zeta(s) = 1 / (s - 1) + 1 - s integral_1^oo {x} / x^(s+1) dif x. $
    The integral on the right-hand side converges absolutely and locally uniformly on ${op("Re")(s) > 0}$, thereby providing a meromorphic continuation of $zeta(s)$ to the half-plane $op("Re")(s) > 0$ whose only singularity is a simple pole at $s = 1$ with residue $1$. Moreover,
    $ lim_(s -> 1) (zeta(s) - 1 / (s - 1)) = gamma, $
    where $gamma = lim_(N -> oo) (sum_(n=1)^N 1 / n - log N) approx 0.5772156649$ is the Euler–Mascheroni constant.
  ]

  #proof[
    For $op("Re")(s) > 1$ and any integer $N >= 1$, writing $floor(x) = x - {x}$ and integrating by parts on each unit interval $[n, n+1]$ yields
    $ sum_(n=1)^N n^(-s) = 1 + integral_1^N x^(-s) dif floor(x) = 1 + N^(1-s) - 1 + s integral_1^N floor(x) x^(-s-1) dif x. $
    Substituting $floor(x) = x - {x}$ and evaluating $s integral_1^N x^(-s) dif x = s / (s - 1) (1 - N^(1-s))$, we obtain
    $ sum_(n=1)^N n^(-s) = 1 / (s - 1) + 1 - N^(1-s) / (s - 1) - s integral_1^N {x} / x^(s+1) dif x. $
    Since $op("Re")(s) > 1$, we have $N^(1-s) -> 0$ as $N -> oo$, establishing the displayed identity. Because $0 <= {x} < 1$, the integrand satisfies $|{x} x^(-s-1)| <= x^(-op("Re")(s)-1)$, which is integrable on $[1, oo)$ uniformly on ${op("Re")(s) >= delta}$ for every $delta > 0$. Thus the right-hand side defines a holomorphic function on ${op("Re")(s) > 0} without {1}$ with a simple pole of residue $1$ at $s = 1$. Evaluating the constant term at $s = 1$ gives $1 - integral_1^oo {x} x^(-2) dif x = lim_(N -> oo) (sum_(n=1)^N 1/n - log N) = gamma$.
  ]

  We now turn to the bridge between $zeta(s)$ and the prime numbers: Euler's product formula.

  #theorem(title: "Euler Product Formula, 1737")[
    For every $s in bb(C)$ with $op("Re")(s) > 1$, the infinite product over all primes converges absolutely and satisfies
    $ zeta(s) = product_p (1 - p^(-s))^(-1). $
    In particular, $zeta(s) != 0$ for all $s in bb(C)$ with $op("Re")(s) > 1$.
  ]

  #proof[
    Fix $s = sigma + i t$ with $sigma > 1$. For every prime $p$, we have $|p^(-s)| = p^(-sigma) <= 2^(-sigma) < 1$, so the geometric series $(1 - p^(-s))^(-1) = sum_(k=0)^oo p^(-k s)$ converges absolutely. For any real $X >= 2$, consider the finite product
    $ P_X (s) = product_(p <= X) (1 - p^(-s))^(-1) = product_(p <= X) (sum_(k=0)^oo p^(-k s)). $
    Since a finite product of absolutely convergent series may be expanded and rearranged freely, the Fundamental Theorem of Arithmetic implies that
    $ P_X (s) = sum_(n in cal(S)(X)) n^(-s), $
    where $cal(S)(X)$ denotes the set of $X$-smooth positive integers (those all of whose prime factors are $<= X$). Every positive integer $n <= X$ belongs to $cal(S)(X)$, so the difference $zeta(s) - P_X (s)$ is the sum of $n^(-s)$ over those integers $n > X$ that have at least one prime factor exceeding $X$. Therefore
    $ |zeta(s) - P_X (s)| <= sum_(n > X) n^(-sigma). $
    Because $sum_(n=1)^oo n^(-sigma) < oo$, the tail vanishes as $X -> oo$, proving $lim_(X -> oo) P_X (s) = zeta(s)$.

    To verify absolute convergence of the infinite product and nonvanishing of $zeta(s)$, note that $|p^(-s)| = p^(-sigma)$ and $sum_p p^(-sigma) <= sum_(n=1)^oo n^(-sigma) < oo$. Recall that an infinite product $product_p (1 - a_p)^(-1)$ with $a_p != 1$ and $sum_p |a_p| < oo$ converges to a nonzero limit: specifically, using $|log(1 - z)| <= 2 |z|$ for $|z| <= 1/2$ (principal branch), the series $-sum_p log(1 - p^(-s))$ converges absolutely for $op("Re")(s) > 1$. Exponentiating shows
    $ zeta(s) = exp(-sum_p log(1 - p^(-s))) != 0 $
    throughout the half-plane $op("Re")(s) > 1$.
  ]

  Euler immediately deduced from the divergence of the harmonic series $sum_(n=1)^oo 1/n = oo$ not merely Euclid's theorem that there are infinitely many primes, but the quantitatively stronger assertion that the sum of the reciprocals of the primes diverges.

  #corollary(title: "Euler's Theorem on Prime Reciprocals")[
    The series $sum_p 1 / p$ diverges; more precisely, as $sigma -> 1^+$,
    $ sum_p 1 / p^sigma = log(1 / (sigma - 1)) + O(1). $
  ]

  #proof[
    For real $sigma > 1$, taking the real logarithm of the Euler product and expanding $-log(1 - x) = sum_(k=1)^oo x^k / k$ for $0 < x < 1$ gives
    $ log zeta(sigma) = sum_p sum_(k=1)^oo 1 / (k p^(k sigma)) = sum_p 1 / p^sigma + sum_p sum_(k=2)^oo 1 / (k p^(k sigma)). $
    The double sum over $k >= 2$ is bounded uniformly in $sigma > 1$:
    $ 0 <= sum_p sum_(k=2)^oo 1 / (k p^(k sigma)) &<= 1 / 2 sum_p sum_(k=2)^oo 1 / p^k = 1 / 2 sum_p 1 / (p(p - 1)) \ &<= 1 / 2 sum_(n=2)^oo 1 / (n(n - 1)) = 1 / 2. $
    On the other hand, Proposition 1.2 gives $zeta(sigma) = 1 / (sigma - 1) + O(1)$ as $sigma -> 1^+$, hence $log zeta(sigma) = log(1 / (sigma - 1)) + O(1)$. Subtracting the bounded $k >= 2$ contribution yields the asymptotic formula and shows that $sum_p p^(-sigma) -> oo$ as $sigma -> 1^+$, forcing $sum_p 1/p = oo$.
  ]

  The logarithmic derivative of the Euler product replaces the multiplicative structure of $zeta(s)$ by an additive Dirichlet series supported exclusively on prime powers. This motivates the von Mangoldt function, which is the natural arithmetic weight in analytic prime number theory.

  #definition(title: "The von Mangoldt Function")[
    The *von Mangoldt function* $Lambda : bb(N)_(>= 1) -> bb(R)_(>= 0)$ is defined by
    $ Lambda(n) = cases(log p & "if" n = p^k "for a prime" p "and integer" k >= 1, 0 & "otherwise.") $
  ]

  Notice that the fundamental arithmetic identity $sum_(d | n) Lambda(d) = log n$ is an immediate reformulation of unique factorization: writing $n = product_i p_i^(a_i)$, the divisors of $n$ that are prime powers are $p_i^k$ for $1 <= k <= a_i$, whose $Lambda$-values sum to $sum_i a_i log p_i = log n$.

  #proposition(title: "Logarithmic Derivative of the Zeta Function")[
    For every $s in bb(C)$ with $op("Re")(s) > 1$,
    $ - (zeta'(s)) / zeta(s) = sum_(n=1)^oo (Lambda(n)) / n^s, $
    with absolute convergence on ${op("Re")(s) > 1}$ and uniform convergence on ${op("Re")(s) >= 1 + delta}$ for every $delta > 0$.
  ]

  #proof[
    For $op("Re")(s) >= 1 + delta > 1$, the proof of Theorem 1.3 established that the holomorphic function $L(s) = -sum_p log(1 - p^(-s))$ converges uniformly and satisfies $exp(L(s)) = zeta(s)$. Differentiating termwise gives
    $ (zeta'(s)) / zeta(s) = L'(s) = - sum_p (p^(-s) log p) / (1 - p^(-s)) = - sum_p sum_(k=1)^oo (log p) / p^(k s). $
    Since $sum_p sum_(k=1)^oo (log p) p^(-k sigma) <= sum_(n=1)^oo (log n) n^(-sigma) < oo$ for $sigma > 1$, we may rearrange the absolutely convergent double sum by grouping terms with $n = p^k$. By definition of $Lambda(n)$, this yields $-(zeta'(s)) / zeta(s) = sum_(n=1)^oo Lambda(n) n^(-s)$.
  ]

  Alternatively, one may deduce Proposition 1.6 directly from the Dirichlet convolution identity $Lambda * 1 = log$: multiplying the absolutely convergent series $(sum_(d=1)^oo Lambda(d) d^(-s)) (sum_(m=1)^oo m^(-s)) = sum_(n=1)^oo (sum_(d | n) Lambda(d)) n^(-s) = sum_(n=1)^oo (log n) n^(-s) = -zeta'(s)$ and dividing by $zeta(s) != 0$ gives the same formula without invoking branches of the logarithm.

  #remark[
    The passage from $zeta(s)$ to $-zeta'(s)/zeta(s)$ has a decisive analytic advantage: whereas a zero of $zeta(s)$ of multiplicity $m$ at $s = rho$ is a somewhat passive vanishing condition, it becomes a *simple pole* of $-zeta'(s)/zeta(s)$ with residue $-m$, while the simple pole of $zeta(s)$ at $s = 1$ becomes a simple pole of $-zeta'(s)/zeta(s)$ with residue $+1$. This residue calculus is the engine behind both Mertens' nonvanishing proof (Section 1.3) and Riemann's explicit formula (Section 1.4).
  ]

  == Analytic Continuation and the Functional Equation

  Proposition 1.2 extended $zeta(s)$ to $op("Re")(s) > 0$, but the Euler–Maclaurin method alone does not expose the deep symmetry connecting $s$ and $1 - s$. In his 1859 memoir, Riemann gave two proofs of the global meromorphic continuation and functional equation of $zeta(s)$: the first via a Hankel contour integral for $(e^x - 1)^(-1)$, and the second via the Mellin transform of Jacobi's theta function. The second proof is not only cleaner and more conceptual, it is also the direct ancestor of Hecke's theory of modular $L$-functions, Tate's adelic thesis, and the theta-correspondence machinery developed in Parts II and III of this monograph. We present it here with complete rigor.

  === Preliminaries on the Gamma Function

  For $op("Re")(s) > 0$, Euler's Gamma function is defined by the Mellin integral
  $ Gamma(s) = integral_0^oo e^(-t) t^(s-1) dif t. $
  Integration by parts yields the functional equation $Gamma(s + 1) = s Gamma(s)$ for $op("Re")(s) > 0$. Iterating this identity in the form
  $ Gamma(s) = (Gamma(s + k + 1)) / (s (s + 1) dots.c (s + k)) $
  extends $Gamma(s)$ meromorphically to all of $bb(C)$, with simple poles at the nonpositive integers $s = -k$ ($k = 0, 1, 2, dots.c$) and residues
  $ op("Res")_(s = -k) Gamma(s) = (-1)^k / k!. $
  In particular, $op("Res")_(s = 0) Gamma(s) = 1$, and $Gamma(1/2) = integral_0^oo e^(-t) t^(-1/2) dif t = 2 integral_0^oo e^(-u^2) dif u = sqrt(pi)$. Furthermore, Euler's reflection formula
  $ Gamma(s) Gamma(1 - s) = pi / sin(pi s) quad (s in bb(C) without bb(Z)) $
  implies that $Gamma(s)$ has no zeros anywhere in $bb(C)$, so $1 / Gamma(s)$ is an entire function whose zeros are precisely the simple zeros at $s = 0, -1, -2, dots.c$. We will also need Legendre's duplication formula
  $ Gamma(s) = pi^(-1/2) 2^(s - 1) Gamma(s / 2) Gamma((s + 1) / 2) $
  and Stirling's asymptotic formula: for any fixed $delta > 0$, in the sector $|op("arg")(s)| <= pi - delta$,
  $ log Gamma(s) = (s - 1 / 2) log s - s + 1 / 2 log(2 pi) + O_delta (1 / |s|) quad (|s| -> oo), $
  which implies on every vertical strip $a <= sigma <= b$ as $|t| -> oo$ that
  $ |Gamma(sigma + i t)| = sqrt(2 pi) |t|^(sigma - 1/2) e^(-pi |t| / 2) (1 + O_(a,b) (1 / |t|)). $

  === Poisson Summation and Jacobi's Theta Function

  Let $cal(S)(bb(R))$ denote the Schwartz space of smooth functions $f : bb(R) -> bb(C)$ all of whose derivatives decay faster than any polynomial, i.e., $sup_(x in bb(R)) |x^j f^((k))(x)| < oo$ for all integers $j, k >= 0$. We normalize the Fourier transform on $cal(S)(bb(R))$ by
  $ hat(f)(xi) = integral_(-oo)^oo f(x) e^(-2 pi i x xi) dif x. $

  #lemma(title: "Poisson Summation Formula")[
    For every Schwartz function $f in cal(S)(bb(R))$,
    $ sum_(n in bb(Z)) f(n) = sum_(m in bb(Z)) hat(f)(m), $
    with both series converging absolutely.
  ]

  #proof[
    Define the periodization $F(x) = sum_(n in bb(Z)) f(x + n)$. Because $f in cal(S)(bb(R))$, the series for $F$ and all its termwise derivatives converge uniformly on compact subsets of $bb(R)$, so $F$ is a smooth $1$-periodic function. Its $m$-th Fourier coefficient is
    $ hat(F)(m) &= integral_0^1 F(x) e^(-2 pi i m x) dif x = sum_(n in bb(Z)) integral_0^1 f(x + n) e^(-2 pi i m (x + n)) dif x \ &= integral_(-oo)^oo f(y) e^(-2 pi i m y) dif y = hat(f)(m), $
    where the interchange of summation and integration is justified by dominated convergence since $sum_(n in bb(Z)) sup_(x in [0,1]) |f(x+n)| < oo$. Moreover, integration by parts twice shows that $|hat(f)(m)| <= C (1 + m^2)^(-1)$, so the Fourier series $sum_(m in bb(Z)) hat(f)(m) e^(2 pi i m x)$ converges uniformly to $F(x)$ for all $x in bb(R)$. Evaluating at $x = 0$ gives $F(0) = sum_(n in bb(Z)) f(n) = sum_(m in bb(Z)) hat(f)(m)$.
  ]

  #definition(title: "Jacobi's Theta Function")[
    For real $t > 0$, *Jacobi's theta function* is defined by
    $ theta(t) = sum_(n in bb(Z)) e^(-pi n^2 t) = 1 + 2 psi(t), quad "where" quad psi(t) = sum_(n=1)^oo e^(-pi n^2 t). $
  ]

  #proposition(title: "Modular Transformation of the Theta Function")[
    For every $t > 0$,
    $ theta(1 / t) = t^(1/2) theta(t), $
    or equivalently,
    $ psi(1 / t) = t^(1/2) psi(t) + 1 / 2 (t^(1/2) - 1). $
  ]

  #proof[
    First compute the Fourier transform of the standard Gaussian $g(x) = e^(-pi x^2) in cal(S)(bb(R))$. Differentiating $hat(g)(xi) = integral_(-oo)^oo e^(-pi x^2 - 2 pi i x xi) dif x$ under the integral sign and integrating by parts yields
    $ hat(g)'(xi) &= integral_(-oo)^oo (-2 pi i x) e^(-pi x^2) e^(-2 pi i x xi) dif x \ &= i integral_(-oo)^oo (dif / (dif x) e^(-pi x^2)) e^(-2 pi i x xi) dif x = -2 pi xi hat(g)(xi). $
    Thus $dif / (dif xi) (e^(pi xi^2) hat(g)(xi)) = 0$, so $hat(g)(xi) = hat(g)(0) e^(-pi xi^2)$. Since $hat(g)(0) = integral_(-oo)^oo e^(-pi x^2) dif x = 1$, we have $hat(g)(xi) = e^(-pi xi^2)$.

    Now fix $t > 0$ and set $f_t (x) = e^(-pi t x^2) = g(t^(1/2) x)$. By a linear change of variables $u = t^(1/2) x$,
    $ hat(f_t)(xi) = integral_(-oo)^oo g(t^(1/2) x) e^(-2 pi i x xi) dif x = t^(-1/2) hat(g)(t^(-1/2) xi) = t^(-1/2) e^(-pi xi^2 / t). $
    Applying the Poisson summation formula (Lemma 1.8) to $f_t in cal(S)(bb(R))$ gives
    $ theta(t) = sum_(n in bb(Z)) e^(-pi n^2 t) = sum_(m in bb(Z)) t^(-1/2) e^(-pi m^2 / t) = t^(-1/2) theta(1 / t). $
    Multiplying by $t^(1/2)$ yields $theta(1 / t) = t^(1/2) theta(t)$. Substituting $theta(t) = 1 + 2 psi(t)$ immediately produces the transformation law for $psi(t)$.
  ]

  === The Completed Zeta Function and Functional Equation

  We now take the Mellin transform of $psi(t)$ to assemble the completed zeta function.

  #theorem(title: "Analytic Continuation and Functional Equation of " + $zeta(s)$)[
    Define the *completed Riemann zeta function* for $op("Re")(s) > 1$ by
    $ xi(s) = pi^(-s/2) Gamma(s / 2) zeta(s). $
    Then $xi(s)$ admits the integral representation
    $ xi(s) = integral_1^oo psi(t) (t^(s/2) + t^((1-s)/2)) (dif t) / t - 1 / s - 1 / (1 - s), $
    where the integral converges absolutely and locally uniformly for all $s in bb(C)$, defining an entire function. Consequently:
    + $xi(s)$ extends to a meromorphic function on $bb(C)$ whose only singularities are simple poles at $s = 0$ (residue $-1$) and $s = 1$ (residue $+1$).
    + $xi(s)$ satisfies the *functional equation*
      $ xi(s) = xi(1 - s) quad (s in bb(C) without {0, 1}). $
    + $zeta(s)$ extends to a meromorphic function on $bb(C)$ whose only singularity is a simple pole at $s = 1$ with residue $1$, and $zeta(0) = -1 / 2$.
  ]

  #proof[
    Assume first that $op("Re")(s) > 1$. For each integer $n >= 1$, substituting $u = pi n^2 t$ into the Gamma integral $Gamma(s / 2) = integral_0^oo e^(-u) u^(s/2 - 1) dif u$ gives
    $ pi^(-s/2) Gamma(s / 2) n^(-s) = integral_0^oo e^(-pi n^2 t) t^(s/2) (dif t) / t. $
    Summing over $n >= 1$, we justify interchanging sum and integral by Tonelli's theorem:
    $ sum_(n=1)^oo integral_0^oo |e^(-pi n^2 t) t^(s/2 - 1)| dif t = sum_(n=1)^oo pi^(-sigma/2) Gamma(sigma / 2) n^(-sigma) = pi^(-sigma/2) Gamma(sigma / 2) zeta(sigma) < oo $
    for $sigma = op("Re")(s) > 1$. Hence Fubini's theorem yields
    $ xi(s) = pi^(-s/2) Gamma(s / 2) zeta(s) = integral_0^oo psi(t) t^(s/2) (dif t) / t quad (op("Re")(s) > 1). $

    Next, split the range of integration at $t = 1$:
    $ xi(s) = integral_0^1 psi(t) t^(s/2) (dif t) / t + integral_1^oo psi(t) t^(s/2) (dif t) / t. $
    In the first integral, substitute $t |-> 1 / t$ (noting $(dif(1/t)) / (1/t) = -(dif t) / t$) and apply Proposition 1.10:
    $ integral_0^1 psi(t) t^(s/2) (dif t) / t &= integral_1^oo psi(1 / t) t^(-s/2) (dif t) / t \ &= integral_1^oo (t^(1/2) psi(t) + 1 / 2 (t^(1/2) - 1)) t^(-s/2) (dif t) / t. $
    Because $op("Re")(s) > 1$, we can evaluate the elementary term explicitly:
    $ 1 / 2 integral_1^oo (t^((1-s)/2) - t^(-s/2)) (dif t) / t = 1 / 2 [ (t^((1-s)/2)) / ((1 - s)/2) - (t^(-s/2)) / (-s / 2) ]_1^oo = - 1 / (1 - s) - 1 / s. $
    Combining the two pieces produces Riemann's fundamental integral representation:
    $ xi(s) = integral_1^oo psi(t) (t^(s/2) + t^((1-s)/2)) (dif t) / t - 1 / s - 1 / (1 - s). $

    To prove that the remaining integral defines an entire function of $s in bb(C)$, observe that for $t >= 1$ and $n >= 1$ we have $n^2 >= n$, hence
    $ 0 < psi(t) = sum_(n=1)^oo e^(-pi n^2 t) <= sum_(n=1)^oo e^(-pi n t) = e^(-pi t) / (1 - e^(-pi t)) <= 2 e^(-pi t). $
    For any compact disk $|s| <= R$, we have $|t^(s/2) + t^((1-s)/2)| <= 2 t^((R+1)/2)$ for $t >= 1$, and $integral_1^oo e^(-pi t) t^((R-1)/2) dif t < oo$. By Morera's theorem and Fubini's theorem (or differentiation under the integral sign), the integral is holomorphic on all of $bb(C)$.

    This proves (1): $xi(s)$ extends meromorphically to $bb(C)$ with simple poles exclusively at $s = 0$ (residue $-1$) and $s = 1$ (residue $+1$). Assertion (2) is immediate by inspection, since the right-hand side of the integral representation is visibly invariant under the substitution $s |-> 1 - s$.

    Finally, for (3), write
    $ zeta(s) = (pi^(s/2)) / Gamma(s / 2) xi(s). $
    Because $pi^(s/2)$ and $1 / Gamma(s / 2)$ are entire functions on $bb(C)$, the only possible poles of $zeta(s)$ are at $s = 0$ and $s = 1$. At $s = 1$, $pi^(1/2) / Gamma(1/2) = 1$, so $zeta(s)$ has a simple pole with residue $1$. At $s = 0$, $Gamma(s / 2) = 2 / s + O(1)$, so $1 / Gamma(s / 2) = s / 2 + O(s^2)$; multiplying by $xi(s) = -1 / s + O(1)$ cancels the pole and yields
    $ zeta(0) = lim_(s -> 0) (s / 2) (- 1 / s) = - 1 / 2. $
    Thus $zeta(s)$ is meromorphic on $bb(C)$ with its sole pole at $s = 1$.
  ]

  Using Euler's reflection formula and Legendre's duplication formula, one obtains the asymmetric form of the functional equation directly relating $zeta(1 - s)$ and $zeta(s)$:

  #corollary(title: "Asymmetric Functional Equation")[
    For all $s in bb(C) without {0, 1}$,
    $ zeta(1 - s) = 2 (2 pi)^(-s) cos((pi s) / 2) Gamma(s) zeta(s). $
  ]

  #proof[
    From $xi(1 - s) = xi(s)$ we have
    $ zeta(1 - s) = pi^(1/2 - s) (Gamma(s / 2)) / (Gamma((1 - s) / 2)) zeta(s). $
    By the reflection formula at $(1 - s) / 2$, $Gamma((1 - s) / 2) Gamma((1 + s) / 2) = pi / sin(pi (1 - s) / 2) = pi / cos(pi s / 2)$, so $1 / Gamma((1 - s) / 2) = pi^(-1) cos(pi s / 2) Gamma((1 + s) / 2)$. Substituting this and applying Legendre's duplication formula $Gamma(s / 2) Gamma((s + 1) / 2) = pi^(1/2) 2^(1 - s) Gamma(s)$ gives
    $ zeta(1 - s) &= pi^(1/2 - s) pi^(-1) cos((pi s) / 2) pi^(1/2) 2^(1 - s) Gamma(s) zeta(s) \ &= 2 (2 pi)^(-s) cos((pi s) / 2) Gamma(s) zeta(s). $
  ]

  #insight-box(title: "Conceptual Insight: Mellin Transforms and Automorphy")[
    Riemann's proof of Theorem 1.11 establishes a paradigm that echoes throughout modern number theory: *analytic continuation and functional equations of $L$-functions come from the Mellin transform of automorphic objects*. Here the automorphic object is the half-integral-weight modular form $theta(i y) = sum_(n in bb(Z)) e^(-pi n^2 y)$ on the upper half-plane, whose modularity under $y |-> 1/y$ is a consequence of Poisson summation on $bb(Z) subset.eq bb(R)$. In Tate's 1950 thesis, this single calculation is lifted to the adeles $bb(A)_bb(Q)$, revealing that $pi^(-s/2) Gamma(s/2)$ is simply the archimedean local factor accompanying the finite Euler factors $(1 - p^(-s))^(-1)$. Remarkably, in Part III of this monograph, the Alpöge–Claude proof returns to this very landscape—deploying chains of *theta lifts* on totally definite unitary groups, whose kernels are higher-dimensional generalizations of Jacobi's theta series.
  ]

  == Trivial Zeros, the Critical Strip, and the Hadamard Product

  Having continued $zeta(s)$ to the entire complex plane, we now locate its zeros. The functional equation and the Euler product immediately restrict all nontrivial zeros to the strip $0 <= op("Re")(s) <= 1$, and a celebrated trigonometric trick eliminates the boundary lines $op("Re")(s) = 1$ and $op("Re")(s) = 0$.

  === Trivial Zeros

  #proposition(title: "Location of the Trivial Zeros")[
    In the open half-plane $op("Re")(s) < 0$, the zeros of $zeta(s)$ are precisely the negative even integers $s = -2, -4, -6, dots.c$, and each such zero is simple.
  ]

  #proof[
    Let $op("Re")(s) < 0$, so that $op("Re")(1 - s) > 1$. By Theorem 1.3, $zeta(1 - s) != 0$, and $Gamma((1 - s) / 2)$ is finite and nonzero because $op("Re")((1 - s) / 2) > 1 / 2$. Hence $xi(s) = xi(1 - s) = pi^(-(1-s)/2) Gamma((1 - s)/2) zeta(1 - s)$ is holomorphic and nonzero throughout ${op("Re")(s) < 0}$. Writing
    $ zeta(s) = (pi^(s/2)) / Gamma(s / 2) xi(s), $
    we see that the zeros of $zeta(s)$ in ${op("Re")(s) < 0}$ coincide, with multiplicity, with the zeros of $1 / Gamma(s / 2)$ in ${op("Re")(s) < 0}$—that is, the poles of $Gamma(s / 2)$ with $op("Re")(s) < 0$. These are precisely the simple poles at $s / 2 = -1, -2, -3, dots.c$, i.e., $s = -2, -4, -6, dots.c$.
  ]

  The negative even integers $s = -2k$ ($k >= 1$) are called the *trivial zeros* of $zeta(s)$. Notice that $s = 0$ is *not* a zero, because the simple pole of $Gamma(s/2)$ at $s = 0$ is offset by the simple pole of $xi(s)$ at $s = 0$, leaving $zeta(0) = -1 / 2$. All other zeros of $zeta(s)$ are called *nontrivial zeros*. By Theorem 1.3 and Proposition 1.13, every nontrivial zero $rho$ satisfies $0 <= op("Re")(rho) <= 1$.

  === Nonvanishing on the Line $op("Re")(s) = 1$

  In 1896, Jacques Hadamard and Charles-Jean de la Vallée Poussin independently proved that $zeta(1 + i t) != 0$ for all $t in bb(R)$, and deduced from this the Prime Number Theorem $pi(x) tilde x / log x$. Two years later, Franz Mertens found a remarkably short proof of nonvanishing on $op("Re")(s) = 1$ resting on a nonnegative trigonometric polynomial.

  #theorem(title: "Hadamard–de la Vallée Poussin, 1896; Mertens, 1898")[
    For every $t in bb(R)$, we have $zeta(1 + i t) != 0$. Consequently, every nontrivial zero $rho$ of $zeta(s)$ lies in the open *critical strip*
    $ 0 < op("Re")(rho) < 1, $
    and the set of nontrivial zeros (counted with multiplicity) is invariant under the symmetries $rho |-> overline(rho)$ and $rho |-> 1 - rho$.
  ]

  #proof[
    For $t = 0$, $zeta(s)$ has a pole at $s = 1$, so there is nothing to check. Fix $t in bb(R) without {0}$. For every real $theta$, we have the elementary inequality
    $ 3 + 4 cos theta + cos(2 theta) &= 3 + 4 cos theta + (2 cos^2 theta - 1) \ &= 2 (1 + cos theta)^2 >= 0. $
    For any real $sigma > 1$, Proposition 1.6 gives
    $ - op("Re") (zeta'(sigma + i y)) / zeta(sigma + i y) = sum_(n=1)^oo (Lambda(n)) / n^sigma cos(y log n) quad (y in bb(R)). $
    Applying this at $y = 0$, $y = t$, and $y = 2 t$, and forming the linear combination with weights $3, 4, 1$, we obtain *Mertens' $3$-$4$-$1$ inequality*:
    $ & 3 (- (zeta'(sigma)) / zeta(sigma)) + 4 (- op("Re") (zeta'(sigma + i t)) / zeta(sigma + i t)) + (- op("Re") (zeta'(sigma + 2 i t)) / zeta(sigma + 2 i t)) \ & quad = sum_(n=1)^oo (Lambda(n)) / n^sigma (3 + 4 cos(t log n) + cos(2 t log n)) >= 0, $
    since $Lambda(n) >= 0$ and $n^(-sigma) > 0$ for every $n >= 1$.

    Now suppose for contradiction that $zeta(s)$ has a zero of order $m >= 1$ at $s = 1 + i t$, and let $k >= 0$ be the order of vanishing of $zeta(s)$ at $s = 1 + 2 i t$. Near $s = 1$, $zeta(s)$ has a simple pole, so
    $ - (zeta'(sigma)) / zeta(sigma) = 1 / (sigma - 1) + O(1) quad (sigma -> 1^+). $
    Near $s = 1 + i t$, $zeta(s) = c_1 (s - 1 - i t)^m (1 + O(s - 1 - i t))$ with $c_1 != 0$, so
    $ - (zeta'(sigma + i t)) / zeta(sigma + i t) = - m / (sigma - 1) + O(1) quad (sigma -> 1^+), $
    and similarly near $s = 1 + 2 i t$,
    $ - (zeta'(sigma + 2 i t)) / zeta(sigma + 2 i t) = - k / (sigma - 1) + O(1) quad (sigma -> 1^+). $
    Multiplying Mertens' inequality by $(sigma - 1) > 0$ and taking the limit as $sigma -> 1^+$ yields
    $ 3 dot.c 1 + 4 dot.c (-m) + 1 dot.c (-k) = 3 - 4 m - k >= 0. $
    Since $m >= 1$ and $k >= 0$ are integers, $3 - 4 m - k <= -1 < 0$, a contradiction. Thus $zeta(1 + i t) != 0$ for all $t in bb(R)$.

    Finally, if $rho$ is a nontrivial zero of $zeta(s)$, then $rho$ is a zero of $xi(s)$. Because $zeta(overline(s)) = overline(zeta(s))$ (by Schwarz reflection from the real axis $s > 1$) and $xi(1 - s) = xi(s)$, both $overline(rho)$ and $1 - rho$ are also zeros of $xi(s)$ with the same multiplicity. In particular, $op("Re")(rho) = 0$ would force $1 - rho$ to be a zero on $op("Re")(s) = 1$, which we have just ruled out. Hence $0 < op("Re")(rho) < 1$.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Mertens' 3–4–1 Inequality",
    module: "Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean",
  )[
    Mertens' trigonometric inequality is not merely a historical curiosity; its quantitative refinement underpins the classical de la Vallée Poussin zero-free region needed in analytic reductions throughout `leanprover-community/riemann-hypothesis`. In `Formalism.ZF`, the file `ThreeFourOne.lean` formalizes the exact argument above in under sixty lines of Lean 4:
    ```lean
    lemma comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
        0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by
      rw [Real.cos_two_mul]
      nlinarith [mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]

    theorem mertensInequality : ThreeFourOne := by
      intro σ t hσ
      have h0 := hasSum_re_L hσ 0
      have h1 := hasSum_re_L hσ t
      have h2 := hasSum_re_L hσ (2 * t)
      have hs := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
      ...
    ```
    Here `hasSum_re_L` applies Mathlib's `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (Proposition 1.6) and extracts the real part via the continuous linear map `Complex.reCLM`, while `re_term_vonMangoldt` identifies each term as $Lambda(n) e^(-sigma log n) cos(y log n)$. Summing termwise via `HasSum.nonneg` yields `ThreeFourOne` for all $sigma > 1$ and $t in bb(R)$.
  ]

  === The Entire Function $Xi(s)$ and Its Hadamard Product

  To apply the factorization theory of entire functions to the nontrivial zeros of $zeta(s)$, we remove the two simple poles of $xi(s)$ at $s = 0$ and $s = 1$.

  #definition(title: "Riemann's Entire Xi-Function")[
    Define the entire function $Xi : bb(C) -> bb(C)$ by
    $ Xi(s) = 1 / 2 s (s - 1) xi(s) = 1 / 2 s (s - 1) pi^(-s/2) Gamma(s / 2) zeta(s). $
  ]

  (Note: Riemann himself wrote $xi(t)$ for $Xi(1/2 + i t)$; many modern authors denote our $Xi(s)$ by $xi(s)$, while we follow the convention of distinguishing the completed zeta function $xi(s) = pi^(-s/2) Gamma(s/2) zeta(s)$ from the entire function $Xi(s) = frac(1, 2) s(s-1) xi(s)$.)

  By Theorem 1.11 and Theorem 1.14, $Xi(s)$ is an entire function satisfying $Xi(s) = Xi(1 - s)$, $Xi(overline(s)) = overline(Xi(s))$, and $Xi(0) = Xi(1) = 1 / 2$ (since $op("Res")_(s=1) xi(s) = 1$). Its zeros are *precisely* the nontrivial zeros of $zeta(s)$, with the same multiplicities.

  Recall that an entire function $f$ has *order at most $lambda$* if for every $epsilon > 0$ there is a constant $C_epsilon > 0$ such that $|f(s)| <= C_epsilon exp(|s|^(lambda + epsilon))$ for all $s in bb(C)$; the *order* of $f$ is the infimum of all such $lambda$.

  #proposition(title: "Order of Growth of " + $Xi(s)$)[
    The entire function $Xi(s)$ has order $1$. More precisely, there exists an absolute constant $C > 0$ such that for all $s in bb(C)$ with $|s| >= 2$,
    $ |Xi(s)| <= exp(C |s| log |s|), $
    while along the positive real axis $sigma -> +oo$, $log Xi(sigma) tilde (sigma / 2) log sigma$.
  ]

  #proof[
    By the symmetry $Xi(s) = Xi(1 - s)$, it suffices to establish the upper bound for $op("Re")(s) >= 1 / 2$ and $|s| >= 2$. From Theorem 1.11,
    $ Xi(s) = 1 / 2 + 1 / 2 s (s - 1) integral_1^oo psi(t) (t^(s/2) + t^((1-s)/2)) (dif t) / t. $
    For $op("Re")(s) >= 1 / 2$, we have $op("Re")(s / 2) >= op("Re")((1 - s) / 2)$, so for $t >= 1$,
    $ |t^(s/2) + t^((1-s)/2)| <= 2 t^(op("Re")(s)/2) <= 2 t^(|s|/2). $
    Using the bound $psi(t) <= 2 e^(-pi t)$ for $t >= 1$, we obtain
    $ |Xi(s)| &<= 1 / 2 + 2 |s (s - 1)| integral_1^oo e^(-pi t) t^(|s|/2 - 1) dif t \ &<= 1 / 2 + 2 |s (s - 1)| pi^(-|s|/2) Gamma(|s| / 2). $
    By Stirling's formula, $Gamma(|s| / 2) <= exp(C_1 |s| log |s|)$ for $|s| >= 2$, which absorbs the polynomial prefactor $2 |s(s-1)| pi^(-|s|/2)$ and yields $|Xi(s)| <= exp(C |s| log |s|)$. In particular, $|Xi(s)| <<_epsilon exp(|s|^(1 + epsilon))$ for every $epsilon > 0$, so the order of $Xi$ is at most $1$.

    For the lower bound on the order, take real $sigma -> +oo$. Since $zeta(sigma) -> 1$ and $log Gamma(sigma / 2) = (sigma / 2) log(sigma / 2) - sigma / 2 + O(log sigma)$, we have
    $ log Xi(sigma) = (sigma / 2) log sigma + O(sigma) quad (sigma -> +oo). $
    Thus $Xi$ cannot satisfy $|Xi(s)| <= exp(|s|^(1 - epsilon))$ for any $epsilon > 0$, proving that the order of $Xi$ is exactly $1$.
  ]

  Hadamard's factorization theorem (1893)—originally invented by Hadamard specifically to prove the product formula Riemann had asserted without proof in 1859—states that any entire function $f$ of order $1$ with $f(0) != 0$ admits a canonical Weierstrass product
  $ f(s) = e^(A + B s) product_rho (1 - s / rho) e^(s / rho), $
  where $rho$ runs over the zeros of $f$ counted with multiplicity, and the product converges uniformly on compact subsets of $bb(C)$ (with $sum_rho |rho|^(-1 - epsilon) < oo$ for every $epsilon > 0$). Applying this to $Xi(s)$ gives the cornerstone factorization of analytic number theory.

  #theorem(title: "Hadamard Product Formula for " + $Xi(s)$)[
    There exist constants $A, B in bb(R)$ such that for all $s in bb(C)$,
    $ Xi(s) = e^(A + B s) product_rho (1 - s / rho) e^(s / rho), $
    where $rho$ ranges over all nontrivial zeros of $zeta(s)$ counted with multiplicity. Specifically,
    $ e^A = Xi(0) = 1 / 2, quad B = - gamma / 2 - 1 + 1 / 2 log(4 pi) = - sum_rho op("Re")(1 / rho). $
    Taking logarithmic derivatives yields the partial-fraction expansion valid for all $s in bb(C)$ distinct from $1$, the nontrivial zeros $rho$, and the trivial zeros $-2k$:
    $ (zeta'(s)) / zeta(s) = B - 1 / (s - 1) + 1 / 2 log pi - 1 / 2 (Gamma'(s / 2 + 1)) / Gamma(s / 2 + 1) + sum_rho (1 / (s - rho) + 1 / rho). $
  ]

  #proof[
    By Proposition 1.16, $Xi(s)$ is entire of order $1$ and $Xi(0) = 1 / 2 != 0$, so Hadamard's factorization theorem gives
    $ Xi(s) = e^(A + B s) product_rho (1 - s / rho) e^(s / rho) $
    with $e^A = Xi(0) = 1 / 2$, hence $A = -log 2$. To verify that $B$ is real and evaluate it in two ways, take the logarithmic derivative:
    $ (Xi'(s)) / Xi(s) = B + sum_rho (1 / (s - rho) + 1 / rho). $
    On the other hand, using $s Gamma(s / 2) = 2 Gamma(s / 2 + 1)$, we can rewrite $Xi(s) = (s - 1) pi^(-s/2) Gamma(s / 2 + 1) zeta(s)$, whose logarithmic derivative is
    $ (Xi'(s)) / Xi(s) = 1 / (s - 1) - 1 / 2 log pi + 1 / 2 (Gamma'(s / 2 + 1)) / Gamma(s / 2 + 1) + (zeta'(s)) / zeta(s). $
    Equating the two expressions for $Xi'(s) / Xi(s)$ yields the stated partial-fraction formula for $zeta'(s) / zeta(s)$.

    To compute $B$ explicitly, let $s -> 1$ in the identity
    $ (Xi'(s)) / Xi(s) = (1 / (s - 1) + (zeta'(s)) / zeta(s)) - 1 / 2 log pi + 1 / 2 (Gamma'(s / 2 + 1)) / Gamma(s / 2 + 1). $
    From Proposition 1.2, $zeta(s) = (s - 1)^(-1) + gamma + O(s - 1)$, so $zeta'(s) / zeta(s) = -(s - 1)^(-1) + gamma + O(s - 1)$, making the first parenthesis tend to $gamma$. For the Gamma term, $Gamma'(3 / 2) / Gamma(3 / 2) = 2 + Gamma'(1 / 2) / Gamma(1 / 2) = 2 - gamma - 2 log 2$ (obtained by differentiating Legendre's duplication formula at $s = 1$). Therefore
    $ (Xi'(1)) / Xi(1) = gamma - 1 / 2 log pi + 1 / 2 (2 - gamma - 2 log 2) = gamma / 2 + 1 - 1 / 2 log(4 pi). $
    By the symmetry $Xi(1 - s) = Xi(s)$, we have $Xi'(s) / Xi(s) = -Xi'(1 - s) / Xi(1 - s)$. Evaluating at $s = 0$ gives
    $ B = (Xi'(0)) / Xi(0) = - (Xi'(1)) / Xi(1) = - gamma / 2 - 1 + 1 / 2 log(4 pi). $
    Finally, pairing each zero $rho$ with $1 - rho$ and $overline(rho)$ in the functional equation $Xi'(s)/Xi(s) = -Xi'(1-s)/Xi(1-s)$ at $s = 0$ gives
    $ B = - B - sum_rho (1 / (1 - rho) + 1 / rho) = -B - 2 sum_rho op("Re")(1 / rho) $
    (since $1 / rho + 1 / overline(rho) = 2 op("Re")(1 / rho) = 2 op("Re")(rho) / |rho|^2 > 0$, the sum $sum_rho op("Re")(1 / rho)$ converges absolutely because $op("Re")(rho) in (0, 1)$ and $sum_rho |rho|^(-2) < oo$). Thus $B = -sum_rho op("Re")(1 / rho)$.
  ]

  The relation $sum_rho op("Re")(1 / rho) = -B approx 0.0230957$ already implies that there are infinitely many nontrivial zeros (indeed, if there were none, $Xi(s) = frac(1,2) e^(B s)$ would violate $Xi(s) = Xi(1-s)$ since $B != 0$, and even more simply $Xi(s)$ has order $1$ with $log Xi(sigma) tilde (sigma / 2) log sigma$). We now count the nontrivial zeros up to height $T$ with remarkable precision.

  === The Riemann–von Mangoldt Zero-Counting Formula

  For $T > 0$, let $N(T)$ denote the number of nontrivial zeros $rho = beta + i gamma$ of $zeta(s)$ (counted with multiplicity) satisfying $0 < gamma <= T$. (When $T$ is the ordinate of a zero, one may adopt the convention of counting zeros on the line $op("Im")(s) = T$ with weight $1 / 2$, though the $O(log T)$ error term renders this convention immaterial for the theorem below.)

  #theorem(title: "Riemann–von Mangoldt Formula, 1905")[
    As $T -> oo$,
    $ N(T) = T / (2 pi) log (T / (2 pi e)) + O(log T). $
    Consequently, for every $T >= 2$, the number of nontrivial zeros $rho = beta + i gamma$ with $T <= gamma <= T + 1$ is $O(log T)$.
  ]

  #proof[
    We give the classical argument-principle proof due to von Mangoldt and Backlund. Assume first that $T >= 2$ is not the ordinate of any zero of $zeta(s)$; since $N(T)$ is nondecreasing, establishing the asymptotic for such $T$ (together with the local count in unit intervals, which follows immediately from $N(T+1) - N(T)$) proves the theorem for all $T >= 2$.

    Let $cal(R)$ be the positively oriented rectangle with vertices $2$, $2 + i T$, $-1 + i T$, and $-1$. Because $Xi(s)$ is entire and strictly positive on the real axis (for $sigma in (0, 1)$, the alternating Dirichlet series $(1 - 2^(1-sigma)) zeta(sigma) = sum_(n=1)^oo (-1)^(n-1) n^(-sigma) > 0$ implies $zeta(sigma) < 0$, so $Xi(sigma) = frac(1, 2) sigma (sigma - 1) pi^(-sigma/2) Gamma(sigma/2) zeta(sigma) > 0$, while $Xi(sigma) > 0$ for $sigma >= 1$ directly and for $sigma <= 0$ by symmetry), the function $Xi(s)$ has no zeros on $partial cal(R)$, and its zeros inside $cal(R)$ are precisely the $N(T)$ nontrivial zeros with $0 < gamma < T$. By the argument principle,
    $ 2 pi N(T) = Delta_(partial cal(R)) op("arg") Xi(s), $
    where $Delta_(partial cal(R)) op("arg") Xi(s)$ denotes the net change in a continuous branch of $op("arg") Xi(s)$ around $partial cal(R)$.

    On the bottom edge $[-1, 2]$, $Xi(sigma) > 0$, so the change in argument is $0$. Let $L_1$ be the right vertical edge from $2$ to $2 + i T$, $L_2$ the top half-edge from $2 + i T$ to $1/2 + i T$, $L_3$ the top half-edge from $1/2 + i T$ to $-1 + i T$, and $L_4$ the left vertical edge from $-1 + i T$ to $-1$. By the symmetries $Xi(1 - s) = Xi(s)$ and $Xi(overline(s)) = overline(Xi(s))$, we have $Xi(1/2 - u + i v) = overline(Xi(1/2 + u + i v))$ for all $u, v in bb(R)$. As $s$ traverses $L_3 union L_4$ from $1/2 + i T$ to $-1$, the reflected point $1 - overline(s)$ traverses $L_1 union L_2$ in reverse, and the conjugation reverses the sign of the argument; hence $Delta_(L_3 union L_4) op("arg") Xi(s) = Delta_(L_1 union L_2) op("arg") Xi(s)$. Thus
    $ pi N(T) = Delta_(L_1 union L_2) op("arg") Xi(s). $

    We now decompose $Xi(s) = frac(1, 2) s(s - 1) pi^(-s/2) Gamma(s / 2) zeta(s)$ along the path $L = L_1 union L_2$ from $2$ to $1/2 + i T$:
    $ pi N(T) &= Delta_L op("arg")(s(s - 1)) + Delta_L op("arg")(pi^(-s/2)) \ & quad + Delta_L op("arg") Gamma(s / 2) + Delta_L op("arg") zeta(s). $
    We evaluate the first three terms directly:
    - For $s(s - 1)$: as $s$ goes from $2$ to $1/2 + i T$, $op("arg")(s) -> pi / 2 + O(1 / T)$ and $op("arg")(s - 1) -> pi / 2 + O(1 / T)$, so $Delta_L op("arg")(s(s - 1)) = pi + O(1 / T)$.
    - For $pi^(-s/2) = exp(-(s/2) log pi)$: the imaginary part of $-(s/2) log pi$ changes from $0$ to $-(T / 2) log pi$, so $Delta_L op("arg")(pi^(-s/2)) = -(T / 2) log pi$.
    - For $Gamma(s / 2)$: at $s = 1/2 + i T$, Stirling's formula gives
      $ op("Im") log Gamma(1 / 4 + (i T) / 2) = T / 2 log (T / 2) - T / 2 - pi / 8 + O(1 / T). $

    Combining these three contributions yields
    $ pi N(T) = T / 2 log (T / (2 pi e)) + 7 / 8 pi + O(1 / T) + Delta_L op("arg") zeta(s). $
    Dividing by $pi$, we obtain the exact relation
    $ N(T) = T / (2 pi) log (T / (2 pi e)) + 7 / 8 + S(T) + O(1 / T), $
    where $S(T) = frac(1, pi) Delta_L op("arg") zeta(s)$. It therefore remains to prove the estimate
    $ S(T) = O(log T). $

    On the vertical segment $L_1$ ($s = 2 + i t$, $0 <= t <= T$), we have $|zeta(2 + i t) - 1| <= sum_(n=2)^oo n^(-2) = pi^2 / 6 - 1 < 0.65 < 1$, so $op("Re") zeta(2 + i t) > 0.35 > 0$ throughout $L_1$. Hence $|Delta_(L_1) op("arg") zeta(s)| < pi / 2$.

    To bound $Delta_(L_2) op("arg") zeta(s)$ along the horizontal segment $L_2 = [1/2 + i T, 2 + i T]$, we use a classic lemma of Backlund: if $op("Re") zeta(sigma + i T)$ has $q$ zeros on the interval $[1/2, 2]$, then $L_2$ is divided into $q + 1$ subintervals on each of which $op("Re") zeta$ maintains constant sign, so the argument of $zeta$ can change by at most $pi$ on each subinterval, giving $|Delta_(L_2) op("arg") zeta(s)| <= (q + 1) pi$. To bound $q$, consider the holomorphic function
    $ g(z) = 1 / 2 (zeta(z + i T) + zeta(z - i T)). $
    For real $z = sigma$, $g(sigma) = op("Re") zeta(sigma + i T)$, so $q$ is at most the number $n(3/2)$ of zeros of $g(z)$ in the disk $|z - 2| <= 3 / 2$. By Jensen's formula applied to $g$ on the disk $|z - 2| <= 7 / 4$,
    $ n(3 / 2) log (7 / 6) &<= integral_0^(7/4) (n(r)) / r dif r \ &= 1 / (2 pi) integral_0^(2 pi) log |g(2 + 7 / 4 e^(i theta))| dif theta - log |g(2)|. $
    Since $|g(2)| = |op("Re") zeta(2 + i T)| > 0.35$, the term $-log |g(2)|$ is bounded above by an absolute constant. On the circle $|z - 2| = 7 / 4$, we have $op("Re")(z) >= 1 / 4$, and Proposition 1.2 immediately gives the polynomial bound $|zeta(sigma + i t)| <= 1 + 1 / |s - 1| + |s| / sigma << |t|$ for $sigma >= 1 / 4$ and $|t| >= 2$. Consequently $|g(z)| << T$ uniformly on $|z - 2| = 7 / 4$, yielding
    $ q <= n(3 / 2) <= C log T + O(1), $
    which proves $|S(T)| <= q + 3/2 = O(log T)$ and completes the proof of the Riemann–von Mangoldt formula.
  ]

  The local zero-count $N(T + 1) - N(T) = O(log T)$ has two indispensable analytic corollaries, which we record for use in the explicit formula below.

  #corollary(title: "Zero-Sum Bounds and Good Heights")[
    + For $T >= 2$,
      $ sum_(|gamma| <= T) 1 / |rho| = O((log T)^2), quad sum_(|gamma| > T) 1 / |rho|^2 = O((log T) / T), $
      and for every $t in bb(R)$ with $|t| >= 2$,
      $ sum_rho 1 / (1 + (t - gamma)^2) = O(log |t|). $
    + For every $T >= 2$, there exists a height $T_* in [T, T + 1]$ such that every nontrivial zero $rho = beta + i gamma$ satisfies $|T_* - gamma| >= c / log T$, where $c > 0$ is an absolute constant.
    + For $s = sigma + i t$ with $-1 <= sigma <= 2$ and $|t| >= 2$ distinct from all zeros $rho$,
      $ (zeta'(s)) / zeta(s) = sum_(|t - gamma| <= 1) 1 / (s - rho) + O(log |t|). $
  ]

  #proof[
    For (1), partition the zeros into dyadic or unit vertical intervals $k <= |gamma| < k + 1$. Since each unit interval contains $O(log(k + 2))$ zeros and $|rho| >= max(1/2, |gamma|)$, we have
    $ sum_(|gamma| <= T) 1 / |rho| << sum_(1 <= k <= T) (log(k + 1)) / k << (log T)^2, $
    and similarly $sum_(|gamma| > T) |rho|^(-2) << sum_(k >= floor(T)) (log k) / k^2 << (log T) / T$. Likewise, grouping zeros by $m <= |t - gamma| < m + 1$ gives
    $ sum_rho 1 / (1 + (t - gamma)^2) << sum_(m=0)^oo (log(|t| + m + 2)) / (1 + m^2) << log |t|. $
    For (2), there are $M = O(log T)$ ordinates $gamma$ in $[T, T + 1]$, which divide $[T, T + 1]$ into at most $M + 1$ subintervals. By the pigeonhole principle, the longest subinterval has length at least $1 / (M + 1) >= 2 c / log T$; its midpoint $T_*$ lies at distance at least $c / log T$ from every zero ordinate.

    For (3), subtract the Hadamard partial-fraction formula (Theorem 1.17) at $s = sigma + i t$ from its value at $s_0 = 2 + i t$. Because $|zeta'(2 + i t) / zeta(2 + i t)| <= sum_(n=1)^oo Lambda(n) n^(-2) = O(1)$ and Stirling's formula gives $|Gamma'(s/2 + 1) / Gamma(s/2 + 1)| = O(log |t|)$ uniformly for $-1 <= sigma <= 2$ and $|t| >= 2$, we obtain
    $ (zeta'(s)) / zeta(s) = sum_rho (1 / (s - rho) - 1 / (2 + i t - rho)) + O(log |t|). $
    For zeros with $|t - gamma| <= 1$, we have $|2 + i t - rho| >= 1$, and there are $O(log |t|)$ such terms, contributing $O(log |t|)$ in total. For zeros with $|t - gamma| > 1$, we have
    $ |1 / (s - rho) - 1 / (2 + i t - rho)| = |2 - sigma| / (|s - rho| |2 + i t - rho|) <= 3 / (t - gamma)^2, $
    whose sum over $|t - gamma| > 1$ is $O(log |t|)$ by (1). This establishes (3).
  ]

  == Prime Counting and Riemann's Explicit Formula

  We now arrive at the centerpiece of Riemann's 1859 memoir: the exact duality between the prime numbers and the nontrivial zeros of $zeta(s)$.

  === Prime-Counting Functions

  The classical prime-counting function is
  $ pi(x) = sum_(p <= x) 1. $
  As Gauss conjectured around 1792 from tables of primes, the density of primes near $x$ is approximately $1 / log x$, so $pi(x)$ is approximated by the *logarithmic integral*
  $ op("li")(x) = integral_2^x (dif u) / (log u). $
  (Some authors define $op("li")(x)$ as the Cauchy principal value $integral_0^x dif u / log u$; the two definitions differ by the constant $op("li")(2) approx 1.04516$.)

  Because the logarithmic derivative $-zeta'(s) / zeta(s) = sum_(n=1)^oo Lambda(n) n^(-s)$ weights each prime power $p^k$ by $log p$, the summatory function most directly coupled to $zeta(s)$ is *Chebyshev's $psi$-function*:
  $ psi(x) = sum_(n <= x) Lambda(n) = sum_(p^k <= x) log p, $
  alongside its prime-only companion $theta.alt(x) = sum_(p <= x) log p$. For contour integration, it is convenient to normalize $psi(x)$ at its jump discontinuities by setting
  $ psi_0 (x) = 1 / 2 (psi(x^+) + psi(x^-)) = sum_(n < x) Lambda(n) + 1 / 2 Lambda(x), $
  where $Lambda(x) = 0$ if $x in.not bb(N)$. Note that $psi(x)$ and $theta.alt(x)$ are very close: since every prime power $p^k <= x$ with $k >= 2$ satisfies $p <= x^(1/2)$ and $k <= log x / log 2$, we have
  $ 0 <= psi(x) - theta.alt(x) = sum_(k=2)^(floor(log_2 x)) theta.alt(x^(1/k)) = O(x^(1/2)), $
  because $theta.alt(y) <= sum_(p <= y) log y <= y log y$, or more sharply by Chebyshev's elementary bound $theta.alt(y) = O(y)$ (indeed $psi(x) - theta.alt(x) <= theta.alt(x^(1/2)) + (log_2 x) theta.alt(x^(1/3)) = O(x^(1/2))$).

  === Perron's Formula

  To extract the partial sums $sum_(n <= x) a(n)$ from a Dirichlet series $F(s) = sum_(n=1)^oo a(n) n^(-s)$, we use the inverse Mellin transform of the step function $bold(1)_(y > 1)$, known as *Perron's formula*.

  #lemma(title: "Effective Discontinuous Integral")[
    Let $c > 0$, $y > 0$, and $T > 0$. Define
    $ delta(y) = cases(1 & "if" y > 1, 1 / 2 & "if" y = 1, 0 & "if" 0 < y < 1,) quad "and" quad I(y, T) = 1 / (2 pi i) integral_(c - i T)^(c + i T) y^s / s dif s. $
    Then:
    + For $y != 1$,
      $ |I(y, T) - delta(y)| <= y^c min(1, 1 / (pi T |log y|)). $
    + For $y = 1$,
      $ |I(1, T) - 1 / 2| <= c / (pi T). $
    In particular, $lim_(T -> oo) I(y, T) = delta(y)$ for every $y > 0$.
  ]

  #proof[
    Suppose first that $y > 1$. For any $U > 0$, consider the closed positively oriented rectangle with vertices $c - i T$, $c + i T$, $-U + i T$, and $-U - i T$. The integrand $y^s / s$ has a single simple pole inside the rectangle at $s = 0$ with residue $1$. By Cauchy's residue theorem,
    $ I(y, T) - 1 = 1 / (2 pi i) (integral_(c + i T)^(-U + i T) + integral_(-U + i T)^(-U - i T) + integral_(-U - i T)^(c - i T)) y^s / s dif s. $
    On the horizontal edges $s = sigma plus.minus i T$ ($-U <= sigma <= c$), we have $|s| >= T$ and $|y^s| = y^sigma$, so each horizontal integral is bounded in modulus by
    $ 1 / (2 pi T) integral_(-U)^c y^sigma dif sigma <= y^c / (2 pi T log y). $
    On the left vertical edge $s = -U + i t$ ($|t| <= T$), $|y^s / s| <= y^(-U) / U$, so the left integral vanishes as $U -> oo$ because $y > 1$. Letting $U -> oo$ yields $|I(y, T) - 1| <= y^c / (pi T log y)$.

    To also obtain the bound $|I(y, T) - 1| <= y^c$ (useful when $y$ is close to $1$), instead close the contour to the left by the circular arc $Gamma_R$ of radius $R = sqrt(c^2 + T^2)$ centered at $0$ passing through $c + i T$ and $c - i T$ with $op("Re")(s) <= c$. On $Gamma_R$, $|y^s| <= y^c$ and $|s| = R$, while the arc length is $< 2 pi R$, so $|(2 pi i)^(-1) integral_(Gamma_R) y^s / s dif s| <= y^c$.

    For $0 < y < 1$, we shift the contour to the *right* to $+U plus.minus i T$ (enclosing no poles) and let $U -> oo$. The exact same estimates give $|I(y, T)| <= y^c / (pi T |log y|)$, and closing by the right circular arc of radius $R$ gives $|I(y, T)| <= y^c$.

    Finally, for $y = 1$, direct parameterization $s = c + i t$ yields
    $ I(1, T) = 1 / (2 pi) integral_(-T)^T (dif t) / (c + i t) = 1 / (2 pi) integral_(-T)^T (c dif t) / (c^2 + t^2) = 1 / pi arctan(T / c). $
    Since $pi / 2 - arctan(T / c) = arctan(c / T) <= c / T$, we obtain $|I(1, T) - 1 / 2| <= c / (pi T)$.
  ]

  Applying Lemma 1.20 term by term to the Dirichlet series $-zeta'(s) / zeta(s) = sum_(n=1)^oo Lambda(n) n^(-s)$ yields the truncated Perron formula for $psi_0 (x)$.

  #proposition(title: "Truncated Perron Formula for " + $psi_0 (x)$)[
    Let $x >= 2$, $T >= 2$, and $c = 1 + 1 / log x$. Then
    $ psi_0 (x) = 1 / (2 pi i) integral_(c - i T)^(c + i T) (- (zeta'(s)) / zeta(s)) x^s / s dif s + O((x (log x)^2) / T + log x). $
  ]

  #proof[
    Because $sum_(n=1)^oo Lambda(n) n^(-c)$ converges absolutely, we may interchange the finite integral and the infinite sum:
    $ 1 / (2 pi i) integral_(c - i T)^(c + i T) (- (zeta'(s)) / zeta(s)) x^s / s dif s = sum_(n=1)^oo Lambda(n) I(x / n, T). $
    Subtracting $psi_0 (x) = sum_(n=1)^oo Lambda(n) delta(x / n)$ and applying Lemma 1.20 gives an error bounded by
    $ E <= sum_(n != x) Lambda(n) (x / n)^c min(1, 1 / (pi T |log(x / n)|)) + Lambda(x) c / (pi T), $
    where the last term is $O((log x) / T)$ (present only if $x in bb(N)$). Note that $x^c = e x$. We split the sum over $n != x$ into two ranges:
    - *Far range* ($|n - x| > x / 2$): here $|log(x / n)| >= log(3 / 2) >> 1$, so the contribution is
      $ << x / T sum_(n=1)^oo (Lambda(n)) / n^c = x / T (- (zeta'(c)) / zeta(c)) << x / T dot.c 1 / (c - 1) = (x log x) / T. $
    - *Near range* ($x / 2 <= n <= 3 x / 2$, $n != x$): here $Lambda(n) <= log(3 x / 2) << log x$ and $(x / n)^c << 1$. For the at most two integers closest to $x$ with $|n - x| < 1$, we use the bound $min(1, dots.c) <= 1$, contributing $O(log x)$. For the remaining integers with $1 <= |n - x| <= x / 2$, we have $|log(x / n)| >> |n - x| / x$, so their contribution is
      $ << (log x) / T sum_(1 <= k <= x / 2) x / k << (x (log x)^2) / T. $
    Combining all pieces yields the claimed error $O(x (log x)^2 / T + log x)$.
  ]

  === Riemann's Explicit Formula

  We are now ready to shift the Perron contour to the left, sweeping past the pole at $s = 1$, the nontrivial zeros $rho$, the origin $s = 0$, and the trivial zeros $s = -2m$.

  #theorem(title: "Riemann–von Mangoldt Explicit Formula")[
    + (*Truncated quantitative form*) For $x >= 2$ and $2 <= T <= x$,
      $ psi(x) = x - sum_(|gamma| <= T) x^rho / rho + O((x (log x)^2) / T + log x). $
    + (*Exact infinite form*) For every real $x > 1$,
      $ psi_0 (x) = x - sum_rho x^rho / rho - log(2 pi) - 1 / 2 log(1 - x^(-2)), $
      where the sum over nontrivial zeros is interpreted symmetrically as $lim_(T -> oo) sum_(|gamma| <= T) x^rho / rho$.
  ]

  #proof[
    Fix $x >= 2$ and $T >= 2$. By Corollary 1.19(2), we may adjust $T$ within $[T, T + 1]$ (which alters the truncated sum $sum_(|gamma| <= T) x^rho / rho$ by at most $O(x (log T) / T)$, absorbed into the error term) so that every nontrivial zero $rho = beta + i gamma$ satisfies $|T - gamma| >= c_0 / log T$. By symmetry of the zeros, $|-T - gamma| >= c_0 / log T$ as well.

    Set $c = 1 + 1 / log x$, and let $U = 2 k + 1$ be a large odd positive integer (so that the vertical line $op("Re")(s) = -U$ stays at distance $1$ from all trivial zeros $-2 m$). Consider the positively oriented rectangle $cal(R)_(T, U)$ with vertices $c - i T$, $c + i T$, $-U + i T$, and $-U - i T$. The meromorphic integrand $F(s) = -(zeta'(s) / zeta(s)) (x^s / s)$ has poles inside $cal(R)_(T, U)$ at:
    - $s = 1$: simple pole of $-zeta'/zeta$ with residue $+1$, giving $op("Res")_(s=1) F(s) = x$;
    - $s = rho$ (each nontrivial zero with $|gamma| < T$): simple pole of $-zeta'/zeta$ with residue $-m_rho$, giving $op("Res")_(s=rho) F(s) = -m_rho x^rho / rho$;
    - $s = 0$: simple pole of $1 / s$ (since $zeta(0) = -1 / 2 != 0$), giving $op("Res")_(s=0) F(s) = -zeta'(0) / zeta(0)$;
    - $s = -2 m$ ($1 <= m <= k$): simple pole of $-zeta'/zeta$ with residue $-1$, giving $op("Res")_(s=-2m) F(s) = -x^(-2m) / (-2m) = x^(-2m) / (2m)$.

    To evaluate $-zeta'(0) / zeta(0)$, differentiate the asymmetric functional equation (Corollary 1.12) logarithmically or use Theorem 1.17 directly: from $Xi(s) = (s - 1) pi^(-s/2) Gamma(s/2 + 1) zeta(s)$, evaluating $Xi'(0) / Xi(0) = B$ yields
    $ (zeta'(0)) / zeta(0) = B + 1 + 1 / 2 log pi - 1 / 2 (Gamma'(1)) / Gamma(1). $
    Since $Gamma'(1) / Gamma(1) = -gamma$ and $B = -gamma / 2 - 1 + frac(1, 2) log(4 pi)$, all terms cancel except $frac(1, 2) log(4 pi) + frac(1, 2) log pi = log(2 pi)$. Hence $-zeta'(0) / zeta(0) = -log(2 pi)$.

    By Cauchy's residue theorem,
    $ 1 / (2 pi i) integral_(c - i T)^(c + i T) F(s) dif s &= x - sum_(|gamma| < T) x^rho / rho - log(2 pi) \ & quad + sum_(m=1)^k x^(-2m) / (2 m) + H_(T, U) + V_(T, U), $
    where $H_(T, U)$ is the contribution of the two horizontal segments $[-U plus.minus i T, c plus.minus i T]$ and $V_(T, U)$ is the contribution of the left vertical segment $[-U - i T, -U + i T]$.

    We now estimate $H_(T, U)$ and $V_(T, U)$:
    - *Horizontal segments in $[-1, c]$*: For $-1 <= sigma <= c$ and $t = plus.minus T$, Corollary 1.19(3) together with the zero-avoidance condition $|T - gamma| >= c_0 / log T$ gives
      $ |(zeta'(sigma plus.minus i T)) / zeta(sigma plus.minus i T)| <= sum_(|T - gamma| <= 1) (log T) / c_0 + O(log T) << (log T)^2, $
      since there are $O(log T)$ zeros in $|T - gamma| <= 1$. Hence the horizontal segments over $-1 <= sigma <= c$ contribute at most
      $ << (log T)^2 / T integral_(-1)^c x^sigma dif sigma << (x (log T)^2) / (T log x). $
    - *Left half-plane $op("Re")(s) <= -1$*: Differentiating the asymmetric functional equation (Corollary 1.12) logarithmically gives
      $ - (zeta'(s)) / zeta(s) = (zeta'(1 - s)) / zeta(1 - s) + log(2 pi) + pi / 2 tan((pi s) / 2) + (Gamma'(1 - s)) / Gamma(1 - s). $
      On both the horizontal segments $[-U plus.minus i T, -1 plus.minus i T]$ (where $|op("Im")(s)| = T >= 2$, so $|tan(pi s / 2)| = O(1)$) and the left vertical segment $s = -U + i t$ (where $op("Re")(s) = -2k - 1$ is an odd integer, so $cos(pi s / 2)$ stays bounded away from $0$ and $|tan(pi s / 2)| = O(1)$), we have $|zeta'(1 - s) / zeta(1 - s)| <= |zeta'(2) / zeta(2)| = O(1)$ and $|Gamma'(1 - s) / Gamma(1 - s)| = O(log |1 - s|) = O(log(U + T))$. Consequently,
      $ |(zeta'(s)) / zeta(s)| << log(U + T) $
      on the remaining boundary of $cal(R)_(T, U)$. Thus the horizontal segments over $[-U, -1]$ contribute at most
      $ << (log(U + T)) / T integral_(-U)^(-1) x^sigma dif sigma << (log(U + T)) / (T x log x), $
      and the left vertical segment $s = -U + i t$ ($|t| <= T$) contributes at most
      $ << T dot.c (log(U + T)) / U x^(-U). $

    For fixed $x > 1$ and $T >= 2$, letting $U = 2 k + 1 -> oo$ kills $V_(T, U)$ (since $x^(-U) -> 0$ exponentially) and replaces the finite sum over $m$ by
    $ sum_(m=1)^oo x^(-2 m) / (2 m) = - 1 / 2 log(1 - x^(-2)). $
    (And for the horizontal segment $[-U, -1]$, splitting at $-1$ and noting $|Gamma'(1 - s) / Gamma(1 - s)| << log(|sigma| + T)$ gives an integrable bound $T^(-1) integral_(-oo)^(-1) x^sigma log(|sigma| + T) dif sigma << (log T) / (T x log x)$ uniformly in $U$.)

    Combining this with Proposition 1.21 yields, for our adjusted $T$,
    $ psi_0 (x) &= x - sum_(|gamma| < T) x^rho / rho - log(2 pi) - 1 / 2 log(1 - x^(-2)) \ & quad + O((x (log x)^2) / T + (x (log T)^2) / (T log x) + log x). $
    When $2 <= T <= x$, the constant $-log(2 pi) - frac(1, 2) log(1 - x^(-2))$ and the difference $|psi(x) - psi_0 (x)| <= frac(1, 2) log x$ are absorbed into $O(log x)$, proving part (1).

    For part (2), fix $x > 1$ and let $T -> oo$ through good heights $T_*$. Every error term in Proposition 1.21—when $x$ is fixed—vanishes as $T -> oo$ (in the proof of Proposition 1.21, the $O(log x)$ term came solely from the at most two integers with $|n - x| < 1$, which for *fixed* $x$ have $|log(x / n)| > 0$ bounded away from $0$, so Lemma 1.20 gives $O_x (1 / T) -> 0$ for *every* term $n != x$, and $O_x (1 / T) -> 0$ for $n = x$ as well!). Likewise the horizontal integral error is $O_x ((log T)^2 / T) -> 0$. Finally, between any good height $T_*$ and any $T in [T_* - 1, T_* + 1]$, there are $O(log T)$ zeros, each contributing $|x^rho / rho| <= x / T$, so the difference is $O(x (log T) / T) -> 0$. Hence $lim_(T -> oo) sum_(|gamma| <= T) x^rho / rho$ exists and equals $x - psi_0 (x) - log(2 pi) - frac(1, 2) log(1 - x^(-2))$.
  ]

  === Equivalence with the Riemann Hypothesis

  The explicit formula makes transparent how the real parts $beta = op("Re")(rho)$ control the size of the error term $psi(x) - x$: a zero at $rho = beta + i gamma$ contributes a term of magnitude $x^beta / |rho|$. Since the functional equation pairs $rho$ with $1 - rho$, the smallest possible uniform upper bound on $op("Re")(rho)$ is $1 / 2$. The Riemann Hypothesis asserts that this optimal bound is achieved: every nontrivial zero satisfies $op("Re")(rho) = 1 / 2$.

  #theorem(title: "Prime-Counting Equivalents of the Riemann Hypothesis")[
    The following three statements are equivalent:
    + (*Riemann Hypothesis*) Every nontrivial zero $rho$ of $zeta(s)$ satisfies $op("Re")(rho) = 1 / 2$.
    + (*Chebyshev error bound*) As $x -> oo$,
      $ psi(x) = x + O(x^(1/2) (log x)^2). $
    + (*Prime-counting error bound*) As $x -> oo$,
      $ pi(x) = op("li")(x) + O(x^(1/2) log x). $
  ]

  #proof[
    *(1) $=>$ (2).* Assume that $op("Re")(rho) = 1 / 2$ for every nontrivial zero $rho$. Then $|x^rho / rho| = x^(1/2) / |rho|$. Applying the truncated explicit formula (Theorem 1.22(1)) with $T = x^(1/2)$ (for $x >= 4$) and Corollary 1.19(1) gives
    $ |psi(x) - x| <= x^(1/2) sum_(|gamma| <= x^(1/2)) 1 / |rho| + O(x^(1/2) (log x)^2) << x^(1/2) (log x)^2. $

    *(2) $=>$ (3).* Assume $psi(x) = x + O(x^(1/2) (log x)^2)$. Since $psi(x) - theta.alt(x) = O(x^(1/2))$, we also have $theta.alt(x) = x + E(x)$ with $E(x) = O(x^(1/2) (log x)^2)$. By Abel summation (Riemann–Stieltjes integration by parts),
    $ pi(x) = sum_(2 <= p <= x) 1 = integral_(2^-)^x (dif theta.alt(u)) / (log u) = (theta.alt(x)) / (log x) + integral_2^x (theta.alt(u)) / (u (log u)^2) dif u. $
    Substituting $theta.alt(u) = u + E(u)$ and integrating $op("li")(x) = integral_2^x dif u / log u$ by parts gives
    $ op("li")(x) = x / (log x) - 2 / (log 2) + integral_2^x (dif u) / (log u)^2, $
    so
    $ pi(x) - op("li")(x) = 2 / (log 2) + (E(x)) / (log x) + integral_2^x (E(u)) / (u (log u)^2) dif u. $
    The boundary term is $E(x) / log x = O(x^(1/2) log x)$, and the integral satisfies
    $ |integral_2^x (E(u)) / (u (log u)^2) dif u| << integral_2^x (u^(1/2) (log u)^2) / (u (log u)^2) dif u = integral_2^x u^(-1/2) dif u << x^(1/2). $
    Thus $pi(x) = op("li")(x) + O(x^(1/2) log x)$.

    *(3) $=>$ (2).* Assume $pi(x) = op("li")(x) + R(x)$ with $R(x) = O(x^(1/2) log x)$. Integrating by parts in the reverse direction gives
    $ theta.alt(x) = integral_(2^-)^x (log u) dif pi(u) = pi(x) log x - integral_2^x (pi(u)) / u dif u. $
    Since $op("li")(x) log x - integral_2^x op("li")(u) / u dif u = x - 2$, we obtain
    $ theta.alt(x) - x = -2 + R(x) log x - integral_2^x (R(u)) / u dif u. $
    Here $|R(x) log x| << x^(1/2) (log x)^2$ and $|integral_2^x R(u) / u dif u| << integral_2^x u^(-1/2) log u dif u << x^(1/2) log x$. Adding $psi(x) - theta.alt(x) = O(x^(1/2))$ recovers $psi(x) = x + O(x^(1/2) (log x)^2)$.

    *(2) $=>$ (1).* Assume $psi(x) = x + O(x^(1/2) (log x)^2)$ (in fact, $psi(x) = x + O_epsilon (x^(1/2 + epsilon))$ for every $epsilon > 0$ already suffices). For $op("Re")(s) > 1$, Proposition 1.6 and Riemann–Stieltjes integration by parts give
    $ - (zeta'(s)) / zeta(s) = integral_(1^-)^oo x^(-s) dif psi(x) = s integral_1^oo psi(x) x^(-s-1) dif x. $
    Since $s / (s - 1) = s integral_1^oo x dot.c x^(-s-1) dif x$ for $op("Re")(s) > 1$, subtracting yields
    $ - (zeta'(s)) / zeta(s) - s / (s - 1) = s integral_1^oo (psi(x) - x) x^(-s-1) dif x. $
    Under the bound $|psi(x) - x| <= C x^(1/2) (log(x + 2))^2$, the integrand is bounded in modulus by $C x^(1/2 - op("Re")(s) - 1) (log(x + 2))^2$, which is integrable on $[1, oo)$ uniformly on every half-plane ${op("Re")(s) >= 1 / 2 + delta}$ ($delta > 0$). Hence the right-hand side defines a holomorphic function on the entire half-plane ${op("Re")(s) > 1 / 2}$. By uniqueness of analytic continuation, the meromorphic function $-zeta'(s) / zeta(s) - s / (s - 1)$ has no poles in ${op("Re")(s) > 1 / 2}$. Because every zero $rho$ of $zeta(s)$ produces a simple pole of $-zeta'(s) / zeta(s)$ with negative integer residue, $zeta(s)$ has no zeros in ${op("Re")(s) > 1 / 2}$. By the functional-equation symmetry $rho |-> 1 - rho$ (Theorem 1.14), $zeta(s)$ also has no zeros in ${op("Re")(s) < 1 / 2}$ inside the critical strip. Therefore every nontrivial zero satisfies $op("Re")(rho) = 1 / 2$.
  ]

  #insight-box(title: "Conceptual Insight: The Music of the Primes and Smoothed Sums")[
    Pairing conjugate zeros $rho = beta + i gamma$ and $overline(rho) = beta - i gamma$ in Theorem 1.22(2) expresses the fluctuation of the primes as a superposition of damped waves in logarithmic scale $u = log x$:
    $ x - psi_0 (x) &= sum_(gamma > 0) (2 x^beta) / |rho| cos(gamma log x - op("arg")(rho)) \ & quad + log(2 pi) + 1 / 2 log(1 - x^(-2)). $
    The Riemann Hypothesis says that every harmonic has the *exact* same amplitude exponent $beta = 1 / 2$—the square-root cancellation characteristic of a random walk. Notice, however, that the sharp step-function cutoff $psi_0 (x)$ produces a merely conditionally convergent sum $sum_rho x^rho / rho$. In Chapter 5 and Part III, we will replace the sharp cutoff by *smoothed* summatory functions such as $S_a (x) = sum_(1 <= n <= x) a(n) (x / n - 1)$ (whose Mellin kernel is $1 / (s(s+1))$ rather than $1 / s$), yielding absolutely convergent spectral expansions that interface cleanly with Landau's nonvanishing theorem and the automorphic machinery of the Alpöge–Claude proof.
  ]

  == The Formal Statement of the Riemann Hypothesis

  We close this opening chapter by stating the Riemann Hypothesis in both its classical mathematical form and its exact machine-checked formulation in Lean 4.

  #conjecture(title: "The Riemann Hypothesis, 1859")[
    Every nontrivial zero $rho$ of the Riemann zeta function $zeta(s)$ lies on the critical line $op("Re")(s) = 1 / 2$. Equivalently, if $s in bb(C)$ satisfies $zeta(s) = 0$ and $s in.not {-2, -4, -6, dots.c}$, then $op("Re")(s) = 1 / 2$.
  ]

  (Throughout Parts I and II we treat the Riemann Hypothesis and its generalization to Dirichlet $L$-functions in their historical setting as conjectures, before presenting their complete, formally verified proof in Part III.)

  Translating a classical analytic statement into a dependent type theory such as Lean 4 requires care over a subtle point that mathematicians routinely pass over in prose: *total functions*. In classical analysis, $zeta(s)$ is undefined at its pole $s = 1$, or takes the value $oo$ on the Riemann sphere $hat(bb(C))$. In Lean 4's Mathlib library, however, `riemannZeta` has type `ℂ → ℂ`—it is a total function returning a complex number for every input `s : ℂ`, including `s = 1`. To avoid exposing an arbitrary junk value at the pole (in Mathlib, `riemannZeta 1` is defined via the constant term of the Laurent expansion, which happens to be nonzero, though users should never rely on that convention), Mathlib's official definition of `RiemannHypothesis` explicitly includes the guard `s ≠ 1` alongside the exclusion of the trivial zeros `s = -2 * (n + 1)` for `n : ℕ`.

  #lean-note(
    title: "Lean 4 Formalization: Mathlib's RiemannHypothesis and Statements.lean",
    module: "src/Statements.lean & src/Main.lean",
  )[
    In Mathlib (`Mathlib.NumberTheory.LSeries.RiemannZeta`), the Riemann Hypothesis is defined as:
    ```lean
    def RiemannHypothesis : Prop :=
      ∀ (s : ℂ) (_ : riemannZeta s = 0)
        (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
        s.re = 1 / 2
    ```
    In the verified repository `leanprover-community/riemann-hypothesis`, the top-level specification file `src/Statements.lean` states the Riemann Hypothesis and three progressively stronger formulations for Dirichlet $L$-functions:
    ```lean
    def RiemannZetaZerosOnLine : Prop :=
      ∀ s : ℂ, riemannZeta s = 0 →
        (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

    def DirichletLNonvanishingRightOfHalf : Prop :=
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

    def DirichletLZerosOnLine : Prop :=
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
    ```
    Notice that `RiemannZetaZerosOnLine` is *definitionally equal* to Mathlib's `RiemannHypothesis`. Indeed, in `src/Main.lean`, once `riemannHypothesis : RiemannHypothesis` is deduced from `DirichletLNonvanishingRightOfHalf` (via `Claim.zeta`), the proof of `RiemannZetaZerosOnLine` is literally a single identifier:
    ```lean
    theorem riemannHypothesis : RiemannHypothesis :=
      Claim.zeta LFunction_ne_zero_of_half_lt_re

    theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine :=
      riemannHypothesis
    ```
    The reduction from `DirichletLNonvanishingRightOfHalf` to `RiemannHypothesis` uses only the functional equation and the nonvanishing of $zeta(s)$ in $op("Re")(s) > 1$ (and on $op("Re")(s) = 1$, which is already subsumed by $1 / 2 < op("Re")(s)$!). Thus proving that no Dirichlet $L$-function vanishes in the half-plane $op("Re")(s) > 1 / 2$ immediately settles both RH and GRH.
  ]

  This observation already foreshadows a central strategic feature of the Alpöge–Claude proof: rather than attacking $zeta(s)$ in isolation, it proves the *Generalized Riemann Hypothesis* simultaneously for all Dirichlet $L$-functions $L(s, chi)$—establishing nonvanishing in the open half-plane $op("Re")(s) > 1 / 2$. In Chapter 2, we extend the classical theory of this chapter from $zeta(s)$ to Dirichlet $L$-functions, introducing Dirichlet characters, Gauss sums, and the functional equation of $Lambda(s, chi)$.

  #exercises((
    [
      Let $f : bb(N)_(>= 1) -> bb(C)$ be a *completely multiplicative* arithmetic function (meaning $f(m n) = f(m) f(n)$ for all $m, n >= 1$ and $f(1) = 1$) such that $|f(n)| <= n^alpha$ for some $alpha in bb(R)$. Prove that the Dirichlet series $D_f (s) = sum_(n=1)^oo f(n) n^(-s)$ converges absolutely for $op("Re")(s) > alpha + 1$, admits the Euler product $D_f (s) = product_p (1 - f(p) p^(-s))^(-1)$, and satisfies $-D_f '(s) / D_f (s) = sum_(n=1)^oo Lambda(n) f(n) n^(-s)$ in this half-plane.
    ],
    [
      (*Euler–Maclaurin continuation and values at negative integers.*) Using repeated integration by parts with the periodic Bernoulli polynomials $tilde(B)_k (x) = B_k ({x})$ starting from Proposition 1.2, prove that for every integer $m >= 1$, $zeta(s)$ extends meromorphically to $op("Re")(s) > 1 - m$. Deduce that for every integer $n >= 1$,
      $ zeta(1 - n) = - B_n / n, $
      where $B_n$ is the $n$-th Bernoulli number (with $B_1 = -1/2$, $B_2 = 1/6$, $B_3 = 0$, $B_4 = -1/30, dots.c$). Verify that this reproduces $zeta(0) = -1/2$, $zeta(-1) = -1/12$, and $zeta(-2k) = 0$ for all $k >= 1$.
    ],
    [
      (*Riemann's first proof of the analytic continuation.*) For $op("Re")(s) > 1$, prove the integral identity
      $ Gamma(s) zeta(s) = integral_0^oo x^(s-1) / (e^x - 1) dif x. $
      By replacing the ray $[0, oo)$ with a Hankel contour $cal(H)$ that loops from $+oo$ along the upper side of the positive real axis, encircles $0$ positively at small radius $epsilon < 2 pi$, and returns to $+oo$ along the lower side, prove that
      $ zeta(s) = (Gamma(1 - s)) / (2 pi i) integral_(cal(H)) (-z)^(s-1) / (e^z - 1) dif z $
      defines the meromorphic continuation of $zeta(s)$ to all of $bb(C)$. By expanding the Hankel contour to circles of radius $(2 N + 1) pi$ and computing the residues at $z = plus.minus 2 pi i k$, recover the asymmetric functional equation (Corollary 1.12).
    ],
    [
      (*Special value $zeta'(0)$.*) Starting from the asymmetric functional equation $zeta(1 - s) = 2 (2 pi)^(-s) cos(pi s / 2) Gamma(s) zeta(s)$ and using $zeta(s) = (s - 1)^(-1) + gamma + O(s - 1)$ as $s -> 1$, compute $zeta'(0)$ directly and verify that $zeta'(0) = -frac(1, 2) log(2 pi)$.
    ],
    [
      (*Classical de la Vallée Poussin zero-free region.*) Combine Mertens' $3$-$4$-$1$ inequality (Theorem 1.14) with the partial-fraction expansion of $zeta'(s) / zeta(s)$ (Theorem 1.17) and the bound $-op("Re")(zeta'(s)/zeta(s)) <= sum_rho op("Re")(-1 / (s - rho)) + C log(|t| + 2)$ (for $1 < sigma <= 2$, $|t| >= 2$) to prove that there exists an absolute constant $c > 0$ such that $zeta(sigma + i t) != 0$ whenever
      $ sigma >= 1 - c / (log(|t| + 2)). $
      *(Hint: If $rho_0 = beta_0 + i gamma_0$ is a zero with $|gamma_0| >= 2$, apply Mertens' inequality at $sigma = 1 + delta / log(|gamma_0| + 2)$ and $t = gamma_0$, keeping only the $rho = rho_0$ term in the $4$-weighted sum and dropping all other zero terms by positivity of $op("Re")(1 / (s - rho))$.)*
    ],
    [
      (*Zero-density sum and the constant $B$.*) Using the Hadamard product (Theorem 1.17) and $Xi(s) = Xi(1 - s)$, give a direct proof of the identity
      $ sum_rho 1 / (rho (1 - rho)) = 2 + gamma - log(4 pi) approx 0.0461914. $
      Assuming that the first nontrivial zero has ordinate $gamma_1 approx 14.1347$ (and $beta_1 = 1/2$), check numerically how much of the total sum is already accounted for by the single conjugate pair $1/2 plus.minus i gamma_1$.
    ],
    [
      (*Alternating Dirichlet eta function.*) Define $eta(s) = sum_(n=1)^oo (-1)^(n-1) n^(-s)$ for $op("Re")(s) > 0$. Prove that $eta(s) = (1 - 2^(1-s)) zeta(s)$ for all $s in bb(C) without {1}$. Deduce that $zeta(sigma) < 0$ for all real $sigma in (0, 1)$, and verify that this justifies the claim $Xi(sigma) > 0$ for all $sigma in bb(R)$ used in the proof of Theorem 1.18.
    ],
    [
      (*Smoothed explicit formula.*) Define the integrated Chebyshev function $psi_1 (x) = integral_1^x psi(u) dif u = sum_(n <= x) Lambda(n) (x - n)$. Using the contour integral
      $ psi_1 (x) = 1 / (2 pi i) integral_(c - i oo)^(c + i oo) (- (zeta'(s)) / zeta(s)) x^(s+1) / (s (s + 1)) dif s quad (c > 1), $
      prove that for all $x > 1$,
      $ psi_1 (x) &= x^2 / 2 - sum_rho x^(rho + 1) / (rho (rho + 1)) - x (zeta'(0)) / zeta(0) \ & quad + (zeta'(-1)) / zeta(-1) - sum_(m=1)^oo x^(1 - 2 m) / (2 m (2 m - 1)), $
      where the sum over nontrivial zeros now converges *absolutely*. Show how this implies that if $op("Re")(rho) <= Theta$ for all nontrivial zeros, then $psi(x) = x + O(x^((1 + Theta)/2))$ by differencing $psi_1 (x + h) - psi_1 (x)$ with an optimal choice of $h$—and compare this with the sharper $O(x^Theta (log x)^2)$ from Theorem 1.22.
    ],
    [
      (*Landau's theorem and the abscissa of holomorphicity.*) Let $Theta = sup {op("Re")(rho) : zeta(rho) = 0, space 0 < op("Re")(rho) < 1}$. Generalize the proof of Theorem 1.23 to show that $psi(x) = x + O_epsilon (x^(Theta + epsilon))$ for every $epsilon > 0$, and conversely that $psi(x) - x = Omega_plus.minus (x^(Theta - epsilon))$ cannot be improved to $O(x^(Theta - epsilon))$ for any $epsilon > 0$. Why does the non-oscillating sign of $psi(x) - x$ (if $psi(x) - x$ were eventually of constant sign) force a real singularity at $s = Theta$ by Landau's theorem on Dirichlet integrals with nonnegative integrands?
    ],
  ))
]
