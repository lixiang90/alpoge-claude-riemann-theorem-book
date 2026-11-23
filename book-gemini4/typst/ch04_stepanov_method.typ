// ============================================================================
// Chapter 4: Stepanov's Method and the Multiplicity Paradigm
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch04() = [
  #chapter(
    "Stepanov's Method and the Multiplicity Paradigm",
    short-title: "Stepanov's Method and Multiplicity",
    epigraph: "In Stepanov's argument resolving Riemann over function fields one uses a divisor involving multiplicity. This argument is a descendant of Stepanov's, but multiplicity is hard to find over the integers, corresponding to something like differentiating whole numbers... The line: for the von Mangoldt sum of length X, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was √X. (And yet, what else could it be?)",
    epigraph-source: "Levent Alpöge, Remark (November 20, 2026)",
    overview: [
      In 1969, Sergei Stepanov stunned the mathematical world by giving a completely elementary proof of the Hasse–Weil bound for hyperelliptic curves over finite fields, bypassing Weil's intersection theory on surfaces and Grothendieck's étale cohomology alike. The engine of Stepanov's proof is an auxiliary polynomial forced to vanish to high multiplicity $m approx sqrt(q)$ at every rational point. This chapter presents a complete, self-contained exposition of Stepanov's method—developing the Hasse–Weil zeta function, Hasse–Schmidt hyperderivatives in positive characteristic, and the full proof of the Hasse–Weil bound via base change over $bb(F)_(q^n)$. We then confront the central obstruction to transferring Stepanov's paradigm to the classical Riemann Hypothesis over $bb(Z)$: integers admit no linear derivation controlling both divisibility and archimedean height. Finally, we trace the conceptual bridge discovered by Alpöge and Claude—from the elementary sign-only identity $q N = M^k + R$ on a path quadric to determinants of automorphic periods and a chain of $m approx sqrt(X)$ iterated theta lifts between totally definite unitary groups.
    ],
    label-name: "ch:stepanov",
  )

  In Chapter 3 we surveyed two monumental geometric proofs of the Riemann Hypothesis for curves over finite fields: André Weil's 1948 proof via the Castelnuovo–Severi inequality on the self-product $C times C$, and Pierre Deligne's 1974 proof via $ell$-adic cohomology and the monodromy of Lefschetz pencils. For two decades after Weil's work, it was widely believed that the square-root bound $|N_q (C) - (q + 1)| <= 2 g sqrt(q)$ lay inextricably deep within algebraic geometry—accessible only through intersection theory on surfaces or the full cohomological machinery of schemes.

  That belief was shattered in 1969 by Sergei A. Stepanov, who proved the Hasse–Weil bound for hyperelliptic curves $y^2 = f(x)$ over prime fields $bb(F)_p$ using nothing beyond univariate polynomials, linear algebra, and derivatives. Within five years, Stepanov (1970–1972), Wolfgang M. Schmidt (1973), and Enrico Bombieri (1973) extended the method to arbitrary prime powers $bb(F)_q$ and arbitrary smooth projective curves $C \/ bb(F)_q$, yielding a ten-page proof of the Riemann Hypothesis for curves over finite fields.

  For the reader of this monograph, Stepanov's method is far more than a historical gem or a pedagogical shortcut. As Levent Alpöge emphasized in his November 2026 announcement, the Alpöge–Claude proof of the classical Riemann Hypothesis is a *direct conceptual descendant* of Stepanov's method. Every major architectural feature of Parts II and III—the chain of $m approx sqrt(X)$ iterated theta lifts, the local divisibility of CM theta values under invariant derivations, the Bost slope inequality, the seesaw period calculation, and the cyclotomic Iwasawa tower—has a transparent prototype inside Stepanov's proof over $bb(F)_q$. Mastering Stepanov's method in full detail is therefore the single best preparation for understanding why the proof over $bb(Z)$ works.

  == The Hasse–Weil Bound for Hyperelliptic Curves over $bb(F)_q$

  Let $q = p^r$ be a power of an odd prime $p$, and let $bb(F)_q$ denote the finite field with $q$ elements. Fix an algebraic closure $overline(bb(F))_q$ of $bb(F)_q$. For each integer $n >= 1$, there is a unique degree-$n$ extension $bb(F)_(q^n) subset.eq overline(bb(F))_q$, characterized as the fixed field of the $n$-th iterate of the $q$-power Frobenius automorphism $x |-> x^q$.

  Let $f(x) in bb(F)_q [x]$ be a squarefree polynomial of odd degree
  $ d = op("deg")(f) = 2 g + 1 >= 3, $
  where $g >= 1$ is an integer. (The case of even degree $d = 2 g + 2$ is closely parallel and is treated in Exercise 4.5.) The affine plane curve
  $ C_0 : y^2 = f(x) $
  is nonsingular over $bb(F)_q$: its partial derivatives are $2 y$ and $-f'(x)$, and since $p != 2$ and $f$ is squarefree, $f(x)$ and $f'(x)$ have no common root in $overline(bb(F))_q$. Its smooth projective completion $C \/ bb(F)_q$ is a smooth, geometrically irreducible projective curve of genus $g$, obtained by adjoining a single smooth $bb(F)_q$-rational point $oo$ at infinity.

  For each $n >= 1$, let
  $ N_(q^n) (C) = |C(bb(F)_(q^n))| = 1 + |\{ (x, y) in bb(F)_(q^n)^2 : y^2 = f(x) \}| $
  denote the number of $bb(F)_(q^n)$-rational points on $C$. Because $q$ is odd, we have the unique nontrivial quadratic character $chi_(q^n) : bb(F)_(q^n)^* -> \{ plus.minus 1 \}$, extended by $chi_(q^n) (0) = 0$. Explicitly, Euler's criterion gives
  $ chi_(q^n) (u) = u^((q^n - 1) / 2) in \{ -1, 0, 1 \} quad "for all" u in bb(F)_(q^n). $
  For any $x in bb(F)_(q^n)$, the equation $y^2 = f(x)$ has $1 + chi_(q^n) (f(x))$ solutions $y in bb(F)_(q^n)$: two if $f(x)$ is a nonzero square, one if $f(x) = 0$, and zero if $f(x)$ is a non-square. Summing over $x in bb(F)_(q^n)$ and adding the single point at infinity yields the exact formula
  $ N_(q^n) (C) = 1 + sum_(x in bb(F)_(q^n)) (1 + chi_(q^n) (f(x))) = (q^n + 1) + sum_(x in bb(F)_(q^n)) chi_(q^n) (f(x)). $

  The quantity $q^n + 1 = |bb(P)^1 (bb(F)_(q^n))|$ is the "expected" number of points if $f(x)$ behaved like a uniformly random coin flip between squares and non-squares. The central theorem governing the fluctuation around $q^n + 1$ is the Hasse–Weil bound.

  #theorem(title: "Hasse–Weil Bound for Hyperelliptic Curves")[
    Let $q$ be an odd prime power, and let $C \/ bb(F)_q$ be the smooth projective hyperelliptic curve of genus $g >= 1$ defined by $y^2 = f(x)$, where $f in bb(F)_q [x]$ is squarefree of odd degree $d = 2 g + 1$. Then
    $ |N_q (C) - (q + 1)| = |sum_(x in bb(F)_q) chi_q (f(x))| <= 2 g sqrt(q). $
  ]

  To see why this bound is equivalent to the Riemann Hypothesis for the curve $C$, recall from Chapter 3 the *Hasse–Weil zeta function* of $C \/ bb(F)_q$, defined as a formal power series in $bb(Q)[[T]]$ by
  $ Z(C, T) = exp( sum_(n=1)^oo N_(q^n) (C) T^n / n ). $
  Equivalently, taking the logarithmic derivative gives the generating function of point counts:
  $ T (Z'(C, T)) / (Z(C, T)) = sum_(n=1)^oo N_(q^n) (C) T^n. $
  By the Riemann–Roch theorem for the curve $C \/ bb(F)_q$ (proved in 1931 by F. K. Schmidt, well before Weil's proof of the Riemann Hypothesis), $Z(C, T)$ is a rational function of $T$ of the exact form
  $ Z(C, T) = (P(T)) / ((1 - T)(1 - q T)), $
  where $P(T) in bb(Z)[T]$ is a polynomial of degree $2 g$ with $P(0) = 1$, satisfying the functional equation
  $ Z(C, 1 / (q T)) = q^(1 - g) T^(2 - 2 g) Z(C, T), $
  or equivalently $q^g T^(2g) P(1 / (q T)) = P(T)$. Factoring $P(T)$ over $bb(C)$ in terms of its *inverse roots* (the Frobenius eigenvalues on $H^1 (C)$) as
  $ P(T) = product_(i=1)^(2g) (1 - alpha_i T), $
  the functional equation implies that the multiset $\{ alpha_1, dots.c, alpha_(2g) \}$ is invariant under the involution $alpha |-> q \/ alpha$. Taking the logarithmic derivative of $Z(C, T) = P(T) / ((1 - T)(1 - q T))$ and comparing coefficients of $T^n$ produces the explicit trace formula
  $ N_(q^n) (C) = q^n + 1 - sum_(i=1)^(2g) alpha_i^n quad (n >= 1). $

  In terms of the variable $s$ with $T = q^(-s)$, the zeros of $Z(C, q^(-s))$ satisfy $q^s = alpha_i$, so $op("Re")(s) = 1\/2$ if and only if $|alpha_i| = sqrt(q)$. Thus the *Riemann Hypothesis for $C \/ bb(F)_q$* is the assertion that $|alpha_i| = sqrt(q)$ for every $1 <= i <= 2 g$.

  A remarkable feature of the finite-field setting—and one whose arithmetic analogue will reappear in Chapter 13 as the Iwasawa tower—is that a *crude* bound on $N_(q^n) (C)$ with an arbitrary constant $c_0$ independent of $n$ automatically self-improves to the *exact* Riemann Hypothesis and the sharp constant $2 g$.

  #proposition(title: "Self-Improvement via Base Change to " + $bb(F)_(q^n)$)[
    Let $C \/ bb(F)_q$ be a smooth projective curve of genus $g$ with zeta function $Z(C, T) = P(T) / ((1 - T)(1 - q T))$, $P(T) = product_(i=1)^(2g) (1 - alpha_i T)$. The following statements are equivalent:
    1. *(Riemann Hypothesis)* $|alpha_i| = sqrt(q)$ for all $1 <= i <= 2 g$.
    2. *(Sharp Hasse–Weil bound)* $|N_(q^n) (C) - (q^n + 1)| <= 2 g q^(n/2)$ for all $n >= 1$.
    3. *(Asymptotic square-root bound)* There exists a constant $c_0 > 0$, independent of $n$, such that
       $ |N_(q^n) (C) - (q^n + 1)| <= c_0 q^(n/2) quad "for all" n >= 1. $
  ]

  #proof[
    The implications (1) $==>$ (2) $==>$ (3) are immediate from $N_(q^n) (C) - (q^n + 1) = - sum_(i=1)^(2g) alpha_i^n$ and the triangle inequality (taking $c_0 = 2 g$).

    To prove (3) $==>$ (1), form the power series
    $ F(T) = sum_(n=1)^oo (N_(q^n) (C) - (q^n + 1)) T^n = - sum_(i=1)^(2g) (alpha_i T) / (1 - alpha_i T). $
    By hypothesis (3), the coefficients satisfy $|N_(q^n) (C) - (q^n + 1)| <= c_0 q^(n/2)$, so by the root test the power series $F(T)$ converges absolutely on the open disk $|T| < q^(-1/2)$ and therefore defines a holomorphic function on $|T| < q^(-1/2)$.

    On the other hand, the right-hand side is a rational function of $T$ whose potential poles are the points $T = 1 \/ alpha_i$. Crucially, *no poles can cancel*: if $alpha in bb(C)^*$ occurs with multiplicity $m_alpha >= 1$ among $\{ alpha_1, dots.c, alpha_(2g) \}$, then the residue of $F(T)$ at $T = 1 \/ alpha$ is
    $ op("Res")_(T = 1 \/ alpha) F(T) = m_alpha / alpha != 0, $
    because every term with $alpha_i = alpha$ contributes the same positive integer $+1$ to the coefficient of $(1 - alpha T)^(-1)$. Since $F(T)$ is holomorphic on $|T| < q^(-1/2)$, none of its poles $1 \/ alpha_i$ can lie in this disk. Hence $|1 \/ alpha_i| >= q^(-1/2)$, which means $|alpha_i| <= sqrt(q)$ for every $1 <= i <= 2 g$.

    Finally, the functional equation pairs each inverse root $alpha_i$ with $q \/ alpha_i$. Applying the same inequality to $q \/ alpha_i$ gives $|q \/ alpha_i| <= sqrt(q)$, hence $|alpha_i| >= sqrt(q)$. Therefore $|alpha_i| = sqrt(q)$ for all $1 <= i <= 2 g$.
  ]

  Notice the crucial asymmetry if one only knows a *one-sided* upper bound $N_(q^n) (C) <= q^n + 1 + c_0 q^(n/2)$. As shown in Exercise 4.2, a one-sided upper bound alone cannot rule out a positive real inverse root $alpha_1 > sqrt(q)$ (which makes $- alpha_1^n$ large and *negative*, depressing $N_(q^n) (C)$ below $q^n + 1$). For hyperelliptic curves, however, a one-sided upper bound *is* sufficient, thanks to quadratic twists!

  #lemma(title: "From Upper Bounds to Two-Sided Bounds via Quadratic Twists")[
    Let $C \/ bb(F)_q$ be the hyperelliptic curve $y^2 = f(x)$ over an odd prime power field $bb(F)_q$. For any $n >= 1$, choose a non-square $nu_n in bb(F)_(q^n)^*$ and let $C'_n \/ bb(F)_(q^n)$ be the quadratic twist defined by $y^2 = nu_n f(x)$ (equivalently $nu_n^(-1) y^2 = f(x)$). Then $C'_n$ is a smooth projective hyperelliptic curve of the same genus $g$ over $bb(F)_(q^n)$, and
    $ N_(q^n) (C) + N_(q^n) (C'_n) = 2 (q^n + 1). $
    Consequently, if there exists a constant $c_0$ (depending only on $op("deg")(f)$) such that *every* hyperelliptic curve $y^2 = tilde(f)(x)$ of degree $d$ over every odd prime power field $bb(F)_Q$ satisfies the upper bound $N_Q <= Q + 1 + c_0 sqrt(Q)$, then $|N_(q^n) (C) - (q^n + 1)| <= c_0 q^(n/2)$ for all $n >= 1$, and hence the exact Hasse–Weil bound $|N_q (C) - (q + 1)| <= 2 g sqrt(q)$ holds.
  ]

  #proof[
    Since $nu_n$ is a non-square in $bb(F)_(q^n)^*$, we have $chi_(q^n) (nu_n) = -1$. Hence for every $x in bb(F)_(q^n)$,
    $ chi_(q^n) (nu_n f(x)) = chi_(q^n) (nu_n) chi_(q^n) (f(x)) = - chi_(q^n) (f(x)), $
    including when $f(x) = 0$. Summing over $x in bb(F)_(q^n)$ gives
    $ N_(q^n) (C) + N_(q^n) (C'_n) &= 2 (q^n + 1) + sum_(x in bb(F)_(q^n)) (chi_(q^n) (f(x)) - chi_(q^n) (f(x))) \ &= 2 (q^n + 1). $
    Applying the hypothesized upper bound to $C'_n$ over $bb(F)_(q^n)$ gives $N_(q^n) (C'_n) <= q^n + 1 + c_0 q^(n/2)$, which immediately rearranges to the lower bound
    $ N_(q^n) (C) = 2(q^n + 1) - N_(q^n) (C'_n) >= q^n + 1 - c_0 q^(n/2). $
    Combining this with the upper bound for $C$ over $bb(F)_(q^n)$ yields $|N_(q^n) (C) - (q^n + 1)| <= c_0 q^(n/2)$ for all $n >= 1$. By Proposition 4.2, $|alpha_i| = sqrt(q)$ for all $i$, and therefore $|N_q (C) - (q + 1)| <= 2 g sqrt(q)$.
  ]

  #remark[
    This reduction is conceptually liberating. To prove the full Hasse–Weil theorem—with its sharp constant $2 g$ and both upper and lower bounds—it suffices to prove a *single, sloppy upper bound* $N_q (C) <= q + 1 + c_0 sqrt(q)$ for all odd prime powers $q$ and all squarefree $f in bb(F)_q [x]$ of odd degree $d$, where $c_0$ depends only on $d$. Even better, if $q$ is bounded in terms of $d$, the trivial bound $N_q (C) <= 2 q + 1$ already suffices. All the mathematical work therefore concentrates on bounding the number of $x in bb(F)_q$ where $f(x)$ is a nonzero square when $q$ is large.
  ]

  == Hasse–Schmidt Hyperderivatives in Positive Characteristic

  In characteristic zero, a polynomial $Phi(x)$ vanishes to order at least $m$ at a point $a$ if and only if its first $m$ ordinary derivatives $Phi(a), Phi'(a), dots.c, Phi^((m-1)) (a)$ all vanish. Over a field $bb(F)_q$ of prime characteristic $p > 0$, this criterion breaks down as soon as $m > p$: the $p$-th ordinary derivative of *every* polynomial is identically zero because
  $ (d / (d x))^p (x^n) = n (n - 1) dots.c (n - p + 1) x^(n - p) equiv 0 quad ("mod" p), $
  the product of $p$ consecutive integers always being divisible by $p$. Even the first derivative fails to detect multiplicities on $p$-th powers, since $(d \/ d x)(g(x)^p) = p g(x)^(p-1) g'(x) = 0$.

  In Stepanov's original 1969 paper, he worked over a *prime* field $bb(F)_p$ where the optimal multiplicity satisfies $m approx sqrt(p) < p$; thus ordinary derivatives narrowly survived! However, to apply Proposition 4.2 and pass to extension fields $bb(F)_(q^n)$ with $q^n = p^(r n)$ large, we *must* handle multiplicities $m approx p^(r n \/ 2) >> p$. The right algebraic tool—introduced by Helmut Hasse and Friedrich Karl Schmidt in 1937 and brought into Stepanov's method by Stepanov (1970) and Schmidt (1973)—is the family of *Hasse–Schmidt hyperderivatives* (also called *Hasse derivatives*).

  #definition(title: "Hasse–Schmidt Hyperderivatives")[
    Let $R$ be any commutative ring with unity, and let $t$ be an indeterminate over $R[x]$. For any polynomial $h(x) in R[x]$, expand $h(x + t) in R[x][t]$ in powers of $t$:
    $ h(x + t) = sum_(k=0)^oo (D^((k)) h)(x) t^k. $
    The coefficient $(D^((k)) h)(x) in R[x]$ is called the *$k$-th Hasse–Schmidt hyperderivative* (or *$k$-th Hasse derivative*) of $h$.
  ]

  Evaluating the binomial theorem on a monomial $x^n$ immediately gives the explicit formula
  $ D^((k)) (x^n) = binom(n, k) x^(n - k) $
  (with the convention $binom(n, k) = 0$ for $k > n$), extended $R$-linearly to all of $R[x]$. Notice that in characteristic zero,
  $ D^((k)) = 1 / (k!) (d / (d x))^k. $
  The miracle of the Hasse derivative is that the binomial coefficients $binom(n, k)$ are integers, so dividing by $k!$ *before* reducing modulo $p$ produces well-defined $R$-linear operators $D^((k)) : R[x] -> R[x]$ over *any* ring $R$, including $bb(F)_q$.

  #proposition(title: "Algebraic Properties of Hasse–Schmidt Hyperderivatives")[
    Let $R$ be a commutative ring and $h, h_1, h_2 in R[x]$. Then for all integers $k, l >= 0$:
    1. *(Linearity and normalization)* $D^((k))$ is $R$-linear, $D^((0)) h = h$, and $D^((1)) h = h'$ is the ordinary formal derivative.
    2. *(Leibniz rule)* $D^((k)) (h_1 h_2) = sum_(i+j=k) (D^((i)) h_1)(D^((j)) h_2)$.
    3. *(Composition rule)* $(D^((k)) compose D^((l))) (h) = binom(k + l, k) D^((k + l)) (h)$.
    4. *(Degree control)* If $h != 0$, then $op("deg")(D^((k)) h) <= op("deg")(h) - k$, with $D^((k)) h = 0$ whenever $k > op("deg")(h)$.
    5. *(Frobenius linearity in characteristic $p$)* Suppose $R$ is an $bb(F)_p$-algebra and $q = p^r$ is a power of $p$. Then for any $g(x) in R[x]$,
       $ D^((k)) (g(x)^q) = cases( (D^((k \/ q)) g)(x)^q & "if" q divides k, 0 & "if" q divides.not k. ) $
       In particular, for every $0 <= k < q$, the operator $D^((k))$ is $R[x^q]$-linear:
       $ D^((k)) (g(x)^q h(x)) = g(x)^q (D^((k)) h)(x). $
  ]

  #proof[
    Property (1) follows directly from the definition, since the constant term of $h(x + t)$ in $t$ is $h(x)$ and the linear coefficient is $h'(x)$.

    For (2), expand both sides of $(h_1 h_2)(x + t) = h_1 (x + t) h_2 (x + t)$ in $R[x][t]$ and compare the coefficient of $t^k$:
    $ sum_(k >= 0) D^((k)) (h_1 h_2)(x) t^k = (sum_(i >= 0) (D^((i)) h_1)(x) t^i)(sum_(j >= 0) (D^((j)) h_2)(x) t^j). $

    For (3), introduce two independent indeterminates $t, u$ and expand $h(x + t + u)$ in two ways:
    $ h((x + t) + u) = sum_(k >= 0) (D^((k)) h)(x + t) u^k = sum_(k, l >= 0) (D^((l)) D^((k)) h)(x) t^l u^k, $
    while on the other hand
    $ h(x + (t + u)) &= sum_(m >= 0) (D^((m)) h)(x) (t + u)^m \ &= sum_(k, l >= 0) binom(k + l, k) (D^((k + l)) h)(x) t^l u^k. $
    Comparing the coefficient of $t^l u^k$ gives (3).

    Property (4) is immediate from $D^((k)) (x^n) = binom(n, k) x^(n - k)$.

    For (5), because $R$ has characteristic $p$ and $q = p^r$, the Frobenius map $u |-> u^q$ is a ring endomorphism of $R[x][t]$. Therefore
    $ g(x + t)^q = (sum_(j >= 0) (D^((j)) g)(x) t^j)^q = sum_(j >= 0) (D^((j)) g)(x)^q t^(j q). $
    Comparing the coefficient of $t^k$ yields the formula for $D^((k)) (g(x)^q)$. When $0 <= k < q$, the only term with $j q <= k$ is $j = 0$, so $D^((0)) (g^q) = g^q$ and $D^((i)) (g^q) = 0$ for all $1 <= i <= k$. The Leibniz rule (2) then collapses to $D^((k)) (g^q h) = g^q D^((k)) h$.
  ]

  The fundamental reason Hasse–Schmidt hyperderivatives rescue Stepanov's method in arbitrary characteristic is that they characterize vanishing order *without any restriction on $m$ relative to $p$*.

  #theorem(title: "Hyperderivative Vanishing Criterion")[
    Let $F$ be any field, $Phi(x) in F[x]$ a polynomial, $a in F$, and $m >= 1$ an integer. Then $(x - a)^m$ divides $Phi(x)$ in $F[x]$ (written $op("ord")_a (Phi) >= m$) if and only if
    $ (D^((k)) Phi)(a) = 0 quad "for all" 0 <= k < m. $
    Consequently, if $Phi(x) in F[x]$ is nonzero and vanishes to order at least $m$ at every point of a finite subset $S subset.eq F$, then
    $ m dot.c |S| <= op("deg")(Phi). $
  ]

  #proof[
    Substituting $x = a$ into the defining identity $Phi(x + t) = sum_(k >= 0) (D^((k)) Phi)(x) t^k$ gives
    $ Phi(a + t) = sum_(k=0)^(op("deg")(Phi)) (D^((k)) Phi)(a) t^k. $
    Replacing $t$ by $x - a$ yields the exact Taylor expansion
    $ Phi(x) = sum_(k=0)^(op("deg")(Phi)) (D^((k)) Phi)(a) (x - a)^k. $
    Since $1, (x - a), (x - a)^2, dots.c$ form a basis of $F[x]$, we have $(x - a)^m divides Phi(x)$ if and only if the coefficients $(D^((k)) Phi)(a)$ vanish for $0 <= k < m$.

    For the second statement, because $F[x]$ is a unique factorization domain and the linear factors $x - a$ ($a in S$) are pairwise coprime, the product $product_(a in S) (x - a)^m$ divides $Phi(x)$. Since $Phi != 0$, comparing degrees gives $m dot.c |S| <= op("deg")(Phi)$.
  ]

  To apply $D^((k))$ to Stepanov's auxiliary polynomial for $y^2 = f(x)$, we need one further algebraic lemma describing how $D^((k))$ acts on the high power $f(x)^((q - 1) / 2)$. Remarkably, although $f(x)^((q - 1) / 2)$ has huge degree $d(q - 1)\/2$, its $k$-th Hasse derivative is simply a *low-degree rational function* times $f(x)^((q - 1) / 2)$ itself!

  #lemma(title: "Hyperderivatives of Powers of " + $f(x)$)[
    Let $F$ be a field, $f(x) in F[x]$ a polynomial of degree $d >= 1$, and $s >= 0$ an integer. Then for every integer $k >= 0$, there exists a polynomial $Q_k (x) in F[x]$ of degree at most $k (d - 1)$ such that
    $ f(x)^k dot.c D^((k)) (f(x)^s) = Q_k (x) dot.c f(x)^s. $
  ]

  #proof[
    Work in the formal power series ring $F(x)[[t]]$ over the rational function field $F(x)$. By definition of the Hasse derivatives of $f$,
    $ f(x + t) = f(x) + sum_(j=1)^d (D^((j)) f)(x) t^j = f(x) (1 + u(t)), $
    where
    $ u(t) = sum_(j=1)^d ((D^((j)) f)(x)) / (f(x)) t^j in t dot.c F(x)[[t]]. $
    Raising both sides to the $s$-th power by the binomial theorem gives
    $ f(x + t)^s = f(x)^s (1 + u(t))^s = f(x)^s sum_(r=0)^s binom(s, r) u(t)^r. $
    Comparing the coefficient of $t^k$ on both sides, we obtain
    $ D^((k)) (f(x)^s) = f(x)^s sum_(r=0)^(min(k, s)) binom(s, r) [t^k] (u(t)^r), $
    where $[t^k](u(t)^r)$ denotes the coefficient of $t^k$ in $u(t)^r$. (The sum truncates at $r <= k$ because $u(t)$ has $t$-order at least $1$, so $u(t)^r$ is divisible by $t^r$.)

    Explicitly, for each $0 <= r <= min(k, s)$,
    $ [t^k](u(t)^r) = sum_(vec(delim: #none, j_1 + dots.c + j_r = k, 1 <= j_i <= d)) (product_(i=1)^r (D^((j_i)) f)(x)) / (f(x)^r). $
    Multiplying through by $f(x)^k$ clears all denominators (since $r <= k$) and defines the polynomial
    $ Q_k (x) = sum_(r=0)^(min(k, s)) binom(s, r) f(x)^(k - r) sum_(vec(delim: #none, j_1 + dots.c + j_r = k, 1 <= j_i <= d)) product_(i=1)^r (D^((j_i)) f)(x) in F[x]. $
    Finally, by Proposition 4.6(4), each factor $(D^((j_i)) f)(x)$ has degree at most $d - j_i$. Therefore every summand in $Q_k (x)$ has degree at most
    $ (k - r) d + sum_(i=1)^r (d - j_i) = (k - r) d + r d - k = k (d - 1). $
    Hence $op("deg")(Q_k) <= k (d - 1)$ and $f(x)^k D^((k)) (f(x)^s) = Q_k (x) f(x)^s$.
  ]

  #remark[
    In characteristic zero, Lemma 4.8 is familiar from calculus: $(d \/ d x) (f^s) = (s f' \/ f) f^s$, and differentiating $k$ times introduces denominator $f^k$ with numerator degree at most $k(d - 1)$. The point of Lemma 4.8 is that this exact algebraic structure survives intact in positive characteristic when ordinary derivatives are replaced by Hasse–Schmidt hyperderivatives, with *zero* dependence of the degree bound $k(d - 1)$ on the exponent $s = (q - 1) \/ 2$!
  ]

  == Complete Proof of the Hasse–Weil Upper Bound via Stepanov's Method

  We now have every tool needed to execute Stepanov's proof of the Hasse–Weil bound in complete, self-contained detail. Keep an eye on the *three-act structure* of the argument, because the exact same three acts will govern the Alpöge–Claude proof over $bb(Z)$ in Part III:
  1. *Construction by linear algebra (pigeonhole):* Build a nonzero auxiliary polynomial $Phi(x)$ in a carefully chosen Frobenius-structured subspace, forced to vanish to order at least $m$ at every point of interest.
  2. *Non-vanishing:* Prove that the auxiliary object $Phi(x)$ is not identically zero, despite the high-order vanishing constraints.
  3. *Multiplicity–degree comparison and optimization:* Apply $m dot.c |S_+| <= op("deg")(Phi)$ and optimize the multiplicity parameter $m approx sqrt(q)$.

  #theorem(title: "Stepanov's Upper Bound")[
    Let $q$ be an odd prime power, and let $f(x) in bb(F)_q [x]$ be a squarefree polynomial of odd degree $d = 2 g + 1 >= 3$. Then the number of $bb(F)_q$-rational points on the hyperelliptic curve $C : y^2 = f(x)$ satisfies
    $ N_q (C) <= q + 1 + 4 d sqrt(q). $
  ]

  #proof[
    Partition $bb(F)_q$ into three disjoint subsets according to the value of $chi_q (f(a))$:
    $ S_+ &= \{ a in bb(F)_q : chi_q (f(a)) = +1 \}, \ S_- &= \{ a in bb(F)_q : chi_q (f(a)) = -1 \}, \ S_0 &= \{ a in bb(F)_q : f(a) = 0 \}. $
    Since $f$ has degree $d$, we have $|S_0| <= d$, and the total point count is
    $ N_q (C) = 1 + 2 |S_+| + |S_0|. $

    First suppose $q < 4 d^2$. Because each $x in bb(F)_q$ gives at most two affine points $(x, plus.minus y)$, the trivial bound yields
    $ N_q (C) <= 2 q + 1 = q + 1 + q < q + 1 + 2 d sqrt(q) < q + 1 + 4 d sqrt(q). $
    Thus we may assume from now on that $q >= 4 d^2$. Since $d >= 3$, this implies $sqrt(q) >= 2 d >= 6$ and $q >= 36$.

    Set $s = (q - 1) \/ 2$. We seek a nonzero polynomial $Phi(x) in bb(F)_q [x]$ of the Frobenius-structured form
    $ Phi(x) = R_1 (x) + R_2 (x) f(x)^s, $
    where
    $ R_1 (x) = sum_(j=0)^(J-1) P_j (x) x^(j q), quad R_2 (x) = sum_(j=0)^(J-1) Q_j (x) x^(j q), $
    and $P_j (x), Q_j (x) in bb(F)_q [x]$ are polynomials of degree strictly less than $I$, written as
    $ P_j (x) = sum_(i=0)^(I-1) a_(i, j) x^i, quad Q_j (x) = sum_(i=0)^(I-1) b_(i, j) x^i quad (a_(i, j), b_(i, j) in bb(F)_q). $
    Here $I, J, m >= 1$ are integer parameters to be chosen shortly, subject to the constraints
    $ 2 (I - 1) + d < q quad "and" quad m < q. $

    *Step 1: Non-identically-zero (linear independence).*
    We claim that $Phi(x) = 0$ identically in $bb(F)_q [x]$ if and only if all $2 I J$ coefficients $a_(i, j), b_(i, j)$ vanish.

    First note that since $I < q$, the terms $P_j (x) x^(j q)$ for $0 <= j < J$ occupy disjoint degree intervals $[j q, j q + I - 1]$. Hence $R_1 (x) = 0$ if and only if every $P_j (x) = 0$, and similarly $R_2 (x) = 0$ if and only if every $Q_j (x) = 0$.

    Suppose for contradiction that $Phi(x) = R_1 (x) + R_2 (x) f(x)^s = 0$ with not all $a_(i, j), b_(i, j)$ zero. Then neither $R_1$ nor $R_2$ can be zero (since $f != 0$). Rearranging gives $R_1 (x) = - R_2 (x) f(x)^s$. Squaring both sides and multiplying by $f(x)$ yields the polynomial identity
    $ f(x) R_1 (x)^2 = f(x)^q R_2 (x)^2. $
    Let $u = max \{ j : P_j != 0 \}$ and $v = max \{ j : Q_j != 0 \}$. Then $op("deg")(R_1) = u q + op("deg")(P_u)$ and $op("deg")(R_2) = v q + op("deg")(Q_v)$, so
    $ op("deg")(f R_1^2) = 2 u q + (2 op("deg")(P_u) + d), $
    $ op("deg")(f^q R_2^2) = (2 v + d) q + 2 op("deg")(Q_v). $
    By our assumption $2 (I - 1) + d < q$, the remainders satisfy
    $ 0 <= 2 op("deg")(P_u) + d <= 2(I - 1) + d < q, \ 0 <= 2 op("deg")(Q_v) <= 2(I - 1) < q. $
    Hence the quotient of $op("deg")(f R_1^2)$ upon Euclidean division by $q$ is $2 u$, which is *even*, whereas the quotient of $op("deg")(f^q R_2^2)$ upon division by $q$ is $2 v + d$, which is *odd* (because $d = 2 g + 1$ is odd!). Therefore $op("deg")(f R_1^2) != op("deg")(f^q R_2^2)$, a contradiction. This proves that the map $(a_(i, j), b_(i, j)) |-> Phi(x)$ is injective.

    *Step 2: Enforcing vanishing to order $>= m$ on $S_+$.*
    Let $0 <= k < m$. Since $m < q$, Proposition 4.6(5) tells us that $D^((k))$ is $bb(F)_q [x^q]$-linear. Applying $D^((k))$ to $Phi(x)$ via the Leibniz rule (Proposition 4.6(2)) gives
    $ D^((k)) Phi(x) &= sum_(j=0)^(J-1) (D^((k)) P_j)(x) x^(j q) \ & quad + sum_(j=0)^(J-1) x^(j q) sum_(r=0)^k (D^((k - r)) Q_j)(x) dot.c D^((r)) (f(x)^s). $
    Multiply both sides by $f(x)^k$ and apply Lemma 4.8, which writes $f(x)^r D^((r)) (f(x)^s) = H_r (x) f(x)^s$ for a polynomial $H_r (x) in bb(F)_q [x]$ of degree at most $r (d - 1)$ (independent of $a_(i, j), b_(i, j)$):
    $ f(x)^k D^((k)) Phi(x) &= sum_(j=0)^(J-1) f(x)^k (D^((k)) P_j)(x) x^(j q) \ & quad + f(x)^s sum_(j=0)^(J-1) x^(j q) sum_(r=0)^k f(x)^(k - r) (D^((k - r)) Q_j)(x) H_r (x). $

    Now evaluate at any point $a in S_+$. By definition of $S_+$, we have $a^q = a$, $f(a) != 0$, and $f(a)^s = chi_q (f(a)) = 1$. Therefore, $f(a)^k (D^((k)) Phi)(a) = Psi_k (a)$, where $Psi_k (x) in bb(F)_q [x]$ is the polynomial obtained by replacing $x^q$ with $x$ and $f(x)^s$ with $1$:
    $ & Psi_k (x) \ & quad = sum_(j=0)^(J-1) x^j [ f(x)^k (D^((k)) P_j)(x) + sum_(r=0)^k f(x)^(k - r) (D^((k - r)) Q_j)(x) H_r (x) ]. $
    Because $f(a)^k != 0$ for every $a in S_+$, the single polynomial identity $Psi_k (x) = 0$ in $bb(F)_q [x]$ automatically forces $(D^((k)) Phi)(a) = 0$ for *every* $a in S_+$ simultaneously!

    Let us bound the degree of $Psi_k (x)$. For each $0 <= j < J$ and $0 <= r <= k$:
    - The first term has degree at most $(J - 1) + k d + (I - 1 - k) = I + J - 2 + k (d - 1)$.
    - The second term has degree at most
      $ & (J - 1) + (k - r) d + (I - 1 - (k - r)) + r (d - 1) \ & quad = I + J - 2 + k (d - 1). $
    Thus $op("deg")(Psi_k) <= I + J - 2 + k (d - 1)$. Since the coefficients of $Psi_k (x)$ are homogeneous $bb(F)_q$-linear forms in the $2 I J$ unknowns $(a_(i, j), b_(i, j))$, forcing $Psi_k (x) = 0$ identically imposes at most $I + J - 1 + k (d - 1)$ homogeneous linear equations.

    Summing over all $0 <= k < m$, the total number $E$ of homogeneous linear equations required to ensure $Psi_k (x) = 0$ for every $0 <= k < m$ satisfies
    $ E &<= sum_(k=0)^(m-1) (I + J - 1 + k(d - 1)) \ &= m (I + J - 1) + (d - 1) (m (m - 1)) / 2. $

    *Step 3: Parameter choice, pigeonhole, and degree comparison.*
    We now choose $I, m, J$ explicitly:
    - Set $I = (q - d) \/ 2$. Since both $q$ and $d = 2 g + 1$ are odd and $q >= 4 d^2 > d$, $I$ is a positive integer satisfying $2 (I - 1) + d = q - 2 < q$.
    - Set $m = ceil(sqrt(q))$. Since $q >= 36$, we have $sqrt(q) <= m < sqrt(q) + 1 < q$.
    - Observe that
      $ 2 I - m = q - d - m > q - sqrt(q) / 2 - sqrt(q) - 1 = q - 3 / 2 sqrt(q) - 1. $
      Since $sqrt(q) >= 6$, we have $(3\/2) sqrt(q) + 1 <= (5\/3) sqrt(q) <= (5\/18) q < q \/ 2$, and therefore
      $ 2 I - m > q / 2 > 0. $
    - Set
      $ J = floor( (m (I - 1) + (d - 1) m (m - 1) \/ 2) / (2 I - m) ) + 1. $
    By construction, $J >= 1$ is an integer satisfying
    $ (2 I - m) J > m (I - 1) + (d - 1) (m (m - 1)) / 2, $
    which rearranges directly to
    $ 2 I J > m (I + J - 1) + (d - 1) (m (m - 1)) / 2 >= E. $

    Since the number of unknowns $2 I J$ strictly exceeds the number of homogeneous linear equations $E$, linear algebra guarantees a nontrivial solution $(a_(i, j), b_(i, j)) in bb(F)_q^(2 I J) without \{ 0 \}$. By Step 1, the resulting polynomial $Phi(x)$ is *not* identically zero. By Step 2 and Theorem 4.7, $Phi(x)$ vanishes to order at least $m$ at every point $a in S_+$.

    Therefore, Theorem 4.7 gives
    $ m dot.c |S_+| <= op("deg")(Phi). $
    Let us bound $op("deg")(Phi)$. Using $I - 1 = (q - d - 2) \/ 2$ and $s = (q - 1) \/ 2$, we have
    $ op("deg")(Phi) &<= (J - 1) q + (I - 1) + d (q - 1) / 2 \ &= (J - 1 + (d + 1) / 2) q - d - 1 < (J - 1 + (d + 1) / 2) q. $
    On the other hand, from the definition of $J$ we obtain
    $ J - 1 &<= (m (I - 1) + (d - 1) m (m - 1) \/ 2) / (2 I - m) \ &= m / 2 + ( (d \/ 2) m^2 - ((d + 1) \/ 2) m ) / (2 I - m) < m / 2 + (d \/ 2) m^2 / (2 I - m). $
    Since $2 I - m > q \/ 2$, this simplifies to
    $ J - 1 < m / 2 + (d m^2) / q. $
    Substituting this into $m dot.c |S_+| < (J - 1 + (d + 1) \/ 2) q$ and dividing by $m$ gives
    $ |S_+| < q / 2 + d m + (d + 1) / 2 dot.c q / m. $
    Because $m = ceil(sqrt(q))$, we have $m < sqrt(q) + 1$ and $q \/ m <= sqrt(q)$, so
    $ |S_+| < q / 2 + d (sqrt(q) + 1) + (d + 1) / 2 sqrt(q) = q / 2 + (3 d + 1) / 2 sqrt(q) + d. $
    Finally, using $|S_0| <= d$ and $N_q (C) = 1 + 2 |S_+| + |S_0|$, we arrive at
    $ N_q (C) < q + 1 + (3 d + 1) sqrt(q) + 3 d. $
    Since $sqrt(q) >= 6$ and $d >= 3$, we have $3 d <= (d \/ 2) sqrt(q)$ and $(3 d + 1) + d \/ 2 = (7 d \/ 2) + 1 <= 4 d$. Hence
    $ N_q (C) <= q + 1 + 4 d sqrt(q), $
    completing the proof.
  ]

  Combining Theorem 4.10 with Lemma 4.3 immediately completes the elementary proof of Theorem 4.1—the full Hasse–Weil bound $|N_q (C) - (q + 1)| <= 2 g sqrt(q)$—and hence the Riemann Hypothesis for every hyperelliptic curve $y^2 = f(x)$ over every odd finite field!

  #remark(title: "Why " + $m approx sqrt(q)$ + " Is Forced")[
    Look closely at the penultimate inequality in the proof of Theorem 4.10:
    $ |S_+| < q / 2 + d m + (d + 1) / 2 dot.c q / m. $
    Here the two error terms represent a fundamental tension:
    - The term $((d + 1)\/2) (q \/ m)$ is the *base degree cost* divided by the multiplicity $m$: taking $m$ larger amortizes the initial degree $approx (d\/2) q$ of $f(x)^((q-1)/2)$ across $m$ derivatives.
    - The term $d m$ is the *multiplicity overhead*: each additional derivative $D^((k))$ adds $d - 1$ to the degree of $Psi_k$, creating $approx (d \/ 2) m^2$ extra linear equations, which forces $J$ to grow by $approx d m^2 \/ q$, adding $d m$ to $|S_+|$.

    By the AM–GM inequality, the sum $d m + ((d + 1)\/2)(q \/ m)$ is minimized precisely at $m approx sqrt(q)$, where both terms balance at $O(d sqrt(q))$. If $m = 1$ (no multiplicity), the first error term is $O(d q)$—completely useless! If $m$ grows too fast (say $m approx q^(2/3)$), the second error term blows up to $O(d q^(2/3))$. *Square-root cancellation requires square-root multiplicity.*
  ]

  #remark(title: "Bombieri's Geometric Reformulation and the Base-Change Tower")[
    In 1973, Enrico Bombieri recast Stepanov's proof in the intrinsic language of divisors and Riemann–Roch on an arbitrary smooth projective curve $C \/ bb(F)_q$ of genus $g$. Instead of explicit polynomials $R_1 (x) + R_2 (x) f(x)^((q-1)/2)$, Bombieri considers the Frobenius pullback $F^* : bb(F)_q (C) -> bb(F)_q (C)$ ($h |-> h^q$) and constructs a nonzero rational function $Phi in L(D)$ in a linear system of the form
    $ sum_(j) g_j (h_j)^q, $
    with poles controlled by a divisor $D$ of degree $approx (m \/ 2 + O(g)) q$, vanishing to order at least $m$ at every $bb(F)_q$-rational point—that is, lying in $L(D - m sum_(P in C(bb(F)_q)) P)$. The Hasse–Schmidt hyperderivatives are replaced by local power-series expansions at $P$, linear independence follows from the $bb(F)_q (C)^q$-linear independence of a small basis of $L(D_0)$, and $m dot.c N_q (C) <= op("deg")(D)$ yields $N_q (C) <= q + O_g (sqrt(q))$.

    Equally important for our story is the second half of the argument: passing from the sloppy bound $4 d sqrt(q)$ to the exact Riemann Hypothesis via the tower of finite extensions $bb(F)_(q^n) \/ bb(F)_q$ (Proposition 4.2). In `remark.pdf` (timeline item 11), Alpöge explicitly identifies the *cyclotomic Iwasawa tower* in his proof over $bb(Q)$ as the arithmetic analogue of this pigeonhole/base-change passage over $bb(F)_(q^n) \/ bb(F)_q$: just as a suboptimal constant $4 d$ over $bb(F)_q$ is killed by ascending the Frobenius tower $bb(F)_(q^n)$, auxiliary analytic losses over $bb(Q)$ are amplified away by ascending an Iwasawa tower!
  ]

  == The Multiplicity Obstruction over $bb(Z)$

  Every number theorist who learns Stepanov's proof experiences the same electric jolt of ambition: *the proof uses no étale cohomology, no intersection theory on $C times C$, no Weil conjectures for surfaces—only linear algebra, a degree bound, and multiplicity $m approx sqrt(q)$. Why can't we run Stepanov's method on $op("Spec")(bb(Z))$ to prove the classical Riemann Hypothesis?*

  Understanding precisely *where* the naive analogy breaks down is the key to understanding the entire Alpöge–Claude architecture. Let us place the function field $bb(F)_q [x]$ side by side with the ring of integers $bb(Z)$ and inspect each of the three pillars of Stepanov's proof.

  === Pillar 1: Degree versus Arakelov Height

  In $bb(F)_q [x]$, the fundamental inequality linking zeros to size is
  $ sum_(a in S) op("ord")_a (Phi) <= op("deg")(Phi) quad (Phi in bb(F)_q [x] without \{ 0 \}). $
  Over $bb(Z)$, this pillar actually *does* have a completely faithful analogue! If $alpha in bb(Z) without \{ 0 \}$ is a nonzero integer divisible by $p^(m_p)$ for primes $p in S$, then the product formula on $bb(Q)$ (or simply the fact that a divisor of a nonzero integer has smaller absolute value) gives
  $ sum_(p in S) m_p log p <= log |alpha|_oo. $
  More generally, in *Arakelov geometry* (which we will develop systematically in Chapter 9), the curve $C \/ bb(F)_q$ corresponds to the arithmetic curve $overline(op("Spec")(bb(Z))) = op("Spec")(bb(Z)) union \{ oo \}$. A vector bundle $cal(E)$ on $C$ corresponds to a *Hermitian lattice* $overline(E) = (E, || dot.c ||_oo)$ over $bb(Z)$, the polynomial degree $op("deg")(Phi)$ corresponds to the *Arakelov degree* $hat(op("deg"))(overline(L))$ (equivalently, the logarithmic height $log ||s||_oo$ of an integral section), and the vanishing inequality $m dot.c |S| <= op("deg")(Phi)$ is replaced by the *Bost slope inequality* (developed in Chapter 9 and used at the heart of the proof in Chapter 12). So Pillar 1 survives the passage from $bb(F)_q [x]$ to $bb(Z)$!

  === Pillar 2: The Absence of Derivations on $bb(Z)$

  The catastrophe strikes at Pillar 2: *how do we force an integer (or an arithmetic section) to vanish to high multiplicity $m$ at every prime $p <= X$ without blowing up its archimedean size?*

  In $bb(F)_q [x]$, vanishing to order $m$ at $a$ is encoded by the $m$ *linear* equations $(D^((k)) Phi)(a) = 0$ ($0 <= k < m$). The operators $D^((k))$ enjoy three miraculous properties simultaneously:
  1. *Linearity:* $D^((k)) (Phi_1 + Phi_2) = D^((k)) Phi_1 + D^((k)) Phi_2$, so vanishing conditions form a system of linear equations solvable by pigeonhole (dimension counting).
  2. *Uniformity across all points:* the *same* operator $D^((k))$ detects vanishing order at every point $a in bb(F)_q$ simultaneously.
  3. *Degree control:* $op("deg")(D^((k)) Phi) <= op("deg")(Phi) - k$—differentiating *reduces* size rather than inflating it.

  Now look at $bb(Z)$. Any derivation $D : bb(Z) -> bb(Z)$ satisfying the Leibniz rule $D(a b) = a D(b) + b D(a)$ must satisfy $D(1) = D(1 dot.c 1) = 2 D(1)$, hence $D(1) = 0$, and by additivity
  $ D(n) = n D(1) = 0 quad "for all" n in bb(Z). $
  There are *no* nontrivial derivations of the ring of integers: $op("Der")(bb(Z), bb(Z)) = 0$.

  Over the past half-century, mathematicians have proposed several profound attempts to manufacture a substitute for "differentiating integers." It is illuminating to see why each naive substitute hits a wall when plugged into Stepanov's machine:

  - *Buium's $p$-derivations:* For a fixed prime $p$, Alexandru Buium (1995) defined the *Fermat quotient operator*
    $ delta_p (n) = (n - n^p) / p in bb(Z) quad (n in bb(Z)). $
    It satisfies a twisted Leibniz rule $delta_p (a b) = a^p delta_p (b) + b^p delta_p (a) + p delta_p (a) delta_p (b)$ and does indeed detect $p$-adic multiplicity: $p^m divides n$ if and only if $n equiv delta_p (n) equiv dots.c equiv delta_p^(m-1) (n) equiv 0$ (mod $p$) (Exercise 4.7). However, $delta_p$ fails all three Stepanov requirements at once: it is *nonlinear* in $a + b$ (mixing in carries via $(a^p + b^p - (a + b)^p) \/ p$), it is *specific to a single prime $p$* rather than uniform across all primes, and its archimedean height explodes *exponentially*: $|delta_p (n)| approx |n|^p \/ p$, so $m$-fold iteration inflates the height to $|n|^(p^m)$—completely destroying the height comparison!

  - *$bb(F)_1$-geometry and $Lambda$-rings:* As James Borger observed (2009), equipping a ring with commuting Frobenius lifts $psi_p$ for all primes $p$ simultaneously is equivalent to giving it a *$Lambda$-ring structure*, which provides a candidate model for geometry "over the field with one element $bb(F)_1$." In footnote 5 of `remark.pdf`, Alpöge remarks on this exact direction, noting how formidable it would be to fight for an $bb(F)_1$-based Stepanov proof à la Borger. The core difficulty is that $bb(Z)$ carries an archimedean place $oo$ that does not commute with the finite-prime Frobenius lifts, and translating linear vanishing conditions across all primes simultaneously into an Arakelov height bound remains out of reach in pure $bb(F)_1$-geometry.

  - *Geometric derivations on auxiliary varieties (transcendence and CM curves):* Where *do* genuine linear derivations exist in arithmetic geometry? On *algebraic varieties of positive dimension* defined over $bb(Z)$ or $cal(O)_K$—for instance, the invariant derivation $D$ on an elliptic curve $E$! In transcendence theory (Siegel, Baker, Philippon, Bost), one constructs an auxiliary polynomial on a group variety $G$ and differentiates along the invariant vector fields of $G$. Here the derivation $D$ is genuinely linear and controls heights via Bost's slope inequality, *and* at primes $p$ inert in a CM field $K$, the invariant derivation $D$ on a CM elliptic curve satisfies $D^p equiv 0$ (mod $p$), producing deep $p$-adic divisibility of normalized theta derivatives $D^a theta(0) \/ Omega^a$ by $p^(a \/ p + a \/ p^3 + dots.c - O(log a))$ (timeline item 2 of `remark.pdf`, which we will study in Chapter 8!). Yet a geometric derivation differentiates along the *vertical* fiber of $E -> op("Spec")(cal(O)_K)$, not along the *horizontal* base $op("Spec")(bb(Z))$ itself!

  === Stepanov Without Multiplicity

  What happens if one tries to run a Stepanov-type positivity argument over $bb(Z)$ with multiplicity $m = 1$? In `remark.pdf` (page 2 and timeline item 4), Alpöge draws an explicit connection between classical positivity bounds on the Guinand–Weil explicit formula (such as $W(1_S) >= 0$ arising from a single positive semidefinite determinant, or Siegel's argument) and *Stepanov's method with multiplicity $m = 1$*.

  Just as setting $m = 1$ in Stepanov's inequality $|S_+| < q \/ 2 + d m + ((d + 1)\/2)(q \/ m)$ fails to cross the square-root barrier, a single determinant of periods over $bb(Z)$ gives positivity ($W(phi) >= 0$) but cannot force all zeros onto $op("Re")(s) = 1\/2$: as noted in timeline item 6 of `remark.pdf`, a test function of the shape $1_((0, 1]) + (tilde.op X^eta) dot.c 1_((0, 1\/X])$ only yields a zero-free region of width $1 - eta$ unless one can inject *high multiplicity* $m -> oo$ (specifically $m approx sqrt(X)$) into the positivity machine.

  The central mystery, then, was not how to mimic $op("deg")(Phi)$ over $bb(Z)$—Arakelov geometry already gives us $hat(op("deg"))$. The central mystery was: *what is the natively arithmetic, natively automorphic substitute for multiplicity $m approx sqrt(X)$?*

  == From $q N = M^k + R$ to Chained Theta Lifts: The Conceptual Bridge

  The breakthrough that unlocked the Alpöge–Claude proof came from an astonishingly simple *new* proof of the Weil and Deligne bounds over finite fields—one that uses neither intersection theory nor Hasse–Schmidt derivatives, but instead combines a *quadric exponential sum* with *iterated Parseval* and a *sign-only* comparison. Because this toy argument is both completely elementary and the direct inspiration for chaining theta lifts over $bb(Z)$, we present it in full detail.

  === The Toy Identity $q N = M^k + R$ on the Path Quadric

  Let $bb(F)_q$ be a finite field of characteristic $p$, and let
  $ e_q (u) = exp( (2 pi i) / p op("Tr")_(bb(F)_q \/ bb(F)_p) (u) ) quad (u in bb(F)_q) $
  be the standard nontrivial additive character of $bb(F)_q$. Let $t : bb(F)_q -> bb(C)$ be any function (in our hyperelliptic setting, $t(x) = chi_q (f(x))$; more generally, the Frobenius trace function of a lisse sheaf on $bb(A)^1_(bb(F)_q)$), and denote its sum by
  $ M = sum_(x in bb(F)_q) t(x). $
  Our goal is to prove square-root cancellation $|M| = O(sqrt(q))$.

  Fix an integer $k >= 2$, and consider the *path quadric* in $k$ variables:
  $ Q(x_1, dots.c, x_k) = x_1 x_2 + x_2 x_3 + dots.c + x_(k-1) x_k. $
  (The name "path quadric" reflects the fact that the monomials $x_j x_(j+1)$ correspond to the edges of the path graph $P_k$ on vertices $\{ 1, 2, dots.c, k \}$.) Form the $(k + 1)$-variable exponential sum
  $ S_k = sum_(h in bb(F)_q) sum_(x_1, dots.c, x_k in bb(F)_q) t(x_1) dots.c t(x_k) dot.c e_q (h (x_1 x_2 + x_2 x_3 + dots.c + x_(k-1) x_k)). $

  We evaluate $S_k$ in two ways—a miniature, finite-field relative trace formula!

  *First evaluation (sum over $h$ first):* By orthogonality of additive characters,
  $ sum_(h in bb(F)_q) e_q (h u) = cases( q & "if" u = 0, 0 & "if" u != 0. ) $
  Summing over $h in bb(F)_q$ first therefore localizes $(x_1, dots.c, x_k)$ to the quadric hypersurface $Q(x_1, dots.c, x_k) = 0$:
  $ S_k = q N, quad "where" quad N = sum_(vec(delim: #none, x_1, dots.c, x_k in bb(F)_q, x_1 x_2 + dots.c + x_(k-1) x_k = 0)) t(x_1) dots.c t(x_k). $

  *Second evaluation (separate the zero mode $h = 0$ from $h != 0$):* The term $h = 0$ has $e_q (0) = 1$, so the sum factors completely into $k$ identical copies of $M$:
  $ sum_(x_1, dots.c, x_k in bb(F)_q) t(x_1) dots.c t(x_k) = (sum_(x in bb(F)_q) t(x))^k = M^k. $
  Let $R$ denote the remaining contribution from $h in bb(F)_q^*$:
  $ R = sum_(h in bb(F)_q^*) sum_(x_1, dots.c, x_k in bb(F)_q) t(x_1) dots.c t(x_k) dot.c e_q (h (x_1 x_2 + x_2 x_3 + dots.c + x_(k-1) x_k)). $
  Equating the two evaluations gives the fundamental identity
  $ q N = M^k + R. $

  Now comes the miracle: the remainder $R$ has *square-root quality for every $k$*, proved in five lines by *iterated Parseval*!

  #proposition(title: "Iterated Parseval Bound on the Path Quadric")[
    Let $t : bb(F)_q -> bb(C)$ satisfy $|t(x)| <= B$ for all $x in bb(F)_q$, and let $k >= 2$. Then the non-zero-mode remainder $R$ in the identity $q N = M^k + R$ satisfies
    $ |R| <= (q - 1) B^k q^((k + 1) / 2) < B^k q^((k + 3) / 2). $
  ]

  #proof[
    Fix $h in bb(F)_q^*$, and define the unnormalized Fourier transform operator $cal(F)_h$ on functions $phi : bb(F)_q -> bb(C)$ by
    $ (cal(F)_h phi)(y) = sum_(x in bb(F)_q) phi(x) e_q (h x y). $
    Because $h != 0$, the additive character $x |-> e_q (h x y)$ runs through all characters of $bb(F)_q$ as $y$ varies, so the Plancherel–Parseval identity gives
    $ ||cal(F)_h phi||_2^2 = sum_(y in bb(F)_q) |(cal(F)_h phi)(y)|^2 = q sum_(x in bb(F)_q) |phi(x)|^2 = q ||phi||_2^2. $

    Now define a sequence of functions $phi_1, phi_2, dots.c, phi_k : bb(F)_q -> bb(C)$ recursively along the path graph by
    $ phi_1 (x) = t(x), quad phi_(j+1) (x) = t(x) dot.c (cal(F)_h phi_j)(x) quad (1 <= j <= k - 1). $
    Unwinding the recursion, the inner sum of $R$ at fixed $h != 0$ is literally
    $ R_h &:= sum_(x_1, dots.c, x_k in bb(F)_q) t(x_1) dots.c t(x_k) e_q (h (x_1 x_2 + dots.c + x_(k-1) x_k)) \ &= sum_(x_k in bb(F)_q) t(x_k) (cal(F)_h phi_(k-1))(x_k). $

    We bound the $L^2$-norms inductively. First, $||phi_1||_2^2 = sum_x |t(x)|^2 <= B^2 q$. For each $1 <= j <= k - 2$, using $|t(x)| <= B$ pointwise and Parseval,
    $ ||phi_(j+1)||_2^2 = sum_(x in bb(F)_q) |t(x)|^2 |(cal(F)_h phi_j)(x)|^2 <= B^2 ||cal(F)_h phi_j||_2^2 = B^2 q ||phi_j||_2^2. $
    By induction, $||phi_(k-1)||_2^2 <= B^(2 k - 2) q^(k - 1)$, and one final application of Parseval gives
    $ ||cal(F)_h phi_(k-1)||_2^2 = q ||phi_(k-1)||_2^2 <= B^(2 k - 2) q^k. $
    Applying Cauchy–Schwarz to $R_h = sum_(x_k) t(x_k) (cal(F)_h phi_(k-1))(x_k)$ yields
    $ |R_h| <= ||t||_2 dot.c ||cal(F)_h phi_(k-1)||_2 <= (B q^(1/2)) (B^(k-1) q^(k/2)) = B^k q^((k + 1) / 2). $
    Summing over all $q - 1$ values of $h in bb(F)_q^*$ gives $|R| <= (q - 1) B^k q^((k + 1) / 2) < B^k q^((k + 3) / 2)$.
  ]

  Pause to appreciate the power of Proposition 4.13. Rewrite the bound on $R$ as
  $ |R|^(1 / k) < B dot.c q^(1 / 2 + 3 / (2 k)). $
  As $k -> oo$, the extra factor $q^(3 \/ (2 k))$ shrinks to $1$—in Nicholas Katz's memorable phrase (quoted in footnote 3 of `remark.pdf`), $R$ has *"square-root quality up to an inch or so"*!

  Now look at how the *sign* of $q N$ finishes the proof of the Weil bound:
  $ q N = M^k + R. $
  As Alpöge explains in footnote 3 of `remark.pdf`, when $t$ is a trace function of a pure sheaf (such as $chi_q (f(x))$ for a hyperelliptic curve, or more generally with generic quadric coefficients via Bertini's theorem), the middle cohomology of the quadric hypersurface $Q(x_1, dots.c, x_k) = 0$ has dimension one off from $bb(A)^k$, giving the cohomological leading term of $q N$ the *opposite sign* from the leading term of $M^k$! Because $q N$ and $M^k$ carry opposite signs, no cancellation can occur between the inverse roots on the two sides: if $M^k$ and $- q N$ are both positive (or have matching signs in the Frobenius power-sum expansion over $bb(F)_(q^n)$), then $q N = M^k + R$ forces
  $ |M|^k <= |M^k - q N| = |R| < B^k q^((k + 3) / 2). $
  Taking $k$-th roots and letting $k -> oo$ (or passing to $bb(F)_(q^n)$) immediately yields the square-root bound $|M| <= B sqrt(q)$—a *sign-only proof of Weil and Deligne*!

  === Translating the Toy Picture into Automorphic Forms over $bb(Z)$

  How does the innocent-looking finite-field identity $q N = M^k + R$ lead all the way to chained theta lifts on unitary groups over $bb(Z)$? Tracing the progression in `remark.pdf` (page 3 and timeline items 3–8) reveals a breathtaking chain of analogies:

  1. *From Gauss sums and the path quadric to theta functions (timeline item 3):*
     Where did the path quadric $x_1 x_2 + dots.c + x_(k-1) x_k$ come from in the first place? Alpöge arrived at it while simplifying an average over multiplicative characters $chi |-> chi(op("disc"))$, which via normalized Gauss sums $y(dot.c)$ living on a metaplectic cover of $op("GL")_2$ (as a theta function!) produces a reciprocity kernel $y(c dot.c c') \/ (y(c) y(c'))$ on the complete graph; simplifying the complete graph to a *path* graph yields $e_q (h (x_1 x_2 + dots.c + x_(k-1) x_k))$, where Gauss-sum cancellation is replaced by iterated Parseval.

     On the arithmetic side over $bb(Z)$, the additive character $e_q (h Q(x))$ of a quadratic form $Q$ is the exact finite-field shadow of the *Weil representation* and its *theta kernel* $theta_phi (g, h)$! On a CM elliptic curve $E = bb(C) \/ bb(Z)[omega]$, placing the Poincaré line bundle on the edges of the path graph literally produces a product of theta functions. Moreover, the Möbius function $mu$ (and by extension the von Mangoldt function $Lambda$) admits an automorphic realization via theta functions on a metaplectic cover—prompting the question: *what is the automorphic incarnation of $q N = M^k + R$?*

  2. *From the definite sign of $q N$ to automorphic determinants of periods (timeline items 4–7):*
     Over a function field, the definite sign of $q N$ came from middle cohomology / holomorphy. Over $bb(Z)$, the definite sign comes from the *Guinand–Weil explicit formula* $W(phi) >= 0$ applied to the smoothed von Mangoldt sum
     $ sum_(n <= X) Lambda(n) (X / n - 1)_+ - X log X + (1 + gamma) X $
     (timeline item 5), expressed via *determinants of automorphic periods*—specifically Gan–Gross–Prasad (GGP) periods on unitary groups (timeline item 7). A single such determinant produces $W(dot.c) >= 0$, which is the automorphic avatar of *Stepanov with multiplicity $m = 1$*.

  3. *From iterated Parseval along a path of length $k$ to a chain of $m$ theta lifts (timeline item 8):*
     Look back at the recursion in Proposition 4.13:
     $ phi_1 = t, quad phi_2 = t dot.c cal(F)_h (phi_1), quad dots.c, quad phi_k = t dot.c cal(F)_h (phi_(k-1)). $
     Each step along the path applies a Fourier/Weil integral operator $cal(F)_h$ and multiplies by a fresh copy of $t$. What is the natively automorphic analogue of applying the Weil representation $m$ times in succession? *Chaining $m$ theta lifts!*

     First, Alpöge and Claude discovered that a single theta lift to $O(2, n)$ gave a natively automorphic determinant achieving *multiplicity $2$* (`remark.pdf`, page 3). Immediately the entire architecture snapped into focus: if one theta lift wins one additional degree of multiplicity, then an *iterated chain of $m$ theta lifts* between totally definite unitary groups,
     $ U(X_0) -> U(X_1) -> U(X_2) -> dots.c -> U(X_m), $
     acting on automorphic representations by the isobaric transfer
     $ pi |-> pi plus.square mu_j [t] quad (j = 1, dots.c, m), $
     synthesizes *automorphic multiplicity $m$*!

     At each step $j = 1, dots.c, m$, the theta lift injects a new Hecke character block $mu_j$, and *seesaw duality* (the Rallis inner product formula, timeline item 12) ensures that the period of the $m$-fold iterated lift remains a Bessel period independent of the Hecke characters—the exact automorphic counterpart of Step 1 (non-vanishing) in Stepanov's proof! Meanwhile, local divisibility of CM theta derivatives $D^a theta(0) \/ Omega^a$ at inert primes, combined with Chowla–Selberg, Weyl's law, and the Siegel mass formula (timeline items 9–10), supplies the order-$m$ arithmetic divisibility that plays the role of $m dot.c |S_+|$.

  4. *Why $m approx sqrt(X)$?*
     Just as in Stepanov's inequality $|S_+| < q \/ 2 + d m + ((d + 1)\/2)(q \/ m)$, where balancing the multiplicity gain against the degree overhead uniquely forces $m approx sqrt(q)$, balancing the order-$m$ divisibility gain of the $m$-fold iterated theta lift against the Arakelov/Bost height cost of the chain for the von Mangoldt sum of length $X$ uniquely forces a chain of length
     $ m approx sqrt(X). $
     As Alpöge wrote in `remark.pdf`: *"The line: for the von Mangoldt sum of length $X$, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was $sqrt(X)$. (And yet, what else could it be?)"*

  #insight-box(title: "The Stepanov–Alpöge–Claude Dictionary")[
    The table below summarizes the structural correspondence between Stepanov's elementary proof of the Riemann Hypothesis over $bb(F)_q$ (this chapter) and the Alpöge–Claude proof of the classical Riemann Hypothesis over $bb(Z)$ (Parts II–III).

    #v(0.3em)
    #table(
      columns: (24%, 36%, 40%),
      stroke: (x: none, y: 0.35pt + luma(200)),
      inset: (x: 4pt, y: 5pt),
      align: (left, left, left),
      [*Component*], [*Stepanov over $bb(F)_q$*], [*Alpöge–Claude over $bb(Z)$*],
      [Target sum], [$sum_(x in bb(F)_q) chi_q (f(x))$], [$sum_(n <= X) Lambda(n) (X \/ n - 1)_+$],
      [Primary scale], [Field cardinality $q$], [Truncation scale $X$ (and $a, b, L$)],
      [Auxiliary object], [Polynomial $Phi(x) = R_1 (x) + R_2 (x) f^((q-1)/2)$], [Automorphic form / GGP period determinant on $U(X_m)$],
      [Source of multiplicity $m$], [Hasse–Schmidt hyperderivatives $D^((k))$ ($0 <= k < m$)], [Chain of $m$ iterated theta lifts $U(X_0) -> dots.c -> U(X_m)$ + CM divisibility],
      [Optimal multiplicity], [$m = ceil(sqrt(q)) approx sqrt(q)$], [Chain length $m approx sqrt(X)$],
      [Non-vanishing mechanism], [Parity of $floor(op("deg") \/ q)$ (Frobenius independence)], [Seesaw duality (Rallis) + Bessel period + relative trace formula],
      [Degree / height bound], [$m dot.c |S_+| <= op("deg")(Phi)$], [Bost's slope inequality / Arakelov height bound $hat(op("deg"))$ (`DivIneqObjU`, `HeightS`)],
      [Amplification tower], [Base change to $bb(F)_(q^n) \/ bb(F)_q$], [Cyclotomic Iwasawa tower via Behrend's theorem + weakened Vandiver (`VWin`)],
    )
  ]

  With this dictionary in hand, Part I is complete. We have seen how Riemann's 1859 memoir framed the prime-counting problem in terms of zeros of $zeta(s)$, how 167 years of analytic and geometric attacks mapped out the terrain, and how Stepanov's multiplicity paradigm reduces the Riemann Hypothesis over finite fields to a balance between multiplicity $m approx sqrt(q)$ and polynomial degree. In Part II, we systematically build the six modern mathematical pillars—Mellin transforms, automorphic representations on unitary groups, the Weil representation and theta lifts, complex multiplication and formal groups, Arakelov geometry and Bost's slope inequality, and Galois cohomology with Iwasawa towers—that realize every single entry of the right-hand column of our dictionary over $bb(Z)$.

  #exercises((
    [
      *Elliptic curves and Frobenius eigenvalues.* Let $p$ be an odd prime and let $E \/ bb(F)_p$ be the elliptic curve $y^2 = x^3 - x$.
      (a) Show that if $p equiv 3$ (mod $4$), then $chi_p (-1) = -1$ and hence $sum_(x in bb(F)_p) chi_p (x^3 - x) = 0$. Deduce that $N_p (E) = p + 1$, $P(T) = 1 + p T^2$, and the Frobenius eigenvalues are $alpha_1 = i sqrt(p)$, $alpha_2 = - i sqrt(p)$.
      (b) Compute $N_(p^n) (E)$ for all $n >= 1$ when $p equiv 3$ (mod $4$), and verify that $|N_(p^n) (E) - (p^n + 1)| = 2 p^(n/2)$ for every even $n$ (showing that the constant $2 g = 2$ in the Hasse–Weil bound is sharp).
      (c) For $p = 5$ and $p = 13$, compute $N_p (E)$ directly, find $P(T) = 1 - a_p T + p T^2$, and verify $|alpha_1| = |alpha_2| = sqrt(p)$.
    ],
    [
      *Why one-sided upper bounds alone do not imply RH.* Consider a formal sequence of integers $N_n = q^n + 1 - sum_(i=1)^(2g) alpha_i^n$ where $\{ alpha_1, dots.c, alpha_(2g) \}$ is invariant under $alpha |-> q \/ alpha$.
      (a) Give an explicit example (for $g = 1$) of a pair $\{ alpha_1, alpha_2 \}$ with $alpha_1 alpha_2 = q$ and $|alpha_1| > sqrt(q)$ such that $N_n <= q^n + 1$ for *every* $n >= 1$. Explain why this shows that a one-sided upper bound $N_(q^n) (C) <= q^n + 1 + c_0 q^(n/2)$ on a *single* curve $C$ does not by itself imply $|alpha_i| = sqrt(q)$, and why Lemma 4.3 needed quadratic twists.
      (b) Conversely, suppose $N_n >= q^n + 1 - c_0 q^(n/2)$ for all $n >= 1$ (a one-sided *lower* bound) *and* $alpha_1 > sqrt(q)$ is positive real. Show that this *does* lead to a contradiction. What if $alpha_1 = R e^(2 pi i theta)$ is non-real with $R > sqrt(q)$? Use Dirichlet's simultaneous approximation theorem to prove that a one-sided *lower* bound $N_n >= q^n + 1 - c_0 q^(n/2)$ for all $n >= 1$ *does* imply $|alpha_i| = sqrt(q)$ for all $i$!
    ],
    [
      *Lucas's theorem and Hasse–Schmidt hyperderivatives.* Let $p$ be a prime and work in $bb(F)_p [x]$.
      (a) Using $D^((k)) (x^n) = binom(n, k) x^(n - k)$ and expanding $(x + t)^n$ via the base-$p$ digits $n = sum_(i >= 0) n_i p^i$ ($0 <= n_i < p$), prove *Lucas's theorem*:
      $ binom(n, k) equiv product_(i >= 0) binom(n_i, k_i) quad ("mod" p), $
      where $k = sum_(i >= 0) k_i p^i$.
      (b) Deduce that $D^((k)) (x^n) = 0$ in $bb(F)_p [x]$ if and only if $k_i > n_i$ for at least one index $i$.
      (c) Show that for every $a >= 0$, the operator $D^((p^a))$ vanishes on $bb(F)_p [x^(p^(a+1))]$ and acts as a derivation on $bb(F)_p [x^(p^a)]$.
    ],
    [
      *Explicit computation of $Q_k (x)$ in Lemma 4.8.* Let $f(x) = x^3 + A x + B in bb(F)_q [x]$ ($q$ odd) and $s = (q - 1) \/ 2$.
      (a) Compute $Q_0 (x)$, $Q_1 (x)$, and $Q_2 (x)$ explicitly in terms of $f(x)$, $f'(x)$, and $D^((2)) f(x)$, and verify that $op("deg")(Q_k) <= 2 k$ for $k = 0, 1, 2$.
      (b) Prove the *Faà di Bruno formula* for Hasse–Schmidt hyperderivatives: if $h(x), g(x) in R[x]$, express $D^((k)) (h(g(x)))$ as a polynomial in $(D^((r)) h)(g(x))$ and $(D^((j)) g)(x)$ with integer coefficients, and show that Lemma 4.8 is a special case with $h(u) = u^s$.
    ],
    [
      *Even-degree hyperelliptic curves.* Suppose $f(x) in bb(F)_q [x]$ ($q$ odd) is squarefree of *even* degree $d = 2 g + 2 >= 4$.
      (a) Explain why the smooth projective completion $C$ of $y^2 = f(x)$ has *two* points at infinity over $overline(bb(F))_q$, which are both $bb(F)_q$-rational if the leading coefficient of $f$ is a square in $bb(F)_q^*$, and form a conjugate pair over $bb(F)_(q^2)$ otherwise.
      (b) Show that after replacing $bb(F)_q$ by a finite extension $bb(F)_(q^r)$ containing a root $alpha$ of $f(x)$, the birational transformation $x' = 1 \/ (x - alpha)$, $y' = y \/ (x - alpha)^(g + 1)$ transforms $y^2 = f(x)$ into an *odd-degree* hyperelliptic equation $(y')^2 = tilde(f)(x')$ of degree $2 g + 1$.
      (c) Deduce the Hasse–Weil bound $|N_q (C) - (q + 1)| <= 2 g sqrt(q)$ for even-degree hyperelliptic curves from Theorem 4.1 and Proposition 4.2.
    ],
    [
      *Stepanov's method for Artin–Schreier curves and exponential sums.* Let $q = p^r$ be a prime power and let $f(x) in bb(F)_q [x]$ be a polynomial of degree $d >= 2$ with $p divides.not d$. Consider the Artin–Schreier curve $C : y^p - y = f(x)$ over $bb(F)_q$.
      (a) Show that $x in bb(F)_q$ lifts to $p$ points $(x, y) in C(bb(F)_q)$ if $op("Tr")_(bb(F)_q \/ bb(F)_p)(f(x)) = 0$, and $0$ points otherwise.
      (b) Using the trace polynomial $T(u) = u + u^p + u^(p^2) + dots.c + u^(q \/ p)$ in place of $f(x)^((q - 1) \/ 2)$, construct a Stepanov auxiliary polynomial
      $ Phi(x) = sum_(j=0)^(J-1) sum_(k=0)^(p-1) P_(j, k) (x) x^(j q) (T(f(x)))^k $
      to prove an upper bound $N_q (C) <= q + 1 + O_(p, d) (sqrt(q))$.
      (c) By twisting $y^p - y = f(x) + c$ for $c in bb(F)_q$ and passing to $bb(F)_(q^n)$, deduce Weil's bound for exponential sums:
      $ |sum_(x in bb(F)_q) e_q (f(x))| <= (d - 1) sqrt(q). $
    ],
    [
      *Buium's $p$-derivation and the height obstruction.* Fix a prime $p$ and define $delta_p (n) = (n - n^p) \/ p$ for $n in bb(Z)$.
      (a) Verify that $delta_p (n) in bb(Z)$ for all $n in bb(Z)$, and prove the sum and product rules:
      $ delta_p (a + b) = delta_p (a) + delta_p (b) - sum_(j=1)^(p-1) 1 / p binom(p, j) a^j b^(p - j), $
      $ delta_p (a b) = a^p delta_p (b) + b^p delta_p (a) + p delta_p (a) delta_p (b). $
      (b) Prove by induction on $m >= 1$ that $p^m divides n$ if and only if $n equiv delta_p (n) equiv dots.c equiv delta_p^(m - 1) (n) equiv 0$ (mod $p$).
      (c) Show that if $|n| >= 2$, then $log |delta_p^(m) (n)|$ grows doubly exponentially in $m$ (like $p^m log |n|$), and explain why this destroys any naive attempt to impose $m approx sqrt(X)$ vanishing conditions in $bb(Z)$ via $delta_p$.
    ],
    [
      *The path quadric identity $q N = M^k + R$ for $k = 2$ and $k = 3$.* Let $q$ be an odd prime power and let $t(x) = chi_q (x)$ be the quadratic character on $bb(F)_q$ (so $M = sum_x chi_q (x) = 0$).
      (a) For $k = 2$, the path quadric is $Q(x_1, x_2) = x_1 x_2$. Compute $N$ and $R$ explicitly, and verify that $q N = M^2 + R$ holds identically with $N = 0$ and $R = 0$.
      (b) Now take $t(x) = chi_q (x - 1)$ (still $M = 0$, but $t(0) = chi_q (-1) != 0$). Compute $N$ and $R$ for $k = 2$ directly, and check that $|R| <= (q - 1) q^(3/2)$ as guaranteed by Proposition 4.13.
      (c) For general $t : bb(F)_q -> bb(C)$ and $k = 2$, show that $R = sum_(h in bb(F)_q^*) sum_(x_1, x_2) t(x_1) t(x_2) e_q (h x_1 x_2)$ can be expressed in terms of the Fourier transform $hat(t)(y) = sum_x t(x) e_q (x y)$, and compare the exact value of $q N - M^2$ with the bound of Proposition 4.13.
    ],
    [
      *Abstract Stepanov optimization and the $2\/3$ barrier.* Suppose an arithmetic multiplicity machine of order $m >= 1$ at scale $X$ produces an inequality of the form
      $ m N <= (1 / 2 m + c_1 (m^(1 + alpha)) / X + c_2) X, $
      where $c_1, c_2 > 0$ are constants and $alpha > 0$ measures the growth exponent of the "cost" of each lift step.
      (a) Optimize over $m > 0$ to show that the resulting bound on $N$ is
      $ N <= 1 / 2 X + C X^(1 - 1 / (alpha + 1)) $
      for an explicit constant $C$ depending on $c_1, c_2, alpha$.
      (b) Verify that $alpha = 1$ (linear growth of per-step degree/height cost, as in Stepanov's method) yields the square-root bound $N <= X \/ 2 + O(X^(1/2))$ at $m approx sqrt(X)$, whereas $alpha = 2$ (quadratic per-step cost) stalls at $N <= X \/ 2 + O(X^(2/3))$ at $m approx X^(1/3)$!
      (c) Compare this calculation with timeline item 14 of `remark.pdf`, where Alpöge notes that a naive computation of the "cost" of each theta lift would stop at $2\/3$ a priori, necessitating the "division" mechanism developed in Part III.
    ],
  ))
]
