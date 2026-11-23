// ============================================================================
// Chapter 2: Dirichlet L-Functions and the Generalized Riemann Hypothesis
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch02() = [
  #chapter(
    "Dirichlet L-Functions and the Generalized Riemann Hypothesis",
    short-title: "Dirichlet L-Functions and GRH",
    epigraph: "The proof of this theorem rests upon the consideration of certain infinite series which are intimately connected with the theory of quadratic forms and with the division of the circle.",
    epigraph-source: "Peter Gustav Lejeune Dirichlet, 1837",
    overview: [
      In 1837, twenty-two years before Riemann's memoir on $zeta(s)$, Dirichlet introduced the $L$-series $L(s, chi)$ attached to periodic multiplicative characters modulo $N$ in order to prove that every reduced residue class $a (op("mod") N)$ contains infinitely many primes. Beyond their foundational role in multiplicative number theory, Dirichlet $L$-functions form the simplest infinite family of automorphic $L$-functions—the degree-$1$ prototypes over $bb(Q)$—and the Generalized Riemann Hypothesis (GRH) asserts that all of their nontrivial zeros lie on the critical line $op("Re")(s) = 1\/2$.

      This chapter develops the complete classical theory of Dirichlet $L$-functions in the precise form required by the Alpöge–Claude proof. We begin with Dirichlet characters, conductors, primitivity, and the finite Euler-factor decomposition of imprimitive $L$-functions (Section 2.1). We then establish the separability of Gauss sums, the modular transformation of twisted theta series, analytic continuation, and the functional equation for primitive characters (Section 2.2). Section 2.3 presents Dirichlet's theorem on primes in arithmetic progressions via the nonvanishing of $L(1, chi)$, together with the class number formula, classical zero-free regions, Siegel zeros, and the Deuring–Heilbronn phenomenon. In Section 2.4 we state GRH and give the complete reduction of both GRH and the classical Riemann Hypothesis to nonvanishing in the right half-plane $op("Re")(s) > 1\/2$, mirroring step-for-step the Lean 4 formalization in `HalfPlane.lean` and `ClaimStrip.lean`. Finally, Section 2.5 explains conceptually why the automorphic and Iwasawa-theoretic engine of Alpöge and Claude proves GRH for all Dirichlet characters simultaneously with RH.
    ],
    label-name: "ch:dirichlet-grh",
  )

  == Dirichlet Characters, Conductors, and Primitivity

  The Riemann zeta function encodes the distribution of all prime numbers simultaneously through its Euler product over every prime $p$. To isolate primes lying in a fixed arithmetic progression $p equiv a (op("mod") N)$ with $gcd(a, N) = 1$, one needs a Fourier-analytic device on the finite abelian group $(bb(Z) \/ N bb(Z))^times$ of reduced residue classes modulo $N$. That device is the group of Dirichlet characters.

  === Definitions and Orthogonality Relations

  Let $N >= 1$ be a positive integer, and let $G_N = (bb(Z) \/ N bb(Z))^times$ denote the multiplicative group of units modulo $N$, which has order $phi(N)$ (Euler's totient function).

  #definition(title: "Dirichlet Character")[
    A *Dirichlet character modulo $N$* is a function $chi : bb(Z) -> bb(C)$ obtained by extending a group homomorphism $tilde(chi) : (bb(Z) \/ N bb(Z))^times -> bb(C)^times$ to all integers via
    $ chi(n) = cases(tilde(chi)(n mod N) & "if" gcd(n, N) = 1, 0 & "if" gcd(n, N) > 1.) $
    Equivalently, $chi : bb(Z) -> bb(C)$ is a Dirichlet character modulo $N$ if and only if:
    1. $chi$ is periodic with period $N$: $chi(n + N) = chi(n)$ for all $n in bb(Z)$;
    2. $chi$ is completely multiplicative: $chi(m n) = chi(m) chi(n)$ for all $m, n in bb(Z)$;
    3. $chi(n) != 0$ if and only if $gcd(n, N) = 1$.
  ]

  Because $G_N$ is a finite group of order $phi(N)$, every value $chi(n)$ with $gcd(n, N) = 1$ satisfies $chi(n)^(phi(N)) = 1$, and hence $|chi(n)| = 1$ whenever $gcd(n, N) = 1$ and $chi(n) = 0$ otherwise. In particular, $|chi(n)| <= 1$ for all $n in bb(Z)$, and the complex conjugate $overline(chi)$ satisfies $overline(chi)(n) = chi(n)^(-1)$ whenever $gcd(n, N) = 1$. We write $chi^(-1) = overline(chi)$ for the inverse character in the dual group $hat(G)_N = op("Hom")(G_N, bb(C)^times)$.

  The identity element of $hat(G)_N$ is the *principal character* modulo $N$, denoted $chi_0$ (or $1_(op("mod") N)$):
  $ chi_0 (n) = cases(1 & "if" gcd(n, N) = 1, 0 & "if" gcd(n, N) > 1.) $
  When $N = 1$, the group $G_1$ is trivial and $chi_0 (n) = 1$ for all $n in bb(Z)$. A Dirichlet character $chi$ is called *real* (or *quadratic*, if non-principal) if $chi(n) in {-1, 0, 1}$ for all $n$, equivalently $chi^2 = chi_0$; otherwise it is *complex*. Since $(-1)^2 = 1$ in $G_N$, every character satisfies $chi(-1) in {1, -1}$. We say that $chi$ is *even* if $chi(-1) = 1$ and *odd* if $chi(-1) = -1$. It is convenient to encode the parity of $chi$ by the indicator
  $ a = a(chi) = (1 - chi(-1)) / 2 in {0, 1}, $
  so that $chi(-1) = (-1)^a$. Notice that for $N in {1, 2}$, we have $-1 equiv 1 (op("mod") N)$, so every character modulo $1$ or $2$ is necessarily even.

  By the structure theorem for finite abelian groups, the dual group $hat(G)_N$ is non-canonically isomorphic to $G_N$ and therefore has cardinality $|hat(G)_N| = phi(N)$. Its utility in analytic number theory rests on the two fundamental orthogonality relations of finite Fourier analysis.

  #proposition(title: "Orthogonality Relations")[
    Let $N >= 1$.
    1. *(Character orthogonality.)* For any Dirichlet characters $chi, psi$ modulo $N$,
       $ sum_(n mod N) chi(n) overline(psi)(n) = cases(phi(N) & "if" chi = psi, 0 & "if" chi != psi.) $
       In particular, $sum_(n mod N) chi(n) = phi(N)$ if $chi = chi_0$, and $0$ otherwise.
    2. *(Element orthogonality.)* For any integers $a, b$ with $gcd(b, N) = 1$,
       $ 1 / phi(N) sum_(chi mod N) chi(a) overline(chi)(b) = cases(1 & "if" a equiv b (op("mod") N), 0 & "otherwise".) $
  ]

  #proof[
    For (1), set $S = sum_(n mod N) (chi overline(psi))(n)$. If $chi = psi$, then $(chi overline(psi))(n) = chi_0 (n)$, which equals $1$ on the $phi(N)$ reduced residue classes and $0$ elsewhere, giving $S = phi(N)$. If $chi != psi$, there exists $c in G_N$ with $(chi overline(psi))(c) != 1$. As $n$ runs over $G_N$, so does $c n$, whence
    $ (chi overline(psi))(c) S = sum_(n in G_N) (chi overline(psi))(c n) = S, $
    and therefore $((chi overline(psi))(c) - 1) S = 0$, forcing $S = 0$.

    For (2), if $gcd(a, N) > 1$ then $chi(a) = 0$ for every $chi$, and $a equiv.not b (op("mod") N)$ since $gcd(b, N) = 1$, so both sides vanish. Assume now that $gcd(a, N) = 1$ and set $g = a b^(-1) in G_N$, so the sum is $T = sum_(chi in hat(G)_N) chi(g)$. If $a equiv b (op("mod") N)$, then $g = 1$ and $chi(1) = 1$ for all $phi(N)$ characters, giving $T = phi(N)$. If $g != 1$, then by the structure of finite abelian groups there exists a character $psi in hat(G)_N$ such that $psi(g) != 1$. Multiplying by $psi(g)$ permutes $hat(G)_N$:
    $ psi(g) T = sum_(chi in hat(G)_N) (psi chi)(g) = T, $
    which forces $T = 0$.
  ]

  === Inducing Characters, Conductors, and Primitivity

  A Dirichlet character modulo $M$ naturally gives rise to a Dirichlet character modulo any multiple $N$ of $M$, simply by restricting support to integers coprime to $N$.

  #definition(title: "Induced Character, Conductor, and Primitivity")[
    Let $M | N$ be positive integers, and let $chi_1$ be a Dirichlet character modulo $M$. The character *induced by $chi_1$ modulo $N$* is the Dirichlet character $chi$ modulo $N$ defined by
    $ chi(n) = cases(chi_1 (n) & "if" gcd(n, N) = 1, 0 & "if" gcd(n, N) > 1.) $
    Equivalently, $chi = chi_1 dot.c chi_(0, N)$, where $chi_(0, N)$ is the principal character modulo $N$.

    Given a Dirichlet character $chi$ modulo $N$, a divisor $d | N$ is called an *inducing modulus* (or *quasi-period*) of $chi$ if $chi$ is induced by some Dirichlet character modulo $d$. The *conductor* of $chi$, denoted $f_chi$ (or $q_chi$), is the smallest positive divisor $d | N$ that is an inducing modulus for $chi$. We say that $chi$ is *primitive* if $f_chi = N$, and *imprimitive* if $f_chi < N$.
  ]

  To work cleanly with conductors, it is essential to reformulate the inducing condition in terms of the kernel of $chi$ on $G_N$. For any divisor $d | N$, the canonical surjection $pi_(N, d) : (bb(Z) \/ N bb(Z))^times -> (bb(Z) \/ d bb(Z))^times$ has kernel
  $ K_(N, d) = { a in (bb(Z) \/ N bb(Z))^times : a equiv 1 (op("mod") d) }. $
  A character $chi in hat(G)_N$ is induced by a character modulo $d$ if and only if $chi$ factors through $pi_(N, d)$, which holds if and only if $chi$ is trivial on $K_(N, d)$—that is, $chi(a) = 1$ whenever $gcd(a, N) = 1$ and $a equiv 1 (op("mod") d)$. Notice that the inducing character $chi_1$ modulo $d$, when it exists, is unique because $pi_(N, d)$ is surjective.

  #theorem(title: "Existence and Uniqueness of the Primitive Inducing Character")[
    Let $chi$ be a Dirichlet character modulo $N$, and let $f = f_chi$ be its conductor.
    1. A divisor $d | N$ is an inducing modulus for $chi$ if and only if $f | d$.
    2. There exists a unique primitive Dirichlet character $chi^*$ modulo $f$ that induces $chi$.
    3. The characters $chi$ and $chi^*$ have the same parity: $chi(-1) = chi^*(-1)$.
  ]

  #proof[
    We first show that if $d_1 | N$ and $d_2 | N$ are both inducing moduli for $chi$, then $g = gcd(d_1, d_2)$ is also an inducing modulus for $chi$. Let $a in bb(Z)$ satisfy $gcd(a, N) = 1$ and $a equiv 1 (op("mod") g)$. We must prove that $chi(a) = 1$.

    Since $g = gcd(d_1, d_2)$, we may write $a - 1 = k_1 d_1 + k_2 d_2$ for some integers $k_1, k_2$. Setting $b_0 = 1 + k_1 d_1 = a - k_2 d_2$, we have $b_0 equiv 1 (op("mod") d_1)$ and $b_0 equiv a (op("mod") d_2)$, though $b_0$ may fail to be coprime to $N$. To repair coprimality, let $L = op("lcm")(d_1, d_2) | N$. By the Chinese Remainder Theorem, for each prime $p | N$ we choose an integer $x_p$:
    - if $p | L$, then either $p | d_1$ (in which case $p divides.not b_0$ since $b_0 equiv 1 (op("mod") d_1)$) or $p | d_2$ (in which case $p divides.not b_0$ since $b_0 equiv a (op("mod") d_2)$ and $gcd(a, N) = 1$); we set $x_p = 0$;
    - if $p | N$ and $p divides.not L$, then $L$ is invertible modulo $p$, so we choose $x_p$ such that $b_0 + x_p L equiv.not 0 (op("mod") p)$.

    Combining these congruences yields an integer $x$ such that $b = b_0 + x L$ satisfies $gcd(b, N) = 1$, $b equiv 1 (op("mod") d_1)$, and $b equiv a (op("mod") d_2)$. Since $d_1$ is an inducing modulus, $chi(b) = 1$. Since $gcd(a, N) = gcd(b, N) = 1$ and $a b^(-1) equiv 1 (op("mod") d_2)$, the fact that $d_2$ is an inducing modulus gives $chi(a) chi(b)^(-1) = 1$. Thus $chi(a) = chi(b) = 1$, proving that $g = gcd(d_1, d_2)$ is an inducing modulus.

    Part (1) follows immediately: if $d | N$ is an inducing modulus, then $gcd(f, d)$ is also an inducing modulus dividing $f$; by minimality of $f$, $gcd(f, d) = f$, so $f | d$. Conversely, if $f | d | N$, then $K_(N, d) subset.eq K_(N, f) subset.eq ker(chi)$, so $d$ is an inducing modulus.

    For (2), since $f$ is an inducing modulus, there is a unique character $chi^*$ modulo $f$ inducing $chi$. If $chi^*$ were induced by a character $psi$ modulo some proper divisor $d | f$, then $chi$ would also be induced by $psi$ modulo $d$, contradicting the minimality of $f$. Hence $chi^*$ is primitive.

    For (3), since $gcd(-1, N) = 1$, the definition of induction immediately gives $chi(-1) = chi^*(-1)$.
  ]

  #example(title: "Small Moduli and Conductors")[
    1. For any $N >= 1$, the principal character $chi_0$ modulo $N$ is induced by the unique character modulo $1$, so $f_(chi_0) = 1$. In particular, $chi_0$ is primitive if and only if $N = 1$.
    2. For $N = 2$, $phi(2) = 1$, so there is only the principal character, which has conductor $1$. Thus *no primitive character has conductor $2$*. More generally, if $N equiv 2 (op("mod") 4)$, then $(bb(Z) \/ N bb(Z))^times tilde.eq (bb(Z) \/ (N\/2) bb(Z))^times$, so every character modulo $N$ is induced from $N\/2$ and no primitive character exists of conductor $N equiv 2 (op("mod") 4)$.
    3. For $N = 4$, $(bb(Z) \/ 4 bb(Z))^times = {1, 3}$ has a unique non-principal character $chi_4$, given by $chi_4 (1) = 1$, $chi_4 (3) = -1$, and $chi_4 (2k) = 0$. Since $f_(chi_4)$ divides $4$ and cannot be $1$ or $2$, we have $f_(chi_4) = 4$, so $chi_4$ is an odd primitive character.
    4. For $N = 12$, $(bb(Z) \/ 12 bb(Z))^times = {1, 5, 7, 11} tilde.eq (bb(Z) \/ 2 bb(Z)) times (bb(Z) \/ 2 bb(Z))$ has four characters: the principal character (conductor $1$), the character induced by the Legendre symbol $(dot.c \/ 3)$ (conductor $3$, odd), the character induced by $chi_4$ (conductor $4$, odd), and their product $chi_(12) (n) = chi_4 (n) (n \/ 3)$, which takes values $chi_(12)(1) = chi_(12)(11) = 1$ and $chi_(12)(5) = chi_(12)(7) = -1$ (conductor $12$, even and primitive).
  ]

  A useful consequence of the Chinese Remainder Theorem is that Dirichlet characters factor uniquely into prime-power components. If $N = product_(i=1)^r p_i^(e_i)$ is the prime factorization of $N$, then
  $ (bb(Z) \/ N bb(Z))^times tilde.eq product_(i=1)^r (bb(Z) \/ p_i^(e_i) bb(Z))^times, $
  so every Dirichlet character $chi$ modulo $N$ decomposes uniquely as a product $chi = product_(i=1)^r chi_i$, where $chi_i$ is a Dirichlet character modulo $p_i^(e_i)$. One readily verifies that $f_chi = product_(i=1)^r f_(chi_i)$, and therefore $chi$ is primitive modulo $N$ if and only if each local component $chi_i$ is primitive modulo $p_i^(e_i)$.

  === Dirichlet $L$-Functions, Euler Products, and Imprimitive Decomposition

  Just as the Riemann zeta function is the Dirichlet series with constant coefficients $1$, each Dirichlet character $chi$ generates a Dirichlet $L$-function.

  #definition(title: "Dirichlet L-Function")[
    For a Dirichlet character $chi$ modulo $N$ and a complex variable $s = sigma + i t$ with $sigma = op("Re")(s) > 1$, the *Dirichlet $L$-function* attached to $chi$ is defined by
    $ L(s, chi) = sum_(n=1)^oo chi(n) / n^s. $
  ]

  Since $|chi(n)| <= 1$, the series converges absolutely and uniformly on every compact subset of the half-plane $op("Re")(s) > 1$, defining a holomorphic function there. When $chi$ is non-principal, much more is true already from elementary summation by parts: because $sum_(n <= x) chi(n)$ is bounded in magnitude by $phi(N)$ (indeed, the sum over any $N$ consecutive integers vanishes by Proposition 2.2(1)), Dirichlet's test shows that the series $sum_(n=1)^oo chi(n) n^(-s)$ converges conditionally—and uniformly on compact subsets—throughout the larger half-plane $op("Re")(s) > 0$. Thus $L(s, chi)$ is automatically holomorphic on $op("Re")(s) > 0$ for every $chi != chi_0$.

  Because $chi$ is completely multiplicative, $L(s, chi)$ admits an Euler product over all primes.

  #proposition(title: "Euler Product")[
    For any Dirichlet character $chi$ modulo $N$ and any $s in bb(C)$ with $op("Re")(s) > 1$,
    $ L(s, chi) = product_p (1 - chi(p) / p^s)^(-1), $
    where the product runs over all rational primes $p$ and converges absolutely and uniformly on compact subsets of $op("Re")(s) > 1$. In particular, $L(s, chi) != 0$ for all $s$ with $op("Re")(s) > 1$.
  ]

  #proof[
    For each prime $p$ and $sigma = op("Re")(s) > 1$, we have $|chi(p) p^(-s)| <= p^(-sigma) < 1$, so the geometric series $(1 - chi(p) p^(-s))^(-1) = sum_(k=0)^oo chi(p^k) p^(-k s)$ converges absolutely. For any $X >= 2$, the fundamental theorem of arithmetic and complete multiplicativity of $chi$ yield
    $ product_(p <= X) (1 - chi(p) / p^s)^(-1) = sum_(n in S(X)) chi(n) / n^s, $
    where $S(X)$ is the set of positive integers all of whose prime factors are $<= X$. Since every integer $1 <= n <= X$ lies in $S(X)$,
    $ abs(L(s, chi) - product_(p <= X) (1 - chi(p) / p^s)^(-1)) <= sum_(n > X) 1 / n^sigma -> 0 quad "as" X -> oo. $
    Absolute convergence of the infinite product follows from $sum_p |chi(p) p^(-s)| <= sum_p p^(-sigma) < oo$, and a convergent infinite product of nonzero factors cannot vanish.
  ]

  The Euler product immediately reveals the exact relationship between an imprimitive Dirichlet $L$-function $L(s, chi)$ and the $L$-function $L(s, chi^*)$ of the primitive character inducing it.

  #proposition(title: "Imprimitive Factorization")[
    Let $chi$ be a Dirichlet character modulo $N$, let $f = f_chi$ be its conductor, and let $chi^*$ be the unique primitive character modulo $f$ inducing $chi$. Then for all $s in bb(C)$ with $op("Re")(s) > 1$,
    $ L(s, chi) = L(s, chi^*) product_(p | N) (1 - chi^*(p) / p^s). $
    Equivalently, since $chi^*(p) = 0$ whenever $p | f$, the product may be restricted to primes $p | N$ with $p divides.not f$. Once $L(s, chi)$ and $L(s, chi^*)$ are meromorphically continued to $bb(C)$ (Section 2.2), this identity holds for all $s in bb(C)$ (away from the simple pole at $s = 1$ when $chi = chi_0$).
  ]

  #proof[
    By definition of induction, for every prime $p$ we have $chi(p) = chi^*(p)$ if $p divides.not N$, and $chi(p) = 0$ if $p | N$. Therefore, for $op("Re")(s) > 1$,
    $ L(s, chi) &= product_(p divides.not N) (1 - chi^*(p) / p^s)^(-1) \ &= (product_p (1 - chi^*(p) / p^s)^(-1)) dot.c product_(p | N) (1 - chi^*(p) / p^s) \ &= L(s, chi^*) product_(p | N) (1 - chi^*(p) / p^s). $
    Because the finite product $product_(p | N) (1 - chi^*(p) p^(-s))$ is an entire function of $s$, the identity extends by the identity theorem of complex analysis to the entire meromorphic domain of $L(s, chi)$ and $L(s, chi^*)$.
  ]

  In particular, for the principal character $chi_0$ modulo $N$, we have $chi_0^* = 1_(op("mod") 1)$ and $L(s, 1_(op("mod") 1)) = zeta(s)$, so
  $ L(s, chi_0) = zeta(s) product_(p | N) (1 - p^(-s)). $
  Thus $L(s, chi_0)$ inherits a simple pole at $s = 1$ with residue $product_(p | N) (1 - p^(-1)) = phi(N) \/ N$.

  A crucial analytic fact—deceptively simple, yet load-bearing in every reduction from general characters to primitive characters—is that the finitely many extra Euler factors introduced by imprimitivity cannot create zeros anywhere in the right half-plane $op("Re")(s) > 0$.

  #lemma(title: "Nonvanishing of Extra Euler Factors")[
    Let $psi$ be any Dirichlet character modulo $M$, let $p$ be a prime, and let $s in bb(C)$ satisfy $op("Re")(s) > 0$. Then
    $ 1 - psi(p) p^(-s) != 0. $
  ]

  #proof[
    Suppose for contradiction that $1 - psi(p) p^(-s) = 0$, so that $psi(p) p^(-s) = 1$. Since $p >= 2 > 1$ and $op("Re")(s) > 0$, we have
    $ |p^(-s)| = p^(-op("Re")(s)) < 1. $
    Combined with the bound $|psi(p)| <= 1$, this yields
    $ 1 = |psi(p) p^(-s)| = |psi(p)| dot.c |p^(-s)| <= 1 dot.c |p^(-s)| < 1, $
    a contradiction.
  ]

  #remark(title: "Imprimitive Zeros on the Imaginary Axis")[
    Lemma 2.9 is sharp as regards the half-plane $op("Re")(s) > 0$. Indeed, if $p | N$ and $p divides.not f_chi$, then $chi^*(p) = e^(i theta_p)$ lies on the unit circle, and the factor $1 - chi^*(p) p^(-s)$ vanishes at the vertical arithmetic progression of points
    $ s_k = (i theta_p + 2 pi i k) / (log p), quad k in bb(Z), $
    all lying on the line $op("Re")(s) = 0$. Consequently, an imprimitive Dirichlet $L$-function has infinitely many zeros on the boundary $op("Re")(s) = 0$ of the critical strip, whereas inside the open critical strip $0 < op("Re")(s) < 1$, $L(s, chi)$ and $L(s, chi^*)$ have the exact same zeros with the exact same multiplicities. This is why the Generalized Riemann Hypothesis is formulated either for all characters in the open strip $0 < op("Re")(s) < 1$ or specifically for primitive characters.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Extra Euler Factors",
    module: "Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean",
  )[
    In the verified Alpöge–Claude library, Lemma 2.9 appears verbatim as `Claim.factor_ne_zero`:
    ```lean
    theorem Claim.factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ}
        (hs : 0 < s.re) (p : ℕ) (hp : p.Prime) :
        (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0
    ```
    Its 14-line proof follows the exact argument above: assuming `ψ p * p ^ (-s) = 1`, it uses `Complex.norm_natCast_cpow_of_pos`, `Real.rpow_lt_one_of_one_lt_of_neg`, and `ψ.norm_le_one` to derive `‖ψ p * p ^ (-s)‖ < 1`, contradicting `norm_one`. The imprimitive factorization itself is supplied by Mathlib's `DirichletCharacter.LFunction_changeLevel`.
  ]

  == Gauss Sums and the Functional Equation for Primitive Characters

  In Chapter 1, we derived the analytic continuation and functional equation of $zeta(s)$ by applying the Poisson summation formula to the classical Jacobi theta function $theta(t) = sum_(n in bb(Z)) e^(-pi n^2 t)$. To perform the same miracle for a Dirichlet $L$-function $L(s, chi)$, we must twist the Gaussian kernel $e^(-pi n^2 t)$ by the periodic function $chi(n)$. The finite Fourier transform of $chi$ on $bb(Z) \/ q bb(Z)$ is the *Gauss sum* $tau(chi)$, and the magic of primitivity is that the finite Fourier transform of a primitive character is a scalar multiple of its conjugate character $overline(chi)$.

  === Gauss Sums and Separability

  Throughout this section, let $q >= 1$ be a positive integer and let $e(x) = e^(2 pi i x)$ for $x in bb(R)$.

  #definition(title: "Gauss Sum")[
    For a Dirichlet character $chi$ modulo $q$ and an integer $n in bb(Z)$, the *generalized Gauss sum* is
    $ tau(n, chi) = sum_(a mod q) chi(a) e((a n) / q). $
    When $n = 1$, we write simply $tau(chi) = tau(1, chi) = sum_(a mod q) chi(a) e(a \/ q)$ and call it the *Gauss sum* of $chi$.
  ]

  If $gcd(n, q) = 1$, changing variables $b equiv a n (op("mod") q)$ immediately gives
  $ tau(n, chi) = sum_(b mod q) chi(b n^(-1)) e(b / q) = overline(chi)(n) tau(chi), $
  for *any* Dirichlet character $chi$ modulo $q$, primitive or not. What distinguishes primitive characters is that this separability identity continues to hold when $gcd(n, q) > 1$—where the right-hand side is $0$.

  #lemma(title: "Separability of Gauss Sums for Primitive Characters")[
    Let $chi$ be a primitive Dirichlet character modulo $q$. Then for *every* integer $n in bb(Z)$,
    $ tau(n, chi) = overline(chi)(n) tau(chi). $
  ]

  #proof[
    We have already verified the identity when $gcd(n, q) = 1$. Suppose now that $d = gcd(n, q) > 1$; we must show that $tau(n, chi) = 0$. Write $q = d q_1$ and $n = d n_1$ with $gcd(n_1, q_1) = 1$ and $1 <= q_1 < q$.

    Because $chi$ is primitive modulo $q$ and $q_1$ is a proper divisor of $q$, $q_1$ is *not* an inducing modulus for $chi$. Hence there exists an integer $c$ such that $gcd(c, q) = 1$, $c equiv 1 (op("mod") q_1)$, and $chi(c) != 1$. For every $a in bb(Z)$, since $c equiv 1 (op("mod") q_1)$ we have
    $ (c a n) / q = (c a n_1) / q_1 equiv (a n_1) / q_1 = (a n) / q quad (op("mod") 1), $
    and therefore $e(c a n \/ q) = e(a n \/ q)$. Changing the summation variable from $a$ to $c a$ (which permutes $bb(Z) \/ q bb(Z)$ since $gcd(c, q) = 1$) gives
    $ tau(n, chi) &= sum_(a mod q) chi(c a) e((c a n) / q) \ &= chi(c) sum_(a mod q) chi(a) e((a n) / q) = chi(c) tau(n, chi). $
    Since $chi(c) != 1$, this forces $tau(n, chi) = 0 = overline(chi)(n) tau(chi)$.
  ]

  The separability lemma is a finite-group analogue of the fact that the Fourier transform of a Gaussian is a Gaussian: the discrete Fourier transform of a primitive character is proportional to $overline(chi)$. Parseval's identity on $bb(Z) \/ q bb(Z)$ immediately pins down the magnitude of the proportionality constant $tau(chi)$.

  #proposition(title: "Magnitude and Conjugate Product of Gauss Sums")[
    Let $chi$ be a primitive Dirichlet character modulo $q$. Then:
    1. $|tau(chi)| = sqrt(q)$;
    2. $tau(overline(chi)) = chi(-1) overline(tau(chi))$;
    3. $tau(chi) tau(overline(chi)) = chi(-1) q$.
  ]

  #proof[
    For (1), compute the sum of $|tau(n, chi)|^2$ over all $n mod q$ in two ways. On the one hand, by Lemma 2.12,
    $ sum_(n mod q) |tau(n, chi)|^2 = sum_(n mod q) |overline(chi)(n)|^2 |tau(chi)|^2 = phi(q) |tau(chi)|^2. $
    On the other hand, expanding the definition of $tau(n, chi)$ and interchanging the order of summation gives
    $ sum_(n mod q) |tau(n, chi)|^2 = sum_(a mod q) sum_(b mod q) chi(a) overline(chi)(b) sum_(n mod q) e(((a - b) n) / q). $
    The inner geometric sum equals $q$ if $a equiv b (op("mod") q)$ and $0$ otherwise. Thus
    $ sum_(n mod q) |tau(n, chi)|^2 = q sum_(a mod q) |chi(a)|^2 = q phi(q). $
    Dividing by $phi(q) > 0$ yields $|tau(chi)|^2 = q$, so $|tau(chi)| = sqrt(q)$.

    For (2), taking complex conjugates and substituting $b = -a$ gives
    $ overline(tau(chi)) &= sum_(a mod q) overline(chi)(a) e(-a / q) = sum_(b mod q) overline(chi)(-b) e(b / q) \ &= overline(chi)(-1) tau(overline(chi)) = chi(-1) tau(overline(chi)), $
    since $chi(-1) = plus.minus 1$. Multiplying both sides by $tau(chi)$ and using (1) yields $tau(chi) tau(overline(chi)) = chi(-1) |tau(chi)|^2 = chi(-1) q$, which is (3).
  ]

  #remark(title: "Quadratic Gauss Sums and Gauss's Sign Determination")[
    When $chi$ is a real primitive character modulo $q$ (so $chi = overline(chi)$), Proposition 2.13(3) gives $tau(chi)^2 = chi(-1) q$, whence $tau(chi) = plus.minus sqrt(q)$ if $chi$ is even and $tau(chi) = plus.minus i sqrt(q)$ if $chi$ is odd. Determining the *sign*—which is equivalent to locating $tau(chi)$ among the two square roots—is surprisingly subtle and occupied Gauss for four years (1801–1805). Gauss proved that for every fundamental discriminant $d$ and its associated primitive quadratic character $chi_d (n) = (d \/ n)$ (the Kronecker symbol), the positive sign always prevails:
    $ tau(chi_d) = cases(sqrt(d) & "if" d > 0, i sqrt(|d|) & "if" d < 0.) $
    For a general complex primitive character $chi$, the argument of $tau(chi) \/ sqrt(q)$ exhibits rich equidistribution behavior (studied by Katz and others via Deligne's Weil II), and the ratio $epsilon(chi) = tau(chi) \/ (i^a sqrt(q))$ plays the role of the *root number* in the functional equation.
  ]

  === Twisted Theta Series and Modular Transformation

  To analytically continue $L(s, chi)$ for a primitive character $chi$ modulo $q > 1$, we construct a twisted theta series adapted to the parity $a = (1 - chi(-1))\/2 in {0, 1}$ of $chi$. Why must even and odd characters be treated separately? If $chi$ is odd, then $chi(-n) = -chi(n)$, so the naive sum $sum_(n in bb(Z)) chi(n) e^(-pi n^2 t \/ q)$ vanishes identically! Multiplying the summand by $n$ restores evenness: $(-n) chi(-n) = n chi(n)$.

  #definition(title: "Twisted Theta Series")[
    Let $chi$ be a primitive Dirichlet character modulo $q > 1$, and let $t > 0$.
    - If $chi$ is *even* ($a = 0$), define
      $ theta(t, chi) = sum_(n = -oo)^oo chi(n) e^(-pi n^2 t \/ q) = 2 sum_(n=1)^oo chi(n) e^(-pi n^2 t \/ q). $
    - If $chi$ is *odd* ($a = 1$), define
      $ theta_1 (t, chi) = sum_(n = -oo)^oo n chi(n) e^(-pi n^2 t \/ q) = 2 sum_(n=1)^oo n chi(n) e^(-pi n^2 t \/ q). $
  ]

  Observe that because $q > 1$ and $chi$ is primitive, $chi(0) = 0$: there is *no constant term* at $n = 0$! This single observation explains why $L(s, chi)$ for $chi != 1$ is entire rather than having a pole at $s = 1$.

  #proposition(title: "Modular Transformation of Twisted Theta Series")[
    Let $chi$ be a primitive Dirichlet character modulo $q > 1$. Then for all $t > 0$:
    1. If $chi$ is even ($a = 0$),
       $ theta(t, chi) = tau(chi) / sqrt(q) dot.c t^(-1\/2) theta(1 / t, overline(chi)). $
    2. If $chi$ is odd ($a = 1$),
       $ theta_1 (t, chi) = tau(chi) / (i sqrt(q)) dot.c t^(-3\/2) theta_1 (1 / t, overline(chi)). $
  ]

  #proof[
    Recall the Poisson summation formula: for any Schwartz function $f in cal(S)(bb(R))$ with Fourier transform $hat(f)(y) = integral_(-oo)^oo f(x) e(-x y) d x$, we have $sum_(k in bb(Z)) f(k) = sum_(m in bb(Z)) hat(f)(m)$.

    Split the sum over $n in bb(Z)$ into residue classes $n = k q + r$ modulo $q$:
    $ theta(t, chi) = sum_(r mod q) chi(r) sum_(k in bb(Z)) e^(-pi (k q + r)^2 t \/ q). $
    For fixed $r$ and $t > 0$, set $f_r (x) = e^(-pi q t (x + r\/q)^2)$. Using the standard Gaussian Fourier transform $cal(F)(e^(-pi c x^2))(y) = c^(-1\/2) e^(-pi y^2 \/ c)$ (for $c > 0$) and the shift rule $cal(F)(g(x + alpha))(y) = e(alpha y) hat(g)(y)$, we obtain
    $ hat(f)_r (m) = (q t)^(-1\/2) e((m r) / q) e^(-pi m^2 \/ (q t)). $
    Applying Poisson summation to each inner sum over $k in bb(Z)$ and interchanging the finite sum over $r$ with the rapidly convergent sum over $m$ yields
    $ theta(t, chi) &= (q t)^(-1\/2) sum_(m in bb(Z)) (sum_(r mod q) chi(r) e((m r) / q)) e^(-pi m^2 \/ (q t)) \ &= (q t)^(-1\/2) sum_(m in bb(Z)) tau(m, chi) e^(-pi m^2 \/ (q t)). $
    By Lemma 2.12 (separability of Gauss sums for primitive $chi$), $tau(m, chi) = overline(chi)(m) tau(chi)$ for every $m in bb(Z)$, so
    $ theta(t, chi) = tau(chi) / sqrt(q) dot.c t^(-1\/2) sum_(m in bb(Z)) overline(chi)(m) e^(-pi m^2 \/ (q t)) = tau(chi) / sqrt(q) dot.c t^(-1\/2) theta(1 / t, overline(chi)). $

    For an odd primitive character $chi$, we apply the same method to $g_r (x) = (q x + r) e^(-pi q t (x + r\/q)^2)$. Since $hat(f)(y) = integral_(-oo)^oo f(x) e^(-2 pi i x y) d x$, differentiating $hat(f)(y)$ with respect to $y$ gives $cal(F)(x f(x))(y) = (i \/ (2 pi)) hat(f)'(y)$. For $f(x) = e^(-pi c x^2)$, we have $hat(f)(y) = c^(-1\/2) e^(-pi y^2 \/ c)$, whose derivative is $hat(f)'(y) = -(2 pi y \/ c) c^(-1\/2) e^(-pi y^2 \/ c)$, and therefore
    $ cal(F)(x e^(-pi c x^2))(y) = -(i y) / c^(3\/2) e^(-pi y^2 \/ c) = 1 / (i c^(3\/2)) y e^(-pi y^2 \/ c). $
    Applying the shift rule to $g_r (x) = q (x + r\/q) e^(-pi q t (x + r\/q)^2)$ yields
    $ hat(g)_r (m) &= q dot.c 1 / (i (q t)^(3\/2)) m e((m r) / q) e^(-pi m^2 \/ (q t)) \ &= 1 / (i sqrt(q) t^(3\/2)) m e((m r) / q) e^(-pi m^2 \/ (q t)). $
    Applying Poisson summation and Lemma 2.12 therefore produces
    $ theta_1 (t, chi) = 1 / (i sqrt(q) t^(3\/2)) sum_(m in bb(Z)) m tau(m, chi) e^(-pi m^2 \/ (q t)) = tau(chi) / (i sqrt(q)) dot.c t^(-3\/2) theta_1 (1 / t, overline(chi)), $
    establishing (2).
  ]

  === Analytic Continuation and the Functional Equation

  Now we take the Mellin transform of $theta(t, chi)$ (for $a = 0$) or $theta_1 (t, chi)$ (for $a = 1$) to obtain the completed Dirichlet $L$-function and its functional equation.

  #definition(title: "Completed Dirichlet L-Function and Root Number")[
    Let $chi$ be a primitive Dirichlet character modulo $q >= 1$, with parity $a = (1 - chi(-1))\/2 in {0, 1}$. The *completed Dirichlet $L$-function* is defined for $op("Re")(s) > 1$ by
    $ Lambda(s, chi) = (q / pi)^((s + a) / 2) Gamma((s + a) / 2) L(s, chi) = q^((s + a) / 2) Gamma_bb(R) (s + a) L(s, chi), $
    where $Gamma_bb(R) (z) = pi^(-z\/2) Gamma(z\/2)$ is the real archimedean gamma factor. The *root number* of $chi$ is the complex number of modulus $1$ defined by
    $ epsilon(chi) = tau(chi) / (i^a sqrt(q)). $
  ]

  By Proposition 2.13, $|epsilon(chi)| = 1$ and
  $ epsilon(chi) epsilon(overline(chi)) = (tau(chi) tau(overline(chi))) / (i^(2 a) q) = (chi(-1) q) / ((-1)^a q) = 1, $
  so $epsilon(overline(chi)) = epsilon(chi)^(-1) = overline(epsilon(chi))$. When $q = 1$ and $chi = 1_(op("mod") 1)$, we have $a = 0$, $tau(chi) = 1$, $epsilon(chi) = 1$, and $Lambda(s, 1) = pi^(-s\/2) Gamma(s\/2) zeta(s)$ is the completed Riemann zeta function (denoted $Lambda(s)$ or $xi(s) \/ (s(s-1))$ in Chapter 1).

  #theorem(title: "Analytic Continuation and Functional Equation")[
    Let $chi$ be a primitive Dirichlet character modulo $q > 1$ with parity $a in {0, 1}$. Then:
    1. Both $Lambda(s, chi)$ and $L(s, chi)$ extend to *entire* functions of $s in bb(C)$.
    2. For all $s in bb(C)$, the completed $L$-function satisfies the functional equation
       $ Lambda(s, chi) = epsilon(chi) Lambda(1 - s, overline(chi)). $
    3. The completed $L$-function $Lambda(s, chi)$ is an entire function of order $1$ (in the sense of Hadamard), bounded in vertical strips $sigma_1 <= op("Re")(s) <= sigma_2$.
  ]

  #proof[
    Assume first that $op("Re")(s) > 1$. By the substitution $u = pi n^2 t \/ q$ in Euler's integral $Gamma(w) = integral_0^oo u^(w - 1) e^(-u) d u$, we have for every integer $n >= 1$:
    $ (q / pi)^((s + a) / 2) Gamma((s + a) / 2) n^(-s) = integral_0^oo n^a e^(-pi n^2 t \/ q) t^((s + a) / 2) (d t) / t. $
    Multiplying by $chi(n)$ and summing over $n >= 1$ (justified by Fubini's theorem since $sum_(n >= 1) n^a integral_0^oo e^(-pi n^2 t \/ q) t^((sigma + a)\/2 - 1) d t < oo$ for $sigma > 1$) yields the integral representation
    $ Lambda(s, chi) = 1 / 2 integral_0^oo theta_a (t, chi) t^((s + a) / 2) (d t) / t, $
    where we write $theta_0 (t, chi) = theta(t, chi)$ and $theta_1 (t, chi)$ uniformly as $theta_a (t, chi)$. Notice that Proposition 2.16 unifies both parities into a single transformation law:
    $ theta_a (t, chi) = epsilon(chi) t^(-1\/2 - a) theta_a (1 / t, overline(chi)). $

    Split the integral at $t = 1$ into $integral_0^1 + integral_1^oo$. In the integral over $(0, 1]$, substitute $t |-> 1\/t$ and apply the unified modular transformation law:
    $ integral_0^1 theta_a (t, chi) t^((s + a) / 2) (d t) / t &= integral_1^oo theta_a (1 / t, chi) t^(-(s + a) / 2) (d t) / t \
      &= epsilon(chi) integral_1^oo theta_a (t, overline(chi)) t^(1\/2 + a - (s + a)\/2) (d t) / t \
      &= epsilon(chi) integral_1^oo theta_a (t, overline(chi)) t^((1 - s + a) / 2) (d t) / t. $
    Adding back the integral over $[1, oo)$, we arrive at the symmetric representation
    $ Lambda(s, chi) = 1 / 2 integral_1^oo (theta_a (t, chi) t^((s + a) / 2) + epsilon(chi) theta_a (t, overline(chi)) t^((1 - s + a) / 2)) (d t) / t. $

    Because $chi(0) = 0$, the series defining $theta_a (t, chi)$ and $theta_a (t, overline(chi))$ start at $n = 1$, so for $t >= 1$ we have the rapid exponential decay $|theta_a (t, chi)| <= C e^(-pi t \/ q)$ for a constant $C > 0$ depending only on $q$. Consequently, the integral converges absolutely and uniformly on every vertical strip $sigma_1 <= op("Re")(s) <= sigma_2$, defining an *entire* function $Lambda(s, chi)$ bounded on every vertical strip!

    Since $L(s, chi) = (q \/ pi)^(-(s + a)\/2) Gamma((s + a)\/2)^(-1) Lambda(s, chi)$ and $1 \/ Gamma(w)$ is an entire function of $w in bb(C)$, it follows immediately that $L(s, chi)$ is also entire.

    To verify the functional equation, replace $(s, chi)$ by $(1 - s, overline(chi))$ in the symmetric integral and multiply by $epsilon(chi)$:
    $ & epsilon(chi) Lambda(1 - s, overline(chi)) \ & quad = 1 / 2 integral_1^oo (epsilon(chi) theta_a (t, overline(chi)) t^((1 - s + a) / 2) + epsilon(chi) epsilon(overline(chi)) theta_a (t, chi) t^((s + a) / 2)) (d t) / t. $
    Because $epsilon(chi) epsilon(overline(chi)) = 1$, this coincides identically with $Lambda(s, chi)$. Finally, standard Stirling-type bounds on the integral $integral_1^oo e^(-pi t \/ q) t^((|s| + 1)\/2) d t \/ t <= C_1 (q |s|)^(C_2 |s|)$ show that $Lambda(s, chi)$ has order at most $1$ (and exact order $1$ by Stirling's formula on the gamma factor for $op("Re")(s) -> +oo$).
  ]

  #corollary(title: "Analytic Continuation for General Characters and Trivial Zeros")[
    1. For *any* non-principal Dirichlet character $chi != chi_0$ modulo $N$, $L(s, chi)$ extends to an entire function of $s in bb(C)$. For $chi = chi_0$, $L(s, chi_0)$ extends to a meromorphic function on $bb(C)$ with a single simple pole at $s = 1$ of residue $phi(N) \/ N$.
    2. For a primitive character $chi$ modulo $q > 1$ with parity $a in {0, 1}$, the zeros of $L(s, chi)$ in the half-plane $op("Re")(s) <= 0$ are precisely the simple zeros at
       $ s = -2 k - a, quad k = 0, 1, 2, dots.c $
       (the *trivial zeros*), corresponding to the simple poles of $Gamma((s + a)\/2)$, provided $L(1, overline(chi)) != 0$ (which we prove in Section 2.3; in particular $s = 0$ is a simple zero of $L(s, chi)$ when $chi$ is even and $q > 1$, whereas $L(0, chi) != 0$ when $chi$ is odd).
  ]

  #proof[
    Part (1) follows from Theorem 2.18(1) and the imprimitive factorization (Proposition 2.8), since $chi != chi_0$ implies $f_chi > 1$ and the finite Euler factor product is entire.

    For (2), if $op("Re")(s) < 0$, then $op("Re")(1 - s) > 1$, so $L(1 - s, overline(chi)) != 0$ by the Euler product (Proposition 2.7) and $Gamma((1 - s + a)\/2) != 0$ since $Gamma$ has no zeros. Thus $Lambda(s, chi) = epsilon(chi) Lambda(1 - s, overline(chi)) != 0$ for all $op("Re")(s) < 0$. From $L(s, chi) = (q \/ pi)^(-(s + a)\/2) Gamma((s + a)\/2)^(-1) Lambda(s, chi)$, the zeros of $L(s, chi)$ in $op("Re")(s) < 0$ coincide with the simple poles of $Gamma((s + a)\/2)$, namely $s = -2k - a$ ($k >= 1$ if $a = 0$, $k >= 0$ if $a = 1$). On the boundary $op("Re")(s) = 0$, once we know $L(1 + i t, overline(chi)) != 0$ for all $t in bb(R)$ (Section 2.3), $Lambda(i t, chi) != 0$ for all $t in bb(R)$; thus $L(i t, chi)$ vanishes on $op("Re")(s) = 0$ if and only if $t = 0$ and $a = 0$, giving the simple zero at $s = 0$ for even primitive characters $q > 1$.
  ]

  #remark(title: "The Value at s = 0 and Generalized Bernoulli Numbers")[
    Evaluating the functional equation at $s = 0$ for an odd primitive character $chi$ modulo $q$ yields
    $ L(0, chi) &= (tau(chi)) / (i sqrt(q)) dot.c (q / pi)^(1\/2) dot.c (Gamma(1)) / (Gamma(1\/2)) L(1, overline(chi)) \ &= (tau(chi)) / (i pi) L(1, overline(chi)) = -1 / q sum_(a = 1)^(q - 1) a chi(a), $
    where the last equality comes from the Hurwitz zeta function or direct Abel summation. Thus $L(0, chi)$ is an algebraic number in the cyclotomic field $bb(Q)(chi)$—specifically $-B_(1, chi)$, the negative of the first generalized Bernoulli number—and its nonvanishing is equivalent to $L(1, overline(chi)) != 0$!
  ]

  == Dirichlet's Theorem on Primes in Arithmetic Progressions

  Dirichlet's original motivation for introducing $L(s, chi)$ was to prove that for any coprime integers $a$ and $N >= 1$, there are infinitely many primes $p equiv a (op("mod") N)$. The strategy is a direct generalization of Euler's proof of the infinitude of primes: take the logarithmic derivative of the Euler product and isolate the residue class $a (op("mod") N)$ by character orthogonality.

  === Reduction to the Nonvanishing of $L(1, chi)$

  For any Dirichlet character $chi$ modulo $N$ and $op("Re")(s) > 1$, taking the logarithmic derivative of the Euler product $L(s, chi) = product_p (1 - chi(p) p^(-s))^(-1)$ yields
  $ - (L'(s, chi)) / (L(s, chi)) = sum_(n=1)^oo (Lambda(n) chi(n)) / n^s = sum_p (chi(p) log p) / p^s + sum_p sum_(k >= 2) (chi(p^k) log p) / p^(k s), $
  where $Lambda(n)$ is the von Mangoldt function. The contribution of higher prime powers $k >= 2$ is bounded in absolute value by $sum_p sum_(k >= 2) (log p) \/ p^(k sigma) <= sum_p (log p) \/ (p(p - 1)) < oo$ uniformly for $sigma >= 1$. Multiplying by $overline(chi)(a)$ and averaging over all $chi in hat(G)_N$, element orthogonality (Proposition 2.2(2)) gives, for real $s > 1$,
  $ sum_(p equiv a (op("mod") N)) (log p) / p^s = - 1 / phi(N) sum_(chi mod N) overline(chi)(a) (L'(s, chi)) / (L(s, chi)) + O(1). $

  As $s -> 1^+$, the principal character $chi_0$ contributes a simple pole:
  $ - (L'(s, chi_0)) / (L(s, chi_0)) = 1 / (s - 1) + O(1). $
  For each non-principal character $chi != chi_0$, $L(s, chi)$ is holomorphic at $s = 1$. If $L(1, chi) != 0$, then $-L'(s, chi) \/ L(s, chi) = O(1)$ as $s -> 1^+$. If, however, $L(s, chi)$ had a zero of order $m_chi >= 1$ at $s = 1$, then $-L'(s, chi) \/ L(s, chi) = -m_chi \/ (s - 1) + O(1)$, which could potentially cancel the pole from $chi_0$. Thus the divergence of $sum_(p equiv a (op("mod") N)) (log p) \/ p^s$ as $s -> 1^+$—and with it Dirichlet's theorem—is completely reduced to a single analytic statement: $L(1, chi) != 0$ for every non-principal character $chi$ modulo $N$.

  === Nonvanishing at $s = 1$: Complex and Real Characters

  The proof of $L(1, chi) != 0$ famously bifurcates into two cases: complex characters ($chi != overline(chi)$) and real characters ($chi = overline(chi)$). Remarkably, the complex case is almost trivial, whereas the real case touches the deepest arithmetic of quadratic number fields.

  To handle both cases cleanly, we first record a classic theorem of Landau on Dirichlet series with nonnegative coefficients—a theorem that will reappear in Part II as the analytic heartbeat of the Alpöge–Claude proof!

  #theorem(title: "Landau's Theorem on Nonnegative Dirichlet Series")[
    Let $F(s) = sum_(n=1)^oo a_n n^(-s)$ be a Dirichlet series with real, nonnegative coefficients $a_n >= 0$ for all $n >= 1$. Suppose that the series converges for $op("Re")(s) > sigma_0$ (with $sigma_0 in bb(R)$) and that $F(s)$ extends analytically to a neighborhood of the real point $s = sigma_0$. Then there exists $delta > 0$ such that the Dirichlet series $sum_(n=1)^oo a_n n^(-s)$ converges for all $s$ with $op("Re")(s) > sigma_0 - delta$.
  ]

  #proof[
    By shifting $s |-> s + sigma_0$, we may assume without loss of generality that $sigma_0 = 0$. Fix $sigma_1 = 1$. Because $F$ is holomorphic on $op("Re")(s) > 0$ and on an open disk around $s = 0$, the open disk $D(1, 1 + 2 delta)$ of center $1$ and radius $1 + 2 delta$ is contained in the domain of holomorphy of $F$ for some $delta > 0$. Expanding $F$ in its Taylor series around $s = 1$ gives, for every real $s in (-delta, 1]$,
    $ F(s) = sum_(k=0)^oo (F^((k))(1)) / k! (s - 1)^k = sum_(k=0)^oo ((-1)^k F^((k))(1)) / k! (1 - s)^k. $
    For $op("Re")(s) > 0$, term-by-term differentiation of $F(s) = sum_(n=1)^oo a_n n^(-s)$ yields $(-1)^k F^((k))(1) = sum_(n=1)^oo a_n (log n)^k n^(-1)$. Since every term $a_n (log n)^k (1 - s)^k \/ (k! n)$ is nonnegative for $s in (-delta, 1]$, Tonelli's theorem permits interchanging the two infinite sums:
    $ F(s) = sum_(n=1)^oo a_n / n sum_(k=0)^oo ((1 - s) log n)^k / k! = sum_(n=1)^oo a_n / n dot.c n^(1 - s) = sum_(n=1)^oo a_n / n^s. $
    In particular, the Dirichlet series converges at $s = -delta \/ 2$, and therefore converges absolutely for all $op("Re")(s) > -delta \/ 2$.
  ]

  With Landau's theorem in hand, the nonvanishing of $L(1, chi)$ for *all* non-principal characters follows in a few transparent strokes.

  #theorem(title: "Nonvanishing of L(1, chi)")[
    For every modulus $N >= 1$ and every non-principal Dirichlet character $chi != chi_0$ modulo $N$,
    $ L(1, chi) != 0. $
  ]

  #proof[
    We consider two cases, and note that in fact the first argument handles all complex characters directly while the second uses Landau's theorem for real characters (and indeed can also be adapted to the full product).

    *Case 1: $chi$ is complex ($chi != overline(chi)$).* Consider the Dedekind-like product over all characters modulo $N$:
    $ zeta_N (s) = product_(psi mod N) L(s, psi) = product_(p divides.not N) product_(psi mod N) (1 - psi(p) / p^s)^(-1), quad op("Re")(s) > 1. $
    Taking the logarithm for real $s > 1$ and using element orthogonality (Proposition 2.2(2)), we obtain
    $ log zeta_N (s) = sum_(psi mod N) sum_(p divides.not N) sum_(k=1)^oo (psi(p^k)) / (k p^(k s)) = phi(N) sum_(p^k equiv 1 (op("mod") N)) 1 / (k p^(k s)) >= 0. $
    Exponentiating shows that $zeta_N (s) >= 1$ for all real $s > 1$.

    Now suppose for contradiction that $L(1, chi) = 0$. Since $overline(L(s, chi)) = L(overline(s), overline(chi))$, we also have $L(1, overline(chi)) = overline(L(1, chi)) = 0$. Because $chi$ is complex, $chi$ and $overline(chi)$ are *distinct* non-principal characters modulo $N$. In the product $zeta_N (s) = product_(psi mod N) L(s, psi)$, the principal character $L(s, chi_0)$ has a simple pole at $s = 1$, every other factor is holomorphic at $s = 1$, and *both* $L(s, chi)$ and $L(s, overline(chi))$ vanish at $s = 1$. Hence $zeta_N (s)$ is holomorphic at $s = 1$ with a zero of order at least $2 - 1 = 1$, forcing $lim_(s -> 1^+) zeta_N (s) = 0$. This contradicts $zeta_N (s) >= 1$ for all $s > 1$!

    *Case 2: $chi$ is real ($chi = overline(chi)$, $chi != chi_0$).* Consider the product
    $ F(s) = zeta(s) L(s, chi) = sum_(n=1)^oo (1 * chi)(n) / n^s, quad op("Re")(s) > 1, $
    where $a_n = (1 * chi)(n) = sum_(d | n) chi(d)$ is the Dirichlet convolution of $1$ and $chi$. Because $a_n$ is multiplicative, we evaluate it on prime powers $p^e$:
    $ a_(p^e) &= 1 + chi(p) + chi(p)^2 + dots.c + chi(p)^e \ &= cases(e + 1 & "if" chi(p) = 1, 1 & "if" chi(p) = 0, 1 & "if" chi(p) = -1 "and" e "is even", 0 & "if" chi(p) = -1 "and" e "is odd".) $
    Two crucial properties jump out: first, $a_n >= 0$ for every integer $n >= 1$; second, $a_(m^2) >= 1$ for every square $m^2$ (since every prime exponent $e$ in $m^2$ is even).

    Now suppose for contradiction that $L(1, chi) = 0$. Then the simple zero of $L(s, chi)$ at $s = 1$ cancels the simple pole of $zeta(s)$ at $s = 1$, so $F(s) = zeta(s) L(s, chi)$ extends to an *entire* function on all of $bb(C)$. By Landau's Theorem (Theorem 2.21), the Dirichlet series $sum_(n=1)^oo a_n n^(-s)$ must converge for all $s in bb(R)$—in particular at $s = 1\/2$! Yet at $s = 1\/2$, dropping non-square terms gives
    $ sum_(n=1)^oo a_n / n^(1\/2) >= sum_(m=1)^oo a_(m^2) / m >= sum_(m=1)^oo 1 / m = +oo, $
    contradicting convergence at $s = 1\/2$. Therefore $L(1, chi) != 0$.
  ]

  #remark(title: "Arithmetic Interpretation via Dedekind Zeta Functions")[
    When $chi = chi_d$ is the primitive quadratic character attached to a fundamental discriminant $d$, the product $F(s) = zeta(s) L(s, chi_d)$ in Case 2 is precisely the *Dedekind zeta function* $zeta_K (s) = sum_(frak(a) subset.eq cal(O)_K) N(frak(a))^(-s)$ of the quadratic number field $K = bb(Q)(sqrt(d))$. Its coefficients $a_n$ count the number of integral ideals of norm $n$, which is manifestly nonnegative and at least $1$ on squares $n = m^2$ (since the principal ideal $(m) subset.eq cal(O)_K$ has norm $m^2$). Similarly, in Case 1, the product $zeta_N (s)$ differs only by finitely many Euler factors at primes $p | N$ from the Dedekind zeta function of the cyclotomic field $bb(Q)(zeta_N)$. Thus the nonvanishing of $L(1, chi)$ is equivalent to the existence of the simple pole of $zeta_K (s)$ at $s = 1$!
  ]

  Combining Theorem 2.22 with our logarithmic-derivative identity yields Dirichlet's celebrated theorem.

  #theorem(title: "Dirichlet, 1837")[
    Let $N >= 1$ and $a in bb(Z)$ satisfy $gcd(a, N) = 1$. Then as $s -> 1^+$,
    $ sum_(p equiv a (op("mod") N)) (log p) / p^s = 1 / phi(N) dot.c 1 / (s - 1) + O(1). $
    In particular, there are infinitely many primes $p equiv a (op("mod") N)$, and the set of such primes has Dirichlet density $1 \/ phi(N)$.
  ]

  === Dirichlet's Class Number Formula

  For a real primitive character $chi_d$ attached to the quadratic field $K = bb(Q)(sqrt(d))$ of discriminant $d$, the residue of $zeta_K (s) = zeta(s) L(s, chi_d)$ at $s = 1$ is simply $L(1, chi_d)$ (since $op("Res")_(s=1) zeta(s) = 1$). On the other hand, counting integral ideals of norm $<= X$ in each ideal class via Minkowski's geometry of numbers computes the residue of $zeta_K (s)$ in terms of the arithmetic invariants of $K$. Equating the two yields *Dirichlet's class number formula*.

  #theorem(title: "Dirichlet's Class Number Formula")[
    Let $K = bb(Q)(sqrt(d))$ be a quadratic number field of fundamental discriminant $d$, with class number $h(d)$ and primitive quadratic character $chi_d (n) = (d \/ n)$.
    1. If $d < 0$ (imaginary quadratic), let $w_d = |cal(O)_K^times|$ be the number of roots of unity in $K$ ($w_(-3) = 6$, $w_(-4) = 4$, and $w_d = 2$ for $d < -4$). Then
       $ L(1, chi_d) = (2 pi h(d)) / (w_d sqrt(|d|)). $
    2. If $d > 0$ (real quadratic), let $epsilon_d > 1$ be the fundamental unit of $cal(O)_K$. Then
       $ L(1, chi_d) = (2 h(d) log epsilon_d) / sqrt(d). $
  ]

  Since $h(d) >= 1$ and $log epsilon_d > 0$, the class number formula provides a *second*, purely algebraic-geometric proof that $L(1, chi_d) > 0$ (indeed, this was Dirichlet's original 1839 proof!). Even more importantly, it reveals an extraordinary bridge between analysis and algebra: *lower bounds on $L(1, chi_d)$ translate directly into lower bounds on the class number $h(d)$*, and conversely, the hypothetical existence of a real zero of $L(s, chi_d)$ extremely close to $s = 1$ would force $h(d)$ to be anomalously small.

  === Zero-Free Regions, Siegel Zeros, and the Deuring–Heilbronn Phenomenon

  To pass from Dirichlet density (Theorem 2.24) to an asymptotic formula for the prime-counting function $pi(x ";" q, a) = |{p <= x : p equiv a (op("mod") q)}|$ with quantitative error terms, one needs nonvanishing of $L(s, chi)$ not just at $s = 1$, but along the entire line $op("Re")(s) = 1$ and inside a zero-free region to its left.

  For complex characters, the classical Hadamard–de la Vallée Poussin trigonometric inequality $3 + 4 cos theta + cos 2 theta = 2(1 + cos theta)^2 >= 0$ applies verbatim to $-op("Re")(3 (zeta'\/zeta)(sigma) + 4 (L'\/L)(sigma + i t, chi) + (L'\/L)(sigma + 2 i t, chi^2)) >= 0$, showing immediately that $L(1 + i t, chi) != 0$ for all $t in bb(R)$ and yielding a zero-free region $sigma > 1 - c \/ log(q (|t| + 2))$ with an explicit absolute constant $c > 0$.

  When $chi$ is a real quadratic character, however, $chi^2 = chi_0$ has a pole at $s = 1$! If $t$ is very small (in particular $t = 0$), the pole of $-(L'\/L)(sigma + 2 i t, chi^2)$ near $s = 1$ destroys the inequality and opens a tiny gap near $s = 1$ where a single real zero could hide.

  #theorem(title: "Classical Zero-Free Region and Exceptional Zero (Landau–Page)")[
    There exists an effective absolute constant $c > 0$ such that for every modulus $q >= 1$:
    1. For every Dirichlet character $chi$ modulo $q$, $L(s, chi)$ has no zeros in the region
       $ sigma >= 1 - c / (log(q (|t| + 2))), $
       with at most *one* exception: there is at most one real primitive character $chi_1$ modulo $q_1 | q$ whose $L$-function has a single real, simple zero $beta_1$ satisfying $1 - c \/ log(2 q) < beta_1 < 1$.
    2. Across *all* moduli $q <= Q$, there is at most *one* real primitive character $chi_1$ of conductor $q_1 <= Q$ having a real zero $beta_1 > 1 - c \/ log(2 Q)$.
  ]

  Such a hypothetical real zero $beta_1$ very close to $1$ is called a *Siegel zero* (or *Landau–Siegel zero*). Of course, GRH rules out Siegel zeros completely (forcing all nontrivial zeros onto $op("Re")(s) = 1\/2$). Before the Alpöge–Claude proof, however, ruling out Siegel zeros—even showing $beta_1 <= 1 - c \/ (log q)^A$ effectively—was one of the most notorious open problems in analytic number theory.

  The best classical unconditional bound on $beta_1$ was proved by Siegel in 1935:

  #theorem(title: "Siegel's Theorem, 1935")[
    For every $epsilon > 0$, there exists a constant $C(epsilon) > 0$ such that for every real primitive Dirichlet character $chi$ modulo $q$,
    $ L(1, chi) >= C(epsilon) q^(-epsilon), $
    and any real zero $beta$ of $L(s, chi)$ satisfies $beta <= 1 - C'(epsilon) q^(-epsilon)$.
  ]

  The catch is that Siegel's proof is *ineffective*: the constant $C(epsilon)$ cannot be computed from the proof, because it depends on whether or not a counterexample to GRH exists at some unknown modulus! Feeding Siegel's bound into the explicit formula for $psi(x ";" q, a) = sum_(n <= x, n equiv a (op("mod") q)) Lambda(n)$ yields the *Siegel–Walfisz theorem*: for every fixed $A > 0$, there exists a (non-effective) constant $c_A > 0$ such that uniformly for $q <= (log x)^A$ and $gcd(a, q) = 1$,
  $ pi(x ";" q, a) = (op("li")(x)) / phi(q) + O_A (x exp(-c_A sqrt(log x))). $

  Remarkably, the very mechanism that makes Siegel's theorem ineffective reveals a striking spectral phenomenon: if a Siegel zero $beta_1$ *did* exist, it would act as a powerful repulsive force pushing *all other* zeros of *all* Dirichlet $L$-functions away from the line $op("Re")(s) = 1$.

  #theorem(title: "Deuring–Heilbronn Phenomenon (Linnik, 1944)")[
    There exist effective absolute constants $c_1, c_2 > 0$ such that if a real primitive character $chi_1$ modulo $q_1$ has a real zero $beta_1 > 1\/2$, then for *every* modulus $q >= 1$, *every* character $chi$ modulo $q$, and *every* zero $rho = beta + i gamma != beta_1$ of $L(s, chi)$,
    $ beta <= 1 - c_1 / (log(q q_1 (|gamma| + 2))) log ( (c_2) / ((1 - beta_1) log(q q_1 (|gamma| + 2))) ) $
    whenever the argument of the outer logarithm exceeds $1$.
  ]

  #insight-box(title: "The Siegel-Zero Barrier vs. the Right Half-Plane")[
    In classical analytic number theory, the Siegel-zero obstruction is deeply intertwined with the $1$-line: classical zero-free regions perturb around $sigma = 1$ using positivity of $3 + 4 cos theta + cos 2 theta$, which fails at $t = 0$ for real characters because $chi^2 = 1$. By contrast, the Alpöge–Claude proof does *not* attempt to enlarge a classical zero-free region leftward from $sigma = 1$. Instead, it assumes a zero $rho = beta + i gamma$ anywhere in the entire open right half-plane $beta > 1\/2$—whether real or complex, whether near $1$ or near $1\/2$—and derives a contradiction from global automorphic multiplicity and Arakelov slope inequalities. Consequently, Siegel zeros are eliminated on the exact same footing as all other off-line zeros!
  ]

  == The Generalized Riemann Hypothesis and Reduction to the Right Half-Plane

  We are now in a position to state the Generalized Riemann Hypothesis cleanly and to establish the exact logical reduction that connects the main analytic engine of the Alpöge–Claude proof to both GRH and the classical Riemann Hypothesis.

  === Statement of the Generalized Riemann Hypothesis

  #conjecture(title: "Generalized Riemann Hypothesis (GRH)")[
    For every modulus $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every complex number $s in bb(C)$ in the open critical strip $0 < op("Re")(s) < 1$,
    $ L(s, chi) = 0 quad ==> quad op("Re")(s) = 1 / 2. $
  ]

  (Of course, following the Alpöge–Claude theorem, this statement is now a proved theorem; we retain the classical terminology here to emphasize its historical formulation before turning to its formal proof in Part III.)

  Notice how GRH unifies and dramatically strengthens every estimate in Section 2.3. Under GRH, the explicit formula for $psi(x ";" q, a)$ yields, uniformly for all $q >= 1$ and $gcd(a, q) = 1$,
  $ pi(x ";" q, a) = (op("li")(x)) / phi(q) + O(x^(1\/2) log(q x)), $
  which gives an asymptotic formula all the way up to $q <= x^(1\/2) \/ (log x)^(2 + epsilon)$ (compared to the polylogarithmic range $q <= (log x)^A$ of Siegel–Walfisz!). Beyond primes in progressions, GRH implies:
  - *Least quadratic nonresidue*: for every odd prime $p$, the smallest quadratic nonresidue modulo $p$ is $O((log p)^2)$ (Ankeny's theorem), and the smallest prime $p equiv a (op("mod") q)$ is $O((phi(q) log q)^2)$ (improving Linnik's theorem).
  - *Artin's primitive root conjecture*: Hooley (1967) showed that GRH (for Dedekind zeta functions of Kummer extensions, of which Dirichlet GRH is the abelian base) implies that every non-square integer $a != -1$ is a primitive root modulo a positive density of primes.
  - *Deterministic primality testing*: Miller's test (1976) runs in polynomial time $O((log n)^4)$ assuming GRH for Dirichlet $L$-functions.
  - *Effective class number bounds*: $L(1, chi_d) >> (log |d|)^(-1)$ effectively, yielding effective bounds on $h(d)$ and resolving all Siegel-zero issues.

  === The Three Formal Statements

  In the Alpöge–Claude proof—and in its Lean 4 formalization—the logical architecture separates the *deep automorphic-arithmetic theorem* from the *elementary functional-equation deduction*. Specifically, consider the following three propositions:

  - *(Half-Plane Nonvanishing, `Claim.HalfPlane`)*: For every $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $op("Re")(s) > 1\/2$, if $chi != 1$ or $s != 1$, then $L(s, chi) != 0$.
  - *(Critical Strip GRH, `Claim.Strip`)*: For every $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $0 < op("Re")(s) < 1$, if $L(s, chi) = 0$ then $op("Re")(s) = 1\/2$.
  - *(Classical Riemann Hypothesis, `Claim.Zeta`)*: For every $s in bb(C)$, if $zeta(s) = 0$, $s$ is not a negative even integer $-2(n + 1)$ ($n in bb(N)$), and $s != 1$, then $op("Re")(s) = 1\/2$.

  (Note: the hypothesis $s != 1$ in `Claim.Zeta` is a harmless convention inherited from Mathlib's definition of `RiemannHypothesis`, where `riemannZeta 1` is assigned a junk/principal value; in `Claim.HalfPlane`, the guard $chi != 1 or s != 1$ similarly avoids the pole of $L(s, 1)$ at $s = 1$, where in Mathlib `DirichletCharacter.LFunction 1 1` is defined via `riemannZeta 1`.)

  We now prove in complete detail that *Half-Plane Nonvanishing implies both Critical Strip GRH and the Classical Riemann Hypothesis*. Every lemma below corresponds one-to-one with a theorem in `ClaimStrip.lean`.

  === Step-by-Step Proof of the Reduction

  #lemma(title: "Reduction to Primitive Characters in the Strip; Claim.prim_zero")[
    Let $chi$ be a Dirichlet character modulo $N >= 1$, and let $chi^*$ be the primitive character modulo $f_chi$ inducing $chi$. If $s in bb(C)$ satisfies $0 < op("Re")(s) < 1$ and $L(s, chi) = 0$, then
    $ L(s, chi^*) = 0. $
  ]

  #proof[
    Since $op("Re")(s) < 1$, we have $s != 1$. By the imprimitive factorization (Proposition 2.8),
    $ 0 = L(s, chi) = L(s, chi^*) product_(p | N) (1 - chi^*(p) p^(-s)). $
    Since $bb(C)$ is an integral domain, either $L(s, chi^*) = 0$ or $1 - chi^*(p) p^(-s) = 0$ for some prime $p | N$. The second possibility is ruled out by Lemma 2.9 because $op("Re")(s) > 0$. Hence $L(s, chi^*) = 0$.
  ]

  #lemma(title: "Nonvanishing of the Archimedean Gamma Factor; Claim.gamma_ne_zero")[
    Let $phi$ be any Dirichlet character modulo $M >= 1$ with parity $a in {0, 1}$, and let $t in bb(C)$ satisfy $op("Re")(t) > 0$. Then the archimedean gamma factor
    $ Gamma_phi (t) = Gamma_bb(R) (t + a) = pi^(-(t + a) / 2) Gamma((t + a) / 2) $
    is nonzero (and finite).
  ]

  #proof[
    If $phi$ is even ($a = 0$), then $op("Re")(t \/ 2) = op("Re")(t) \/ 2 > 0$. If $phi$ is odd ($a = 1$), then $op("Re")((t + 1) \/ 2) = (op("Re")(t) + 1) \/ 2 > 1\/2 > 0$. In either case, $w = (t + a) \/ 2$ lies in the open right half-plane $op("Re")(w) > 0$, where $Gamma(w)$ has neither zeros nor poles, and $pi^(-w) = exp(-w log pi) != 0$. Thus $Gamma_phi (t) != 0$.
  ]

  #lemma(title: "Reflection of Primitive Zeros; Claim.prim_reflect")[
    Let $psi$ be a primitive Dirichlet character modulo $M >= 1$, and let $s in bb(C)$ satisfy $0 < op("Re")(s) < 1$. If $L(s, psi) = 0$, then
    $ L(1 - s, overline(psi)) = 0. $
  ]

  #proof[
    Because $op("Re")(s) > 0$ and $op("Re")(1 - s) = 1 - op("Re")(s) > 0$, we have both $s != 0$ and $1 - s != 0$. By Lemma 2.31, $Gamma_psi (s) != 0$, and $L(s, psi) = M^(-(s + a)\/2) Lambda(s, psi) \/ Gamma_psi (s)$ vanishes at $s$ if and only if $Lambda(s, psi) = 0$.

    Now $overline(psi) = psi^(-1)$ is also primitive modulo $M$ (since $f_(overline(psi)) = f_psi = M$). By the functional equation for $overline(psi)$ (Theorem 2.18 for $M > 1$, and the functional equation of $xi(s)$ for $M = 1$),
    $ Lambda(1 - s, overline(psi)) = epsilon(overline(psi)) Lambda(s, psi) = epsilon(overline(psi)) dot.c 0 = 0. $
    (In fact, since $Gamma_(overline(psi)) (1 - s)$ is finite and nonzero for $op("Re")(1 - s) > 0$ by Lemma 2.31, dividing $Lambda(1 - s, overline(psi)) = 0$ by $M^((1 - s + a)\/2) Gamma_(overline(psi)) (1 - s)$ yields $L(1 - s, overline(psi)) = 0$.)
  ]

  #theorem(title: "Reduction of GRH to the Right Half-Plane; Claim.strip")[
    Assume Half-Plane Nonvanishing (`Claim.HalfPlane`): for every $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every $s in bb(C)$ with $op("Re")(s) > 1\/2$ and $(chi != 1 or s != 1)$, we have $L(s, chi) != 0$. Then GRH (`Claim.Strip`) holds: every zero of $L(s, chi)$ in $0 < op("Re")(s) < 1$ satisfies $op("Re")(s) = 1\/2$.
  ]

  #proof[
    Let $N >= 1$, let $chi$ be a Dirichlet character modulo $N$, and let $s in bb(C)$ satisfy $0 < op("Re")(s) < 1$ and $L(s, chi) = 0$. Note that $s != 0$ (since $op("Re")(s) > 0$) and $s != 1$ (since $op("Re")(s) < 1$). We compare $op("Re")(s)$ with $1\/2$ by trichotomy:
    - *Case 1: $op("Re")(s) > 1\/2$.* Since $s != 1$, Half-Plane Nonvanishing immediately gives $L(s, chi) != 0$, contradicting $L(s, chi) = 0$.
    - *Case 2: $op("Re")(s) < 1\/2$.* Let $chi^*$ be the primitive character modulo $f_chi >= 1$ inducing $chi$. By Lemma 2.30 (`prim_zero`), $L(s, chi^*) = 0$. By Lemma 2.32 (`prim_reflect`), $L(1 - s, overline(chi^*)) = 0$. However,
      $ op("Re")(1 - s) = 1 - op("Re")(s) > 1 - 1 / 2 = 1 / 2, $
      and $1 - s != 1$ because $s != 0$. Applying Half-Plane Nonvanishing to the character $overline(chi^*)$ modulo $f_chi$ at the point $1 - s$ yields $L(1 - s, overline(chi^*)) != 0$, a contradiction.
    - *Case 3: $op("Re")(s) = 1\/2$.* This is the only remaining possibility.
  ]

  Finally, we deduce the classical Riemann Hypothesis for $zeta(s)$—ruling out *all* zeros outside the critical line except the trivial zeros at negative even integers.

  #theorem(title: "Reduction of RH to the Right Half-Plane; Claim.zeta")[
    Assume Half-Plane Nonvanishing (`Claim.HalfPlane`). Then the classical Riemann Hypothesis (`Claim.Zeta`) holds: every $s in bb(C)$ with $zeta(s) = 0$, $s != -2(n + 1)$ for all $n in bb(N)$, and $s != 1$ satisfies $op("Re")(s) = 1\/2$.
  ]

  #proof[
    Let $s in bb(C)$ satisfy $zeta(s) = 0$, $s != -2(n + 1)$ for all $n in bb(N)$, and $s != 1$. First, $s != 0$ because $zeta(0) = -1\/2 != 0$. We split into three regions according to $op("Re")(s)$:
    1. *$0 < op("Re")(s) < 1$.* Since $L(s, 1_(op("mod") 1)) = zeta(s)$, we have $L(s, 1_(op("mod") 1)) = 0$, so Theorem 2.33 (`Claim.strip`) gives $op("Re")(s) = 1\/2$.
    2. *$op("Re")(s) >= 1$.* By the Hadamard–de la Vallée Poussin nonvanishing theorem (Chapter 1), $zeta(s) != 0$ for all $op("Re")(s) >= 1$ (including $op("Re")(s) = 1$, and $s != 1$ by assumption), contradicting $zeta(s) = 0$.
    3. *$op("Re")(s) <= 0$.* Recall that $zeta(s) = Lambda(s) \/ Gamma_bb(R) (s)$ for $s != 0$, where $Lambda(s) = pi^(-s\/2) Gamma(s\/2) zeta(s)$ satisfies $Lambda(1 - s) = Lambda(s)$. The reciprocal $1 \/ Gamma_bb(R) (s)$ vanishes precisely when $s \/ 2 in {0, -1, -2, dots.c}$, i.e., when $s = 0$ or $s = -2(n + 1)$ for some $n in bb(N)$. Both are excluded by hypothesis and $s != 0$, so $Gamma_bb(R) (s)$ is finite and nonzero, and hence $zeta(s) = 0$ implies $Lambda(s) = 0$.

       Since $op("Re")(s) <= 0$, we have $op("Re")(1 - s) = 1 - op("Re")(s) >= 1 > 0$, so $1 - s != 0$. By the functional equation, $Lambda(1 - s) = Lambda(s) = 0$, and therefore
       $ zeta(1 - s) = (Lambda(1 - s)) / (Gamma_bb(R) (1 - s)) = 0. $
       Yet $op("Re")(1 - s) >= 1$, contradicting the nonvanishing of $zeta$ on $op("Re")(w) >= 1$!

    Hence only Case (1) can occur, and $op("Re")(s) = 1\/2$.
  ]

  #lean-note(
    title: "Lean 4 Formalization: The Reduction Pipeline",
    module: "Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean",
  )[
    Every single step of Section 2.4 is formalized cleanly in 132 lines of Lean 4 in `ClaimStrip.lean` (building on `HalfPlane.lean` and Mathlib's `DirichletContinuation` and `Nonvanishing`). The exact correspondence is:
    - `Claim.factor_ne_zero` (`HalfPlane.lean`) $arrow.l.r$ Lemma 2.9;
    - `Claim.prim_zero` (`ClaimStrip.lean`, lines 53–63) $arrow.l.r$ Lemma 2.30;
    - `Claim.gamma_ne_zero` (`ClaimStrip.lean`, lines 65–70) $arrow.l.r$ Lemma 2.31;
    - `Claim.prim_reflect` (`ClaimStrip.lean`, lines 72–87) $arrow.l.r$ Lemma 2.32;
    - `Claim.strip : HalfPlane → Strip` (`ClaimStrip.lean`, lines 89–103) $arrow.l.r$ Theorem 2.33;
    - `Claim.zeta : HalfPlane → Zeta` (`ClaimStrip.lean`, lines 105–130) $arrow.l.r$ Theorem 2.34.

    Notice one subtle formal detail in `Claim.zeta` (line 115): in Mathlib, `Gammaℝ s` is defined as `π ^ (-s / 2) * Gamma (s / 2)`, and at poles of `Gamma (s / 2)` (i.e., $s = -2n$), Lean's `Complex.Gamma` returns `0` by junk-value convention, so `Complex.Gammaℝ_eq_zero_iff` characterizes the poles as the points where `Gammaℝ s = 0`—which makes `riemannZeta_def_of_ne_zero : riemannZeta s = completedRiemannZeta s / Gammaℝ s` hold cleanly via Lean's `x / 0 = 0` convention! Thus `hG : Gammaℝ s ≠ 0` simultaneously excludes $s = 0$ and the trivial zeros $s = -2(n+1)$.
  ]

  == Why Alpöge and Claude Proved GRH Alongside RH

  A reader encountering the Alpöge–Claude theorem for the first time might naturally ask: *Why does a proof of the Riemann Hypothesis prove the Generalized Riemann Hypothesis for all Dirichlet $L$-functions at the same time?* Historically, many partial results toward RH—such as zero-density estimates, Hardy's theorem on infinitely many critical-line zeros, or Selberg's positive-proportion theorem—were first proved for $zeta(s)$ and only later extended to $L(s, chi)$ with extra work. Why does the Alpöge–Claude method deliver `DirichletLNonvanishingRightOfHalf` uniformly for *every* modulus $N$ and *every* Dirichlet character $chi$?

  The answer lies in four structural features of the proof, which we preview here and develop in full in Parts II and III:

  1. *The analytic trigger is character-agnostic.* The proof begins by assuming, for contradiction, that $L(s, chi)$ has a zero $rho = beta + i gamma$ with $beta > 1\/2$ (for some fixed modulus $N$ and character $chi$, with $chi != 1$ or $rho != 1$). As we will see in Chapter 5, Landau's nonnegativity theorem and Mellin inversion convert this off-line zero into a lower bound on a smoothed arithmetic sum $S_a (x)$ at large scales $x -> oo$. In this analytic front-end, the character $chi$ enters solely as a bounded completely multiplicative twist ($|chi(n)| <= 1$) of the Dirichlet coefficients. Replacing $1$ by $chi$ does not alter the analytic mechanism; it merely replaces the pole-and-zero configuration of $zeta(s)$ with that of $L(s, chi)$ (or a Hermitian-positive combination built from $L(s, chi)$ and $L(s, overline(chi))$).

  2. *Level $N$ is invisible at asymptotic scale $X -> oo$.* In the automorphic heart of the proof (Part III), one constructs a chain of $m approx sqrt(X)$ theta lifts across totally definite unitary groups $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ over a CM field $K \/ K_0$, synthesizing "automorphic multiplicity" analogous to Stepanov's high-order vanishing polynomial over $bb(F)_q$. Twisting by a fixed Dirichlet character $chi$ of conductor $f_chi | N$ corresponds automorphically to twisting by a finite-order Hecke character of $bb(A)_K^times \/ K^times$ ramified only at primes dividing $N$. This enlarges the finite set $S$ of bad places and refines the compact open level subgroup at $v | N$, which multiplies volumes, conductors, and local heights by constants depending on $N$. Because the contradiction is taken in the asymptotic limit $X -> oo$ (with $m approx sqrt(X)$ growing arbitrarily large while $N$ and $rho$ remain *fixed*), every fixed-$N$ constant is completely swamped by the exponential growth in $X$ and $m$!

  3. *Cyclotomic Iwasawa towers already live in the world of Dirichlet characters.* To control the arithmetic complexity (Arakelov heights and Harder–Narasimhan slopes) of the automorphic forms produced by the theta-lift chain, the proof invokes Galois cohomology and Poitou–Tate duality along a cyclotomic $bb(Z)_ell$-extension, constructing a "weakened Vandiver window" (`VWin`) in which the relevant Selmer/Tate–Shafarevich kernels vanish. Because the Galois group $op("Gal")(bb(Q)(mu_(ell^oo)) \/ bb(Q)) tilde.eq bb(Z)_ell^times$ acts on these cohomology groups by decomposing them into character eigenspaces, incorporating a fixed Dirichlet character $chi$ into the base CM field or twist is completely native to the Iwasawa-theoretic machinery.

  4. *The functional-equation reflection is uniform in $(N, chi)$.* Finally, as Section 2.4 just demonstrated, once the automorphic engine establishes `DirichletLNonvanishingRightOfHalf` for all $(N, chi)$, the passage from the right half-plane $op("Re")(s) > 1\/2$ to the full critical strip $0 < op("Re")(s) < 1$ requires only primitivization (`prim_zero`) and the functional equation (`prim_reflect`). Both are completely uniform in $(N, chi)$, and specializing to $N = 1$, $chi = 1$ yields the classical Riemann Hypothesis as an immediate corollary.

  #insight-box(title: "Why Proving More Is Sometimes Easier")[
    It is a recurring phenomenon in number theory—seen in Artin's conjecture for function fields, Weil's proof of RH for curves (which required all abelian varieties and correspondences), and Deligne's proof of the Weil conjectures (which required all smooth $ell$-adic sheaves, not just constant sheaves)—that a statement about a single $L$-function becomes *easier* to prove once embedded in its natural functorial family. Here, embedding $zeta(s)$ into the family of all Dirichlet $L$-functions $L(s, chi)$—and indeed into automorphic representations on unitary groups of arbitrarily high rank—exposes the rigid arithmetic geometry (CM periods, Arakelov slopes, and Iwasawa towers) that $zeta(s)$ alone hides.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Top-Level Statements",
    module: "src/Statements.lean & src/Main.lean",
  )[
    The public interface of `leanprover-community/riemann-hypothesis` is defined in `src/Statements.lean` (20 lines, importing only Mathlib's `DirichletContinuation`):
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

    def PrimitiveDirichletLZerosOnLine : Prop :=
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        ∀ s : ℂ, 0 < s.re → s.re < 1 →
          DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
    ```
    In `src/Main.lean`, the entire 17-million-line automorphic engine culminates in a single theorem:
    ```lean
    theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
      UpperTheory.FinalTheorems.everyCharacter
    ```
    From this one theorem, `Main.lean` deduces Mathlib's `RiemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive` in ten lines by invoking `Claim.zeta` and `Claim.strip` from `ClaimStrip.lean`!
  ]

  #exercises((
    [
      Let $N = product_(i=1)^r p_i^(e_i)$ be the prime factorization of $N >= 1$. Prove that every Dirichlet character $chi$ modulo $N$ factors uniquely as $chi = product_(i=1)^r chi_i$, where $chi_i$ is a Dirichlet character modulo $p_i^(e_i)$, and show that the conductor satisfies $f_chi = product_(i=1)^r f_(chi_i)$. Deduce that the number of primitive Dirichlet characters modulo $N$ is given by the multiplicative function
      $ phi^*(N) = sum_(d | N) mu(N / d) phi(d), $
      and verify that $phi^*(N) = 0$ if and only if $N equiv 2 (op("mod") 4)$.
    ],
    [
      Let $chi$ be a Dirichlet character modulo $N$ induced by the primitive character $chi^*$ modulo $f = f_chi$.
      (a) Compute the Gauss sum $tau(chi)$ in terms of $tau(chi^*)$: prove that
      $ tau(chi) = mu(N / f) chi^*(N / f) tau(chi^*). $
      (b) Deduce that $|tau(chi)| = sqrt(N)$ if and only if $chi$ is primitive modulo $N$.
      (c) Show by explicit example (e.g., $N = 8$, $chi$ induced by $chi_4$) that Lemma 2.12 ($tau(n, chi) = overline(chi)(n) tau(chi)$ for all $n in bb(Z)$) fails for imprimitive characters.
    ],
    [
      Let $chi$ be a primitive Dirichlet character modulo $q > 1$. Prove the *Pólya–Vinogradov inequality*: for all integers $M$ and $H >= 1$,
      $ abs(sum_(n = M + 1)^(M + H) chi(n)) <= sqrt(q) log q $
      (or with an explicit constant $C sqrt(q) log q$). *Hint*: Expand $chi(n) = (1 \/ tau(overline(chi))) sum_(a = 1)^(q - 1) overline(chi)(a) e(a n \/ q)$ using Lemma 2.12, sum the geometric series in $n$, and bound $|1 - e(a \/ q)|^(-1)$ in terms of $norm(a \/ q)$.
    ],
    [
      Let $chi$ be an odd primitive Dirichlet character modulo $q > 1$. Using the Hurwitz zeta function $zeta(s, alpha) = sum_(n=0)^oo (n + alpha)^(-s)$ (and the fact that $zeta(0, alpha) = 1\/2 - alpha$), prove that
      $ L(0, chi) = - 1 / q sum_(a = 1)^(q - 1) a chi(a). $
      Combine this with the functional equation (Theorem 2.18) to express $L(1, overline(chi))$ as a finite trigonometric sum, and verify Dirichlet's class number formula for $d = -3$ and $d = -4$ directly (obtaining $h(-3) = h(-4) = 1$).
    ],
    [
      Let $chi$ be a real primitive character modulo $q > 1$, and let $F(s) = zeta(s) L(s, chi) = sum_(n=1)^oo a_n n^(-s)$. Using the lower bound $a_(m^2) >= 1$ and the partial-summation estimate $sum_(n <= x) a_n >= floor(sqrt(x))$, give a direct *elementary* proof (without invoking Landau's theorem) that $L(1, chi) != 0$ by showing that if $L(1, chi) = 0$ then $F(s)$ would be bounded as $s -> (1\/2)^+$, or by analyzing $sum_(n <= x) a_n n^(-1\/2)$ via the hyperbola method.
    ],
    [
      Prove the classical nonvanishing of $L(1 + i t, chi)$ for all $t in bb(R)$ and all Dirichlet characters $chi$ modulo $N$ (with $t != 0$ if $chi = chi_0$) using the Mertens–de la Vallée Poussin inequality
      $ & op("Re")(3 log L(sigma, chi_0) + 4 log L(sigma + i t, chi) + log L(sigma + 2 i t, chi^2)) \ & quad >= 0 quad (sigma > 1). $
      Explain carefully why this argument succeeds when $t != 0$ even if $chi$ is a real quadratic character, and pinpoint the exact step where it breaks down at $t = 0$ for real $chi$.
    ],
    [
      Let $chi$ be a primitive Dirichlet character modulo $q > 1$ with parity $a in {0, 1}$. Prove that the completed $L$-function $Lambda(s, chi)$ admits a Hadamard product factorization
      $ Lambda(s, chi) = e^(A(chi) + B(chi) s) product_rho (1 - s / rho) e^(s / rho), $
      where $rho$ runs over all nontrivial zeros of $L(s, chi)$ in $0 < op("Re")(rho) < 1$ counted with multiplicity. Show that
      $ op("Re")(B(chi)) = - sum_rho op("Re")(1 / rho) = - sum_rho (op("Re")(rho)) / |rho|^2. $
    ],
    [
      Using the imprimitive factorization (Proposition 2.8) and the proof of Lemma 2.9 (`Claim.factor_ne_zero`), determine the *exact* set of zeros of $L(s, chi_0)$ in $bb(C)$ for the principal character $chi_0$ modulo $N = 6$, together with their multiplicities. Which zeros lie on the line $op("Re")(s) = 0$, which lie in $op("Re")(s) < 0$, and which lie in $0 < op("Re")(s) < 1$?
    ],
    [
      *(Critical-line symmetry without GRH.)* Let $chi$ be a primitive Dirichlet character modulo $q >= 1$. Prove that if $rho$ is a nontrivial zero of $L(s, chi)$ in $0 < op("Re")(s) < 1$, then $1 - overline(rho)$ is *also* a nontrivial zero of $L(s, chi)$ of the same multiplicity, while $overline(rho)$ and $1 - rho$ are nontrivial zeros of $L(s, overline(chi))$. In particular, deduce that for a *complex* character $chi$, the nontrivial zeros of $L(s, chi)$ are symmetric about the vertical line $op("Re")(s) = 1\/2$, though not necessarily about the real axis $op("Im")(s) = 0$.
    ],
  ))
]
