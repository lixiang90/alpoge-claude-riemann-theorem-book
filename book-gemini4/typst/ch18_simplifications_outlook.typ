// ============================================================================
// Chapter 18: Prospects for Simplification, the Extended Riemann Hypothesis,
//             and Open Horizons
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch18() = [
  #chapter(
    "Simplifications, the Extended Riemann Hypothesis, and Open Horizons",
    short-title: "Simplifications and Open Horizons",
    epigraph: "An astounding amount of mathematics is present in the argument, far more than I had imagined would be necessary as a student. My intuition insists it will be massively simplified, likely immediately. ... In a time of revolution in mathematics I hope the argument provides a glimpse towards the miracles that lie ahead, and shows us the joy and wonder we are about to find in the simplest things.",
    epigraph-source: "Levent Alpöge, Remark on the Formalized Proof of the Riemann Hypothesis (2026)",
    overview: [
      The resolution of the Riemann Hypothesis and the Generalized Riemann Hypothesis for Dirichlet $L$-functions marks not an endpoint, but the opening of a vast new mathematical landscape. This concluding chapter surveys the immediate aftermath and the horizons ahead. In Section 18.1, we harvest the avalanche of classical conditional theorems—from optimal prime counting and short-interval prime distribution to Ankeny's quadratic nonresidue bound, Miller's deterministic primality test, and effective class number bounds—while carefully delineating the boundary between corollaries of Dirichlet GRH and those awaiting the Extended Riemann Hypothesis (ERH). Section 18.2 examines the remarkable collateral arithmetic discoveries already embedded inside the proof, notably the weakened Vandiver bound and its consequences for étale cohomology and algebraic $K$-groups of $bb(Z)$ via Quillen–Lichtenbaum. Section 18.3 maps out a concrete four-part program for massively simplifying the argument, from eliminating Behrend's sphere trick to compressing twenty million lines of Lean 4 into a human-length monograph. Section 18.4 analyzes the path toward ERH for Dedekind zeta functions and the qualitatively deeper obstacles confronting Grand RH for automorphic and Hasse–Weil $L$-functions. Finally, Section 18.5 reflects on the unity of number theory, the emergence of formal proof assistants as a medium of publication, and the great unsolved problems that continue to beckon.
    ],
    label-name: "ch-simplifications-outlook",
  )

  == Immediate Consequences of RH and GRH

  For more than a century after Riemann's 1859 memoir, analytic number theory grew in two parallel universes. In the unconditional universe, mathematicians forged extraordinary workarounds—zero-free regions, zero-density estimates, large sieves, and dispersion methods—to approximate what the Riemann Hypothesis predicted. In the conditional universe, hundreds of theorems in number theory, algebra, and theoretical computer science were proved "assuming RH" or "assuming GRH," waiting like sealed letters for the day the hypothesis would become a theorem.

  With the Alpöge–Claude–Riemann Theorem established and machine-verified without assumptions (Chapters 1–17), every theorem whose proof depends solely on the nonvanishing of $zeta(s)$ and Dirichlet $L$-functions $L(s, chi)$ in the half-plane $op("Re")(s) > 1/2$ becomes an unconditional theorem of mathematics. Before cataloging this avalanche of corollaries, however, a precision of terminology is essential. In the literature, the acronym "GRH" is sometimes used loosely to mean the Riemann Hypothesis for Dirichlet $L$-functions and at other times to mean the Riemann Hypothesis for Dedekind zeta functions $zeta_K (s)$ of arbitrary number fields (which we call the *Extended Riemann Hypothesis*, ERH). The Lean 4 formalization of November 2026 proves RH (`riemannHypothesis`) and GRH for all Dirichlet $L$-functions (`LFunction_eq_zero_re`). Consequently:
  - Every corollary of RH and Dirichlet GRH—including all theorems depending on Dedekind zeta functions of *abelian* number fields, by Kronecker–Weber—is now unconditionally proved.
  - Theorems requiring non-abelian Dedekind zeta functions (such as Hooley's proof of Artin's primitive root conjecture and the full non-abelian Lagarias–Odlyzko Chebotarev theorem) stand at the threshold of Section 18.4, awaiting the extension of the method to ERH.

  We now survey the principal unconditional corollaries of RH and Dirichlet GRH.

  === Optimal Prime Counting and the Lindelöf Hypothesis

  The most immediate consequence of the Riemann Hypothesis is the sharp error term in the Prime Number Theorem, first deduced conditionally by Helge von Koch in 1901 and refined into explicit numerical inequalities by Lowell Schoenfeld in 1976.

  #corollary(title: "Optimal Prime Counting; von Koch 1901, Schoenfeld 1976")[
    As $x -> oo$, the Chebyshev function $psi(x) = sum_(n <= x) Lambda(n)$ and the prime-counting function $pi(x) = sum_(p <= x) 1$ satisfy
    $ psi(x) = x + O(sqrt(x) (log x)^2), quad pi(x) = op("li")(x) + O(sqrt(x) log x), $
    where $op("li")(x) = integral_2^x (dif t) / (log t)$. Explicitly, for all real $x >= 2657$,
    $ |pi(x) - op("li")(x)| < 1 / (8 pi) sqrt(x) log x, $
    and for all $x >= 73.2$, $|psi(x) - x| < 1 / (8 pi) sqrt(x) (log x)^2$.
  ]

  #proof[
    By the truncated explicit formula (Chapter 1), for $x >= 2$ and $2 <= T <= x$,
    $ psi(x) = x - sum_(|gamma| <= T) x^rho / rho + O((x (log x)^2) / T + log x). $
    Since every nontrivial zero $rho = 1/2 + i gamma$ satisfies $op("Re")(rho) = 1/2$, we have $|x^rho| = sqrt(x)$ uniformly in $rho$. Using the Riemann–von Mangoldt zero-counting formula $N(T) = (T / (2 pi)) log(T / (2 pi e)) + O(log T)$, partial summation yields
    $ sum_(|gamma| <= T) 1 / |rho| <= sum_(|gamma| <= T) 1 / |gamma| << (log T)^2. $
    Choosing $T = sqrt(x)$ balances the two error terms and gives $psi(x) = x + O(sqrt(x) (log x)^2)$. Passing from $psi(x)$ to $theta(x) = sum_(p <= x) log p$ introduces only $psi(x) - theta(x) = O(sqrt(x))$, and partial summation from $theta(x)$ to $pi(x)$ yields
    $ pi(x) - op("li")(x) = (theta(x) - x) / (log x) + integral_2^x (theta(t) - t) / (t (log t)^2) dif t + O(1) = O(sqrt(x) log x), $
    since the factor $1 / log x$ removes one power of $log x$ from the $O(sqrt(x) (log x)^2)$ error. Schoenfeld's explicit constant $1 / (8 pi)$ follows by inserting explicit zero-counting bounds into the smoothed explicit formula.
  ]

  In the opposite direction, Littlewood proved in 1914 that $psi(x) - x = Omega_(plus.minus)(sqrt(x) log log log x)$, so the exponent $1/2$ in Corollary 18.1 is strictly best possible.

  Closely allied to prime counting is the growth of $zeta(s)$ and $L(s, chi)$ on vertical lines. By a classical theorem of Littlewood (1924), RH implies the *Lindelöf Hypothesis*—and indeed a logarithmic refinement far stronger than $O_epsilon ((|t|+2)^epsilon)$.

  #corollary(title: "Lindelöf Hypothesis and Vertical Bounds; Littlewood 1924")[
    For every real $t$ with $|t| >= 2$ and every primitive Dirichlet character $chi$ of modulus $q >= 1$,
    $ |L(1/2 + i t, chi)| << exp(C (log(q |t|)) / (log log(q |t|))) $
    for an absolute constant $C > 0$. In particular, for every $epsilon > 0$,
    $ zeta(1/2 + i t) <<_epsilon (|t| + 2)^epsilon, quad L(1/2 + i t, chi) <<_epsilon (q (|t| + 2))^epsilon. $
    Moreover, on the edge of the critical strip $op("Re")(s) = 1$,
    $ (1 + o(1)) (pi^2) / (12 e^gamma log log(q |t|)) &<= |L(1 + i t, chi)| \
      &<= (1 + o(1)) 2 e^gamma log log(q |t|) $
    as $q (|t| + 2) -> oo$.
  ]

  === Primes in Short Intervals and Prime Gaps

  Unconditionally, Baker, Harman, and Pintz (2001) proved that the interval $[x, x + x^(0.525)]$ contains a prime for all sufficiently large $x$. Corollary 18.1 immediately drops the exponent below $1/2$ to $x^(1/2) log x$, and Cramér's spectral argument refines the constant and mean-square statistics.

  #corollary(title: "Primes in Short Intervals and Prime Gaps; Cramér 1920, Selberg 1943")[
    Let $p_1 < p_2 < dots.c$ denote the sequence of prime numbers.
    + There exists an effective absolute constant $C > 0$ such that for all $x >= 2$, the interval $[x, x + C sqrt(x) log x]$ contains a prime; equivalently,
      $ p_(n+1) - p_n = O(sqrt(p_n) log p_n). $
    + In mean square, the prime gaps satisfy Cramér's bound
      $ sum_(p_n <= x) (p_(n+1) - p_n)^2 << x (log x)^3. $
    + For any function $phi(x) -> oo$ as $x -> oo$, almost all intervals $[x, x + phi(x) (log x)^2]$ (meaning all $x in [X, 2 X]$ outside a subset of Lebesgue measure $o(X)$) contain $(1 + o(1)) phi(x) log x$ primes.
  ]

  Notice the striking contrast between the pointwise bound (1) and the almost-all bound (3). Even with RH proved, Cramér's probabilistic conjecture $p_(n+1) - p_n = O((log p_n)^2)$ remains out of reach: bridging the gap from $sqrt(x) log x$ to $(log x)^2$ requires cancellation among the oscillatory terms $x^(i gamma) / (1/2 + i gamma)$ across zeros of $zeta(s)$, a problem belonging to the fine vertical statistics of zeros (Section 18.5).

  === Primes in Arithmetic Progressions and Linnik's Constant

  For primes in arithmetic progressions $p equiv a mod q$ with $(a, q) = 1$, the unconditional workhorse of analytic number theory has long been the Bombieri–Vinogradov theorem (1965), which gives square-root-quality equidistribution *on average* over moduli $q <= x^(1/2) (log x)^(-B)$. With GRH for Dirichlet $L$-functions proved, this average statement upgrades to a *pointwise* theorem for every individual modulus $q$.

  #corollary(title: "Pointwise Equidistribution in Arithmetic Progressions")[
    Uniformly for all integers $q >= 1$, all $a$ coprime to $q$, and all $x >= 2$,
    $ psi(x \; q, a) = sum_(n <= x \ n equiv a mod q) Lambda(n) = x / (phi(q)) + O(sqrt(x) (log(q x))^2), $
    $ pi(x \; q, a) = (op("li")(x)) / (phi(q)) + O(sqrt(x) log(q x)). $
    Consequently, the least prime $p(a, q)$ congruent to $a mod q$ satisfies
    $ p(a, q) << phi(q)^2 (log q)^2. $
  ]

  This dramatically sharpens Linnik's theorem ($p(a, q) << q^L$, with the best unconditional exponent $L = 5$ due to Xylouris), bringing the exponent of $q$ all the way down to $2 + o(1)$. Yet, just as for prime gaps, the conjectured true size $p(a, q) << phi(q) (log q)^2$ (Heath-Brown's conjecture) lies one factor of $phi(q)$ beyond what GRH alone supplies without horizontal correlation across characters.

  === Ternary and Binary Additive Problems

  In 1923, Hardy and Littlewood introduced the circle method and proved, conditional on GRH, that every sufficiently large odd integer $n$ can be written as a sum of three primes $n = p_1 + p_2 + p_3$. Vinogradov (1937) famously removed the dependence on GRH asymptotically using bilinear exponential-sum estimates, and Helfgott (2013) completed the unconditional proof for all odd $n >= 7$. Even so, GRH transforms the quantitative landscape of additive prime problems:
  - In ternary Goldbach and general Waring–Goldbach problems, GRH yields power-saving error terms on major arcs of much wider range, enabling asymptotic formulas for $n = p_1 + p_2 + p_3$ with primes restricted to short intervals $[n/3 - H, n/3 + H]$ of length $H = n^(1/2 + epsilon)$ or to arithmetic progressions of large modulus $q <= n^(1/4 - epsilon)$.
  - For the binary Goldbach conjecture ($2 n = p_1 + p_2$), while RH and GRH do not yet eliminate all possible exceptions, they slash the exceptional set $E(X) = \# {2 n <= X : 2 n != p_1 + p_2}$ from the unconditional Montgomery–Vaughan bound $E(X) << X^(1 - delta)$ down to
    $ E(X) << X^(1/2) (log X)^3 $
    (Hardy–Littlewood 1924; Goldston 1992; Languasco–Perelli–Zaccagnini).

  === Smallest Quadratic Nonresidue and Deterministic Primality Testing

  One of the most celebrated applications of GRH lies at the crossroads of analytic number theory and computational complexity. For an odd prime $p$, let $n_p$ denote the smallest positive integer that is not a quadratic residue modulo $p$ (so the Legendre symbol satisfies $(n_p / p) = -1$). Unconditionally, Burgess's character-sum bound gives only $n_p <<_epsilon p^(1 / (4 sqrt(e)) + epsilon)$. Under GRH, Ankeny (1952) proved a logarithmic-squared bound, which Eric Bach (1990) made completely explicit.

  #corollary(title: "Least Quadratic Nonresidue; Ankeny 1952, Bach 1990")[
    For every odd prime $p$, the smallest quadratic nonresidue $n_p$ modulo $p$ satisfies
    $ n_p = O((log p)^2). $
    More explicitly, for every nonprincipal Dirichlet character $chi$ modulo $q >= 3$, the least positive integer $n$ with $chi(n) != 1$ and $(n, q) = 1$ satisfies
    $ n < 2 (log q)^2. $
  ]

  #proof[
    We sketch Ankeny's analytic mechanism to display how GRH enters directly. Let $chi(n) = (n / p)$ be the Legendre symbol modulo $p$, and consider for a parameter $Y >= 2$ the smoothly weighted sum
    $ S(Y) = sum_(n=1)^oo Lambda(n) chi(n) e^(-n / Y). $
    If $n_p > Y$, then $chi(q) = 1$ for every prime $q <= Y$, so $chi(n) = 1$ for all prime powers $n <= Y$. Comparing $S(Y)$ with the unsigned sum $sum_(n=1)^oo Lambda(n) e^(-n / Y) = Y + O(sqrt(Y) (log Y)^2)$ (by RH for $zeta(s)$) shows that if $n_p > Y$, then
    $ S(Y) &= sum_(n <= Y) Lambda(n) e^(-n / Y) + O(sum_(n > Y) Lambda(n) e^(-n / Y)) \
      &= (1 - 2 / e) Y + O(sqrt(Y) (log Y)^2) >> Y. $
    On the other hand, expressing $e^(-n / Y)$ as a Mellin transform $e^(-u) = (2 pi i)^(-1) integral_(2 - i oo)^(2 + i oo) Gamma(s) u^(-s) dif s$ gives
    $ S(Y) = 1 / (2 pi i) integral_(2 - i oo)^(2 + i oo) (- (L'(s, chi)) / L(s, chi)) Y^s Gamma(s) dif s. $
    Shifting the contour to $op("Re")(s) = -1/2$ picks up poles only at the nontrivial zeros $rho = 1/2 + i gamma$ of $L(s, chi)$ (and at $s = 0$), yielding
    $ S(Y) = - sum_rho Y^rho Gamma(rho) + O(log p). $
    Because GRH places every zero on $op("Re")(rho) = 1/2$, Stirling's formula $|Gamma(1/2 + i gamma)| << e^(-pi |gamma| / 2)$ together with the zero-density bound $N(T + 1, chi) - N(T, chi) << log(p (|T| + 2))$ gives
    $ |S(Y)| << sqrt(Y) sum_rho e^(-pi |gamma| / 2) + log p << sqrt(Y) log p. $
    Comparing the lower bound $S(Y) >> Y$ with the upper bound $|S(Y)| << sqrt(Y) log p$ yields $Y << (log p)^2$, a contradiction as soon as $Y = C (log p)^2$ for a sufficiently large constant $C$. Bach's explicit bound $n < 2 (log q)^2$ is obtained by replacing $e^(-n / Y)$ with an optimal compactly supported kernel.
  ]

  In 1976, Gary Miller observed that Ankeny's bound immediately turns the probabilistic Rabin–Miller primality test into a *deterministic polynomial-time algorithm*.

  #corollary(title: "Miller's Deterministic Primality Test; Miller 1976, Bach 1990")[
    An odd integer $n > 2$ (write $n - 1 = 2^s d$ with $d$ odd) is prime if and only if for every integer $a$ with $2 <= a < min(n, 2 (log n)^2)$, either $a^d equiv 1 mod n$ or $a^(2^r d) equiv -1 mod n$ for some $0 <= r < s$. Consequently, primality of $n$ can be decided deterministically in $tilde(O)((log n)^4)$ bit operations.
  ]

  While Agrawal, Kayal, and Saxena (AKS, 2002) famously proved unconditionally that `PRIMES` lies in `P` in time $tilde(O)((log n)^6)$, Miller's test is now unconditionally *both* asymptotically faster and vastly simpler to implement—the exact algorithm already used in practice, finally equipped with an unconditional proof of correctness.

  === Elimination of Siegel Zeros and Effective Class Number Bounds

  Perhaps the most dramatic relief for classical algebraic number theory is the permanent exorcism of *Landau–Siegel zeros*—hypothetical real zeros $beta < 1$ of quadratic Dirichlet $L$-functions $L(s, chi_D)$ lying abnormally close to $s = 1$. Because GRH places all nontrivial zeros on $op("Re")(s) = 1/2$, no real zero can exist in the interval $(1/2, 1)$.

  #corollary(title: "Effective Class Number Bounds for Imaginary Quadratic Fields")[
    Let $-D < 0$ be a fundamental discriminant, $chi_(-D) (n) = (-D / n)$ the associated primitive quadratic character, and $h(-D)$ the class number of $bb(Q)(sqrt(-D))$. Then as $D -> oo$,
    $ (1 + o(1)) (pi^2) / (12 e^gamma log log D) <= L(1, chi_(-D)) <= (1 + o(1)) 2 e^gamma log log D. $
    In particular, by Dirichlet's class number formula $h(-D) = (w_D sqrt(D)) / (2 pi) L(1, chi_(-D))$ (where $w_D = 2$ for $D > 4$), there is an *effective* absolute constant $c > 0$ such that
    $ h(-D) >= c sqrt(D) / (log log D) quad (D >= 15). $
  ]

  Compare this with the pre-2026 state of the art: Siegel's 1935 theorem gave $h(-D) >>_epsilon D^(1/2 - epsilon)$ with a notoriously *ineffective* constant, while the celebrated Goldfeld–Gross–Zagier theorem (1976–1986) gave an effective lower bound of only $h(-D) >>_epsilon (log D)^(1 - epsilon)$. Corollary 18.7 simultaneously achieves the sharp Littlewood order $sqrt(D) / log log D$ and full effectivity—solving Gauss's class number problem for every fixed $h >= 1$ with an explicit search bound of size $D << h^2 (log log(h + 3))^2$.

  === Effective Chebotarev Density and Artin's Primitive Root Conjecture

  Two of the crown jewels of conditional number theory sit precisely on the boundary between Dirichlet GRH and the Extended Riemann Hypothesis (ERH):
  + *The Effective Chebotarev Density Theorem (Lagarias–Odlyzko 1977).* Let $L / K$ be a finite Galois extension of number fields with Galois group $G = op("Gal")(L / K)$, degree $n_L = [L : bb(Q)]$, and discriminant $d_L$. For a conjugacy class $C subset.eq G$, let $pi_C (x, L / K)$ count unramified prime ideals $frak(p)$ of $K$ with $N(frak(p)) <= x$ and $op("Frob")_frak(p) in C$. Under ERH for the Dedekind zeta function $zeta_L (s)$,
    $ pi_C (x, L / K) = (|C|) / (|G|) op("li")(x) + O((|C|) / (|G|) sqrt(x) (log |d_L| + n_L log x)), $
    and the least prime ideal with Frobenius in $C$ satisfies $N(frak(p)) << (log |d_L|)^2$.
  + *Artin's Primitive Root Conjecture (Hooley 1967).* For any integer $a != -1, 0, 1$ that is not a perfect square, let $N_a (x)$ count primes $p <= x$ for which $a$ is a primitive root modulo $p$. Hooley proved that if ERH holds for the Kummer fields $K_k = bb(Q)(zeta_k, a^(1/k))$ for all squarefree $k >= 1$, then
    $ N_a (x) = A(a) op("li")(x) + O((x log log x) / ((log x)^2)), $
    where $A(a) > 0$ is a rational multiple of Artin's constant $A = product_p (1 - (p(p-1))^(-1)) approx 0.3739558$.

  Here the abelian/non-abelian distinction is razor-sharp. Whenever $L / bb(Q)$ is *abelian*, the Kronecker–Weber theorem implies that $L subset.eq bb(Q)(zeta_m)$ for some $m$, and $zeta_L (s)$ factors as a finite product of Dirichlet $L$-functions $L(s, chi)$. Thus *the effective Chebotarev density theorem for all abelian extensions of $bb(Q)$ is already an unconditional corollary of the Alpöge–Claude–Riemann Theorem!* By contrast, for $q >= 3$ prime, the Kummer field $K_q = bb(Q)(zeta_q, a^(1/q))$ has non-abelian Galois group $bb(Z)/q bb(Z) times.r (bb(Z)/q bb(Z))^times$, so $zeta_(K_q) (s)$ contains Artin $L$-functions of dimension $q - 1 >= 2$. Consequently, Hooley's theorem on Artin's primitive root conjecture and the general non-abelian Lagarias–Odlyzko theorem are not yet immediate corollaries of Dirichlet GRH; they stand as the premier prizes awaiting the extension of the proof to ERH in Section 18.4.

  #align(center)[
    #set text(size: 8.1pt)
    #table(
      columns: (1.05fr, 1.35fr, 1.45fr, 0.72fr),
      inset: 4.5pt,
      stroke: 0.4pt + gtm-rule,
      fill: (_, row) => if row == 0 { gtm-tint } else { white },
      [*Problem*], [*Pre-2026 Unconditional*], [*Post-2026 (RH / Dirichlet GRH)*], [*Status*],
      [$|pi(x) - op("li")(x)|$], [$O(x exp(-c (log x)^(3/5) (log log x)^(-1/5)))$], [$< (8 pi)^(-1) sqrt(x) log x$ ($x >= 2657$)], [Unconditional],
      [Prime gaps $p_(n+1) - p_n$], [$O(p_n^(0.525))$ (Baker–Harman–Pintz)], [$O(sqrt(p_n) log p_n)$], [Unconditional],
      [Least prime $p(a, q)$], [$O(q^5)$ (Xylouris)], [$O(phi(q)^2 (log q)^2)$], [Unconditional],
      [Least nonresidue $n_p$], [$O_epsilon (p^(1 / (4 sqrt(e)) + epsilon))$ (Burgess)], [$< 2 (log p)^2$ (Bach)], [Unconditional],
      [Primality test], [$tilde(O)((log n)^6)$ (AKS)], [$tilde(O)((log n)^4)$ (Miller)], [Unconditional],
      [Effective $h(-D)$], [$>>_epsilon (log D)^(1 - epsilon)$ (GGZ)], [$>> sqrt(D) / log log D$], [Unconditional],
      [Chebotarev ($L / bb(Q)$ abelian)], [Ineffective / $O(x exp(-c sqrt(log x)))$], [$O(sqrt(x) (log |d_L| + n_L log x))$], [Unconditional],
      [Artin primitive roots], [All but $<= 2$ primes (Heath-Brown)], [$A(a) op("li")(x) + O(x log log x / (log x)^2)$], [Awaits ERH],
    )
  ]

  == Collateral Arithmetic Discoveries

  Great proofs in number theory rarely solve only the problem on their title page. Just as Wiles's proof of Fermat's Last Theorem established the modularity of semistable elliptic curves and launched the modern Taylor–Wiles patching method, the Alpöge–Claude–Riemann proof generates substantial arithmetic byproducts that live independently of the zeros of $zeta(s)$. The most striking of these—already flagged by Alpöge in footnote 6 of his announcement remark—lies in Iwasawa theory, étale cohomology, and the algebraic $K$-theory of the integers.

  === The Weakened Vandiver Bound (`VWin`)

  Recall from Chapters 15 and 16 how the global integral structure of the iterated theta lifts encounters an arithmetic obstruction. After gluing integral lattices across auxiliary Hecke characters to achieve a "greatest common divisor" averaging effect, certain torsion classes remain in the étale / Galois cohomology group
  $ H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e)) $
  (where $E$ is the auxiliary CM quadratic field, $ell$ is an odd prime, and $e >= 1$ is an integer weight parameter) that cannot be killed by twisting. Controlling these residual classes is closely tied to one of the oldest open conjectures in algebraic number theory: Kummer–Vandiver's conjecture.

  #conjecture(title: "Kummer–Vandiver Conjecture")[
    For every prime $ell$, the prime $ell$ does not divide the class number $h^+_ell = \# op("Cl")(bb(Q)(zeta_ell)^+)$ of the maximal real subfield $bb(Q)(zeta_ell)^+ = bb(Q)(zeta_ell + zeta_ell^(-1))$ of the $ell$-th cyclotomic field.
  ]

  Vandiver's conjecture has been verified numerically for all primes $ell < 1.63 times 10^8$, yet no general proof—nor even a proof that it holds for infinitely many primes—was previously known. In the cohomological reformulation of Kurihara (1992) and Soulé, the failure of Vandiver's conjecture at a prime $ell$ manifests as nontrivial $ell$-torsion in the second étale cohomology groups $H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (e + 1))$ for even integers $e >= 2$ (and in the corresponding minus-eigenspaces of $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ via Poitou–Tate duality).

  To close the Bost slope and divisibility inequality without assuming Vandiver's conjecture, the Alpöge–Claude–Riemann proof establishes an unconditional, quantitative *weakening of Vandiver* (denoted `VWin` in the proof architecture) that bounds the order and exponent of the untwistable classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$—and dually in $H^2_op("et") (cal(O)_E [1/ell], bb(Z)_ell (e + 1))$—using the automorphic congruences and Eisenstein-ideal machinery developed for the theta-lift chain.

  === From Étale Cohomology to Algebraic $K$-Groups $K_n (bb(Z))$

  The arithmetic significance of `VWin` is magnified enormously by the *Quillen–Lichtenbaum conjecture*, now a celebrated theorem following Voevodsky's proof of the Bloch–Kato conjecture and Rost's norm-variety work (together with the étale descent and regulator machinery of Dwyer–Friedlander, Levine, and Weibel).

  #theorem(title: "Quillen–Lichtenbaum Isomorphism for Z; Voevodsky–Rost")[
    For every odd prime $ell$ and every integer $e >= 1$, the étale Chern character maps induce canonical isomorphisms
    $ K_(2 e) (bb(Z)) times.o bb(Z)_ell tilde.equiv H^2_op("et") (op("Spec") bb(Z)[1/ell], bb(Z)_ell (e + 1)), $
    $ K_(2 e + 1) (bb(Z)) times.o bb(Z)_ell tilde.equiv H^1_op("et") (op("Spec") bb(Z)[1/ell], bb(Z)_ell (e + 1)). $
    In particular, the odd-primary torsion of the even $K$-groups $K_(2 e) (bb(Z))$ is completely governed by the finite abelian groups $H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (e + 1))$.
  ]

  Recall Borel's computation of the ranks of $K_n (bb(Z))$: for $n >= 2$, $K_n (bb(Z))$ is a finitely generated abelian group of rank $1$ if $n equiv 1 mod 4$, and finite otherwise. By the Soulé–Kurihara correspondence, for $e = 2 k$ even:
  - The group $K_(4 k) (bb(Z))$ is finite, and its $ell$-primary part $K_(4 k) (bb(Z))[ell^oo] tilde.equiv H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (2 k + 1))$ is governed by the $(1 - 2 k)$-th eigenspace of the $ell$-class group of $bb(Q)(zeta_ell)^+$.
  - For $e = 2 k - 1$ odd, the order of $K_(4 k - 2) (bb(Z))$ is controlled (up to powers of $2$) by the numerator of the Bernoulli number $B_(2 k) / (2 k)$ (equivalently, the special value $zeta(1 - 2 k)$), via the Lichtenbaum–Mazur–Wiles main conjecture of Iwasawa theory.
  - Vanishing of $K_(4 k) (bb(Z))$ for all $k >= 1$ is intimately linked to Vandiver's conjecture; even proving the *vanishing* or *cyclicity* of specific $K_(4 k) (bb(Z))$ for small or moderate $k$ had long been a stubborn open problem.

  Because the proof of GRH needed to bound the untwistable classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ unconditionally, Poitou–Tate duality translates `VWin` directly into upper bounds on $\# H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (e + 1))$ and hence on the odd-primary parts of $K_(2 e) (bb(Z))$. As Alpöge remarked candidly in footnote 6 of his announcement:

  #insight-box(title: "Alpöge's Remark on Vandiver and K-Groups of Z (Footnote 6)")[
    *"This is still pretty strong!! I believe vanishing of a number of $K$-groups of $bb(Z)$ follows, and cyclicity up to 100ish maybe? I had Lichtenbaum, so I knew we would have a lot of slack in fighting these $K$'s."*

    What makes this byproduct so remarkable is that the analytic positivity engine of GRH—specifically, the Bost slope and divisibility constraints on iterated unitary theta lifts—is strong enough to force nontrivial structural constraints on the algebraic $K$-theory of $bb(Z)$ without ever assuming Vandiver's conjecture. Extracting the sharpest possible bounds on $K_(4 k) (bb(Z))$ and $H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (e + 1))$ from the `VWin` module is already an active, standalone research problem in algebraic $K$-theory.
  ]

  #lean-note(title: "Collateral Arithmetic Theorems in the Formalization", module: "Development/AutomorphicArithmetic & AbelianVarietyTheory")[
    Unlike informal arguments where intermediate lemmas are often tailored narrowly to the final contradiction, a formal Lean 4 development must state every intermediate theorem with clean hypotheses and explicit dependencies. The weakened Vandiver bound `VWin`—controlling the cohomology classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$—is already isolated as a self-contained theorem in the dependency graph. Connecting its Lean statement directly to Mathlib's developing étale cohomology and algebraic $K$-theory libraries will yield machine-checked theorems on $K_n (bb(Z))$ as immediate corollaries.
  ]

  === Three Further Collateral Gems

  Beyond `VWin` and $K_n (bb(Z))$, three other ingredients forged during the proof merit independent development:
  + *Inert-prime divisibility on CM curves.* For an elliptic curve with complex multiplication by $cal(O)_K$ and a prime $p$ inert in $K$, the invariant derivation $D$ satisfies $D^p equiv 0 mod p$, and the normalized derivatives $(D^a dot.c theta(0)) / Omega^a$ are divisible by $p^(a/p + a/p^3 + dots.c - O(log a))$ (Chapter 7). This sharp $p$-adic congruence provides a new arithmetic bridge between CM periods and supersingular differentials.
  + *The sign-only "path quadric" proof of Weil–Deligne.* In the function-field toy setting that catalyzed the entire proof, Alpöge discovered a strikingly elementary proof of the Weil–Deligne Riemann Hypothesis over finite fields via the identity $q N = M^k + R$ applied to the path quadric $x_1 x_2 + x_2 x_3 + dots.c + x_(k-1) x_k$, where Bertini's theorem gives a definite sign on the left-hand side opposite to the zero-mode $M^k$, and $k$-fold iterated Parseval bounds $|R|$ at square-root quality without invoking Deligne's full Rankin–Selberg / Lefschetz-pencil machinery (`remark.pdf`, footnote 3). Even on its own, this proof is a gem of arithmetic geometry.
  + *Seesaw invariance of $sqrt(X)$-iterated unitary theta lifts.* The discovery that an $m$-fold iterated theta lift $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ between totally definite unitary groups produces a Gross–Prasad / Bessel period independent of the auxiliary Hecke characters $mu_1, dots.c, mu_m$ via the Rallis seesaw identity, while accumulating multiplicity $m approx sqrt(X)$ in a natively automorphic fashion, introduces a genuinely new tool into the theory of automorphic forms and special values of $L$-functions.

  == Roadmap for Massive Simplifications

  Every landmark proof in mathematics begins as an expedition across uncharted terrain—carrying extra gear, taking detours around cliffs whose passes are not yet visible, and building temporary bridges just sturdy enough to cross. The history of number theory offers abundant precedent:
  - The Prime Number Theorem was first proved in 1896 by Hadamard and de la Vallée Poussin using the theory of entire functions of finite order; within decades Landau simplified it, Wiener and Ikehara recast it via Tauberian theory, and in 1980 Donald Newman distilled the core complex-analytic argument into a single page.
  - Deligne's first proof of the Weil conjectures (1974) required delicate Rankin–Selberg estimates and Lefschetz pencils; his second proof (1980) introduced weights and the Fourier transform to yield a vastly more conceptual framework.
  - Wiles's 1995 proof of Fermat's Last Theorem was rapidly streamlined by Diamond and Fujiwara, and eventually absorbed into the sweeping modularity lifting theorems of Kisin, Khare–Wintenberger, and Taylor.

  In his November 2026 announcement, Alpöge was remarkably candid about the current state of the proof: *"An astounding amount of mathematics is present in the argument, far more than I had imagined would be necessary as a student. My intuition insists it will be massively simplified, likely immediately."* He further noted that *"I may have baked lots of strange suboptimal choices into the argument, and expect short arguments to follow fairly quickly, though I have not had time to search for such myself (yet!)."*

  Examining the architecture of the 2026 proof reveals four concrete, high-leverage targets for dramatic simplification.

  === Eliminating Behrend's 3-AP-Free Sphere Trick

  In choosing the parameters of the Iwasawa tower (Chapter 16; `remark.pdf`, item 19), the 2026 proof imports a celebrated construction from additive combinatorics: *Behrend's theorem (1946)*, which embeds a dense subset free of nontrivial three-term arithmetic progressions (3-APs) into $[1, N]$ by projecting integer lattice points on a high-dimensional Euclidean sphere $sum_(j=1)^d x_j^2 = R^2$ into base $2 M$, achieving density $N exp(-c sqrt(log N))$.

  Why did Behrend's spheres appear in a proof of the Riemann Hypothesis? In the tower selection, one needs a large family of auxiliary indices whose pairwise sums avoid three-term linear resonances that would create off-diagonal coincidences in the glued integral structure. Because Behrend's sets are strictly convex on the sphere (no three distinct points on a sphere are collinear), they guarantee the absence of 3-APs in one stroke.

  Yet, as Alpöge observed in footnote 7 of his remark: *"This is the sort of trick that intuitively to me is obviously going to be unnecessary."* There are at least three reasons why Behrend's construction is likely a removable scaffold:
  + *Overkill of strict 3-AP-freeness.* The automorphic orthogonality and Bost slope inequalities do not genuinely require *zero* three-term additive collisions; they only require that the number of collisions be bounded by a small fraction of the diagonal, which holds effortlessly for a random subset, a Sidon-type perturbation, or a simple greedy / prime-supported index set.
  + *Suboptimal density loss.* Behrend's sub-polynomial loss $exp(-c sqrt(log N))$ forces extra slack elsewhere in the parameter optimization (such as the length of the theta-lift chain and the conductor bounds). Replacing it with a Fourier-analytic or second-moment weighting on a full interval or arithmetic progression should both shorten the proof and tighten the quantitative constants.
  + *Conceptual decoupling.* Removing additive combinatorics from the tower selection isolates the Iwasawa-theoretic core cleanly from combinatorial sphere packing, making the mechanism transparent to number theorists.

  === Tightening the $m approx sqrt(X)$ Theta-Lift Chain and Bypassing $O(2, n)$ / $op("GL")_5$ Detours

  A second major source of complexity in the 2026 proof is historical sediment from the order in which the pieces were discovered. As documented in the timeline of `remark.pdf`, the proof's evolution passed through several intermediate vehicles:
  - *Multiplicity $2$ on $O(2, n)$:* The initial breakthrough came from realizing that a "natively automorphic" determinant on $O(2, n)$ mimicked Stepanov's multiplicity-$2$ construction by analogy with the definite-sign left-hand side of $q N = M^k + R$.
  - *Sixfold cover of $op("GL")_5$:* The automorphy of the auxiliary character/kernel $mu$ (and the relative trace formula bound reducing via Cauchy–Schwarz to the norm of a projected Poincaré series) entered through a theta representation on the sixfold metaplectic cover of $op("GL")_5$.
  - *The $m approx sqrt(X)$ unitary chain:* Only later did Claude propose iterating theta lifts $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ between totally definite unitary groups ($pi |-> pi plus.square mu_j [t]$) to arbitrary multiplicity $m approx sqrt(X)$, paired with the Rallis seesaw identity showing that the resulting Bessel period is independent of the Hecke characters.

  Once the unitary chain $U(X_0) -> dots.c -> U(X_m)$ is recognized as the true engine of the proof, the auxiliary detours through $O(2, n)$ and the sixfold cover of $op("GL")_5$ look very much like historical scaffolding. Two concrete simplifications immediately suggest themselves:
  + *Purely unitary formulation.* Can the entire relative trace formula and approximate orthogonality bound be formulated directly inside unitary dual pairs $U(n) times U(n')$ (or $op("GL")_2 times op("GL")_2$ / metaplectic $tilde(op("SL"))_2$), bypassing the sixfold cover of $op("GL")_5$ and $O(2, n)$ altogether? Eliminating higher metaplectic covers would strip out one of the most technically demanding layers of the representation theory.
  + *Reducing the "cost per lift."* In item 14 of `remark.pdf`, a naive computation of the arithmetic cost of each theta lift showed that the argument would stall at $op("Re")(s) = 2/3$ without a delicate "division" and character-averaging step to beat the $2/3$ barrier down to $1/2$. Understanding the exact geometric reason for that $2/3$ threshold—and whether a better choice of local test vectors or Archimedean weights lowers the per-lift cost directly—could shrink both the required chain length $m$ and the analytic machinery needed to control the level and Chowla–Selberg / Siegel mass divisibility.

  === Streamlining Arakelov Covolumes and Integral-Structure Gluing

  At the arithmetic heart of the proof sits a delicate balance between two quantities: a *lower bound* on the divisibility (or height) of the $m$-fold iterated lift, and an *upper bound* on the Arakelov covolume provided by Bost's slope inequality (Chapters 13–15). In the 2026 formalization, bridging this gap required:
  - gluing an integral structure across families of Hecke characters to emulate a "greatest common divisor" averaging effect;
  - proving approximate orthogonality of the columns of the resulting integral matrix via Cauchy–Schwarz on projected Poincaré series;
  - computing explicit covolumes, theta-series indices, and congruences between lifted forms and ambient cusp forms.

  From the vantage point of Arakelov geometry and automorphic forms, this glued integral structure is almost certainly a shadow of a cleaner canonical object. Specifically, replacing explicit column-by-column approximate orthogonality with a canonical adelic $L^2$-norm comparison—via the Rallis inner product formula and a single global Petersson norm identity—could collapse tens of thousands of lines of explicit matrix and covolume estimates into a concise structural theorem. Likewise, if the integral structure can be defined directly on an algebraic cycle or Kudla–Millson / Borcherds-style generating series, much of the ad hoc congruence bookkeeping may evaporate.

  === Compressing 20 Million Lines of Lean 4 into a Human-Length Monograph

  The physical scale of the 2026 Lean 4 artifact—roughly 20 million lines of code distributed across fourteen compressed archives—initially astonished the mathematical community. Even more amusingly, Alpöge noted in footnote 2 of `remark.pdf` that when he experimented with automatically expanding the Lean proof into English prose, it ballooned past $250,000$ pages (with "Theorem 1" opening by solemnly invoking the total order of $bb(R)$ to deduce that if $sigma != 1/2$ then $sigma > 1/2$ or $sigma < 1/2$).

  It is crucial not to confuse the *size of an initial machine-verified search artifact* with the *intrinsic conceptual length of the mathematics*. Why does a first-generation human–AI formalization reach $20$ million lines?
  + *Lack of global refactoring:* Under intense research iteration, local lemmas are proved inline rather than factored into reusable abstractions; similar estimates for slightly different parameters are duplicated rather than unified.
  + *Missing library infrastructure:* Large swaths of the codebase build foundational background—adelic Haar measures, Siegel domains, unitary theta kernels, Bost slope inequalities, and explicit interval arithmetic—that did not yet exist in Mathlib.
  + *Low-level tactic verbosity:* Machine-generated formal proofs often spell out elementary algebraic rearrangements, finite case splits, and explicit numerical verifications that a human mathematician compresses into a single sentence ("by Cauchy–Schwarz and Stirling's formula").

  #insight-box(title: "A Realistic Compression Trajectory: From 20M Lines to a Journal Monograph")[
    We can already foresee three distinct stages of compression over the coming years:
    + *Stage I (Engineering deduplication and Mathlib upstreaming):* Refactoring duplicated modules, extracting general APIs for adelic analysis and theta lifts into Mathlib, and replacing verbose tactic scripts with high-level automation should shrink the formalization by an order of magnitude, from ~20 million lines to roughly 1–2 million lines, without changing a single mathematical idea.
    + *Stage II (Human-length journal monograph, ~50–150 pages):* Eliminating Behrend's spheres, bypassing the $O(2, n)$ / sixfold $op("GL")_5$ detours, and streamlining the covolume gluing will bring the proof into the familiar scale of landmark twentieth- and twenty-first-century papers—comparable in length to Wiles's proof of Fermat's Last Theorem (109 pages) or Ngô's proof of the Fundamental Lemma (126 pages).
    + *Stage III (The "Book" proof, ~15–40 pages?):* Once the true conceptual core of the "$sqrt(X)$ multiplicity via automorphic positivity" mechanism is fully understood—perhaps revealing a direct analytic or cohomological analogue of Stepanov's method over $op("Spec") bb(Z)$ without the full apparatus of unitary theta towers—a short, self-contained graduate textbook proof may well emerge.
  ]

  == Toward the Extended and Grand Riemann Hypotheses

  With RH and Dirichlet GRH established, the natural hierarchy of Riemann Hypotheses comes into sharp focus:
  $ &underbrace(zeta(s), "RH (2026)") quad subset.eq quad underbrace(L(s, chi), "Dirichlet GRH (2026)") \
    &quad subset.eq quad underbrace(zeta_K (s) "," space L(s, psi), "ERH (Number Fields)") quad subset.eq quad underbrace(L(s, pi), "Grand RH (" op("GL")_n ")"). $
  Understanding what carries over smoothly from Dirichlet GRH to ERH—and where genuinely new obstructions appear when ascending to $op("GL")_n$—illuminates both the power and the boundaries of the Alpöge–Claude–Riemann method.

  === Abelian ERH Is Already a Theorem

  Before examining general number fields, we record an immediate but important structural corollary of Dirichlet GRH.

  #proposition(title: "Extended Riemann Hypothesis for Abelian Number Fields")[
    Let $K / bb(Q)$ be any finite abelian extension of number fields. Then every nontrivial zero $rho$ of the Dedekind zeta function $zeta_K (s)$ in the critical strip $0 < op("Re")(s) < 1$ satisfies $op("Re")(rho) = 1/2$.
  ]

  #proof[
    By the Kronecker–Weber theorem, $K$ is contained in a cyclotomic field $bb(Q)(zeta_m)$ for some positive integer $m$. Let $H = op("Gal")(bb(Q)(zeta_m) / K) subset.eq (bb(Z) / m bb(Z))^times$, and let $X_K$ denote the group of primitive Dirichlet characters $chi$ whose conductor divides $m$ and whose induced character on $(bb(Z) / m bb(Z))^times$ is trivial on $H$. By Artin reciprocity (or elementary prime-splitting factorization of the Euler product),
    $ zeta_K (s) = product_(chi in X_K) L(s, chi), $
    where $L(s, chi)$ is the primitive Dirichlet $L$-function attached to $chi$ (with $L(s, chi_0) = zeta(s)$ for the trivial character). Since every factor $L(s, chi)$ has no zeros in $op("Re")(s) > 1/2$ by the Alpöge–Claude–Riemann Theorem, and the functional equation $xi_K (s) = xi_K (1 - s)$ reflects zeros across $op("Re")(s) = 1/2$, every nontrivial zero of $zeta_K (s)$ lies on the critical line $op("Re")(s) = 1/2$.
  ]

  Thus, for example, ERH holds unconditionally for all quadratic fields, all cyclotomic fields $bb(Q)(zeta_m)$, and all subfields thereof—already settling effective Chebotarev for abelian extensions and optimal prime-ideal counting in abelian number fields.

  === Why Alpöge Expects ERH for Arbitrary Number Fields

  For a general (non-abelian) number field $K$ of degree $d = [K : bb(Q)]$, the Dedekind zeta function
  $ zeta_K (s) = sum_(frak(a) != 0) N(frak(a))^(-s) = product_(frak(p)) (1 - N(frak(p))^(-s))^(-1) quad (op("Re")(s) > 1) $
  no longer factors into Dirichlet $L$-functions over $bb(Q)$. (Even if $K / bb(Q)$ is Galois, Artin's factorization $zeta_K (s) = product_rho L(s, rho)^(dim rho)$ involves higher-dimensional Artin $L$-functions whose holomorphicity is itself the Artin conjecture!) Yet Alpöge expressed strong confidence in `remark.pdf`: *"the method easily extends much further, resolving the so-called Generalized Riemann Hypothesis, and I expect, with more time, the Extended Riemann Hypothesis too."*

  Why does the architecture of the Alpöge–Claude–Riemann proof point naturally toward ERH? Four structural pillars remain intact over any number field $K$:
  + *Nonnegative von Mangoldt weights.* The logarithmic derivative of $zeta_K (s)$ is
    $ - (zeta'_K (s)) / (zeta_K (s)) = sum_(frak(a) != 0) Lambda_K (frak(a)) N(frak(a))^(-s), $
    where $Lambda_K (frak(a)) = log N(frak(p)) >= 0$ if $frak(a) = frak(p)^k$ is a prime-ideal power, and $0$ otherwise. Crucially, the coefficients $Lambda_K (frak(a))$ are *real and nonnegative*, exactly as for $zeta(s)$! Consequently, the Guinand–Weil explicit formula for $zeta_K (s)$ retains the identical positivity criterion $W_K (1_(0,1] + X^eta 1_(0,1/X]) >= 0$ that drives the bootstrap.
  + *Automorphic groups over totally real / CM bases.* The unitary theta-lift chain $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ and the Rallis seesaw identity are natively adelic constructions that work over any totally real number field $F$ and CM quadratic extension $E / F$. Indeed, much of the theory of totally definite unitary groups, GGP periods, and Siegel–Weil formulas is already formulated over arbitrary totally real fields $F$. (For a non-CM number field $K$, one can either work with Hecke characters over a CM field containing the Galois closure, or adapt the base-change and Weil-restriction formalism.)
  + *Arakelov geometry over $cal(O)_K$.* Bost's slope inequality is already a theorem of Arakelov geometry over arbitrary number fields $K$, with archimedean places $v | oo$ summed over all $r_1 + r_2$ infinite places of $K$. The main new feature is the presence of an infinite unit group $cal(O)_K^times$ of rank $r_1 + r_2 - 1 > 0$ (Dirichlet's unit theorem), which modifies the fundamental domains and regulator factors in the covolume computation without altering the underlying slope mechanism.
  + *Iwasawa theory and `VWin` over $K$.* The weakened Vandiver bound `VWin` for $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ already lives over a CM field $E$; extending it from imaginary quadratic $E$ to general CM fields $E / F$ requires controlling higher-rank Leopoldt/Vandiver obstructions, which is technically heavier but conceptually parallel.

  Completing this extension to ERH would immediately unlock Hooley's proof of Artin's primitive root conjecture, the full non-abelian Lagarias–Odlyzko effective Chebotarev density theorem, and optimal bounds on class groups and regulators of arbitrary number fields.

  === New Obstacles for Grand RH on $op("GL")_n$

  When we ascend beyond $op("GL")_1$ (Dirichlet and Hecke $L$-functions) and Dedekind zeta functions to the *Grand Riemann Hypothesis*—the assertion that for every cuspidal automorphic representation $pi$ of $op("GL")_n (bb(A)_K)$ ($n >= 2$), every nontrivial zero of the principal $L$-function $L(s, pi)$ lies on $op("Re")(s) = 1/2$—we encounter qualitatively new obstacles that do not appear anywhere in the $op("GL")_1$ proof.

  Let $pi = times.o.big'_v pi_v$ be a cuspidal automorphic representation of $op("GL")_n (bb(A)_bb(Q))$ with unitary central character. At every unramified prime $p$, $pi_p$ is specified by its Satake parameters $alpha_(1, p), dots.c, alpha_(n, p) in bb(C)^times$, and the Euler product is
  $ L(s, pi) = product_p product_(j=1)^n (1 - alpha_(j, p) p^(-s))^(-1) quad (op("Re")(s) >> 1). $
  Taking the logarithmic derivative yields
  $ - (L'(s, pi)) / (L(s, pi)) &= sum_(k=1)^oo sum_p (alpha_(1, p)^k + dots.c + alpha_(n, p)^k) (log p) p^(-k s) \
    &= sum_(m=1)^oo Lambda_pi (m) m^(-s). $

  Four fundamental barriers separate $L(s, pi)$ ($n >= 2$) from the 2026 proof of Dirichlet GRH:

  + *Loss of von Mangoldt positivity.* For $zeta(s)$ and $zeta_K (s)$, the coefficients $Lambda(m) >= 0$ are nonnegative; for Dirichlet $L$-functions $L(s, chi)$, the coefficients $chi(m) Lambda(m)$ have modulus $Lambda(m)$ and satisfy the elementary character-orthogonality trick $1 + op("Re")(chi(p) p^(-i t)) >= 0$. For $n >= 2$, by contrast, the coefficients $a_pi (p^k) = sum_(j=1)^n alpha_(j, p)^k$ oscillate in sign and phase (governed by the Sato–Tate distribution for $op("GL")_2$!). One cannot directly apply a positivity-based Weil functional to $L(s, pi)$ alone without a mechanism to restore positivity. The standard analytic device is to pass to the *Rankin–Selberg $L$-function* $L(s, pi times tilde(pi))$, whose logarithmic derivative has genuinely nonnegative coefficients
    $ Lambda_(pi times tilde(pi)) (p^k) = |sum_(j=1)^n alpha_(j, p)^k|^2 log p >= 0, $
    or to form the nonnegative matrix-valued product $L(s, pi) L(s, tilde(pi)) L(s, pi times tilde(pi)) zeta(s)$. However, passing from $L(s, pi)$ to $L(s, pi times tilde(pi))$ squares the degree from $n$ to $n^2$ and introduces a pole at $s = 1$, drastically increasing the analytic conductor and the required multiplicity chain!
  + *The Ramanujan–Petersson conjecture.* For $op("GL")_1$, every local parameter trivially satisfies $|chi(p)| = 1$. For $op("GL")_n$ ($n >= 2$), the *Generalized Ramanujan Conjecture* asserts that every unramified local component $pi_p$ is tempered, i.e.,
    $ |alpha_(j, p)| = 1 quad (1 <= j <= n), $
    and likewise that $pi_oo$ is tempered at the archimedean place. While Deligne (1974) proved Ramanujan for holomorphic modular forms on $op("GL")_2$, and subsequent breakthroughs (Clozel, Shin, Caraiani, Allen–Calegari–Caraiani–Gee–Helm–Le Hung–Newton–Scholze–Taylor–Thorne) established it for regular algebraic conjugate-self-dual representations, Ramanujan remains *wide open* for Maass cusp forms on $op("GL")_2$ and for general cuspidal representations on $op("GL")_n$ ($n >= 3$). Note that the Riemann Hypothesis for $L(s, pi)$ does not even cleanly decouple from Ramanujan: if a single unramified prime had $|alpha_(1, p)| = p^theta > 1$, the local Euler factor would already possess zeros on $op("Re")(s) = theta$, and in the global explicit formula, non-temperedness inflates the size of $Lambda_pi (p^k)$ and threatens to overwhelm the $sqrt(X)$ divisibility-versus-covolume balance.
  + *Higher-rank theta lifts and multiplicity chains.* In the Alpöge–Claude–Riemann proof, the iterated theta lift $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ works because each step appends a *one-dimensional* Hecke character $mu_j [t]$ (a $op("GL")_1$ object!) via classical Howe duality on unitary dual pairs, while the Rallis seesaw keeps the Bessel period invariant. To replicate this for a cuspidal representation $pi$ of $op("GL")_n$ ($n >= 2$), one would need an $m$-fold iterated functorial lift appending $pi$ (or its Speh representations $pi [t]$) onto higher-rank classical groups while preserving a tractable period integral and an explicit Rallis inner-product formula. Constructing such lifts unconditionally already touches the heart of Langlands functoriality and Arthur's endoscopic classification.
  + *Lack of elementary CM / Galois-module twists.* Over $op("GL")_1$, twisting by Hecke characters $mu_j$ of an imaginary quadratic field $E$ connects directly to CM elliptic curves, Chowla–Selberg periods, and cyclotomic Iwasawa theory (`VWin`). For non-self-dual or Maass representations on $op("GL")_n$, there is no obvious geometric realization as an abelian variety or motive, making the Arakelov-geometric side (Bost slope inequality and integral structures) far more elusive.

  === Rankin–Selberg $L$-Functions, Elliptic Curves, and Birch–Swinnerton-Dyer

  Among all $op("GL")_n$ $L$-functions ($n >= 2$), one family stands out as the most natural and fertile testing ground for extending the 2026 method: the *Hasse–Weil $L$-functions* $L(s, E)$ of elliptic curves $E / bb(Q)$.

  By the Modularity Theorem (Wiles 1995; Taylor–Wiles 1995; Breuil–Conrad–Diamond–Taylor 2001), for every elliptic curve $E / bb(Q)$ of conductor $N$, there exists a weight-$2$ cuspidal holomorphic newform $f_E in S_2 (Gamma_0 (N))$ such that
  $ L(s, E) &= L(s, f_E) \
    &= product_(p | N) (1 - a_p p^(-s))^(-1) product_(p divides.not N) (1 - a_p p^(-s) + p^(1 - 2 s))^(-1), $
  where $a_p = p + 1 - \# E(bb(F)_p)$ for $p divides.not N$, and the central point of the functional equation (normalized algebraically) is $s = 1$ (corresponding to $s = 1/2$ in the analytic normalization $L(s - 1/2, E)$). Crucially, *three of the four $op("GL")_n$ obstacles soften dramatically for $L(s, E)$*:
  - Ramanujan–Petersson is *known* by Hasse's theorem $|a_p| <= 2 sqrt(p)$ (and Deligne's theorem for higher weights).
  - The representation $pi(f_E)$ is *algebraic and geometric*, realized in the cohomology of modular curves $X_0 (N)$ and equipped with canonical integral structures, Heegner points, and CM twists.
  - The Rankin–Selberg $L$-function $L(s, E times E) = zeta(s) L(s, op("Sym")^2 E)$ is completely known to be automorphic (Gelbart–Jacquet 1978), providing a degree-$4$ nonnegative-coefficient $L$-function whose zeros govern those of $L(s, E)$.

  What would Grand RH for $L(s, E)$ (and its quadratic twists $L(s, E_D)$) tell us about the *Birch and Swinnerton-Dyer (BSD) conjecture*? Recall that BSD asserts:
  $ op("ord")_(s = 1) L(s, E) = op("rank") E(bb(Q)), $
  and predicts the leading Taylor coefficient at $s = 1$ in terms of the regulator $op("Reg")(E)$, the Tate–Shafarevich group $op("Sha")(E)$, the torsion subgroup, and local Tamagawa numbers.

  It is vital to note a subtle distinction: *Grand RH for $L(s, E)$ does not by itself prove BSD!* Indeed, the central point $s = 1$ (analytically $s = 1/2$) lies *on* the critical line, so GRH is completely compatible with $L(s, E)$ vanishing to any order $r >= 0$ at $s = 1$. Nevertheless, Grand RH for $L(s, E)$ exerts profound control over the analytic rank and arithmetic of elliptic curves:
  + *Upper bounds on analytic rank (Mestre 1986).* Under GRH for $L(s, E)$, the explicit formula applied to a nonnegative test function yields the sharp upper bound
    $ op("ord")_(s = 1) L(s, E) <= (1/2 + o(1)) (log N) / (log log N), $
    improving exponentially over the unconditional convexity bound $O(log N)$.
  + *Average analytic rank and Goldfeld's conjecture.* Combined with the Katz–Sarnak philosophy of low-lying zeros in families, GRH for quadratic twists $L(s, E_D)$ yields sharp upper bounds on the average analytic rank of $E_D$ as $|D| -> oo$ (approaching the conjectured average $1/2$ predicted by Goldfeld 1979).
  + *Effective nonvanishing and Gross–Zagier / Kolyvagin.* In the Kolyvagin–Gross–Zagier framework (which proves BSD whenever $op("ord")_(s=1) L(s, E) <= 1$), controlling the low-lying zeros and special values $L(1, E_D)$ of auxiliary quadratic twists is essential for constructing non-torsion Heegner points and bounding $\# op("Sha")(E)$.

  Thus, while BSD and Grand RH for $L(s, E)$ are logically independent, a proof of Grand RH for modular forms of weight $2$—perhaps via a $op("GL")_2$ generalization of the unitary theta-lift chain—would immediately reshape the entire landscape of elliptic curves.

  == Mathematics in the Post-2026 Era

  In November 1859, Bernhard Riemann concluded his brief paragraph on the zeros of $xi(t)$ with one of the most famous sentences in the history of science: *"One would certainly wish for a rigorous proof of this; I have, however, after some fleeting futile attempts, temporarily put aside the search for it, as it seemed dispensable for the next purpose of my investigation."* One hundred and sixty-seven years later, in November 2026, that proof finally arrived—and in a form that neither Riemann nor almost any mathematician of the twentieth century could have imagined.

  === The Unity of Number Theory

  Looking back across the eighteen chapters of this monograph, what inspires the deepest awe is not any single technical estimate, but the breathtaking *unity* of mathematics revealed by the proof. A question born from counting prime numbers and integrating a single meromorphic function in $bb(C)$ turned out to summon almost every major edifice of modern arithmetic:
  - *Classical Fourier and complex analysis:* the Guinand–Weil explicit formula, Mellin transforms, and positivity of Weil's quadratic form.
  - *Arithmetic geometry over finite fields:* Stepanov's polynomial method with multiplicity, Weil–Deligne cohomology, and the elementary path-quadric proof of $q N = M^k + R$.
  - *Elliptic curves and complex multiplication:* inert-prime derivations $D^p equiv 0$ and Chowla–Selberg period relations.
  - *Automorphic representations and the Langlands program:* iterated theta lifts $U(X_0) -> dots.c -> U(X_m)$ of length $m approx sqrt(X)$ between totally definite unitary groups, Gross–Prasad / Bessel periods, the Rallis seesaw identity, and the Siegel mass formula.
  - *Arakelov geometry:* Bost's slope inequality and covolume bounds on arithmetic Hermitian vector bundles.
  - *Iwasawa theory and algebraic $K$-theory:* Galois cohomology $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$, the weakened Vandiver bound `VWin`, and Quillen–Lichtenbaum links to $K_n (bb(Z))$.
  - *Additive combinatorics:* Behrend's 3-AP-free spheres guiding the tower selection.

  For a century and a half, mathematicians spoke of the "shadows" of the Riemann Hypothesis—its reflections in prime gaps, character sums, class groups, function fields, and random matrix theory. In the Alpöge–Claude–Riemann proof, those shadows finally converged upon their source. Even if future simplifications strip away half of this machinery, the fact that all of these worlds interlocked seamlessly to seal the critical line is a permanent testimony to the deep coherence of number theory.

  === Formal Proof Assistants as a New Medium of Publication

  The events of November 2026 also mark a watershed in *how mathematics is verified, communicated, and discovered*. For the first time in history, the resolution of a preeminent open problem was presented to the world not as a traditional preprint whose referees must spend years hunting for subtle gaps, but as a machine-checked Lean 4 kernel certificate—verifying every logical step from the axioms of dependent type theory down to `theorem riemannHypothesis : RiemannHypothesis`.

  Alpöge described this unprecedented situation with characteristic honesty: *"This puts us in the rather extraordinary situation this age has made possible, in which I am presenting the world with a complete argument before having mastered a massive neighbourhood around its mathematics. It being obviously inappropriate to attempt to post some massive unreadable travesty of 'slop', I decided to only present Lean."*

  This inversion of the traditional order—*machine-verified certainty first, human conceptual mastery and polished exposition second*—redefines the division of labor in mathematics:
  - *Verification* is no longer a bottleneck of human fallibility. When a proof spans thousands of interdependent lemmas across half a dozen subfields, a small trusted kernel eliminates the agonizing ambiguity of "is Lemma 14.37 really airtight?"
  - *Understanding*, however, remains an irreducibly human (and shared) enterprise. A 20-million-line Lean repository establishes *that* the Riemann Hypothesis is true; it does not by itself tell a graduate student *why* it is true, how its ideas connect to neighboring problems, or which parts are essential and which are accidental. Writing monographs, giving lectures, isolating conceptual bottlenecks, and discovering short "Book proofs" become *more* valuable, not less, in the post-2026 era.

  Equally historic is the nature of the collaboration itself. Alpöge brought decades of mathematical taste, breadth, and strategic intuition—recognizing the toy-setting analogy, steering the argument toward Stepanov-with-multiplicity in a natively automorphic framework—while Claude provided tireless technical mastery across higher-rank automorphic forms, Arakelov estimates, and Lean formalization, culminating in the astonishing suggestion to chain $m approx sqrt(X)$ theta lifts ("Claude flew, and danced, and sparkled near that finish line. ... And yet, what else could it be?"). Rather than diminishing human mathematical creativity, this partnership amplified it, allowing a single mathematician's decades-long dream to cross an ocean of technical complexity in months.

  === Open Frontiers That Remain

  It is natural, when a 167-year-old guiding star is finally reached, to feel a moment of bittersweetness—what Alpöge called *"in my case a loss of a principal guiding light."* Yet the resolution of RH and Dirichlet GRH does not exhaust the mystery of the primes; it illuminates how much deeper the ocean still runs. Among the great open frontiers standing before the next generation of mathematicians:

  + *The fine vertical statistics and simplicity of zeros of $zeta(s)$.* Knowing that every nontrivial zero has the form $rho = 1/2 + i gamma$ with $gamma in bb(R)$ leaves wide open whether every zero is *simple* ($zeta'(1/2 + i gamma) != 0$), whether the positive ordinates $gamma > 0$ are linearly independent over $bb(Q)$, and whether their local pair correlations obey Montgomery's GUE law
    $ 1 - ((sin(pi u)) / (pi u))^2. $
    Even the *Hilbert–Pólya dream*—exhibiting a natural self-adjoint operator whose spectrum is literally the set of ordinates ${gamma}$—now transforms from a speculative proof strategy into a pure question of spectral geometry and arithmetic physics.
  + *Additive prime problems beyond RH.* Twin primes ($p$ and $p + 2$ both prime), Goldbach's strong conjecture ($2 n = p_1 + p_2$ for all $n >= 2$), Landau's conjecture (infinitely many primes of the form $n^2 + 1$), and Cramér's prime-gap conjecture ($p_(n+1) - p_n = O((log p_n)^2)$) all remain open. None of them follows from RH or GRH alone; each demands new ideas about additive correlations of the von Mangoldt function.
  + *The Extended and Grand Riemann Hypotheses.* Completing the extension to Dedekind zeta functions $zeta_K (s)$ (unlocking Artin's primitive root conjecture and general effective Chebotarev), and confronting the Ramanujan–Petersson and positivity barriers for automorphic $L$-functions $L(s, pi)$ on $op("GL")_n$ and Hasse–Weil $L$-functions $L(s, E)$.
  + *The remaining pillars of arithmetic and geometry.* Langlands functoriality in full generality, the Birch and Swinnerton-Dyer conjecture, the Hodge conjecture, the full Kummer–Vandiver conjecture (building on the breach opened by `VWin`), and the $a b c$ conjecture.

  Riemann's 1859 memoir taught mathematics that the distribution of the simplest objects we know—the prime numbers—is governed by hidden symmetries of extraordinary depth. The Alpöge–Claude–Riemann Theorem of 2026 closes the first great chapter of that story, while opening another that promises to be richer still: an era in which human intuition, formal verification, and artificial intelligence work side by side to uncover what Alpöge called *"the joy and wonder we are about to find in the simplest things."*

  #exercises((
    [
      (*From $psi(x)$ to $pi(x)$ under RH.*) Assume $psi(x) = x + O(sqrt(x) (log x)^2)$ for all $x >= 2$.
      + Prove that $theta(x) = sum_(p <= x) log p$ satisfies $psi(x) - theta(x) = sqrt(x) + O(x^(1/3) log x)$, and hence $theta(x) = x + O(sqrt(x) (log x)^2)$.
      + Using Stieltjes integration by parts $pi(x) - pi(2) = integral_(2^-)^x (dif theta(t)) / (log t)$, deduce carefully that $pi(x) = op("li")(x) + O(sqrt(x) log x)$. Explain why the exponent of $log x$ drops from $2$ to $1$, whereas the exponent $1/2$ of $x$ cannot change.
      + Show that if we also knew the stronger (still open!) bound $psi(x) = x + O(sqrt(x) log log log x)$, then $pi(x) - op("li")(x)$ would satisfy $O(sqrt(x) (log log log x) / (log x))$, and compare this with Littlewood's oscillation theorem $pi(x) - op("li")(x) = Omega_(plus.minus)((sqrt(x) log log log x) / (log x))$.
    ],
    [
      (*Ankeny's bound $n_p = O((log p)^2)$ via a compactly supported kernel.*) In the proof sketch of Corollary 18.5, we used the exponential weight $e^(-n / Y)$. Replace $e^(-n / Y)$ by the Fejér-type weight $(1 - n / Y)_+$ (whose Mellin transform is $Y^s / (s (s + 1))$).
      + Express $sum_(n <= Y) Lambda(n) chi(n) (1 - n / Y)$ as a contour integral involving $-L'(s, chi) / L(s, chi)$, and shift the contour to $op("Re")(s) = -1/2$ assuming GRH for $L(s, chi)$.
      + Using the zero-density estimate $N(T + 1, chi) - N(T, chi) << log(p (|T| + 2))$, prove that $sum_rho 1 / |rho (rho + 1)| << log p$, deduce that the sum over nontrivial zeros is $O(sqrt(Y) log p)$, and conclude that $n_p << (log p)^2$.
    ],
    [
      (*Effective class number lower bound for imaginary quadratic fields.*) Let $-D < 0$ be a fundamental discriminant and $chi_(-D)$ the associated quadratic Dirichlet character.
      + Assuming GRH for $L(s, chi_(-D))$, use the Hadamard product and Borel–Carathéodory theorem (or the explicit formula for $log L(s, chi_(-D))$ at $s = 1 + 1 / log log D$) to prove Littlewood's bound $|log L(1, chi_(-D))| <= log log log D + O(1)$.
      + Deduce Corollary 18.7: $h(-D) >> sqrt(D) / log log D$ with an effective implied constant.
      + For a fixed positive integer $h_0$, determine the asymptotic upper bound on the largest fundamental discriminant $-D < 0$ with $h(-D) = h_0$ implied by this inequality.
    ],
    [
      (*Abelian ERH vs. Kummer non-abelian extensions in Artin's conjecture.*)
      + Using Proposition 18.10, deduce the effective Chebotarev density theorem (Lagarias–Odlyzko) unconditionally for every finite abelian extension $K / bb(Q)$.
      + For an odd prime $q >= 3$ and a nonsquare integer $a > 1$ that is not a $q$-th power, show that the Kummer extension $K_q = bb(Q)(zeta_q, a^(1/q))$ is Galois over $bb(Q)$ with Galois group isomorphic to the non-abelian semidirect product $bb(Z) / q bb(Z) times.r (bb(Z) / q bb(Z))^times$ of order $q (q - 1)$.
      + Factor $zeta_(K_q) (s)$ into Artin $L$-functions and verify that it contains an irreducible Artin $L$-function of degree $q - 1 >= 2$. Explain why Hooley's 1967 proof of Artin's primitive root conjecture therefore requires ERH beyond Dirichlet GRH.
    ],
    [
      (*Weakened Vandiver (`VWin`) and $K_(2 e) (bb(Z))$ via Quillen–Lichtenbaum.*) Let $ell$ be an odd prime and $e >= 1$ an integer.
      + Using the Quillen–Lichtenbaum isomorphism $K_(2 e) (bb(Z)) times.o bb(Z)_ell tilde.equiv H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (e + 1))$, explain why showing $H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (2 k + 1)) = 0$ for all odd primes $ell$ implies that $K_(4 k) (bb(Z))$ is a finite $2$-group.
      + By Poitou–Tate duality and the Kummer exact sequence, relate the $ell$-torsion of $H^2_op("et") (cal(O)_E [1/ell], bb(Z)_ell (e + 1))$ to the untwistable classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ bounded by `VWin`.
      + (*Research-oriented.*) Assuming a quantitative bound of the form $\# H^2_op("et") (bb(Z)[1/ell], bb(Z)_ell (2 k + 1)) < ell^2$ for all primes $ell$ in a range, what structural conclusions (such as cyclicity or vanishing of $ell$-primary parts) follow for $K_(4 k) (bb(Z))$?
    ],
    [
      (*Eliminating Behrend's 3-AP-free spheres.*) In Behrend's construction, the integer points on the sphere $sum_(j=1)^d x_j^2 = R^2$ with $0 <= x_j < M$ form a 3-AP-free set when mapped to integers in base $2 M$.
      + Verify that no three distinct points on a Euclidean sphere are collinear, and deduce that the base-$2 M$ encoding contains no nontrivial three-term arithmetic progression $a + c = 2 b$.
      + (*Open-ended.*) Suppose an analytic orthogonality argument only requires a subset $A subset.eq [1, N]$ of size $|A| >= c N$ (or $N / (log N)^A$) whose number of 3-APs is $O(|A|^2 / N^delta)$ rather than literally $0$, or whose additive energy $E(A) = \# {(a_1, a_2, a_3, a_4) in A^4 : a_1 + a_2 = a_3 + a_4}$ is bounded. Compare a random subset $A$ of density $p$ against Behrend's set: how much density is gained, and what trade-off appears in the off-diagonal error term?
    ],
    [
      (*Positivity obstruction for $op("GL")_2$ and Rankin–Selberg $L$-functions.*) Let $f in S_2 (Gamma_0 (N))$ be a normalized cuspidal Hecke eigenform with Fourier coefficients $a_f (p) = alpha_p + beta_p$ ($alpha_p beta_p = p$, $|alpha_p| = |beta_p| = sqrt(p)$ for $p divides.not N$).
      + Normalize $tilde(alpha)_p = alpha_p / sqrt(p)$ and $tilde(beta)_p = beta_p / sqrt(p)$ so that $L(s, f)$ has critical line $op("Re")(s) = 1/2$. Show that the coefficients $Lambda_f (p) = (tilde(alpha)_p + tilde(beta)_p) log p$ of $-L'(s, f) / L(s, f)$ change sign infinitely often (hint: use the convergence or non-pole at $s = 1$ of $L(s, f)$ together with Landau's theorem on Dirichlet series with nonnegative coefficients).
      + Now form the Rankin–Selberg $L$-function $L(s, f times f) = product_(p divides.not N) (1 - tilde(alpha)_p^2 p^(-s))^(-1) (1 - p^(-s))^(-2) (1 - tilde(beta)_p^2 p^(-s))^(-1) dot.c L_N (s)$ (where $L_N (s)$ is the finite product over $p | N$). Verify that for every unramified prime $p$ and every $k >= 1$,
        $ Lambda_(f times f) (p^k) = (tilde(alpha)_p^k + tilde(beta)_p^k)^2 log p >= 0. $
      + Discuss why the Guinand–Weil explicit formula for $L(s, f times f)$ restores von Mangoldt positivity, and explain how the degree $4$ (and the pole at $s = 1$ coming from the factor $zeta(s)$) alters the required multiplicity $m$ in a hypothetical theta-lift proof of Grand RH for $L(s, f)$.
    ],
  ))
]
