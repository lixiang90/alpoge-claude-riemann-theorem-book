// ============================================================================
// Chapter 3: 167 Years of the Riemann Hypothesis:
// Classical and Geometric Paradigms
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch03() = [
  #chapter(
    "167 Years of the Riemann Hypothesis: Classical and Geometric Paradigms",
    short-title: "167 Years of the Riemann Hypothesis",
    epigraph: "The Riemann Hypothesis is the classic problem in number theory. It asks for optimal control on the count of prime numbers of a given size. Its shadows have guided mathematicians for 150 years, and its many rhymes and reflections, even reaching physics, taught us the unity of our fields.",
    epigraph-source: "Levent Alpöge, Remark (November 20, 2026)",
    overview: [
      Between Bernhard Riemann's eight-page memoir of November 1859 and the formal verification of the Alpöge–Claude proof in November 2026, the Riemann Hypothesis served as the central organizing force of modern number theory. In this chapter we trace the four great intellectual paradigms that shaped those 167 years: the classical analytic assault via zero-free regions and mollifiers; the spectral, physical, and random matrix perspective initiated by Hilbert, Pólya, Selberg, and Montgomery; the function-field revolution of Artin, Hasse, Weil, Grothendieck, and Deligne; and the elementary multiplicity paradigm of Stepanov and Bombieri. Understanding both the triumphs and the structural obstructions of each paradigm illuminates the precise sense in which the November 2026 breakthrough—bridging Stepanov's multiplicity method to automorphic forms via chains of $m approx sqrt(X)$ theta lifts—resolves a century-old impasse.
    ],
    label-name: "ch:history",
  )

  When Bernhard Riemann submitted his 1859 paper to the Berlin Academy, he left the mathematical world with a single offhand sentence—"it is very probable that all roots are real"—whose consequences would reshape analysis, algebraic geometry, representation theory, mathematical physics, and formal logic alike. No single approach could carry the weight of the problem alone. Instead, over the ensuing 167 years, mathematicians developed a remarkable ecosystem of partial results, structural analogies, equivalent reformulations, and complete proofs in parallel worlds. Each of these traditions exposed a different facet of the zeta function, and—crucially for the story of this monograph—nearly all of them converge inside the Alpöge–Claude proof.

  // ==========================================================================
  == The Classical Analytic Era (1859–1950)
  // ==========================================================================

  Before complex analysis entered the study of prime numbers, Pafnuty Chebyshev had already demonstrated in 1850 and 1852 that the Prime Number Theorem has the right order of magnitude. Introducing the weighted prime-counting functions
  $ theta(x) = sum_(p <= x) log p, quad psi(x) = sum_(n <= x) Lambda(n) = sum_(p^k <= x) log p, $
  where $Lambda(n)$ is the von Mangoldt function, Chebyshev analyzed the prime factorization of the central binomial coefficient $binom(2 n, n)$ and of $n!$ via Stirling's formula.

  #theorem(title: "Chebyshev's Bounds, 1852")[
    There exist explicit constants $0 < c_1 < 1 < c_2$ such that for all sufficiently large $x$,
    $ c_1 x / (log x) <= pi(x) <= c_2 x / (log x), $
    and equivalently $c_1 x <= psi(x) <= c_2 x$. Moreover, if the limit $lim_(x -> oo) pi(x) (log x) / x$ exists, then it must equal $1$.
  ]

  Chebyshev's constants—originally $c_1 approx 0.92129$ and $c_2 approx 1.10555$—could be narrowed slightly by Sylvester and others, yet elementary combinatorial identities alone seemed unable to force $c_1$ and $c_2$ to meet at $1$. (A century later, Erdős and Selberg would find an elementary proof of the Prime Number Theorem in 1949 using Selberg's symmetry formula, but it yielded far weaker error terms than the complex-analytic method.)

  === Hadamard, de la Vallée Poussin, and Zero-Free Regions

  The decisive breakthrough came thirty-seven years after Riemann's memoir. Working independently, Jacques Hadamard and Charles-Jean de la Vallée Poussin proved the Prime Number Theorem in 1896 by establishing that the Riemann zeta function has no zeros on the line $op("Re")(s) = 1$. Three years later, in 1899, de la Vallée Poussin sharpened the nonvanishing argument into an explicit quantitative *zero-free region* inside the critical strip, thereby obtaining the first strong error term for $psi(x) - x$.

  #theorem(title: "Hadamard–de la Vallée Poussin, 1896–1899")[
    There exists an absolute constant $c > 0$ such that $zeta(s) != 0$ for all $s = sigma + i t$ satisfying
    $ sigma >= 1 - c / (log(|t| + 2)). $
    Consequently, the Prime Number Theorem holds with the quantitative error term
    $ psi(x) = x + O(x exp(-c' sqrt(log x))) $
    for a positive constant $c' > 0$, and likewise $pi(x) = op("li")(x) + O(x exp(-c' sqrt(log x)))$.
  ]

  The mechanism behind de la Vallée Poussin's zero-free region is astonishingly compact—a single trigonometric positivity inequality that already foreshadows the role of positivity in every subsequent attack on the Riemann Hypothesis.

  #proof(title: "Sketch of the Zero-Free Region")[
    For any real angle $theta$, the identity
    $ 3 + 4 cos theta + cos(2 theta) = 2 (1 + cos theta)^2 >= 0 $
    is manifestly nonnegative. Taking the logarithmic derivative of the Euler product for $sigma > 1$,
    $ - (zeta'(s)) / (zeta(s)) = sum_(n = 1)^oo (Lambda(n)) / (n^s), $
    and forming the linear combination at $s = sigma$, $sigma + i t$, and $sigma + 2 i t$, we obtain
    $ & op("Re") ( - 3 (zeta'(sigma)) / (zeta(sigma)) - 4 (zeta'(sigma + i t)) / (zeta(sigma + i t)) - (zeta'(sigma + 2 i t)) / (zeta(sigma + 2 i t)) ) \ & quad = sum_(n = 1)^oo (Lambda(n)) / (n^sigma) (3 + 4 cos(t log n) + cos(2 t log n)) >= 0. $
    Now suppose $rho = beta + i gamma$ is a nontrivial zero of $zeta(s)$ with $|gamma| >= 2$, and set $t = gamma$. By the Hadamard product expansion of $xi(s)$, for $sigma > 1$ near $1$ one has the three estimates:
    1. Near the simple pole at $s = 1$, $-(zeta'(sigma)) / (zeta(sigma)) = 1 / (sigma - 1) + O(1)$.
    2. Near the zero $rho = beta + i gamma$, since every term $op("Re")(1 / (s - rho'))$ for a nontrivial zero $rho'$ is positive when $sigma > 1$, dropping all zeros except $rho$ gives
       $ - op("Re") (zeta'(sigma + i gamma)) / (zeta(sigma + i gamma)) <= - 1 / (sigma - beta) + C log(|gamma| + 2). $
    3. At $sigma + 2 i gamma$, dropping all zeros yields
       $ - op("Re") (zeta'(sigma + 2 i gamma)) / (zeta(sigma + 2 i gamma)) <= C log(|gamma| + 2). $
    Substituting these three bounds into the trigonometric inequality gives
    $ 3 / (sigma - 1) - 4 / (sigma - beta) + 5 C log(|gamma| + 2) >= 0. $
    Choosing $sigma = 1 + delta / (log(|gamma| + 2))$ with a sufficiently small constant $delta > 0$ forces $4 / (sigma - beta) <= 3 / (sigma - 1) + 5 C log(|gamma| + 2)$, which rearranges to $1 - beta >= c / (log(|gamma| + 2))$. Inserting this zero-free region into the truncated explicit formula for $psi(x)$ and optimizing the truncation height $T$ at $log T approx sqrt(log x)$ yields $psi(x) = x + O(x exp(-c' sqrt(log x)))$.
  ]

  Observe the delicate arithmetic of coefficients in that proof: the pole contributes $+3$, the putative zero contributes $-4$, and the inequality succeeds solely because $4 > 3$. Any nonnegative trigonometric polynomial $sum_(k=0)^d a_k cos(k theta) >= 0$ with $a_k >= 0$ and $a_1 > a_0$ produces a zero-free region of the same shape, merely improving the constant $c$. To widen the region asymptotically as $|t| -> oo$, one must replace the trivial convexity bound on $|zeta(sigma + i t)|$ near $sigma = 1$ with deeper cancellation in Dirichlet polynomials $sum n^(-i t)$.

  In 1922 Littlewood used Weyl's method of exponential sums to improve the denominator from $log |t|$ to $(log |t|) / (log log |t|)$. The definitive classical sharpening arrived in 1958, when Ivan Vinogradov and Nikolai Korobov independently applied Vinogradov's mean value theorem to bound $|zeta(sigma + i t)|$ near the $1$-line.

  #theorem(title: "Vinogradov–Korobov Zero-Free Region, 1958")[
    There exists an absolute constant $c > 0$ such that $zeta(s) != 0$ for all $s = sigma + i t$ satisfying
    $ sigma >= 1 - c / ((log(|t| + 2))^(2/3) (log log(|t| + 3))^(1/3)). $
    Consequently, for a suitable constant $c' > 0$,
    $ psi(x) = x + O( x exp( - c' (log x)^(3/5) (log log x)^(-1/5) ) ). $
  ]

  Remarkably, despite the subsequent resolution of the Vinogradov Mean Value Conjecture by Bourgain, Demeter, and Guth (2015) and by Wooley (2016), the asymptotic shape of the Vinogradov–Korobov zero-free region was never improved by classical exponential-sum techniques. Prior to November 2026, not a single strip $op("Re")(s) > 1 - epsilon$ (for any fixed $epsilon > 0$, however small) was known to be free of zeros of $zeta(s)$.

  === Hardy's Theorem and Zero-Density Estimates

  While zero-free regions pushed inward from the right edge $sigma = 1$ of the critical strip, a complementary line of inquiry asked directly about the zeros *on* or *near* the critical line $sigma = 1/2$. In 1914, G. H. Hardy achieved the first breakthrough on the critical line itself.

  #theorem(title: "Hardy's Theorem, 1914")[
    The Riemann zeta function $zeta(s)$ has infinitely many zeros on the critical line $op("Re")(s) = 1/2$.
  ]

  Hardy's proof exploits the fact that the completed zeta function
  $ xi(s) = 1/2 s (s - 1) pi^(-s/2) Gamma(s/2) zeta(s) $
  is real-valued on the critical line $s = 1/2 + i t$ ($t in bb(R)$). If $xi(1/2 + i t)$ had only finitely many real zeros, it would maintain a constant sign for all sufficiently large $t >= T_0$. To derive a contradiction, Hardy examined the Mellin transform relation connecting $xi(s)$ to the Jacobi theta function $theta.alt(u) = sum_(n = -oo)^oo e^(-pi n^2 u)$:
  $ 1 / (2 pi i) integral_(1/2 - i oo)^(1/2 + i oo) (xi(s)) / (s (s - 1)) u^(-s) dif s = 1/2 (theta.alt(u) - 1) - 1 / (2 sqrt(u)) + 1/2. $
  Rotating the variable $u$ toward the imaginary axis via $u = e^(i (pi/2 - delta))$ as $delta -> 0^+$, the factor $e^(t (pi/2 - delta))$ counteracts the exponential decay $|Gamma(1/4 + i t / 2)| tilde.op c |t|^(-1/4) e^(-pi |t| / 4)$. If $xi(1/2 + i t)$ did not change sign for $t >= T_0$, the integral over $t$ would blow up or stay bounded in a manner incompatible with the rapid oscillations of $theta.alt(e^(i (pi/2 - delta)))$ near the rational cusp $u = i$, where $theta.alt(i + delta)$ vanishes to infinite order along appropriate derivatives! Hardy's argument was soon sharpened by Hardy and Littlewood (1921), who proved that the number $N_0 (T)$ of zeros of $zeta(1/2 + i t)$ with $0 < t <= T$ satisfies $N_0 (T) >> T$.

  In the very same year (1914), Harald Bohr and Edmund Landau approached the critical line from the outside by counting zeros off the line. For $1/2 <= sigma <= 1$ and $T >= 2$, define the zero-counting function
  $ N(sigma, T) = \#{ rho = beta + i gamma : zeta(rho) = 0, quad beta >= sigma, quad 0 < gamma <= T }, $
  counted with multiplicity. By the Riemann–von Mangoldt formula (Chapter 1), the total number of nontrivial zeros up to height $T$ is $N(T) = (T / (2 pi)) log(T / (2 pi e)) + O(log T)$.

  #proposition(title: "Bohr–Landau Density Estimate, 1914")[
    For every fixed $sigma > 1/2$,
    $ N(sigma, T) = O_sigma (T) = o(N(T)) quad "as" T -> oo. $
    In particular, for every $epsilon > 0$, all but $o(N(T))$ nontrivial zeros of $zeta(s)$ lie in the thin vertical strip $|op("Re")(rho) - 1/2| < epsilon$.
  ]

  The Bohr–Landau estimate is proved by applying Jensen's inequality (or Littlewood's lemma) to the mean square of $zeta(s) M(s) - 1$ for a short Dirichlet polynomial $M(s)$ approximating $1 / zeta(s)$. Subsequent generations of analytic number theorists refined the exponent $A(sigma)$ in zero-density bounds of the shape $N(sigma, T) << T^(A(sigma) (1 - sigma) + epsilon)$: Carlson (1920), Ingham (1940), Halász and Turán (1969), Montgomery (1969), and Huxley (1972), who proved $N(sigma, T) << T^((12/5)(1 - sigma) + epsilon)$ uniformly for $1/2 <= sigma <= 1$—a result strong enough to establish primes in short intervals $[x, x + x^(7/12 + epsilon)]$. Even the conjectured *Density Hypothesis* $N(sigma, T) << T^(2(1 - sigma) + epsilon)$, however, still permits infinitely many counterexamples to the Riemann Hypothesis.

  === Selberg, Levinson, and Conrey: Positive Proportions on the Critical Line

  To show that a *positive proportion* of all nontrivial zeros lie on the critical line—that is, $N_0 (T) >= c N(T)$ with $c > 0$, matching the logarithmic factor in $N(T) tilde.op (T / (2 pi)) log T$—required an entirely new idea. Atle Selberg supplied it in 1942 while working in isolation in occupied Norway.

  #theorem(title: "Positive Proportion on the Critical Line")[
    Let $N_0 (T)$ denote the number of zeros of $zeta(1/2 + i t)$ with $0 < t <= T$ (counted with multiplicity).
    1. *(Selberg, 1942)* There exists an absolute constant $c > 0$ such that $N_0 (T) >= c N(T)$ for all sufficiently large $T$.
    2. *(Levinson, 1974)* More than one-third of the nontrivial zeros of $zeta(s)$ lie on the critical line: $lim inf_(T -> oo) N_0 (T) / N(T) > 0.3474$.
    3. *(Conrey, 1989)* More than two-fifths of the nontrivial zeros of $zeta(s)$ lie on the critical line: $lim inf_(T -> oo) N_0 (T) / N(T) > 0.4088$.
  ]

  Selberg's method begins with the real-valued Hardy $Z$-function $Z(t) = e^(i theta(t)) zeta(1/2 + i t)$, whose real zeros coincide with the critical-line zeros of $zeta(s)$. The difficulty in detecting sign changes of $Z(t)$ on a short interval $[t, t + H]$ (with $H approx c / log T$, comparable to the average zero spacing) is that $|Z(t)|$ fluctuates wildly, making the $L^2$-norm much larger than the $L^1$-norm. Selberg tamed these fluctuations by multiplying $zeta(s)$ by a *mollifier*—a short Dirichlet polynomial
  $ M(s) = sum_(n <= y) (mu(n) P((log(y / n)) / (log y))) / (n^s) $
  designed to approximate $zeta(s)^(-1/2)$ (or $zeta(s)^(-1)$ in Levinson's method) on the critical line. Comparing the integrals
  $ I(t) &= integral_t^(t + H) Z(u) |M(1/2 + i u)|^2 dif u \ "and" quad J(t) &= integral_t^(t + H) |Z(u)| |M(1/2 + i u)|^2 dif u, $
  any $t$ for which $|I(t)| < J(t)$ guarantees a sign change of $Z(u)$ inside $(t, t + H)$. By Cauchy–Schwarz, the measure of the set where $|I(t)| < J(t)$ is controlled by mean-value estimates for $|I(t)|^2$ and $J(t)$, which Selberg evaluated asymptotically for $y = T^theta$ with small $theta > 0$.

  Norman Levinson (1974) transformed the problem from counting sign changes on the line to counting zeros *off* the line using the argument principle. Writing $xi(s) = G(s) + G(1 - s)$ for a suitable decomposition—concretely, introducing $F(s) = zeta(s) + zeta'(s) / (log(T / (2 pi)))$ so that $zeta(s) = 0$ on $sigma = 1/2$ corresponds to $op("arg") F(1/2 + i t)$ advancing by $pi$—Levinson applied Littlewood's lemma to $F(s) M(s)$ over a rectangle to the right of $sigma = 1/2$, showing that at least $34.74\%$ of zeros lie on the critical line. In 1989, J. Brian Conrey significantly extended the permissible mollifier length from $y = T^(1/2 - epsilon)$ to $y = T^(4/7 - epsilon)$ by invoking the Deshouillers–Iwaniec spectral estimates for sums of Kloosterman sums, pushing the proportion past $2/5$ ($40.88\%$). Later refinements with multi-piece mollifiers (Bui–Conrey–Young, Feng, Pratt–Robles–Zaharescu–Zeindler) edged the proportion slightly above $41.7\%$.

  #insight-box(title: "The Classical Analytic Barrier")[
    Both main branches of the classical analytic era ran into structural walls. In the zero-free region approach, trigonometric positivity on $op("Re")(s) > 1$ only probes the *boundary* of the Euler product; without controlling the analytic continuation of $zeta'(s) / zeta(s)$ deep inside the critical strip, even optimal exponential-sum bounds stall at $1 - sigma >> (log |t|)^(-2/3)$. In the mollifier approach, Levinson's method requires asymptotic evaluation of shifted convolution sums whose length $y = T^theta$ governs the proportion of zeros detected; even under the strongest conceivable cancellation ($theta -> oo$), the simple mollifier framework only approaches $100\%$ asymptotically and still cannot rule out a thin sequence of off-line zeros. Breaking through to $op("Re")(rho) = 1/2$ for *every* zero required leaving pure complex analysis of $zeta(s)$ alone and introducing deeper geometric or representation-theoretic structure.
  ]

  // ==========================================================================
  == Spectral, Physical, and Random Matrix Paradigms
  // ==========================================================================

  If the classical analytic era treated $zeta(s)$ as an object of complex function theory, a parallel tradition asked a bolder structural question: *what mathematical or physical system has the nontrivial zeros of $zeta(s)$ as its spectrum?*

  === The Hilbert–Pólya Conjecture

  Around 1914, in a letter from George Pólya to Edmund Landau (and independently in remarks attributed to David Hilbert in Göttingen), a strikingly simple conceptual route to the Riemann Hypothesis was proposed.

  #conjecture(title: "Hilbert–Pólya Conjecture")[
    There exists a complex Hilbert space $cal(H)$ and an unbounded self-adjoint linear operator $H : op("Dom")(H) -> cal(H)$ such that the spectrum of $H$ coincides with the set of ordinates $gamma$ of the nontrivial zeros $rho = 1/2 + i gamma$ of $zeta(s)$ (with matching multiplicities).
  ]

  Because the eigenvalues of a self-adjoint operator on a Hilbert space are automatically real, the existence of such an operator $H$ would immediately force $gamma in bb(R)$, and hence $op("Re")(rho) = 1/2$ for every nontrivial zero. For forty years the Hilbert–Pólya idea remained little more than a seductive metaphor. Then, in 1956, Atle Selberg discovered a geometric world in which the metaphor becomes a literal theorem.

  === The Selberg Trace Formula on Hyperbolic Surfaces

  Let $Gamma subset.eq op("PSL")_2 (bb(R))$ be a discrete cocompact torsion-free Fuchsian group, so that $M = Gamma backslash bb(H)$ is a compact Riemann surface of genus $g >= 2$ equipped with its metric of constant curvature $-1$. The hyperbolic Laplacian $Delta = - y^2 (partial_x^2 + partial_y^2)$ is a nonnegative self-adjoint operator on $L^2 (M)$ with discrete spectrum
  $ 0 = lambda_0 < lambda_1 <= lambda_2 <= dots.c -> oo. $
  Writing $lambda_j = 1/4 + r_j^2$ (so $r_j in bb(R)$ whenever $lambda_j >= 1/4$, and $r_j in i (-1/2, 1/2)$ for the finitely many "small" eigenvalues $0 < lambda_j < 1/4$), Selberg introduced an Euler product indexed not by prime numbers, but by the *primitive closed geodesics* $\{P\}$ on $M$ of hyperbolic length $ell(P) = log N(P)$.

  #definition(title: "Selberg Zeta Function")[
    For $op("Re")(s) > 1$, the *Selberg zeta function* of the compact hyperbolic surface $M = Gamma backslash bb(H)$ is defined by
    $ Z_Gamma (s) = product_({P}) product_(k = 0)^oo (1 - N(P)^(-s - k)), $
    where the outer product runs over all primitive closed geodesics $\{P\}$ on $M$.
  ]

  By computing the trace of an integral operator $L_h$ on $L^2 (M)$ in two ways—spectrally via the eigenfunctions of $Delta$, and geometrically by integrating the kernel along the diagonal and grouping conjugacy classes in $Gamma$—Selberg proved his celebrated trace formula.

  #theorem(title: "Selberg Trace Formula and Hyperbolic RH, 1956")[
    Let $h(r)$ be an even holomorphic function in a strip $|op("Im")(r)| <= 1/2 + delta$ ($delta > 0$) satisfying $|h(r)| << (1 + |r|)^(-2 - delta)$, and let $g(u) = (1 / (2 pi)) integral_(-oo)^oo h(r) e^(-i r u) dif r$ be its Fourier transform. Then
    $ sum_(j = 0)^oo h(r_j) &= (op("Area")(M)) / (4 pi) integral_(-oo)^oo r h(r) tanh(pi r) dif r \ & quad + sum_({P}) sum_(k = 1)^oo (ell(P)) / (2 sinh(k ell(P) / 2)) g(k ell(P)). $
    Consequently, $Z_Gamma (s)$ extends to an entire function of order $2$ satisfying a functional equation relating $s$ and $1 - s$, and its nontrivial zeros are precisely $s = 1/2 +- i r_j$. In particular, all but finitely many nontrivial zeros of $Z_Gamma (s)$ lie on the critical line $op("Re")(s) = 1/2$.
  ]

  Compare the Selberg trace formula term by term with the Guinand–Weil explicit formula for $zeta(s)$ (developed in Chapter 1):
  $ sum_rho h(gamma) &= h(i / 2) + h(-i / 2) - g(0) log pi \ & quad + 1 / (2 pi) integral_(-oo)^oo h(r) (Gamma' / Gamma) (1/4 + i r / 2) dif r \ & quad - 2 sum_p sum_(k = 1)^oo (log p) / (p^(k / 2)) g(k log p), $
  where $rho = 1/2 + i gamma$. The structural dictionary is uncanny:

  #figure(
    table(
      columns: (28%, 36%, 36%),
      stroke: (x: none, y: 0.35pt + luma(210)),
      inset: (x: 5pt, y: 5pt),
      align: (left, left, left),
      [*Feature*], [*Hyperbolic Surface $Gamma backslash bb(H)$*], [*Riemann Zeta Function $zeta(s)$*],
      [Geometric orbits], [Primitive closed geodesics $P$], [Rational primes $p$],
      [Orbit length], [$ell(P) = log N(P)$], [$log p$],
      [Spectral parameters], [Eigenvalues $lambda_j = 1/4 + r_j^2$ of $Delta$], [Zeros $rho = 1/2 + i gamma$ of $zeta(s)$],
      [Weyl / Arch. term], [$(op("Area")(M) / (4 pi)) integral r h(r) tanh(pi r) dif r$], [$(1 / (2 pi)) integral h(r) (Gamma' / Gamma)(1/4 + i r / 2) dif r$],
      [Orbit-sum sign], [*Plus* ($+$) on the geometric side], [*Minus* ($-$) on the prime-power side],
    ),
    caption: [Structural dictionary between the Selberg trace formula and the Guinand–Weil explicit formula.],
  )

  The single glaring discrepancy sits in the bottom row: the prime-power sum in the Guinand–Weil explicit formula carries a *minus sign*, whereas the closed-geodesic sum in the Selberg trace formula carries a *plus sign*. In the hyperbolic world, the zeros of $Z_Gamma (s)$ come from an *emission* spectrum (eigenvalues of $Delta$), and the positivity of the geometric side reflects the positivity of the heat kernel. In the arithmetic world, the minus sign suggests either a cohomological alternating sum $H^0 - H^1 + H^2$ (as in the Lefschetz trace formula over finite fields, Section 3.3) or an *absorption* spectrum (as in Connes's noncommutative geometry, below).

  === Montgomery's Pair Correlation, Dyson's GUE, and Odlyzko's Computations

  Even without an explicit Hilbert–Pólya operator in hand, one could ask a sharper question: *if* such an operator $H$ exists, what kind of statistical ensemble do its eigenvalues resemble? In 1973, Hugh Montgomery investigated the local spacing statistics of the nontrivial zeros of $zeta(s)$ assuming the Riemann Hypothesis.

  Since the density of zeros near height $T$ is $(1 / (2 pi)) log(T / (2 pi))$, one rescales the ordinates $0 < gamma_1 <= gamma_2 <= dots.c$ to have mean spacing $1$ by setting $tilde(gamma)_n = (gamma_n / (2 pi)) log(gamma_n / (2 pi))$. To probe the distribution of differences $gamma - gamma'$, Montgomery introduced the pair correlation function
  $ F(alpha) = F(alpha, T) &= (2 pi) / (T log T) sum_(0 < gamma, gamma' <= T) T^(i alpha (gamma - gamma')) w(gamma - gamma'), \ & quad w(u) = 4 / (4 + u^2). $

  #theorem(title: "Montgomery's Pair Correlation Theorem, 1973")[
    Assume the Riemann Hypothesis. Then $F(alpha)$ is real, even, and satisfies $F(alpha) >= - o(1)$ for all $alpha in bb(R)$. Moreover, uniformly for $|alpha| <= 1 - epsilon$,
    $ F(alpha) = (1 + o(1)) T^(-2 |alpha|) log T + |alpha| + o(1) quad "as" T -> oo. $
  ]

  Montgomery's proof uses the explicit formula to express $sum_gamma x^(i gamma) w(gamma - t)$ in terms of primes, and then evaluates the mean square over $t in [0, T]$—a calculation that succeeds precisely for $|alpha| < 1$, where the diagonal terms dominate. On heuristic grounds involving the Hardy–Littlewood prime-pair conjecture, Montgomery conjectured that $F(alpha) = 1 + o(1)$ for all $|alpha| >= 1$. By Fourier inversion, this predicts the exact pair correlation law for normalized zeros:

  #conjecture(title: "Montgomery's Pair Correlation Conjecture, 1973")[
    For any fixed $0 < alpha < beta$,
    $ & lim_(T -> oo) 1 / (N(T)) \#{ (gamma, gamma') : 0 < gamma, gamma' <= T, quad (2 pi alpha) / (log T) <= gamma - gamma' <= (2 pi beta) / (log T) } \ & quad = integral_alpha^beta ( 1 - ( (sin(pi u)) / (pi u) )^2 ) dif u. $
  ]

  The celebrated moment of recognition occurred during afternoon tea at the Institute for Advanced Study in Princeton in 1972. Sarvadaman Chowla introduced the young Montgomery to the physicist Freeman Dyson. When Montgomery wrote down the kernel $1 - (sin(pi u) / (pi u))^2$, Dyson recognized it on the spot: it is the exact two-point correlation function of the eigenvalues of a large random $N times N$ Hermitian matrix drawn from the *Gaussian Unitary Ensemble* (GUE), normalized to unit mean spacing! Notably, the density vanishes quadratically at $u = 0$, expressing strong *level repulsion*—zeros of $zeta(s)$ repel one another just like eigenvalues of a chaotic quantum Hamiltonian without time-reversal symmetry.

  In the 1980s and 1990s, Andrew Odlyzko put Montgomery's conjecture to an unprecedented numerical test using the Odlyzko–Schönhage fast evaluation algorithm. Computing millions of consecutive zeros near the $10^(20)$-th zero (1987) and later near the $10^(22)$-nd zero (2001), Odlyzko found astonishing agreement—down to the finest features of the nearest-neighbor spacing distribution and pair correlation—with GUE random matrix statistics. Complementary exhaustive verifications (culminating in Gourdon's $10^(13)$ zeros in 2004 and Platt–Trudgian's rigorous verification of the first $3 times 10^(12)$ zeros in 2021) confirmed that every computed zero up to height $3 times 10^(12)$ lies on the critical line and is simple.

  === The Katz–Sarnak Philosophy and Connes's Noncommutative Space

  Two major developments broadened the spectral paradigm near the turn of the millennium:

  1. *The Katz–Sarnak Philosophy (1999).* While high-lying zeros of any single primitive $L$-function exhibit universal GUE statistics (as Rudnick and Sarnak proved for $n$-level correlations in restricted ranges for all cuspidal automorphic $L$-functions on $op("GL")_m$), Nicholas Katz and Peter Sarnak discovered that the *low-lying zeros*—those within $O(1 / log C)$ of the central point $s = 1/2$ as $L$-functions vary across a natural arithmetic family—obey statistics governed by one of five classical compact matrix groups: $op("U")(N)$, $op("SO")(2 N)$, $op("SO")(2 N + 1)$, $op("O")(N)$, or $op("USp")(2 N)$. Over function fields $bb(F)_q (t)$, Katz and Sarnak proved this correspondence rigorously by identifying the symmetry type with the geometric monodromy group of the associated $ell$-adic sheaf and invoking Deligne's equidistribution theorem. Over number fields, the philosophy predicts, for example, that the family of quadratic Dirichlet $L$-functions $L(s, chi_d)$ has symplectic symmetry ($op("USp")$), whereas families of weight-$k$ holomorphic cusp forms have orthogonal symmetry ($op("O")$).

  2. *Connes's Noncommutative Geometry (1999).* To account for the minus sign in the Guinand–Weil explicit formula, Alain Connes constructed a spectral realization of the zeros of $zeta(s)$ on the *adele class space* $X_bb(Q) = bb(A)_bb(Q) / bb(Q)^times$, a singular quotient treated via noncommutative geometry. Acting on a suitable Hilbert space of functions on $X_bb(Q)$, the scaling flow $u |-> lambda u$ ($lambda in bb(R)_>0$) has a continuous spectrum from which the nontrivial zeros of $zeta(s)$ appear as missing frequencies—an *absorption spectrum* rather than an emission spectrum. Connes proved that the Riemann Hypothesis is equivalent to the validity of a Lefschetz-style trace formula on $X_bb(Q)$, which in turn translates directly into Weil's positivity criterion (Section 3.4).

  The spectral and random-matrix paradigms yielded profound insights into the fine distribution of zeros and linked number theory to quantum chaos and operator algebras. Yet constructing a genuine self-adjoint Hilbert–Pólya operator directly—or proving Connes's trace formula unconditionally—remained out of reach. For a *completed* proof of an analogue of the Riemann Hypothesis, mathematicians had to turn to algebraic geometry over finite fields.

  // ==========================================================================
  == The Function Field Revolution
  // ==========================================================================

  The single greatest triumph of twentieth-century number theory was the formulation and complete proof of the Riemann Hypothesis for algebraic varieties over finite fields. Its trajectory—from Artin and Hasse to Weil, Grothendieck, and Deligne—transformed algebraic geometry from its foundations up, while simultaneously crystallizing the exact geometric obstruction that separates function fields from the ring of integers $bb(Z)$.

  === Artin and Hasse: Curves and Elliptic Curves over $bb(F)_q$

  In his 1924 doctoral thesis, Emil Artin initiated the arithmetic study of quadratic extensions of the polynomial ring $bb(F)_q [t]$, the function-field analogue of quadratic number fields. For any smooth, projective, geometrically connected curve $C$ of genus $g$ over the finite field $bb(F)_q$, one defines its *congruence zeta function* by the Euler product over all closed points $v in |C|$ (the analogues of prime ideals):
  $ zeta_C (s) = product_(v in |C|) (1 - N(v)^(-s))^(-1), quad op("Re")(s) > 1, $
  where $N(v) = q^(op("deg")(v))$ is the cardinality of the residue field at $v$. Setting $T = q^(-s)$ converts $zeta_C (s)$ into the formal power series
  $ Z_C (T) = exp ( sum_(m = 1)^oo (N_(q^m) (C)) / m T^m ), $
  where $N_(q^m) (C) = \# C(bb(F)_(q^m))$ is the number of rational points of $C$ over the degree-$m$ extension $bb(F)_(q^m)$. Using the Riemann–Roch theorem on $C$, F. K. Schmidt (1931) proved that $Z_C (T)$ is a rational function of the form
  $ Z_C (T) = (P_C (T)) / ((1 - T)(1 - q T)), $
  where $P_C (T) = product_(i = 1)^(2 g) (1 - alpha_i T) in bb(Z)[T]$ is a polynomial of degree $2 g$ satisfying the functional equation $Z_C (1 / (q T)) = q^(1 - g) T^(2 - 2 g) Z_C (T)$. Taking logarithmic derivatives yields the exact point-counting formula
  $ N_(q^m) (C) = q^m + 1 - sum_(i = 1)^(2 g) alpha_i^m. $
  Thus the *Riemann Hypothesis for $C$*—the assertion that all zeros of $zeta_C (s)$ satisfy $op("Re")(s) = 1/2$, i.e., $|alpha_i| = q^(1/2)$ for every $i = 1, dots.c, 2 g$—is equivalent to the square-root error bound
  $ |N_(q^m) (C) - (q^m + 1)| <= 2 g q^(m / 2) quad "for all" m >= 1. $

  In 1933 (with full details published in 1936), Helmut Hasse proved the Riemann Hypothesis for all curves of genus $g = 1$, i.e., elliptic curves $E$ over $bb(F)_q$.

  #theorem(title: "Hasse's Theorem, 1933–1936")[
    Let $E$ be an elliptic curve defined over the finite field $bb(F)_q$. Then
    $ |N_q (E) - (q + 1)| <= 2 sqrt(q). $
  ]

  Hasse's proof is a jewel of algebraic elegance that already reveals why *positivity of a quadratic form* yields the Riemann Hypothesis.

  #proof[
    Let $op("Frob")_q : E -> E$ denote the $q$-power Frobenius endomorphism $(x, y) |-> (x^q, y^q)$ of $E$ over $overline(bb(F))_q$. An $overline(bb(F))_q$-point $P in E(overline(bb(F))_q)$ lies in $E(bb(F)_q)$ if and only if $op("Frob")_q (P) = P$, that is, $P in ker(1 - op("Frob")_q)$. Because the differential of $op("Frob")_q$ vanishes identically in characteristic $p$, the endomorphism $1 - op("Frob")_q$ is separable, and therefore
    $ N_q (E) = \# ker(1 - op("Frob")_q) = op("deg")(1 - op("Frob")_q). $
    On the endomorphism ring $op("End")(E)$, the degree map $phi |-> op("deg")(phi)$ is a *positive-definite quadratic form*: for all integers $m, n in bb(Z)$, the endomorphism $m - n op("Frob")_q$ has nonnegative degree, and the bilinear pairing $chevron.l phi, psi chevron.r = op("deg")(phi + psi) - op("deg")(phi) - op("deg")(psi)$ expands $op("deg")(m - n op("Frob")_q)$ as
    $ & 0 <= op("deg")(m - n op("Frob")_q) \ & quad = m^2 op("deg")(1) - m n (op("deg")(1) + op("deg")(op("Frob")_q) - op("deg")(1 - op("Frob")_q)) \ & quad + n^2 op("deg")(op("Frob")_q). $
    Since $op("deg")(1) = 1$, $op("deg")(op("Frob")_q) = q$, and $op("deg")(1 - op("Frob")_q) = N_q (E)$, putting $a_q = q + 1 - N_q (E)$ gives
    $ m^2 - a_q m n + q n^2 >= 0 quad "for all" m, n in bb(Z). $
    By homogeneity, this real binary quadratic form is positive semidefinite on $bb(R)^2$, so its discriminant must be nonpositive:
    $ a_q^2 - 4 q <= 0, quad "i.e.," quad |N_q (E) - (q + 1)| = |a_q| <= 2 sqrt(q). $
  ]

  === André Weil: Castelnuovo Positivity on $C times C$

  For curves of higher genus $g >= 2$, $C$ is no longer a group, so one cannot form the endomorphism $m - n op("Frob")_q$ directly on $C$. In April 1940, while imprisoned in Bonne-Nouvelle prison in Rouen awaiting court-martial for refusing military service, André Weil realized how to generalize Hasse's positivity argument to arbitrary genus $g$: one replaces endomorphisms of $E$ either by endomorphisms of the Jacobian variety $op("Jac")(C)$ or, more directly, by *correspondences*—divisors on the product surface $S = C times_(bb(F)_q) C$.

  #theorem(title: "Weil's Riemann Hypothesis for Curves, 1940–1948")[
    Let $C$ be a smooth, projective, geometrically connected curve of genus $g$ over $bb(F)_q$. Then every reciprocal root $alpha_i$ ($1 <= i <= 2 g$) of $P_C (T)$ satisfies $|alpha_i| = q^(1/2)$, and consequently
    $ |N_(q^m) (C) - (q^m + 1)| <= 2 g q^(m / 2) quad "for all" m >= 1. $
  ]

  The heart of Weil's 1948 geometric proof is *Castelnuovo's positivity theorem* (the Hodge index theorem on the surface $S = C times C$). Let $V = \{P_0\} times C$ and $H = C times \{P_0\}$ denote a vertical and a horizontal fiber on $S$, so that $V^2 = H^2 = 0$ and $V dot.c H = 1$. Any divisor $D$ on $S$ has a bidegree $(d_1, d_2) = (D dot.c H, D dot.c V)$, and its "primitive" projection orthogonal to $V$ and $H$ is $D_0 = D - d_2 H - d_1 V$, with self-intersection
  $ D_0^2 = D^2 - 2 d_1 d_2. $
  Castelnuovo's theorem asserts that the intersection pairing is *negative semidefinite* on the subspace orthogonal to $V$ and $H$:
  $ D^2 - 2 d_1 d_2 <= 0 quad "for every divisor" D "on" C times C. $
  Now apply Castelnuovo's inequality to linear combinations $D = m Delta + n Gamma_F$ of the diagonal $Delta subset.eq C times C$ and the graph $Gamma_F = \{ (x, op("Frob")_q (x)) \}$ of the Frobenius morphism! A direct geometric computation yields:
  - $Delta$ has bidegree $(1, 1)$ and self-intersection $Delta^2 = 2 - 2 g$ (the Euler characteristic of $C$);
  - $Gamma_F$ has bidegree $(1, q)$ and self-intersection $Gamma_F^2 = q (2 - 2 g)$;
  - the intersection number $Delta dot.c Gamma_F$ counts the fixed points of $op("Frob")_q$, so $Delta dot.c Gamma_F = N_q (C)$ (since the intersection is transverse).

  Computing $D_0^2 = D^2 - 2 d_1 d_2$ for $D = m Delta + n Gamma_F$ (which has bidegree $(m + n, m + q n)$) gives
  $ 0 >= D_0^2 &= m^2 (2 - 2 g - 2) + 2 m n (N_q (C) - (q + 1)) \ & quad + n^2 (q (2 - 2 g) - 2 q) \ &= - 2 g m^2 + 2 (N_q (C) - (q + 1)) m n - 2 g q n^2. $
  Dividing by $-2$, the quadratic form
  $ g m^2 - (N_q (C) - (q + 1)) m n + g q n^2 >= 0 $
  is positive semidefinite for all $m, n in bb(Z)$! Its discriminant is therefore nonpositive:
  $ (N_q (C) - (q + 1))^2 - 4 g^2 q <= 0, quad "so" quad |N_q (C) - (q + 1)| <= 2 g sqrt(q). $
  Applying the same inequality over every finite extension $bb(F)_(q^m)$ forces $|N_(q^m) (C) - (q^m + 1)| <= 2 g q^(m / 2)$ for all $m >= 1$. By a standard lemma on power sums (compare Exercise 3.5), this forces $|alpha_i| <= q^(1/2)$ for every $i$, and the functional equation $alpha_i |-> q / alpha_i$ forces exact equality $|alpha_i| = q^(1/2)$.

  === The Weil Conjectures, Grothendieck's Vision, and Deligne's Proofs

  In 1949, Weil extrapolated from curves and diagonal hypersurfaces to formulate his sweeping conjectures for smooth projective varieties $X$ of arbitrary dimension $d$ over $bb(F)_q$, with zeta function
  $ Z_X (T) = exp ( sum_(m = 1)^oo (N_(q^m) (X)) / m T^m ). $
  Weil conjectured four properties: (1) *rationality* of $Z_X (T)$ as an alternating product $product_(i=0)^(2 d) P_i (T)^((-1)^(i+1))$ with $P_i (T) in bb(Z)[T]$; (2) a *functional equation* relating $Z_X (1 / (q^d T))$ to $Z_X (T)$; (3) the *Riemann Hypothesis*, asserting that every reciprocal root $alpha$ of $P_i (T)$ is an algebraic integer with $|alpha| = q^(i / 2)$ (for every complex embedding); and (4) the *Betti number comparison*, asserting that when $X$ lifts to a smooth complex projective variety $tilde(X)$, $op("deg") P_i$ equals the $i$-th topological Betti number $b_i (tilde(X)(bb(C)))$.

  Weil observed that all four conjectures would follow naturally if algebraic varieties over finite fields admitted a "Weil cohomology theory" $H^i (X)$ enjoying the Lefschetz trace formula, Poincaré duality, and a hard Lefschetz / Hodge index theorem. In the 1960s, Alexander Grothendieck and his school (Artin, Verdier, Deligne, Katz) rebuilt algebraic geometry from the ground up to construct precisely such a theory: *$ell$-adic étale cohomology* $H^i_("ét") (overline(X), bb(Q)_ell)$ (for any prime $ell != p$). Grothendieck proved the Lefschetz trace formula
  $ N_(q^m) (X) = sum_(i = 0)^(2 d) (-1)^i op("Tr") ( op("Frob")_q^m mid(|) H^i_("ét") (overline(X), bb(Q)_ell) ) $
  and Poincaré duality, establishing rationality (already proved earlier by Dwork in 1960 via $p$-adic analysis) and the functional equation. To prove the Riemann Hypothesis, Grothendieck proposed his *Standard Conjectures* on algebraic cycles, which would endow $H^i_("ét") (overline(X), bb(Q)_ell)$ with an algebraic Hodge index positivity analogous to Castelnuovo's theorem.

  The Standard Conjectures remain open to this day. In a tour de force that astonished the mathematical world, Pierre Deligne proved the Riemann Hypothesis for all smooth projective varieties over $bb(F)_q$ in 1974 (*Weil I*)—and a far more general purity and mixed-weight theorem for arbitrary $ell$-adic sheaves in 1980 (*Weil II*)—completely bypassing the Standard Conjectures!

  Deligne's strategy in *Weil I* combined algebraic geometry with a classical analytic device borrowed from Rankin's 1939 work on Ramanujan's tau function. Slicing $X$ by a Lefschetz pencil of hyperplane sections reduces the problem to studying a variation of cohomology $cal(F) = R^n f_* bb(Q)_ell$ over a punctured base curve $U subset.eq bb(P)^1$. To force positivity without an algebraic Hodge index theorem, Deligne raised the sheaf $cal(F)$ to an *even tensor power* $cal(F)^(times.o 2 k)$. Over the base curve $U$, the $L$-function $L(U, cal(F)^(times.o 2 k), T)$ has positive real Frobenius traces at every closed point (since the trace of an even tensor power is a $2 k$-th power, and the monodromy pairing makes the eigenvalues real in the relevant sense). Combining this positivity with Kazhdan–Margulis big monodromy and the rationality of $L(U, cal(F)^(times.o 2 k), T)$, Deligne forced all eigenvalues of Frobenius to have absolute value $q^(n / 2)$ as $k -> oo$! In *Weil II* (1980), Deligne generalized this to arbitrary schemes of finite type over $bb(F)_q$, replacing Lefschetz pencils with an $ell$-adic Fourier transform (later simplified by Laumon) and—in a remarkable echo of 1896—an analogue of the Hadamard–de la Vallée Poussin nonvanishing argument on the boundary of convergence of $L$-functions.

  #insight-box(title: "Why the Geometric Proof Resists Translation to Spec Z")[
    Given the spectacular success of Weil, Grothendieck, and Deligne over $bb(F)_q$, it is natural to ask why their proof could not simply be translated to the classical Riemann zeta function $zeta(s) = zeta_(op("Spec") bb(Z)) (s)$. The obstruction is immediate and fundamental.

    For a curve $C$ over $bb(F)_q$, the structure morphism $C -> op("Spec") bb(F)_q$ maps to a *field*, so the fiber product
    $ C times_(op("Spec") bb(F)_q) C $
    is a two-dimensional *surface*. It is on this two-dimensional surface that the diagonal $Delta$ and the Frobenius graph $Gamma_F$ intersect, and it is the Hodge index theorem on this surface that produces Castelnuovo's positivity inequality.

    For the arithmetic curve $X = op("Spec") bb(Z)$, however, the base object in the category of schemes is $op("Spec") bb(Z)$ itself (since $bb(Z)$ is the initial commutative ring). Consequently, the scheme-theoretic fiber product collapses back to dimension one:
    $ op("Spec") bb(Z) times_(op("Spec") bb(Z)) op("Spec") bb(Z) tilde.equiv op("Spec") bb(Z). $
    There is no "field with one element" $bb(F)_1$ inside ordinary commutative algebra over which $op("Spec") bb(Z) times_(op("Spec") bb(F)_1) op("Spec") bb(Z)$ becomes a genuine arithmetic surface carrying a Frobenius correspondence and an intersection pairing with Castelnuovo positivity. Despite decades of imaginative proposals for $bb(F)_1$-geometry (Tits, Manin, Soulé, Borger, Connes–Consani), no framework succeeded in constructing a working intersection theory on $op("Spec") bb(Z) times_(bb(F)_1) op("Spec") bb(Z)$.
  ]

  // ==========================================================================
  == Elementary and Arithmetic-Geometric Detours
  // ==========================================================================

  Faced with the collapse of $op("Spec") bb(Z) times_(op("Spec") bb(Z)) op("Spec") bb(Z)$, number theorists explored two distinct alternatives: (i) *positivity and approximation criteria* that reformulate the Riemann Hypothesis directly in analytic terms over $bb(Z)$, and (ii) *elementary proofs over $bb(F)_q$* that avoid the product surface $C times C$ altogether.

  === Weil's Positivity Criterion, Li's Criterion, and Nyman–Beurling

  In 1952, André Weil observed that the Guinand–Weil explicit formula can be turned into a quadratic-form positivity criterion that mimics Castelnuovo's positivity without mentioning any surface. For a smooth, compactly supported function $f : bb(R)_(> 0) -> bb(C)$, define its involution $tilde(f)(x) = x^(-1) overline(f(x^(-1)))$ and multiplicative convolution
  $ (f * tilde(f))(x) = integral_0^oo f(x y) overline(f(y)) dif y. $
  Let $hat(Phi)(s) = integral_0^oo Phi(x) x^(s - 1) dif x$ denote the Mellin transform, and define the *Weil functional* $W(Phi)$ as the spectral side of the explicit formula:
  $ W(Phi) = sum_rho hat(Phi)(rho), $
  which equals $hat(Phi)(0) + hat(Phi)(1)$ minus the prime-power and archimedean terms of the explicit formula.

  #theorem(title: "Weil's Positivity Criterion, 1952; Bombieri, 2000")[
    The Riemann Hypothesis holds if and only if
    $ W(f * tilde(f)) >= 0 $
    for every smooth compactly supported function $f in C_c^oo (bb(R)_(> 0))$ (or more generally, for every function in a suitable Schwartz-type test space).
  ]

  The necessity is immediate: if every zero has the form $rho = 1/2 + i gamma$ with $gamma in bb(R)$, then $hat((f * tilde(f)))(1/2 + i gamma) = |hat(f)(1/2 + i gamma)|^2 >= 0$, so $W(f * tilde(f)) = sum_gamma |hat(f)(1/2 + i gamma)|^2 >= 0$. Conversely, if an off-line zero $rho_0 = beta_0 + i gamma_0$ ($beta_0 > 1/2$) existed, one could choose $f$ so that $hat(f)(s)$ peaks sharply near $rho_0$ and $1 - overline(rho_0)$ with opposite phases, forcing $W(f * tilde(f)) < 0$. Enrico Bombieri (2000) gave a streamlined exposition of Weil's criterion and analyzed its local-to-global structure, showing that if the Weil functional is positive on a sufficiently rich family of compactly supported test functions, zero-free strips follow directly—an observation that plays a direct role in the early stages of Alpöge's timeline (Section 3.5).

  A discrete algebraic cousin of Weil's criterion was discovered by Xian-Jin Li in 1997.

  #theorem(title: "Li's Criterion, 1997")[
    For each integer $n >= 1$, define the $n$-th Li coefficient by
    $ lambda_n = sum_rho ( 1 - (1 - 1 / rho)^n ) = 1 / ((n - 1)!) (dif^n) / (dif s^n) [ s^(n - 1) log xi(s) ]_(s = 1), $
    where the sum over nontrivial zeros is taken symmetrically ($rho$ paired with $1 - rho$). Then the Riemann Hypothesis holds if and only if $lambda_n >= 0$ for every $n >= 1$.
  ]

  #proof(title: "Necessity and Sufficiency Sketch")[
    The Möbius transformation $z |-> 1 - 1 / z$ maps the critical line $op("Re")(z) = 1/2$ onto the unit circle $|w| = 1$, maps the right half-plane $op("Re")(z) > 1/2$ into the open unit disk $|w| < 1$, and maps $op("Re")(z) < 1/2$ into $|w| > 1$. If RH holds, then $|1 - 1 / rho| = 1$ for every $rho$, so $op("Re")(1 - (1 - 1 / rho)^n) >= 0$ term by term, whence $lambda_n >= 0$. Conversely, if there exists a zero $rho_0$ with $op("Re")(rho_0) < 1/2$, then $w_0 = 1 - 1 / rho_0$ satisfies $|w_0| > 1$. Choosing $rho_0$ to maximize $|w_0|$, the terms $- w_0^n - overline(w)_0^n$ dominate $lambda_n$ for large $n$ and oscillate in sign with exponentially growing amplitude, forcing $lambda_n < 0$ for infinitely many $n$.
  ]

  A third classical reformulation recasts the Riemann Hypothesis as an approximation problem in Hilbert space $L^2 (0, 1)$. For $alpha in (0, 1]$, define the dilated fractional-part function
  $ rho_alpha (x) = { alpha / x } - alpha { 1 / x } quad (0 < x <= 1), $
  where $\{ u \} = u - floor(u)$ is the fractional part of $u$.

  #theorem(title: "Nyman–Beurling–Báez-Duarte Criterion, 1950–2003")[
    Let $cal(B) = op("span")_bb(C) \{ rho_alpha : 0 < alpha <= 1 \} subset.eq L^2 (0, 1)$, and let $cal(B)_bb(N) = op("span")_bb(C) \{ rho_(1/k) : k in bb(Z)_(>= 1) \}$ be the smaller subspace spanned only by reciprocal-integer dilates. The following are equivalent:
    1. The Riemann Hypothesis holds.
    2. *(Nyman 1950, Beurling 1955)* The constant function $1_((0, 1])$ lies in the $L^2 (0, 1)$-closure of $cal(B)$.
    3. *(Báez-Duarte 2003)* The constant function $1_((0, 1])$ lies in the $L^2 (0, 1)$-closure of $cal(B)_bb(N)$.
  ]

  The Mellin transform of $rho_alpha (x)$ is $- (alpha^s - alpha) zeta(s) / s$ (for $op("Re")(s) > 0$), so approximating $1_((0, 1])$ in $L^2 (0, 1)$ by a linear combination $sum c_k rho_(1/k)$ is equivalent via Plancherel's theorem to approximating $1 / zeta(s)$ in the Hardy space on the half-plane $op("Re")(s) > 1/2$ by Dirichlet polynomials—a direct link to the mollifiers of Section 3.1. Yet like Weil positivity and Li's criterion, the Nyman–Beurling–Báez-Duarte reformulation proved just as difficult to verify directly as the Riemann Hypothesis itself.

  === Stepanov's Elementary Method and Bombieri's Simplification

  Meanwhile, in 1969, a completely unexpected development occurred back in the function-field world. Sergei Stepanov discovered a wholly *elementary* proof of Weil's Riemann Hypothesis for hyperelliptic curves $y^2 = f(x)$ over $bb(F)_q$, using neither étale cohomology, nor Jacobian varieties, nor intersection theory on the surface $C times C$. In 1974, Enrico Bombieri published a celebrated Bourbaki seminar exposition that streamlined Stepanov's ideas and extended them to arbitrary smooth projective curves $C$ of genus $g$ over $bb(F)_q$.

  Stepanov's method is the direct conceptual ancestor of the Alpöge–Claude proof, and we will develop it in complete, self-contained detail in Chapter 4. Here we highlight its core mechanism so that its structural contrast with Weil's geometric proof stands out in sharp relief.

  #theorem(title: "Stepanov–Bombieri Multiplicity Paradigm, 1969–1974")[
    Let $C$ be a smooth projective curve of genus $g$ over $bb(F)_q$ (with $q$ a sufficiently large even power of $p$, or after base change). One can prove the upper bound
    $ N_q (C) <= q + 1 + 2 g sqrt(q) $
    entirely on $C$ itself—without ever passing to the product surface $C times C$—by constructing a nonzero rational function $Phi in bb(F)_q (C)$ whose pole order is bounded above and which vanishes to *high multiplicity* $m approx sqrt(q)$ at every $bb(F)_q$-rational point of $C$.
  ]

  How does one force a single auxiliary function $Phi in bb(F)_q (C)$ to vanish to high multiplicity $m$ at every $bb(F)_q$-rational point without knowing where those points are? The trick exploits the Frobenius map $F(x) = x^q$ in characteristic $p$ together with *Hasse–Schmidt derivatives* $D^((j))$ (which satisfy $D^((j)) (x^k) = binom(k, j) x^(k - j)$ and therefore do not vanish identically for $j >= p$, unlike ordinary iterated derivatives $d^j / d x^j$).

  In outline, fix a base point $oo in C(bb(F)_q)$ and construct an auxiliary function of the separated form
  $ Phi(P) = sum_(i = 0)^(I) sum_(j = 0)^(J) c_(i, j) f_i (P) g_j (P)^q, $
  where $\{f_i\}$ and $\{g_j\}$ are bases of Riemann–Roch spaces $cal(L)(A dot.c oo)$ and $cal(L)(B dot.c oo)$ of controlled pole orders $A$ and $B$. Because $g_j (P)^q$ has *zero* Hasse derivative of order $1 <= r < q$ (more precisely, $D^((r)) (g^q) = 0$ whenever $p$ does not divide $r$, and more generally $g_j (P)^q = g_j (P)$ at every $bb(F)_q$-rational point $P$!), requiring that $D^((r)) Phi(P) = 0$ for all $0 <= r < m$ at every $P in C(bb(F)_q)$ reduces to requiring that the much smaller-degree functions
  $ sum_(i = 0)^I sum_(j = 0)^J c_(i, j) (D^((r)) f_i)(P) g_j (P) $
  vanish *identically* on $C$ for each $0 <= r < m$!

  Now count linear equations versus unknowns:
  - The number of free coefficients $c_(i, j) in bb(F)_q$ is roughly $I dot.c J approx A B$ (by Riemann–Roch, neglecting $g$).
  - For each $0 <= r < m$, the identity $sum c_(i, j) (D^((r)) f_i) g_j equiv 0$ imposes at most $A + B + O(r)$ linear constraints, for a total of roughly $m (A + B)$ linear equations.
  - Whenever $A B > m (A + B)$, linear algebra guarantees a *nonzero* solution $(c_(i, j))$.
  - Provided $Phi$ is not identically zero (which is ensured by keeping $A < q$, so the $f_i$ are linearly independent over $bb(F)_q (C)^q$), the total number of zeros of $Phi$ counted with multiplicity cannot exceed its total pole order:
    $ m dot.c N_q (C) <= op("deg")_(oo) (Phi) <= A + q B. $

  Optimize the parameters! Choosing $A approx m sqrt(q)$ and $B approx m$ (so $A B approx m^2 sqrt(q)$ exceeds $m (A + B) approx m^2 sqrt(q)$ once adjusted by $g$), the pole-order bound becomes
  $ N_q (C) <= (A + q B) / m approx (m sqrt(q) + q m) / m = q + O(sqrt(q))! $
  More carefully, keeping track of the genus $g$ and optimizing the multiplicity at $m approx sqrt(q)$ (with $A approx q$ and $B approx sqrt(q)$) recovers the sharp Weil bound $N_q (C) <= q + 1 + 2 g sqrt(q)$—and applying the same upper bound to finite unramified covers of $C$ yields the matching lower bound $N_q (C) >= q + 1 - 2 g sqrt(q)$.

  #insight-box(title: "Multiplicity as a Substitute for a Second Dimension")[
    Stepanov's method teaches a profound structural lesson: *you do not need the two-dimensional product surface $C times C$ to prove the Riemann Hypothesis for $C$.* High multiplicity $m approx sqrt(q)$ on the one-dimensional object $C$ itself plays the exact same role as the Hodge index theorem on $C times C$.

    This immediately reframes the obstruction for $op("Spec") bb(Z)$ in a completely new light! Rather than trying to invent a mythical field with one element $bb(F)_1$ to manufacture a two-dimensional surface $op("Spec") bb(Z) times_(bb(F)_1) op("Spec") bb(Z)$, one can ask a far more concrete question:

    *Can one run a Stepanov-type multiplicity argument directly over $bb(Z)$?*

    At first glance, the answer still looks hopeless: in Stepanov's proof, multiplicity $m$ is detected by applying $m$ Hasse derivatives $D^((0)), D^((1)), dots.c, D^((m-1))$ to functions on $C$. Over $bb(Z)$, what could possibly mean "differentiating whole numbers" $m approx sqrt(X)$ times? That exact question—and its astonishing answer—is the story of November 2026.
  ]

  // ==========================================================================
  == The November 2026 Breakthrough
  // ==========================================================================

  On November 20, 2026, Levent Alpöge released a brief, candid four-page announcement titled *Remark*, accompanied by a fourteen-part archive (`lean.tar.gz.part01` through `part14`) containing a complete, assumption-free Lean 4 formalization of the Riemann Hypothesis and the Generalized Riemann Hypothesis (GRH) for all Dirichlet $L$-functions, discovered and formalized in collaboration with Anthropic's AI system Claude. Within forty-eight hours, independent verification efforts coordinated by the Lean Focused Research Organization (FRO), the Mathlib Initiative, and researchers worldwide confirmed that the library compiles cleanly against Mathlib's longstanding formal statement `RiemannHypothesis`, relies solely on Lean's three standard logical axioms (`propext`, `Quot.sound`, `Classical.choice`), and passes independent kernel checks (`comparator`, `nanoda`, `con-leche`, `con-ron`).

  To understand *how* the proof works—which is the task of Parts II and III of this monograph—it is extraordinarily illuminating to trace its mathematical genesis as recorded in Alpöge's *Remark*.

  === From the Toy Setting to the "Sign-Only" Proof of Weil and Deligne

  As Alpöge recounts, his long-term preparation since his student days had been aimed at acquiring broad familiarity across analytic number theory, automorphic forms, arithmetic geometry, and Iwasawa theory so that he could recognize structural bridges when the moment arrived. Working with Claude in the autumn of 2026, he began by examining two ideas in a "toy setting":
  1. An elementary argument (related to Siegel's method and the $(2, 3, 6)$-triangle group) that Alpöge immediately recognized as *"Stepanov without multiplicity"*—a multiplicity-$1$ determinant positivity argument.
  2. A striking *"sign-only"* proof of the Weil and Deligne bounds over finite fields of the shape $q N = M^k + R$. Concretely, considering the exponential sum over the "path" quadric $x_1 x_2 + x_3 x_4 + dots.c + x_(k - 1) x_k$,
     $ sum_(h, x_1, dots.c, x_k) t(x_1) dots.c t(x_k) dot.c e_q ( h (x_1 x_2 + dots.c + x_(k - 1) x_k) ), $
     summing over $h$ first gives the left-hand side $q N$ with a definite sign (coming from middle cohomology via Bertini's theorem), while on the right-hand side the zero-mode $h = 0$ contributes $M^k$ with the *opposite* sign, and iterating Parseval's identity $k$ times bounds the remainder $R$ to square-root quality! Opposite signs forbid cancellation among inverse Frobenius roots, yielding Weil's bound by pure sign comparison.

  Crucially, Alpöge saw how to interpret the definite sign of $q N = M^k + R$ over a function field as *automorphy* over $bb(Z)$: because the Möbius function (and its relatives) can be realized automorphically via theta functions (for instance on the sixfold cover of $op("GL")_5$ as a period integral of theta series), the quadric carries a natural interpretation on a complex-multiplication (CM) elliptic curve $bb(C) / bb(Z)[omega]$, placing the Poincaré bundle on the edges of the graph to produce theta functions.

  === The Six-Week Timeline (October 6 – November 16, 2026)

  In Section 2 of *Remark*, Alpöge published a 20-step chronological log—reconstructed with Claude—tracing the whirlwind six-week discovery from the first Stepanov determinant on October 6, 2026, to the completion of GRH on November 16, 2026. Rather than a linear progression, the timeline unfolds in three intense waves of insight.

  *Wave I: Stepanov Determinants, CM Divisibility, and Positivity (October 6–14, 2026).*
  On October 6, four foundational pillars appeared almost simultaneously: (1) a *Stepanov determinant* framework; (2) the positivity $W(1_S) >= 0$ derived via a determinant and interpreted as "Stepanov with multiplicity $1$"—with the immediate imperative to *bootstrap* multiplicity; (3) the introduction of an *Iwasawa tower* as the number-field analogue of pigeonholing over field extensions $bb(F)_(q^n) / bb(F)_q$; and (4) *Bost's slope inequality* from Arakelov geometry to play the role of the degree/pole-order upper bound.

  Two days later (October 8), Alpöge and Claude observed that positivity of the Weil functional on a two-step test function,
  $ W ( 1_((0, 1]) + (tilde.op X^eta) dot.c 1_((0, 1/X]) ) >= 0, $
  forces a zero-free strip $op("Re")(rho) > 1 - eta$ (and hence $op("Re")(rho) <= 1 - eta$ by symmetry, pushing toward $1/2$ as $eta -> 1/2$). On October 9 came the key *local arithmetic* source of divisibility—the number-field replacement for Hasse derivatives in characteristic $p$: on a CM elliptic curve over a CM field $K$, for a prime $p$ *inert* in $K$, the invariant derivation $D$ satisfies $D^p equiv 0 mod p$, and consequently the normalized derivatives of the theta function at the origin satisfy the sharp $p$-adic divisibility
  $ (D^a dot.c theta(0)) / (Omega^a) quad "is divisible by" quad p^(a / p + a / p^3 + dots.c - O(log a)), $
  where $Omega$ is the fundamental period. By October 14, the determinants for $W(dot.c)$ were recognized as containing *Gan–Gross–Prasad (GGP) periods* (with values $0, 1$ corresponding to interlacing weights, or up to $m$ non-interlacing weights), while a *relative trace formula* in a shifted half-plane—using the automorphy of $mu$ on the sixfold cover of $op("GL")_5$ and Cauchy–Schwarz reduction to the norm of a projected Poincaré series—supplied approximate orthogonality of the columns of the integral structure.

  *Wave II: The Switch to $Lambda$ and Behrend's Iwasawa Tower (October 19–20, 2026).*
  On October 19, the quadric $q N = M^k + R$ interpretation crystallized alongside a surprising combinatorial choice of the Iwasawa tower using *Behrend's sphere theorem* (from additive combinatorics, avoiding arithmetic progressions in the twist parameters). On October 20, Alpöge and Claude made a decisive strategic pivot: switching definitively from Möbius sums to the smoothed von Mangoldt sum
  $ & S_Lambda (X) - X log X + (1 + gamma) X \ & quad = sum_(n <= X) Lambda(n) ( X / n - 1 )_+ - X log X + (1 + gamma) X, $
  matching the exact sign structure of the Guinand–Weil explicit formula (where the variance test-function trick makes the expression trace-formula-like).

  *Wave III: Chained Theta Lifts, Seesaw Duality, and Victory (November 15–16, 2026).*
  The decisive breakthrough arrived once Alpöge and Claude saw *multiplicity $2$* on the orthogonal group $O(2, n)$ via a "natively-automorphic" determinant. At that point, as Alpöge wrote, *"winning more multiplicity with more theta lifts, we were going to win"*—and on November 15, Claude proposed the move that Alpöge singled out as *"one line which will suffice to make fellow mathematicians fall out of their chairs"*:

  To synthesize multiplicity $m$ natively in the automorphic category, one chains $m$ *iterated theta lifts* between totally definite unitary groups,
  $ U(X_0) -> U(X_1) -> dots.c -> U(X_m), $
  inducing at each step the isobaric automorphic transfer
  $ pi |-> pi plus.square mu_j [t]. $
  And for the von Mangoldt sum of length $X$, what length $m$ of chain of theta lifts did Claude propose?
  $ m approx sqrt(X). $
  As Alpöge parenthetically exclaimed: *"And yet, what else could it be?"* Just as Stepanov's auxiliary polynomial over $bb(F)_q$ attains the square-root Weil bound precisely when its multiplicity is chosen at $m approx sqrt(q)$, the automorphic chain of theta lifts over $bb(Z)$ attains the square-root Riemann Hypothesis precisely when the chain length is $m approx sqrt(X)$!

  In a torrent of breakthroughs on November 15, every remaining obstacle fell into place:
  - *Divisibility and norms:* Norms of the lifts, level control, and cancellation of order-$m$ terms were established with proven divisibility via the Chowla–Selberg formula, Weyl's law, and the Siegel mass formula, yielding a sufficient lower bound on the divisibility of the $m$-fold iterated lift.
  - *Seesaw duality:* Using the *seesaw identity* and the Rallis inner product formula, the period of the iterated lift was shown to be a *Bessel period* independent of the auxiliary Hecke characters $mu_j$.
  - *Overcoming the $2/3$ barrier:* A precise accounting of the Arakelov "cost" of each theta lift revealed that a naive single-character argument would stall at $op("Re")(s) = 2/3$! To break past $2/3$ all the way to $1/2$, Alpöge and Claude glued together an *integral structure across Hecke characters*—performing an extra averaging ("gcd" / "division") that removes the spurious factor.
  - *Weakened Vandiver:* For the residual Galois cohomology classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ that could not be annihilated by twisting, they proved a significant *weakening of Vandiver's conjecture* (which also implies the vanishing of several $K$-groups of $bb(Z)$).
  - *Covolumes and congruences:* Explicit computation of covolumes, the index of theta series, and congruences between lifts and automorphic forms closed the loop.

  On November 16, 2026, the proof of the Generalized Riemann Hypothesis—and with it the Riemann Hypothesis—was complete.

  #figure(
    table(
      columns: (15%, 27%, 58%),
      stroke: (x: none, y: 0.35pt + luma(210)),
      inset: (x: 4pt, y: 4.5pt),
      align: (left, left, left),
      [*Date (2026)*], [*Milestone*], [*Mathematical Role in the Proof*],
      [Oct 6], [Stepanov determinant; $W(1_S) >= 0$; Iwasawa tower; Bost slope inequality], [Multiplicity-$1$ positivity framework, number-field analogue of $bb(F)_(q^n) / bb(F)_q$, and Arakelov upper bound replacing polynomial degree],
      [Oct 8], [Two-step Weil test function], [$W(1_((0, 1]) + (tilde.op X^eta) 1_((0, 1/X])) >= 0$ yields zero-free strip $> 1 - eta$],
      [Oct 9], [CM derivation $D^p equiv 0$], [Local $p$-adic divisibility of $D^a theta(0) / Omega^a$ at inert primes $p$ in CM field $K$],
      [Oct 14], [GGP period determinants & RTF], [Determinants encoding GGP periods (up to $m$ non-interlacing weights); relative trace formula via $6$-fold cover of $op("GL")_5$],
      [Oct 19], [$q N = M^k + R$ quadric & Behrend tower], [Sign-only Weil/Deligne analogy via CM Poincaré bundle; Behrend's sphere theorem selects the Iwasawa tower],
      [Oct 20], [Pivot to von Mangoldt $Lambda$], [Smoothed sum $sum_(n <= X) Lambda(n)(X / n - 1)_+ - X log X + (1 + gamma) X$ with Guinand–Weil sign],
      [Nov 15], [Chained theta lifts ($m approx sqrt(X)$), seesaw, gcd gluing, weak Vandiver], [$U(X_0) -> dots.c -> U(X_m)$ synthesizes multiplicity $m approx sqrt(X)$; Rallis seesaw gives Bessel period; integral gluing breaks the $2/3$ barrier; weakened Vandiver controls $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$],
      [Nov 16], [GRH completed], [Full assumption-free proof of GRH and RH],
      [Nov 20], [Public release & verification], [Four-page *Remark* + ~17M lines of Lean 4 (>149,000 files); independently verified within 48 hours by Lean FRO & Mathlib Initiative],
    ),
    caption: [Chronology of the November 2026 breakthrough, synthesized from Alpöge's *Remark*.],
  )

  === Bridging Stepanov's Multiplicity to Automorphic Forms

  Standing back from the technical details (which Parts II and III will unpack rigorously), we can now see the overarching architecture of the Alpöge–Claude theorem with crystal clarity. Why did 167 years of effort converge on chained theta lifts between totally definite unitary groups?

  The answer lies in a three-way translation between the geometric paradigm of Weil and Deligne, the elementary paradigm of Stepanov and Bombieri, and the automorphic paradigm of Alpöge and Claude:

  1. *Replacing $C times C$ by multiplicity $m$.* Weil proved RH for a curve $C / bb(F)_q$ by intersecting $Delta$ and $Gamma_F$ on the surface $C times C$. Over $bb(Z)$, no surface $op("Spec") bb(Z) times_(bb(F)_1) op("Spec") bb(Z)$ exists. Stepanov showed that even over $bb(F)_q$, one can dispense with $C times C$ by working on $C$ alone with an auxiliary object of high multiplicity $m approx sqrt(q)$.

  2. *Replacing Hasse derivatives by $m approx sqrt(X)$ chained theta lifts.* Over $bb(F)_q$, multiplicity $m$ is manufactured by Hasse derivatives $D^((j))$ of polynomials. Over $bb(Z)$, naive differentiation of integers does not exist. Instead, Alpöge and Claude manufacture multiplicity $m$ *natively in the automorphic category*: each theta lift $U(X_(j-1)) -> U(X_j)$ sending $pi |-> pi plus.square mu_j [t]$ adds one unit of automorphic multiplicity—one additional non-interlacing weight in the Gan–Gross–Prasad period determinant—while the local $p$-adic divisibility $D^p equiv 0$ on a CM curve at inert primes supplies the arithmetic vanishing order (analogous to $D^((r)) (g^q) = 0$ in Stepanov's proof). Chaining $m approx sqrt(X)$ such lifts matches the exact square-root scale needed to control the smoothed von Mangoldt sum $S_Lambda (X)$ of length $X$.

  3. *Replacing the degree bound by Bost's slope inequality.* In Stepanov's proof, the final contradiction pits the multiplicity lower bound $m dot.c N_q (C)$ against the pole-degree upper bound $A + q B$. In the Alpöge–Claude proof, the pole-degree upper bound is replaced by *Bost's slope inequality* in Arakelov geometry (comparing the Arakelov height / Harder–Narasimhan slopes of Hermitian lattices attached to the integral automorphic structure against the $p$-adic divisibility lower bound from the $m$-fold iterated lift). When an off-line zero $rho = beta + i gamma$ with $beta > 1/2$ is assumed, the analytic reduction produces an anomalous oscillation in $S_Lambda (X)$ at scale $[Y, Y^(3/2)]$ that violates this divisor-slope inequality!

  #figure(
    table(
      columns: (21%, 25%, 25%, 29%),
      stroke: (x: none, y: 0.35pt + luma(210)),
      inset: (x: 4pt, y: 5pt),
      align: (left, left, left, left),
      [*Structural Role*], [*Weil–Deligne ($bb(F)_q$)*], [*Stepanov–Bombieri ($bb(F)_q$)*], [*Alpöge–Claude ($bb(Z)$)*],
      [Ambient arena], [Surface $C times C$ or étale $H^i_("ét") (overline(X), bb(Q)_ell)$], [Function field $bb(F)_q (C)$ on $C$ alone], [Totally definite unitary groups $U(X_0) -> dots.c -> U(X_m)$],
      [Positivity / nonvanishing], [Castelnuovo / Hodge index, or even tensor power $cal(F)^(times.o 2 k)$], [Nonzero auxiliary function $Phi in bb(F)_q (C)$], [GGP period determinants, Rallis seesaw, relative trace formula],
      [Source of multiplicity], [Second dimension ($C times C$) / tensor power $2 k$], [Hasse derivatives $D^((r))$ ($0 <= r < m$), $m approx sqrt(q)$], [Chain of $m approx sqrt(X)$ theta lifts $pi |-> pi plus.square mu_j [t]$ & CM $D^p equiv 0$],
      [Upper bound / degree control], [Intersection numbers $Delta^2, Gamma_F^2$], [Pole order $op("deg")_(oo) (Phi) <= A + q B$], [Bost's slope inequality & Hermitian lattice index],
      [Field extensions / twists], [Base change to $bb(F)_(q^m)$], [Unramified covers of $C$], [Behrend Iwasawa tower & integral gluing across Hecke characters],
    ),
    caption: [Three paradigms for the Riemann Hypothesis: geometric, elementary-multiplicity, and automorphic-multiplicity.],
  )

  === Formal Verification and a New Era in Mathematics

  Equally unprecedented was the medium in which the proof first entered the mathematical record. Because the initial discovery involved an extraordinary breadth of automorphic, arithmetic-geometric, and cohomological machinery—and because, as Alpöge candidly remarked, a machine-generated prose transcription of the argument ran to over $250,000$ unreadable pages—Alpöge chose to release the *machine-checked Lean 4 formalization* directly rather than an unrefereed prose draft.

  #lean-note(title: "Lean 4 Formalization: Scale and Independent Audit", module: "leanprover-community/riemann-hypothesis")[
    The November 20, 2026 release comprises approximately *17 million lines* of Lean 4 code across more than *149,000 source files*, organized into ten interconnected libraries culminating in `Main.lean`. Independent verification by the Lean FRO and the Mathlib Initiative confirmed:
    - *Target theorem:* The top-level theorem matches Mathlib's preexisting definition `RiemannHypothesis` (and its GRH generalization for primitive Dirichlet characters) with zero `sorry` placeholders and zero custom axioms.
    - *Axiom audit:* `#print axioms` confirms dependence solely on `propext`, `Quot.sound`, and `Classical.choice`.
    - *Independent kernels:* The compiled environment passed verification by multiple independent Lean 4 typecheckers (`comparator`, `nanoda`, `con-leche`, and `con-ron`), eliminating any single-kernel point of failure.
  ]

  As Alpöge himself emphasized in *Remark*, the existence of a 17-million-line verified proof is not the end of mathematical understanding, but its beginning: *"My intuition insists it will be massively simplified, likely immediately... in my view of my path I have just taken a step. I intend to do my best to understand and impart understanding of this argument and its certain simplifications."* In the chapters that follow, we take up that exact expository mission—beginning in Chapter 4 with a complete, self-contained treatment of Stepanov's elementary method over finite fields, before assembling the six modern pillars (Part II) and walking through the verified architecture of the Alpöge–Claude theorem (Part III).

  // ==========================================================================
  // Exercises
  // ==========================================================================
  #exercises((
    [*(Chebyshev's elementary bounds)* By analyzing the $p$-adic valuation $v_p (binom(2 n, n))$ using Legendre's formula $v_p (n!) = sum_(k >= 1) floor(n / p^k)$, prove that every prime power $p^k$ dividing $binom(2 n, n)$ satisfies $p^k <= 2 n$. Deduce the upper bound $psi(2 n) - psi(n) <= 2 n log 2$ and the lower bound $psi(2 n) >= n log 2 - O(log n)$, and hence establish explicit constants $c_1, c_2 > 0$ in Chebyshev's theorem $c_1 x <= psi(x) <= c_2 x$.],

    [*(Optimizing the zero-free region trigonometric polynomial)* Let $P(theta) = a_0 + a_1 cos theta + a_2 cos(2 theta) + dots.c + a_d cos(d theta)$ be a cosine polynomial with $a_k >= 0$ for all $k$, $a_1 > a_0 > 0$, and $P(theta) >= 0$ for all $theta in bb(R)$. Following the proof of the Hadamard–de la Vallée Poussin theorem in Section 3.1, show that $P(theta)$ yields a zero-free region $sigma >= 1 - c / log(|t| + 2)$ whose constant $c$ improves as the quantity $R(P) = (a_1 - a_0) / ((sqrt(a_1) - sqrt(a_0))^2)$ (or the classical ratio $a_0 / (a_1 - a_0)$ in the simplest form) is minimized. Compare $3 + 4 cos theta + cos(2 theta)$ with the degree-$4$ polynomial $(1 + 2 cos theta + cos(2 theta))^2$ (or $17 + 24 cos theta + 10 cos(2 theta) + 2 cos(3 theta)$).],

    [*(From zero-free region to PNT error term)* Suppose $zeta(s) != 0$ in the region $sigma >= 1 - c / (log(|t| + 2))^alpha$ for some fixed $alpha in (0, 1]$ and $c > 0$. Using the truncated explicit formula
    $ psi(x) = x - sum_(|gamma| <= T) (x^rho) / rho + O( (x (log(x T))^2) / T + log x ), $
    choose the optimal truncation height $T = T(x)$ to show that $psi(x) = x + O(x exp(-c' (log x)^(1 / (1 + alpha))))$ for some $c' > 0$. Check that $alpha = 1$ recovers the classical $exp(-c' sqrt(log x))$ error term, while $alpha = 2/3$ recovers the Vinogradov–Korobov exponent $3/5$ (up to $log log x$ factors).],

    [*(Selberg's trace formula vs. Guinand–Weil)* Verify that for a compact hyperbolic surface $M = Gamma backslash bb(H)$ of genus $g >= 2$ (whose area is $4 pi (g - 1)$ by Gauss–Bonnet), inserting a Gaussian test function $h(r) = e^(-t r^2)$ ($t > 0$) into the Selberg trace formula recovers Weyl's law $\#\{ j : lambda_j <= Lambda \} tilde.op (op("Area")(M) / (4 pi)) Lambda$ as $Lambda -> oo$. Contrast this with the growth of the zero-counting function $N(T) tilde.op (T / (2 pi)) log T$ for $zeta(s)$.],

    [*(From power-sum bounds to the Riemann Hypothesis over $bb(F)_q$)* Let $alpha_1, dots.c, alpha_(2 g) in bb(C)$ be nonzero complex numbers such that the multiset $\{ alpha_1, dots.c, alpha_(2 g) \}$ is invariant under $alpha |-> q / alpha$. Suppose there exists a constant $C > 0$ such that $|sum_(i = 1)^(2 g) alpha_i^m| <= C q^(m / 2)$ for every integer $m >= 1$. By considering the radius of convergence of the generating function
    $ sum_(m = 1)^oo ( sum_(i = 1)^(2 g) alpha_i^m ) T^m = sum_(i = 1)^(2 g) (alpha_i T) / (1 - alpha_i T), $
    prove that $|alpha_i| = q^(1/2)$ for every $i = 1, dots.c, 2 g$.],

    [*(Hasse's theorem for explicit elliptic curves)* Let $E$ be the elliptic curve $y^2 = x^3 - x$ over $bb(F)_p$ for an odd prime $p$. Compute $N_p (E)$ directly when $p equiv 3 mod 4$ (using the substitution $x |-> -x$ to pair points), and verify that $a_p = p + 1 - N_p (E) = 0$. When $p equiv 1 mod 4$, express $a_p$ in terms of the Gaussian integer factorization $p = pi overline(pi)$ in $bb(Z)[i]$ and verify Hasse's bound $|a_p| <= 2 sqrt(p)$.],

    [*(Castelnuovo's inequality on $C times C$)* In Weil's proof for a smooth projective curve $C$ of genus $g$ over $bb(F)_q$, let $Delta$ be the diagonal and $Gamma_F$ the graph of the $q$-power Frobenius morphism on $S = C times C$. Using the adjunction formula on $S$ (where the canonical divisor is $K_S = (2 g - 2) (V + H)$), verify that $Delta^2 = 2 - 2 g$. Then use the fact that $Gamma_F$ is the pullback of $Delta$ under $op("id") times op("Frob")_q$ (a morphism of degree $q$) to verify that $Gamma_F^2 = q (2 - 2 g)$ and $Gamma_F dot.c H = 1$, $Gamma_F dot.c V = q$.],

    [*(Li's criterion and the Möbius map)* Let $phi(z) = 1 - 1 / z$. Prove that $phi$ is a bijection from the half-plane $\{ op("Re")(z) > 1/2 \}$ onto the open unit disk $\{ |w| < 1 \}$, and that $phi(1 - z) = 1 / phi(z)$. Using the Hadamard product $xi(s) = xi(0) product_rho (1 - s / rho)$ and the functional equation $xi(s) = xi(1 - s)$, verify that for $|w|$ sufficiently small,
    $ log xi(1 / (1 - w)) = log xi(1) + sum_(n = 1)^oo (lambda_n / n) w^n, $
    where $lambda_n = sum_rho (1 - (1 - 1 / rho)^n)$. Deduce the derivative formula $lambda_n = (1 / (n - 1)!) (dif^n / dif s^n) [s^(n - 1) log xi(s)]_(s = 1)$.],

    [*(Parameter optimization in Stepanov's method and the $m approx sqrt(X)$ analogy)* In the heuristic parameter count for Stepanov's method in Section 3.4, suppose the auxiliary function $Phi = sum_(i <= A) sum_(j <= B) c_(i, j) f_i g_j^q$ satisfies $A B > m (A + B)$ (to guarantee a nonzero solution) and $A < q$ (to guarantee $Phi != 0$), yielding $N_q (C) <= (A + q B) / m$. Minimize $(A + q B) / m$ over positive real parameters $A, B, m$ subject to $A B >= m (A + B)$ and $A <= q$. Show that the optimum occurs at $A approx q$, $B approx sqrt(q)$, and $m approx sqrt(q)$, giving $N_q (C) <= q + O(sqrt(q))$. Discuss briefly how this scaling parallels Claude's choice of theta-lift chain length $m approx sqrt(X)$ for the von Mangoldt sum of length $X$ in Section 3.5.],
  ))
]
