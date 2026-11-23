// ============================================================================
// Chapter 13: Chaining Theta Lifts and Automorphic Multiplicity
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch13() = [
  #chapter(
    "Chaining Theta Lifts and Automorphic Multiplicity",
    short-title: "Chaining Theta Lifts",
    epigraph: "The line: for the von Mangoldt sum of length X, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was sqrt(X). (And yet, what else could it be?)",
    epigraph-source: "Levent Alpöge, Remarks on the Proof of the Generalized Riemann Hypothesis (2026)",
    overview: [
      In Stepanov's elementary proof of the Riemann Hypothesis for curves over finite fields, the decisive mechanism is the construction of an auxiliary polynomial vanishing to high order $m$ at every rational point, forcing a degree-versus-multiplicity contradiction. Over the integers, no direct algebraic analogue of $m$-fold differentiation exists. This chapter develops the central breakthrough of the Alpöge–Claude proof: synthesizing multiplicity $m$ in a natively automorphic framework by chaining $m$ successive unitary theta lifts along a tower of totally definite Hermitian spaces $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$. We derive the fundamental scaling law $m approx sqrt(X)$ balancing multiplicity gain against lift cost for a von Mangoldt sum of length $X$; analyze the single-step spectral transfer $pi |-> pi plus.square mu_j [t]$ and its connection to Gan–Gross–Prasad (GGP) periods and interlacing weights; prove the seesaw duality theorem showing that the global period of the $m$-fold lift reduces to a Bessel period independent of the auxiliary Hecke characters $mu_j$ and evaluated via the Rallis inner product formula and the doubling method; dissect the a priori $2/3$ lift-cost barrier and its resolution through character twisting and integral "division"; and finally assemble the global test vectors and evaluation grids as formalized in `SiegelEisensteinSecondTermHypotheses.lean`.
    ],
    label-name: "ch-chained-theta-lifts",
  )

  == The Core Breakthrough: Why Length $m approx sqrt(X)$?

  A recurring motif throughout the history of the Riemann Hypothesis is the asymmetry between the function-field setting and the number-field setting. Over a finite field $bb(F)_q$, a smooth projective curve $C \/ bb(F)_q$ carries the Frobenius endomorphism $op("Fr")_q$, a geometric intersection pairing on $C times C$, and---in Stepanov's 1969 elementary proof of the Hasse–Weil bound---a ring of regular functions equipped with Hasse–Schmidt derivatives $D^((k))$. In Stepanov's argument, one constructs a nonzero function $f$ on $C$ of controlled pole order $d$ at infinity that vanishes to multiplicity at least $m$ at every $bb(F)_q$-rational point (or along the graph of Frobenius). Counting zeros against poles yields
  $ m dot.c |C(bb(F)_q)| <= d, $
  and optimizing the auxiliary parameter $m$ against the field size $q$ produces the square-root error term $|C(bb(F)_q) - (q + 1)| <= 2 g sqrt(q)$.

  The fundamental obstruction to transplanting Stepanov's method to $op("Spec")(bb(Z))$ is already visible in this single inequality: *what is multiplicity over the integers?* Differentiating a polynomial $P(T) in bb(Z)[T]$ is elementary, because $T$ is a formal variable; "differentiating whole numbers" makes no literal sense in $bb(Z)$, and although Arakelov geometry and Borger's $Lambda$-rings suggest formal surrogates, neither supplies a direct positivity mechanism compatible with the Guinand–Weil explicit formula. Recall from the explicit formula for the von Mangoldt function $Lambda(n)$ that for a test function $Phi$ of support length $X$, the prime-side sum takes the shape
  $ W(Phi) = sum_(n <= X) Lambda(n) (X / n - 1)_+ - X log X + (1 + gamma) X, $
  or, in the sharp positivity formulation driving zero-free regions beyond $1 - eta$,
  $ W(1_((0, 1]) + C X^eta dot.c 1_((0, 1/X])) >= 0. $
  To turn such a positivity criterion into a contradiction for a hypothetical off-line zero $rho = beta + i gamma$ with $beta > 1/2$, one needs an automorphic determinant or period functional that vanishes to high order $m$ along the arithmetic locus while retaining strict control over its archimedean and finite-place heights.

  The decisive conceptual leap of Alpöge and Claude is that *iterated theta lifting provides a natively automorphic substitute for $m$-fold multiplicity*. Rather than attempting to differentiate a single automorphic form $m$ times---which destroys automorphy or introduces uncontrolled poles---one passes the form successively through a chain of $m$ global theta correspondences between totally definite unitary groups of steadily growing rank.

  #definition(title: "Tower of Totally Definite Unitary Spaces")[
    Let $E \/ F$ be a CM extension of number fields, where $F$ is totally real of degree $d_F = [F : bb(Q)]$ and $E$ is a totally imaginary quadratic extension of $F$ with nontrivial Galois involution $c in op("Gal")(E \/ F)$. Fix an integer $m >= 1$ and a sequence of non-degenerate Hermitian $E$-vector spaces
    $ X_0, X_1, dots.c, X_m $
    with alternating sign parity (or equivalently, alternating Hermitian and skew-Hermitian forms $chevron.l dot.c, dot.c chevron.r_(X_j)$ over $E$, where skew-Hermitian forms are converted to Hermitian ones by scaling by a fixed purely imaginary element $xi_0 in E^times$ with $xi_0^c = -xi_0$). We say that $(X_0, X_1, dots.c, X_m)$ is a *totally definite unitary tower* of length $m$ and step increment $t >= 1$ if:
    + For every archimedean place $v | oo$ of $F$, the Hermitian form on $X_j times.o_F F_v$ is positive definite, so that $U(X_j)(F_v) tilde.equiv U(n_j)$ is compact, where $n_j = dim_E X_j$.
    + The ranks satisfy the linear growth law
      $ n_j = n_(j-1) + t quad (1 <= j <= m), $
      so that $n_m = n_0 + m t$.
    + For each $1 <= j <= m$, the pair $(U(X_(j-1)), U(X_j))$ forms a reductive dual pair inside the symplectic group $op("Sp")(W_j)$ associated to the $F$-symplectic space $W_j = op("Res")_(E \/ F) (X_(j-1) times.o_E X_j)$.
  ]

  At each step $j in {1, dots.c, m}$ of the tower, choosing a nontrivial additive character $psi : bb(A)_F \/ F -> bb(C)^times$ and a pair of splitting Hecke characters $(chi_j, chi'_j)$ of $bb(A)_E^times \/ E^times$ whose restrictions to $bb(A)_F^times$ match the quadratic character $omega_(E \/ F)$ with parities determined by $n_(j-1)$ and $n_j$, we obtain a global Weil representation $omega_(psi, chi_j, chi'_j)$ of $U(X_(j-1))(bb(A)_F) times U(X_j)(bb(A)_F)$ on the Schwartz space $cal(S)(bb(X)_j (bb(A)_F))$, where $bb(X)_j$ is a maximal isotropic subspace (a polarization) of $W_j$. For any Schwartz function $Phi_j in cal(S)(bb(X)_j (bb(A)_F))$ and $(g, h) in U(X_(j-1))(bb(A)_F) times U(X_j)(bb(A)_F)$, the associated theta kernel is
  $ theta_(Phi_j) (g, h) = sum_(x in bb(X)_j (F)) (omega_(psi, chi_j, chi'_j) (g, h) Phi_j)(x). $
  Because $U(X_(j-1))$ is totally definite, the adelic quotient $[U(X_(j-1))] = U(X_(j-1))(F) backslash U(X_(j-1))(bb(A)_F)$ is *compact*. Consequently, there are no convergence obstructions to integrating against any automorphic form $f$ on $[U(X_(j-1))]$: the single-step theta lift
  $ theta_(Phi_j) (f)(h) = integral_([U(X_(j-1))]) theta_(Phi_j) (g, h) overline(f(g)) dif g $
  is automatically an automorphic form on $[U(X_j)]$, and by compactness of $[U(X_j)]$ it is automatically square-integrable.

  #definition(title: "The m-Fold Iterated Theta Lift")[
    Given an automorphic form $f_0 in cal(A)(U(X_0))$, splitting data $(chi_j, chi'_j)_(j=1)^m$, and Schwartz functions $Phi_j in cal(S)(bb(X)_j (bb(A)_F))$ for $1 <= j <= m$, the *$m$-fold iterated theta lift* $f_m = Theta^(m)_(underline(Phi)) (f_0) in cal(A)(U(X_m))$ is defined recursively for $1 <= j <= m$ by
    $ f_j (h_j) = theta_(Phi_j) (f_(j-1)) (h_j) = integral_([U(X_(j-1))]) theta_(Phi_j) (h_(j-1), h_j) overline(f_(j-1) (h_(j-1))) dif h_(j-1). $
  ]

  Why does this $m$-fold iteration mimic Stepanov multiplicity $m$? Every step $U(X_(j-1)) -> U(X_j)$ appends a controlled one-dimensional (or $t$-dimensional) character block $mu_j [t]$ to the Arthur–Langlands parameter of the representation, while simultaneously forcing the global period of $f_m$ to pass through $m$ layers of arithmetic divisibility. In the CM setting (where the underlying Hermitian lattices admit CM points and integral structures over $cal(O)_E$), each theta step introduces a factor of algebraic divisibility controlled by the Chowla–Selberg period relation, Weyl's dimension formula for representations of the compact group $U(n_j)$, and the Siegel mass formula for the genus of $X_j$. At the same time, the determinant built out of the GGP periods of the chain---which we study in Section 13.2---acquires $m$ independent non-interlacing spectral degrees of freedom, allowing it to annihilate $m$ terms of the arithmetic expansion simultaneously, just as an $m$-fold zero of a Stepanov auxiliary polynomial annihilates the first $m$ Taylor coefficients.

  This immediately raises the central quantitative question: *given a von Mangoldt sum of length $X$, how long should the chain $m$ be?*

  #insight-box(title: "The Balancing Law: Multiplicity Gain vs. Lift Cost")[
    Let $X$ be the length of the truncated von Mangoldt sum $sum_(n <= X) Lambda(n) (X / n - 1)_+$. Suppose a chain of $m$ theta lifts along $U(X_0) -> dots.c -> U(X_m)$ synthesizes automorphic multiplicity $m$ in a Stepanov-type determinant. Two opposing forces govern the choice of $m$:
    + *Multiplicity gain (vanishing order).* Each step of the chain contributes one unit of multiplicity, allowing the auxiliary determinant to cancel order-$m$ terms and lowering the effective error-term budget per prime power by a factor proportional to $1 / m$ (equivalently, raising the divisibility lower bound linearly in $m$). To resolve $X$ prime-power terms down to square-root cancellation $X^(1/2)$, the multiplicity $m$ must be large enough that the residual uncancelled tail has size at most $X / m$.
    + *Lift cost (rank, norm, and level growth).* Each step $U(X_(j-1)) -> U(X_j)$ increases the rank by $t$ and multiplies the archimedean weight, covolume, and conductor by a step factor. Over $m$ steps, the aggregate logarithmic height / complexity of the lifted form and its evaluation grid scales linearly in $m$ per prime-power input, contributing a total cost proportional to $m$ against the budget $X$.

    Equating the residual error scale $X / m$ with the accumulated lift complexity $m$ yields
    $ X / m asymp m <==> m^2 asymp X <==> m approx sqrt(X). $
  ]

  We can make this heuristic completely precise by examining the exact exponent trade-off in the Stepanov–Bost slope inequality framework.

  #proposition(title: "Optimal Chain Length m approx sqrt(X)")[
    Suppose that for a von Mangoldt test functional of support length $X >= 2$ and a chain of $m >= 1$ iterated theta lifts $U(X_0) -> dots.c -> U(X_m)$ with fixed step increment $t >= 1$, the following two asymptotic estimates hold for a hypothetical zero $rho = beta + i gamma$ with $1/2 < beta <= 1$:
    + (*Multiplicity divisibility lower bound.*) The logarithmic arithmetic divisibility of the $m$-fold iterated lift at the evaluation locus satisfies
      $ log cal(D)_m >= c_1 m X^beta - O(m log X), $
      reflecting order-$m$ vanishing across the prime-power contribution of size $asymp X^beta$.
    + (*Archimedean and covolume upper bound.*) After twisting and integral division (Section 13.4), the logarithmic norm and complexity upper bound on the $m$-fold lift satisfies
      $ log cal(H)_m <= c_2 (m^2 + X) log X, $
      where the quadratic term $m^2$ arises from summing the linear rank growth $n_j = n_0 + j t$ over $1 <= j <= m$ (as $sum_(j=1)^m n_j = m n_0 + t m (m+1) / 2 asymp (t/2) m^2$), and the linear term $X$ is the ambient prime-sum support.

    Then the Bost slope inequality $log cal(D)_m <= log cal(H)_m$ is sharpest when $m^2 asymp X$, i.e., $m = floor(kappa sqrt(X))$ for an explicit constant $kappa > 0$. With this choice, the slope inequality forces
    $ c_1 kappa X^(beta + 1/2) <= c_2 (kappa^2 + 1) X log X + O(X^(1/2) log X), $
    which yields a contradiction as $X -> oo$ for every $beta > 1/2$.
  ]

  #proof[
    Dividing the slope inequality $c_1 m X^beta - O(m log X) <= c_2 (m^2 + X) log X$ by $m$ gives
    $ c_1 X^beta <= c_2 (m + X / m) log X + O(log X). $
    For fixed $X >= 2$, the function $g(m) = m + X / m$ on $m in (0, oo)$ is strictly convex, with derivative $g'(m) = 1 - X / m^2$ vanishing uniquely at $m = sqrt(X)$, where $g(sqrt(X)) = 2 sqrt(X)$. More generally, setting $m = floor(kappa sqrt(X))$ for any fixed $kappa > 0$ gives $m + X / m = (kappa + kappa^(-1)) sqrt(X) + O(1)$, so the right-hand side is $O(X^(1/2) log X)$. If $beta > 1/2$, then $X^beta / (X^(1/2) log X) = X^(beta - 1/2) / log X -> oo$ as $X -> oo$, contradicting the inequality for all sufficiently large $X$.
  ]

  Notice how naturally the quadratic rank sum $sum_(j=1)^m n_j asymp m^2$ appears in Proposition 13.3: in a chain of $m$ lifts where the $j$-th group has rank $n_j asymp j$, the total dimension of the ambient Weil spaces, the sum of the Weyl dimension logarithms, and the cumulative covolume across the tower all carry a factor of $sum_(j=1)^m j = m(m+1)/2 asymp m^2$. Dividing by the multiplicity $m$ leaves $m$ on one side and $X / m$ on the other. Choosing $m approx sqrt(X)$ is therefore not an arbitrary tuning parameter; it is the unique saddle point of the automorphic Stepanov inequality.

  #remark[
    In `remark.pdf` (Section 2, items 7–10), Alpöge notes that the breakthrough crystallized in two stages. First, seeing multiplicity $2$ on $O(2, n)$ via a natively automorphic determinant demonstrated that theta lifts could play the role of Stepanov's derivative. Second, passing to totally definite unitary groups $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ eliminated the archimedean non-compactness obstructions at the intermediate steps, allowing the chain length $m$ to be pushed all the way to $m approx sqrt(X)$ rather than stopping at a fixed small integer.
  ]

  == Spectral Transfer and Interlacing Weights ($pi |-> pi plus.square mu_j [t]$)

  We now dissect a single link $U(X_(j-1)) -> U(X_j)$ of the chain. To understand both how automorphic representations transform along the tower and how multiplicity $m$ is encoded in periods, we must track two simultaneous structures: the *Langlands–Arthur spectral transfer* under base change to $op("GL")_n (bb(A)_E)$, and the *branching law* governing Gan–Gross–Prasad (GGP) periods between successive unitary groups.

  === Local and Global Spectral Transfer

  Let $V = X_(j-1)$ and $W = X_j$ be consecutive Hermitian spaces in the tower, with ranks $n = dim_E V$ and $n' = dim_E W = n + t$. Let $pi = times.o.big'_v pi_v$ be an irreducible automorphic representation of $U(V)(bb(A)_F)$. Because $U(V)$ is totally definite, every automorphic representation $pi$ of $U(V)(bb(A)_F)$ is discrete, and at every archimedean place $v | oo$ its local component $pi_v$ is a finite-dimensional irreducible algebraic representation of the compact unitary group $U(n)$, parameterized by its highest weight
  $ underline(a)_v = (a_(v, 1) >= a_(v, 2) >= dots.c >= a_(v, n)) in bb(Z)^n. $
  By the theory of unitary base change (Rogawski for $n <= 3$, Labesse for stable base change of definite unitary groups, and Mok / Kaletha–Minguez–Shin–White in full generality; formalized in the Lean proof under `BaseChangeDefiniteUnitaryGroup`), $pi$ admits a global base change $op("BC")(pi)$ to an isobaric automorphic representation of $op("GL")_n (bb(A)_E)$:
  $ op("BC")(pi) = tau_1 plus.square tau_2 plus.square dots.c plus.square tau_r, $
  where each $tau_i$ is a conjugate-self-dual discrete automorphic representation of $op("GL")_(n_i) (bb(A)_E)$ with $sum_(i=1)^r n_i = n$, and $plus.square$ denotes the Langlands isobaric sum (normalized parabolic induction from the Levi subgroup $product_i op("GL")_(n_i)$).

  For a single Hecke character $mu_j : bb(A)_E^times \/ E^times -> bb(C)^times$ and an integer $t >= 1$, let $mu_j [t]$ denote the $t$-dimensional Arthur–Speh representation (or character block) of $op("GL")_t (bb(A)_E)$ associated to the $t$-dimensional irreducible representation of $op("SL")_2 (bb(C))$ twisted by $mu_j$: at every unramified finite place $w$ of $E$, the Satake parameters of $mu_j [t]_w$ are the geometric progression
  $ mu_(j, w) (pi.alt_w) dot.c q_w^((t - 1)/2), space mu_(j, w) (pi.alt_w) dot.c q_w^((t - 3)/2), space dots.c, space mu_(j, w) (pi.alt_w) dot.c q_w^(-(t - 1)/2). $
  When $t = 1$, $mu_j [1]$ is simply the Hecke character $mu_j$ itself on $op("GL")_1 (bb(A)_E)$.

  #theorem(title: "Unitary Theta Spectral Transfer")[
    Let $(U(V), U(W))$ be a unitary dual pair with $dim_E V = n$ and $dim_E W = n + t$ ($t >= 1$), equipped with splitting Hecke characters $(chi_j, chi'_j)$ of $bb(A)_E^times \/ E^times$. Let $pi$ be an irreducible automorphic representation of $U(V)(bb(A)_F)$, and suppose its global theta lift $sigma = Theta_(psi, chi_j, chi'_j) (pi)$ to $U(W)(bb(A)_F)$ is nonzero. Let $mu_j = chi_j (chi'_j)^(-1)$ (up to the standard parity twist determined by the sign of the Hermitian spaces). Then at every finite place $v$ of $F$ where $V_v, W_v, pi_v, psi_v, chi_(j, v), chi'_(j, v)$ are unramified, the local theta lift $sigma_v = theta_v (pi_v)$ is unramified, and its local base change to $op("GL")_(n+t) (E_v)$ satisfies
    $ op("BC")_v (sigma_v) tilde.equiv (op("BC")_v (pi_v) times.o chi_(j, v)^(-1) chi'_(j, v)) plus.square mu_(j, v) [t]. $
    Globally, after absorbing the splitting character twist into the normalization of the base change, the transfer map on Arthur parameters acts by
    $ pi |-> pi plus.square mu_j [t]. $
    Iterating along the tower $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ with auxiliary characters $mu_1, dots.c, mu_m$, the base change of a nonzero $m$-fold theta lift $pi_m$ of $pi_0$ has the isobaric decomposition
    $ op("BC")(pi_m) = op("BC")(pi_0) plus.square mu_1 [t] plus.square mu_2 [t] plus.square dots.c plus.square mu_m [t]. $
  ]

  #proof[
    We verify the unramified local statement at a finite place $v$ of $F$, which by strong multiplicity one for isobaric representations of $op("GL")_(n+t) (bb(A)_E)$ (Jacquet–Shalika, formalized as `JacquetShalika`) determines the global isobaric decomposition. There are two cases depending on whether $v$ splits or remains inert in $E$.

    *Case 1: $v$ splits in $E$, say $E_v tilde.equiv F_v times F_v$.* Then $U(V)(F_v) tilde.equiv op("GL")_n (F_v)$ and $U(W)(F_v) tilde.equiv op("GL")_(n+t) (F_v)$. Under the Kudla splitting (`KudlaSplittingSplitUnitary`), the local Weil representation $omega_(psi_v, chi_(j, v), chi'_(j, v))$ on $cal(S)(M_(n, n+t) (F_v))$ acts by
    $ (omega_v (g, h) Phi)(x) = chi_(j, v) (det g) chi'_(j, v) (det h)^(-1) |det g|_v^((n+t)/2) \ times |det h|_v^(-n/2) Phi(g^(-1) x h), $
    where $chi_(j, v)$ and $chi'_(j, v)$ denote the characters on the first factor of $E_v^times tilde.equiv F_v^times times F_v^times$. Let $pi_v$ be the unramified spherical principal series representation of $op("GL")_n (F_v)$ with Satake parameter $op("diag")(alpha_1, dots.c, alpha_n)$. By the explicit unramified Howe correspondence for $(op("GL")_n, op("GL")_(n+t))$ (Minguez, Kudla–Rallis), the unique unramified quotient $sigma_v = theta_v (pi_v)$ is the spherical constituent of the normalized parabolic induction from the Levi subgroup $op("GL")_n (F_v) times op("GL")_t (F_v)$ of
    $ (pi_v times.o mu_(j, v)^(-1)) times.o (mu_(j, v) dot.c |det|_v^((t-1)/2) times.o dots.c times.o mu_(j, v) dot.c |det|_v^(-(t-1)/2)). $
    In particular, the $t$ extra Satake parameters are precisely $q_v^((t-1)/2), q_v^((t-3)/2), dots.c, q_v^(-(t-1)/2)$ twisted by the splitting character $mu_(j, v)$, which is the Satake parameter of the $t$-dimensional Speh/Arthur block $mu_(j, v) [t]$. Thus the Langlands parameter of $sigma_v$ is the direct sum of the twisted parameter of $pi_v$ and the parameter of $mu_(j, v) [t]$.

    *Case 2: $v$ is inert in $E$.* Then $U(V)(F_v)$ and $U(W)(F_v)$ are unramified quasi-split unitary groups over $F_v$, and the Rallis tower / unramified Howe duality theorem (Kudla–Rallis, Harris–Kudla–Sweet) computes the Satake parameter of $theta_v (pi_v)$ via the spherical Hecke algebra homomorphism $cal(H)(U(W)(F_v), K_(W, v)) -> cal(H)(U(V)(F_v), K_(V, v))$ induced by the Weil representation. Under the Satake isomorphism, this homomorphism corresponds to the embedding of dual groups $""^L U(V) -> ""^L U(W)$ that appends the $t$-dimensional $op("SL")_2$-block $mu_(j, v) [t]$ in the $L$-group. Passing to base change on $op("GL")_(n+t) (E_v)$ yields $op("BC")_v (sigma_v) tilde.equiv op("BC")_v (pi_v) plus.square mu_(j, v) [t]$ (with the twist absorbed).

    By induction on $j = 1, dots.c, m$, the unramified local components of $op("BC")(pi_m)$ agree at almost all places with $op("BC")(pi_0) plus.square mu_1 [t] plus.square dots.c plus.square mu_m [t]$. By the Jacquet–Shalika strong multiplicity one theorem for isobaric sums on $op("GL")_(n_m) (bb(A)_E)$, the global isobaric decompositions coincide.
  ]

  The algebraic beauty of Theorem 13.5 lies in the complete decoupling of the base representation $pi_0$ from the $m$ auxiliary characters $mu_1, dots.c, mu_m$: each lift step adjoins a fresh, freely tunable character block $mu_j [t]$ to the Arthur parameter without perturbing the Satake parameters of $pi_0$!

  === GGP Periods, Interlacing Weights, and the ${0, 1}$-Determinant

  To connect the spectral transfer $pi |-> pi plus.square mu_j [t]$ to the explicit formula $W(dot.c)$ and Stepanov multiplicity, we now examine the archimedean branching laws and Gan–Gross–Prasad (GGP) periods.

  Consider an embedding of totally definite Hermitian spaces $V subset.eq W$ of codimension $1$, so that $W = V plus.o E e_0$ with $chevron.l e_0, e_0 chevron.r > 0$ at every archimedean place $v | oo$. At each archimedean place $v$, we have an embedding of compact unitary groups $U(n) subset.eq U(n + 1)$. Let $V_(underline(a))$ and $V_(underline(b))$ be irreducible algebraic representations of $U(n)$ and $U(n + 1)$ with highest weights
  $ underline(a) = (a_1 >= a_2 >= dots.c >= a_n) in bb(Z)^n, \ underline(b) = (b_1 >= b_2 >= dots.c >= b_(n+1)) in bb(Z)^(n+1). $

  #theorem(title: "Weyl Branching Law and GGP Multiplicity One for Compact Unitary Groups")[
    The restriction of $V_(underline(b))$ from $U(n+1)$ to $U(n)$ is multiplicity-free:
    $ dim_bb(C) op("Hom")_(U(n)) (V_(underline(b)), V_(underline(a))) in {0, 1}. $
    Moreover, $dim_bb(C) op("Hom")_(U(n)) (V_(underline(b)), V_(underline(a))) = 1$ if and only if the highest weights *interlace*:
    $ b_1 >= a_1 >= b_2 >= a_2 >= dots.c >= b_n >= a_n >= b_(n+1). $
  ]

  #proof[
    This is the classical Gelfand–Tsetlin branching rule for $U(n) subset.eq U(n+1)$, which follows immediately from the Weyl character formula. Indeed, the character of $V_(underline(b))$ evaluated on $op("diag")(z_1, dots.c, z_n, 1) in U(n) subset.eq U(n+1)$ is the Schur polynomial $s_(underline(b)) (z_1, dots.c, z_n, 1)$. Expanding the $(n+1) times (n+1)$ Vandermonde-type numerator determinant $det(z_i^(b_k + n + 1 - k))$ along its last row (where $z_(n+1) = 1$) and dividing by the denominator $product_(1 <= i < j <= n) (z_i - z_j) product_(i=1)^n (z_i - 1)$ yields
    $ s_(underline(b)) (z_1, dots.c, z_n, 1) = sum_(underline(a) prec underline(b)) s_(underline(a)) (z_1, dots.c, z_n), $
    where the sum ranges over all integer $n$-tuples $underline(a)$ satisfying the interlacing inequalities $b_1 >= a_1 >= b_2 >= dots.c >= a_n >= b_(n+1)$. Since the Schur polynomials $s_(underline(a))$ form a basis of irreducible characters of $U(n)$, each interlacing $underline(a)$ occurs with multiplicity $1$ and all non-interlacing $underline(a)$ occur with multiplicity $0$.
  ]

  Globally, let $pi$ be an irreducible automorphic representation of $U(V)(bb(A)_F)$ and $sigma$ an irreducible automorphic representation of $U(W)(bb(A)_F)$. The global *Gan–Gross–Prasad (GGP) period* is the linear functional on $sigma times.o overline(pi)$ defined by
  $ cal(P)_(op("GGP")) (phi.alt, f) = integral_([U(V)]) phi.alt(g) overline(f(g)) dif g quad (phi.alt in sigma, space f in pi). $
  By the Ichino–Ikeda / N. Harris / Beuzart-Plessis–Chaudouard–Zydor theorem (the GGP conjecture for unitary groups), when $pi$ and $sigma$ are tempered (or more generally in the relevant Arthur packets), the squared modulus $|cal(P)_(op("GGP")) (phi.alt, f)|^2$ is proportional to the central $L$-value $L(1/2, op("BC")(sigma) times op("BC")(pi)^or)$ multiplied by a product of local matrix-coefficient integrals $cal(P)_v (phi.alt_v, f_v)$. Crucially, at every archimedean place $v | oo$, the local functional $cal(P)_v$ vanishes identically unless $op("Hom")_(U(n)) (sigma_v, pi_v) != 0$---that is, unless the highest weights of $sigma_v$ and $pi_v$ *interlace*!

  This explains item 7 of `remark.pdf`: *"Determinants for $W(dot.c)$'s containing the desired periods, indeed GGP periods, with values $0, 1$ meaning interlacing weights, or up to $m$ non-interlacing ones."* When one forms the Gram/correlation determinant of GGP periods across a family of representations indexed by weights, the archimedean local factor is literally a ${0, 1}$-valued incidence matrix recording whether the weights interlace. Under a single step $U(V) subset.eq U(W)$, the interlacing condition is rigid: all $n$ weights $a_1, dots.c, a_n$ must lie strictly between consecutive $b_i$. However, when we chain $m$ steps $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$, each step introduces a new character block $mu_j [t]$ whose archimedean infinity-type weight can be placed freely, relaxing the rigid interlacing constraint by up to $m$ non-interlacing slots! Those $m$ non-interlacing degrees of freedom are the spectral manifestation of Stepanov multiplicity $m$: they create an $m$-dimensional kernel of linear relations among the weight blocks, allowing the determinant to match and cancel $m$ consecutive orders of the explicit formula simultaneously.

  === Nonvanishing and Spectral Isolation: `ThetaIntegralsAgree`, `LocalMatching`, and `FunctionalsSeparate`

  In passing from the formal algebraic picture of $pi |-> pi plus.square mu_j [t]$ to a rigorous proof of nonvanishing and spectral isolation in Lean 4, three technical obstacles must be overcome:
  1. *Model independence of theta integrals (`ThetaIntegralsAgree`).* In the unitary theta correspondence, one works simultaneously with two realizations of the Weil representation: the *Fock / polynomial model* at archimedean places (ideal for computing highest weights, interlacing conditions, and algebraic rationality) and the *mixed / Schrödinger model* at finite and split places (ideal for computing Fourier coefficients, Siegel–Weil integrals, and seesaw identities). One must prove that matching Schwartz functions under the intertwining isomorphism produce identical global theta integrals (up to a nonzero scalar).
  2. *Local matching of archimedean and finite factors (`LocalMatching`).* To assemble factorizable test vectors across the tower, the intertwining maps between the two Weil models must factor cleanly as a tensor product $P_r times.o_bb(C) P_f tilde.equiv Pi$ of an archimedean polynomial module $P_r$ and a finite-place module $P_f$, uniformly across triples $(W, W_1, X)$ and splitting characters $(alpha, beta)$ with prescribed infinity exponents.
  3. *Separation of functionals (`FunctionalsSeparate`).* To isolate a specific automorphic component $pi_m$ (and guarantee that its GGP/Bessel period does not accidentally vanish due to cancellation with other representations in the same Hecke or archimedean packet), the collection of local theta functionals and unramified Hecke operators must separate distinct representations in the discrete spectrum.

  #lean-note(title: "Lean 4 Formalization: ThetaIntegralsAgree, LocalMatching, and FunctionalsSeparate", module: "ThetaIntegralsAgree.lean & FunctionalsSeparateOfHoweUnramOfSiegelWeil.lean")[
    In `Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean` (namespace `GlobalTheory.SquareSt`), the three core analytic-algebraic compatibility conditions are stated explicitly as propositions:
    - `WeilConvergence`: For any datum `D : D7`, standard additive character $psi$, Hermitian spaces $M, X$ with signature $(M."rank" - p, p)$ at some real place $tau$ satisfying the convergence range $X."rank" < 2 (M."rank" - p)$, every theta function $Phi$ in the oscillator space is integrable against the Haar fundamental domain (`ModInt theta omega nu F Phi`).
    - `LocalMatching`: For triples $(W, W_1, X)$ of Hermitian spaces with frames $(A, A_1, B)$ and prescribed rational infinity exponents $(a, b)$, there exist an archimedean polynomial quotient $P_r$ with surjective maps $q, q'$ and a finite-place quotient $P_f$ with surjective maps $r, r'$ and an isomorphism $e : P_r times.o_bb(C) P_f tilde.equiv Pi$ intertwining the Fock-model vectors (`fockF`) across the two matched Weil representations $omega_A, omega_B$.
    - `ThetaIntegralsAgree`: Whenever `IsMatch` holds for $(W, W_1, X, A, A_1, B, alpha, beta)$, there exists a nonzero constant $c in bb(C)^times$ such that for every algebraic Schwartz function $Phi'$ on the second model there is a finite-relation-equivalent integrable representative $Phi_0$ whose global theta integral agrees with that of any matched $Phi$ on the first model: `thetaInt omegaA nu F Phi = c * thetaInt omegaB nu1 F1 Phi0`.

    In `FunctionalsSeparateOfHoweUnramOfSiegelWeil.lean`, the separation theorem `functionalsSeparate_of_howeUnram_of_siegelWeil` proves `FunctionalsSeparate` directly from three inputs: the local theta inputs `ThetaLocalInputs`, unramified Howe duality (`HoweUnram`), and the convergent unitary Siegel–Weil formula (`SiegelWeilUnitaryConvergent`), together with the real-branch input `realInputE_holds`.
  ]

  Together, `ThetaIntegralsAgree`, `LocalMatching`, and `FunctionalsSeparate` form the bridge between local representation theory and global automorphic nonvanishing: `LocalMatching` lets us choose local test vectors independently at archimedean and finite places; `ThetaIntegralsAgree` ensures the global theta integral computed in the Schrödinger model (where seesaw duality lives) equals the one in the Fock model (where interlacing weights live); and `FunctionalsSeparate` ensures that the resulting period functionals separate the spectral components without accidental cancellation.

  == Seesaw Duality and Bessel Periods Independent of Hecke Characters

  A crucial miracle occurs when we compute the global period of the $m$-fold iterated theta lift $f_m = Theta^(m)_(underline(Phi)) (f_0)$. A priori, $f_m$ depends intricately on all $m$ auxiliary Hecke characters $mu_1, dots.c, mu_m$ that were injected along the tower $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$. If the global period of $f_m$ tangled $f_0$ inextricably with $mu_1, dots.c, mu_m$, we could never vary the $mu_j$ to kill obstructions or average over them to perform "division". The *seesaw duality identity* (`remark.pdf` item 12) resolves this completely: it collapses the period of the iterated lift onto a *Bessel / GGP period* on the base group that is structurally independent of the auxiliary Hecke characters $mu_j$, while the dependence on $mu_j$ factors out cleanly into a Rallis / doubling-method $L$-value!

  === The Seesaw Formalism for Unitary Dual Pairs

  Recall Kudla's seesaw principle. Suppose $(G_1, H_1)$ and $(G_2, H_2)$ are two reductive dual pairs inside the same ambient symplectic group $op("Sp")(W)$ such that $G_1 subset.eq G_2$ and $H_2 subset.eq H_1$. We display this configuration as a *seesaw diagram*:
  #math.equation(block: true, numbering: none)[$ G_2 quad quad quad H_1 \ | quad times quad | \ G_1 quad quad quad H_2 $]
  where vertical lines denote subgroup inclusions ($G_1 subset.eq G_2$ and $H_2 subset.eq H_1$) and diagonals connect mutually centralizing reductive dual pairs ($(G_1, H_1)$ and $(G_2, H_2)$). Because the Weil representation $omega$ of $op("Sp")(W)(bb(A)_F)$ restricts compatibly to both dual pairs, the theta kernel $theta_Phi$ satisfies the fundamental formal adjointness (seesaw identity): for any automorphic forms $f_1 in cal(A)(G_1)$ and $f_2 in cal(A)(H_2)$,
  $ chevron.l theta_Phi (f_1), f_2 chevron.r_(H_2) &= integral_([H_2]) (integral_([G_1]) theta_Phi (g_1, h_2) overline(f_1 (g_1)) dif g_1) overline(f_2 (h_2)) dif h_2 \ &= chevron.l theta_Phi^* (f_2), f_1 chevron.r_(G_1), $
  provided the double integral converges absolutely (which is automatic when both $[G_1]$ and $[H_2]$ are compact, i.e., for totally definite unitary groups!).

  Now consider an orthogonal decomposition of Hermitian spaces:
  $ V_0 = A plus.o L, quad X = T plus.o L'', $
  where $L = E zeta_1$ and $L'' = E zeta$ are one-dimensional Hermitian lines of *opposite norm*:
  $ chevron.l zeta_1, zeta_1 chevron.r_L = - chevron.l zeta, zeta chevron.r_(L''). $
  In `SeeSawFourier.lean`, this condition is formalized as `OppLines L L'' zeta1 zeta`. Because $L plus.o L''$ is a split hyperbolic plane (an isotropic two-dimensional Hermitian space), the partial Fourier transform along the line $L$ exchanges the Weil representation model on $V_0 times.o S = (A plus.o L) times.o S$ with that on $S times.o X = S times.o (T plus.o L'')$.

  #lemma(title: "Seesaw Line Fourier Transform")[
    Let $V_0 = A plus.o L$ and $X = T plus.o L''$ be orthogonal decompositions of Hermitian $E$-spaces with one-dimensional lines $L = E zeta_1$ and $L'' = E zeta$ satisfying $chevron.l zeta_1, zeta_1 chevron.r_L = -chevron.l zeta, zeta chevron.r_(L'')$. Let $S$ be any Hermitian $E$-space, and let $v$ be a finite place of $F$ splitting in $E$ with local field $k = F_v$. Under the partial Fourier transform
    $ hat(f)(eta) = integral_(k^n) f(y) psi_v (-eta dot.c y) dif y $
    along the line coordinate, the mixed Weil model $M_1$ for $(L, S)$ is intertwined with the mixed Weil model $M_2$ for $(S, L'')$:
    $ M_2 (op("ofRow")(hat(f))) (beta(x)) = M_1 (op("ofCol")(f)) (x), $
    where $beta : W_0 (L, S) -> W_0 (S, L'')$ is the canonical involution induced by the opposite-norm lines $(zeta_1, zeta)$.
  ]

  #proof[
    At a split place $v$, the Heisenberg action of $W_0 (L, S)$ translates the argument of $f$ along one Lagrangian and multiplies by a phase along the dual Lagrangian. The Euclidean Fourier transform $f |-> hat(f)$ swaps translation by $a in k^n$ with multiplication by $psi_v (-eta dot.c a)$, and swaps multiplication by $psi_v (a' dot.c y)$ with translation by $a'$. Because $chevron.l zeta_1, zeta_1 chevron.r_L = -chevron.l zeta, zeta chevron.r_(L'')$, the symplectic form on $L times.o S$ matches the negative of the symplectic form on $S times.o L''$ under $beta$, so the Heisenberg intertwining relations `IsModel` are preserved identically. By Stone–von Neumann uniqueness of the Heisenberg representation, the intertwiner $M_2$ is uniquely determined up to a scalar, fixed to $1$ by evaluating at the origin.
  ]

  === Reduction of the Iterated Lift Period to a Character-Independent Bessel Period

  Applying the seesaw identity inductively along the tower $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ produces the main structural theorem of this section. To state it cleanly, let $H_m subset.eq U(X_m)$ be the Bessel / GGP subgroup stabilizing an orthogonal decomposition
  $ X_m = X_0 plus.o L_1 plus.o L_2 plus.o dots.c plus.o L_m, $
  where each $L_j$ has dimension $t$ (in the simplest case $t = 1$, each $L_j$ is an anisotropic line). For a character $eta_m$ on the unipotent/toric part of the Bessel subgroup (or, in the totally definite setting, a test vector $phi.alt_B$ on the orthogonal complement $L_1 plus.o dots.c plus.o L_m$), define the *Bessel / GGP period* of an automorphic form $f_m in cal(A)(U(X_m))$ against $f_0 in cal(A)(U(X_0))$ by
  $ &cal(B)(f_m, f_0; phi.alt_B) \
    &= integral_([U(X_0)]) integral_([U(X_0^perp)]) f_m (g_0, g_perp) overline(f_0 (g_0)) overline(phi.alt_B (g_perp)) dif g_perp dif g_0. $
  More generally, when $X_m$ is split at an auxiliary place or when one passes to the quasi-split/indefinite realization via `LocalMatching`, $cal(B)$ is the global Bessel period attached to the GGP subgroup $U(X_0) times.l N_m subset.eq U(X_m)$ with generic character $psi_(N_m)$.

  #theorem(title: "Seesaw Independence of the Iterated Bessel Period")[
    Let $f_0 in pi_0$ be an automorphic form on the totally definite unitary group $U(X_0)(bb(A)_F)$, and let $f_m = Theta^(m)_(underline(Phi)) (f_0) in cal(A)(U(X_m))$ be its $m$-fold iterated theta lift along the tower $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ with auxiliary splitting Hecke characters $(mu_1, dots.c, mu_m)$. Suppose the Schwartz functions $Phi_j = Phi_j^((0)) times.o Phi_j^((perp))$ are chosen compatibly with the orthogonal decompositions $X_j = X_(j-1) plus.o L_j$. Then the global period of $f_m$ decomposes via $m$ applications of seesaw duality as
    $ cal(P)(f_m) = cal(B)_(X_0) (f_0; Phi_("base")) dot.c product_(j=1)^m cal(I)_j (mu_j; Phi_j^((perp))), $
    where:
    + The *base Bessel period* $cal(B)_(X_0) (f_0; Phi_("base"))$ depends only on $f_0$ and the base Hermitian geometry of $X_0$, and is completely *independent* of the auxiliary Hecke characters $mu_1, dots.c, mu_m$.
    + Each factor $cal(I)_j (mu_j; Phi_j^((perp)))$ is a global theta-period (or doubling zeta integral) on the rank-$t$ orthogonal complement $U(L_j)$ depending solely on $mu_j$ and $Phi_j^((perp))$.
  ]

  #proof[
    We proceed by induction on the chain length $m >= 1$. For $m = 1$, write $X_1 = X_0 plus.o L_1$ and consider the seesaw diagram inside the symplectic space $op("Res")_(E \/ F) (X_0 times.o X_1) = op("Res")_(E \/ F) (X_0 times.o X_0) plus.o op("Res")_(E \/ F) (X_0 times.o L_1)$:
    #math.equation(block: true, numbering: none)[$ U(X_1) quad quad quad U(X_0) times U(X_0) \ | quad quad times quad quad | \ U(X_0) times U(L_1) quad quad quad U(X_0)^Delta $]
    where $U(X_0)^Delta subset.eq U(X_0) times U(X_0)$ is the diagonal embedding. For a factorizable Schwartz function $Phi_1 = Phi_1^((0)) times.o Phi_1^((perp))$ on $(X_0 times.o X_0) plus.o (X_0 times.o L_1)$ and $(g, h_0, h_1) in U(X_0) times U(X_0) times U(L_1)$, the theta kernel splits as a product:
    $ theta_(Phi_1) (g, (h_0, h_1)) = theta_(Phi_1^((0))) (g, h_0) dot.c theta_(Phi_1^((perp))) (g, h_1). $
    Integrating the single-step lift $f_1 (h_0, h_1) = integral_([U(X_0)]) theta_(Phi_1) (g, (h_0, h_1)) overline(f_0 (g)) dif g$ against a character-eigenform $eta_1$ on $[U(L_1)]$ and a test form $phi.alt_0$ on $[U(X_0)]$, Fubini's theorem (justified unconditionally by the compactness of $[U(X_0)]$ and $[U(L_1)]$) yields
    $ &integral_([U(X_0)]) integral_([U(L_1)]) f_1 (h_0, h_1) overline(phi.alt_0 (h_0)) overline(eta_1 (h_1)) dif h_1 dif h_0 \
    &= integral_([U(X_0)]) overline(f_0 (g)) (integral_([U(X_0)]) theta_(Phi_1^((0))) (g, h_0) overline(phi.alt_0 (h_0)) dif h_0) \
    &quad times (integral_([U(L_1)]) theta_(Phi_1^((perp))) (g, h_1) overline(eta_1 (h_1)) dif h_1) dif g. $
    In this triple integral, the splitting character $mu_1$ enters the second inner integral via the action of $U(L_1)$ on $Phi_1^((perp))$, while the first inner integral is the self-dual theta lift of $phi.alt_0$ on the equal-rank pair $(U(X_0), U(X_0))$---which by the equal-rank Siegel–Weil / Rallis mechanism (or by choosing $Phi_1^((0))$ to project onto the diagonal Bessel kernel) produces a form on $U(X_0)$ whose pairing with $f_0$ is independent of $mu_1$ once the splitting twist on $U(X_0)$ is compensated by $mu_1^(-1)$ in the $U(L_1)$-integral.

    More specifically, in the $m$-step induction, suppose the seesaw reduction has been carried out for the top step $U(X_(m-1)) -> U(X_m)$ with $X_m = X_(m-1) plus.o L_m$. Pairing $f_m = theta_(Phi_m) (f_(m-1))$ against the Bessel data on $U(X_(m-1)) times U(L_m)$ swaps the integral over $[U(X_m)]$ for an integral over $[U(X_(m-1))]$ against the theta lift of the $U(L_m)$-character $eta_m$ (twisted by $mu_m$). Because $eta_m$ is chosen to cancel the splitting character $mu_m$ on the $U(L_m)$ factor, the resulting integral on $[U(X_(m-1))]$ factors into the $m$-th scalar factor $cal(I)_m (mu_m; Phi_m^((perp)))$ times a Bessel period of $f_(m-1)$ on $U(X_(m-1))$ whose kernel does not depend on $mu_m$. Applying the induction hypothesis $m - 1$ times collapses the entire $m$-fold iterated lift onto the base Bessel period $cal(B)_(X_0) (f_0; Phi_("base"))$ multiplied by $product_(j=1)^m cal(I)_j (mu_j; Phi_j^((perp)))$.
  ]

  === The Rallis Inner Product Formula and the Doubling Method

  Having isolated the dependence on $mu_j$, we must evaluate the $L^2$-norm $norm(f_m)_(L^2 ([U(X_m)]))^2$ of the $m$-fold iterated lift---both to prove nonvanishing and to control the exact archimedean and finite-place cost of each lift step. The tool that evaluates the Petersson inner product of theta lifts is the *Rallis inner product formula*, which reduces $chevron.l theta_Phi (f), theta_(Phi') (f') chevron.r$ via the *Piatetski-Shapiro–Rallis doubling method* to an Euler product of local doubling zeta integrals and a central/special value of the standard $L$-function!

  Let $V$ and $W$ be Hermitian spaces over $E$ of ranks $n = dim_E V$ and $m' = dim_E W$, and form the *doubled space*
  $ bb(V) = V plus.o (-V), $
  where $-V$ denotes $V$ equipped with the negated Hermitian form $-chevron.l dot.c, dot.c chevron.r_V$. Then $bb(V)$ is a split Hermitian space of rank $2 n$ containing the maximal isotropic diagonal subspace $V^Delta = {(v, v) : v in V}$. Let $P subset.eq U(bb(V))$ be the Siegel parabolic subgroup stabilizing $V^Delta$. We have a natural embedding
  $ iota : U(V) times U(V) arrow.hook U(bb(V)), $
  which sits inside the doubling seesaw diagram:
  #math.equation(block: true, numbering: none)[$ U(bb(V)) quad quad quad U(W) times U(W) \ | quad quad times quad quad | \ U(V) times U(V) quad quad quad U(W)^Delta $]
  Applying the seesaw identity to $f, f' in pi subset.eq cal(A)(U(V))$ and Schwartz functions $Phi, Phi' in cal(S)(bb(X)(bb(A)_F))$ yields
  $ &chevron.l theta_Phi (f), theta_(Phi') (f') chevron.r_(U(W)) \
    &= integral_([U(V)] times [U(V)]) (integral_([U(W)]) theta_(Phi times.o overline(Phi')) (iota(g_1, g_2), h) dif h) \
    &quad times overline(f(g_1)) f'(g_2) dif g_1 dif g_2. $
  The inner integral over $[U(W)]$ is precisely the *theta integral* $I(g; Phi times.o overline(Phi'))$ for the dual pair $(U(W), U(bb(V)))$. By the *convergent unitary Siegel–Weil formula* (Ichino, Kudla–Rallis, Gan–Qiu–Takeda; formalized in Lean as `SiegelWeilUnitaryConvergent` and `WeilSiegelFormulaUnitary`), in the convergence range $m' > n$ (or for anisotropic $W$, which holds unconditionally here because $W$ is totally definite!), this theta integral equals the special value of a degenerate Siegel Eisenstein series on $U(bb(V))$:
  $ integral_([U(W)]) theta_(Phi times.o overline(Phi')) (g, h) dif h = E(g, s_0; cal(F)_(Phi times.o overline(Phi'))), quad s_0 = (m' - n) / 2, $
  where $cal(F)_(Phi times.o overline(Phi')) (g, s)$ is the standard section of the degenerate principal series $I(s, chi) = op("Ind")_(P(bb(A)_F))^(U(bb(V))(bb(A)_F)) (chi dot.c |det|_(bb(A)_E)^s)$ associated to $Phi times.o overline(Phi')$ at $s = s_0$ via the Weil representation!

  Substituting the Siegel–Weil formula into the doubling integral gives the *Piatetski-Shapiro–Rallis doubling integral*
  $ &Z(s, f, f', cal(F)) \
    &= integral_([U(V)] times [U(V)]) E(iota(g_1, g_2), s; cal(F)) overline(f(g_1)) f'(g_2) dif g_1 dif g_2. $
  By the basic unfolding of the doubling method (unfolding the Siegel Eisenstein series over the open $U(V) times U(V)$-orbit in $P backslash U(bb(V))$), this global integral factors completely into an Euler product of local doubling zeta integrals!

  #theorem(title: "Rallis Inner Product Formula via the Doubling Method")[
    Let $V$ and $W$ be totally definite Hermitian spaces over $E$ of ranks $n = dim_E V$ and $m' = dim_E W$ with $m' >= n$, and let $pi = times.o.big'_v pi_v$ be an irreducible automorphic representation of $U(V)(bb(A)_F)$. Let $f = times.o.big'_v f_v$ and $f' = times.o.big'_v f'_v$ be factorizable vectors in $pi$, and let $Phi = times.o.big'_v Phi_v$ and $Phi' = times.o.big'_v Phi'_v$ be factorizable Schwartz functions. Let $S$ be a finite set of places of $F$ containing all archimedean places and all finite places where $E \/ F, V, W, pi, psi, chi, chi', f, f', Phi, Phi'$ are ramified. Then:
    $ &chevron.l theta_Phi (f), theta_(Phi') (f') chevron.r_(U(W)) \ &= (L^S (s_0 + 1/2, op("BC")(pi) times chi)) / (b_n^S (s_0, chi)) dot.c product_(v in S) Z_v (s_0, f_v, f'_v, Phi_v, Phi'_v), $
    where $s_0 = (m' - n) / 2$, the normalizing factor is the product of abelian $L$-functions
    $ b_n^S (s, chi) = product_(r=0)^(n-1) L^S (2 s + n - r, chi|_(bb(A)_F^times) dot.c omega_(E \/ F)^r), $
    and for each $v in S$, the local doubling zeta integral is
    $ &Z_v (s, f_v, f'_v, Phi_v, Phi'_v) \ &= integral_(U(V)(F_v)) chevron.l pi_v (g_v) f_v, f'_v chevron.r_v dot.c cal(F)_(Phi_v times.o overline(Phi'_v)) (iota(g_v, 1), s) dif g_v. $
  ]

  #proof[
    By the seesaw identity for $(U(V) times U(V), U(W)^Delta)$ and $(U(bb(V)), U(W) times U(W))$, we have
    $ &chevron.l theta_Phi (f), theta_(Phi') (f') chevron.r_(U(W)) \ &= integral_([U(V)] times [U(V)]) I(iota(g_1, g_2); Phi times.o overline(Phi')) overline(f(g_1)) f'(g_2) dif g_1 dif g_2. $
    Because $W$ is totally definite (hence anisotropic), the convergent unitary Siegel–Weil formula replaces $I(g; Phi times.o overline(Phi'))$ by the Siegel Eisenstein series $E(g, s_0; cal(F))$ at $s_0 = (m' - n)/2$. For $op("Re")(s) >> 0$, unfolding $E(g, s; cal(F)) = sum_(gamma in P(F) backslash U(bb(V))(F)) cal(F)(gamma g, s)$ over the double cosets $P(F) backslash U(bb(V))(F) \/ (U(V)(F) times U(V)(F))$ reveals that all non-open orbits contribute zero (by cuspidality / orthogonality on the compact group $U(V)$, or more generally by the vanishing of degenerate orbits for cuspidal/definite $pi$), while the unique open orbit has stabilizer $U(V)^Delta (F)$. Folding the sum back against the integral over $[U(V)] times [U(V)]$ collapses the double integral to a single adelic integral of matrix coefficients:
    $ Z(s, f, f', cal(F)) &= integral_(U(V)(bb(A)_F)) chevron.l pi(g) f, f' chevron.r_(U(V)) cal(F)(iota(g, 1), s) dif g \ &= product_v Z_v (s, f_v, f'_v, cal(F)_v). $
    At every unramified finite place $v in.not S$, the Piatetski-Shapiro–Rallis unramified computation (`UnramifiedDoublingGL` and `DoublingMethodLocalZetaIntegrals`) evaluates the spherical integral explicitly as
    $ Z_v (s, f_v, f'_v, cal(F)_v) = (L_v (s + 1/2, op("BC")(pi_v) times chi_v)) / (b_(n, v) (s, chi_v)) chevron.l f_v, f'_v chevron.r_v. $
    Taking the product over $v in.not S$, analytically continuing both sides in $s$ to $s = s_0 = (m' - n)/2$ (using the meromorphic continuation of $E(g, s; cal(F))$ and the partial $L$-function), and evaluating at $s = s_0$ yields the stated Rallis inner product formula.
  ]

  When we iterate Theorem 13.9 along the $m$-step tower $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ with $n_j = n_(j-1) + t$, each step has $s_0 = t / 2$, so the squared $L^2$-norm of the $m$-fold iterated lift $f_m$ is governed by the product of the $m$ special $L$-values
  $ product_(j=1)^m (L^S ((t + 1) / 2, op("BC")(pi_(j-1)) times mu_j^(-1))) / (b_(n_(j-1))^S (t / 2, mu_j^(-1))) $
  times the product of local doubling zeta integrals at the ramified and archimedean places $v in S$! Because $s_0 + 1/2 = (t + 1)/2 >= 1$, for $t >= 2$ (and even for $t = 1$, at the edge of absolute convergence $s_0 + 1/2 = 1$), these $L$-values sit *outside* the critical strip (or on its right boundary $op("Re")(s) = 1$), where nonvanishing is known unconditionally by Jacquet–Shalika!

  #lean-note(title: "Lean 4 Formalization: Doubling Method and Rallis Tower Compatibility", module: "DoublingMethodOfEisensteinFacts.lean & ThetaTowerCompatibility.lean")[
    The doubling method and Rallis inner product pipeline is formalized across three layers in `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/`:
    - `DoublingMethodOfEisensteinFacts.lean` proves `doubling_zeta_of_eisenstein_facts`, deriving `DoublingMethodLocalZetaIntegrals` from `CuspRapidDecay` and `SiegelEisensteinContinuation` (via `ResidueKilled.dm_of_two`).
    - `ThetaTowerCompatibility.lean` proves `theta_tower_compatibility`, taking `WeilRepresentationUnitaryPair`, `CuspRapidDecay`, and `DoublingMethodLocalZetaIntegrals` to deduce the global anisotropic Rallis inner product form `GlobalFormAniso D` from the Fock-model Siegel–Weil identity `SiegelWeilFockAniso D`.
    - `EulerFactorFromDoubling.lean` and `HeckeFormOfDoubling.lean` extract the unramified Euler factors $(L_v (s + 1/2, op("BC")(pi_v) times chi_v)) / (b_(n, v) (s, chi_v))$ and match them against the Hecke eigenvalues on the lifted group $U(X_j)$.
  ]

  == The $2/3$ Lift-Cost Barrier and Its Resolution via Twisting and "Division"

  At first sight, having established the $m$-fold iterated lift $U(X_0) -> dots.c -> U(X_m)$, its spectral transfer $pi |-> pi plus.square mu_j [t]$, and the seesaw / Rallis evaluation of its periods and norms, one might expect the proof of the Generalized Riemann Hypothesis to follow immediately by setting $m approx sqrt(X)$ and applying Bost's slope inequality. Yet a subtle and formidable quantitative obstruction intervenes: *a naive accounting of the archimedean and level cost of each theta lift step stalls at the exponent $sigma = 2/3$, strictly short of the critical line $sigma = 1/2$!*

  Understanding this $2/3$ barrier---and how Alpöge and Claude shatter it via character twisting and algebraic "division" (`remark.pdf` items 14–15)---is essential to grasping why the proof requires the full machinery of integral structures, Hecke character families, and relative trace formulas.

  === Precise Accounting of the Lift Cost: Why Naive Iteration Stalls at $2/3$

  Let us compute the exact cost of a single theta lift step $U(X_(j-1)) -> U(X_j)$ of rank increment $t$ (for clarity, normalize $t = 1$, so $n_j = n_0 + j$). Suppose we start with an arithmetic input of size $X$ (the length of the von Mangoldt sum) and seek to rule out a zero $rho = beta + i gamma$ with $beta > sigma_0$. Three quantities grow as $j$ runs from $1$ to $m$:

  + *Weyl dimension and archimedean norm cost.* At each archimedean place $v | oo$, the representation $pi_j$ on the compact group $U(n_j)$ has highest weight $underline(a)^((j))$ whose entries grow by $O(1)$ per step (or remain bounded by $W_j asymp j$) to accommodate the interlacing constraints. By the Weyl dimension formula,
    $ dim V_(underline(a)^((j))) = product_(1 <= r < s <= n_j) (a_r^((j)) - a_s^((j)) + s - r) / (s - r), $
    whose logarithm scales like $O(n_j^2 log n_j)$ for generic weights, or $O(n_j log n_j)$ when the weights are concentrated in a narrow band of width $O(1)$ above the base weights.
  + *Covolume and Siegel mass cost.* By the Siegel–Tamagawa mass formula for a totally definite Hermitian lattice $Lambda_j subset X_j$ of rank $n_j$ and discriminant $D_j$, the mass of the genus of $Lambda_j$ is
    $ op("mass")(Lambda_j) &= sum_([Lambda'] in op("gen")(Lambda_j)) 1 / (abs(op("Aut")(Lambda'))) \
      &asymp D_j^((n_j + 1)/2) product_(r=1)^(n_j) (Gamma(r)) / ((2 pi)^r) L(r, omega_(E \/ F)^r). $
    Taking logarithms, the archimedean Gamma-factor $product_(r=1)^(n_j) Gamma(r) = G(n_j + 1)$ (the Barnes $G$-function) satisfies
    $ log G(n_j + 1) = 1 / 2 n_j^2 log n_j - 3 / 4 n_j^2 + O(n_j log n_j). $
    Summing this covolume / mass contribution over $j = 1, dots.c, m$---or even taking the final group $U(X_m)$ of rank $n_m asymp m$---produces a logarithmic archimedean cost of order $m^2 log m$ from the group volume alone, *plus* an additional factor whenever the level (conductor) $N_j$ of the auxiliary character $mu_j$ grows!
  + *The naive level and conductor cost.* Suppose each step $j = 1, dots.c, m$ requires an auxiliary Hecke character $mu_j$ of conductor $Q_j$ to separate the $j$-th block $mu_j [t]$ from the preceding blocks $mu_1 [t], dots.c, mu_(j-1) [t]$ and from the base spectrum. If the $m$ characters $mu_1, dots.c, mu_m$ are chosen naively as distinct characters of conductor $Q_j asymp j$ (or $Q_j asymp X^alpha$), then at the $j$-th step the Rallis inner product formula involves $L(s_0 + 1/2, op("BC")(pi_(j-1)) times mu_j^(-1))$ and local zeta integrals at the primes dividing $Q_j$. The conductor of $pi_j$ grows multiplicatively:
    $ op("cond")(pi_m) = op("cond")(pi_0) dot.c product_(j=1)^m Q_j^(n_(j-1) + O(1)). $
    Even if $Q_j$ is as small as $asymp m$ (so that $m$ distinct characters exist), the naive *un-divided* global period integral on $U(X_m)$ retains the full product of the $m$ auxiliary local factors $product_(j=1)^m cal(I)_j (mu_j)$ together with the ambient lattice index.

  Let us see precisely how these exponents combine to produce the $2/3$ barrier!

  #proposition(title: "The Naive 2/3 Lift-Cost Barrier")[
    Consider a naive $m$-fold iterated theta lift $U(X_0) -> dots.c -> U(X_m)$ applied to a von Mangoldt sum of length $X$ to test a hypothetical zero $rho = beta + i gamma$ with $1/2 < beta < 1$. Suppose:
    + The arithmetic divisibility lower bound from order-$m$ vanishing has logarithmic size $log cal(D)_m >= c_1 m X^beta$.
    + Without cancelling the auxiliary character factors across steps, the *un-divided* logarithmic height upper bound on the $m$-fold lift satisfies
      $ log cal(H)_m^("naive") <= c_2 (m^3 + X) log X, $
      where the cubic term $m^3$ arises because at each of the $m$ steps, the $j$-th lift carries a rank-$j$ covolume/norm cost *multiplied* by the number of auxiliary level/character parameters (or equivalently, $sum_(j=1)^m j^2 = m(m+1)(2m+1)/6 asymp m^3 / 3$ from the uncancelled Barnes $G$-function / Siegel mass $exp(O(j^2))$ accumulated across all $m$ intermediate spaces $X_1, dots.c, X_m$).

    Then the naive Bost slope inequality $log cal(D)_m <= log cal(H)_m^("naive")$ yields
    $ c_1 X^beta <= c_2 (m^2 + X / m) log X. $
    Minimizing $m^2 + X / m$ over $m > 0$ uniquely selects $m asymp X^(1/3)$, at which point
    $ m^2 + X / m asymp X^(2/3), $
    yielding a contradiction only for $beta > 2/3$ and stalling completely at the barrier $beta = 2/3$.
  ]

  #proof[
    Dividing $c_1 m X^beta <= c_2 (m^3 + X) log X$ by $m$ gives $c_1 X^beta <= c_2 (m^2 + X / m) log X$. Setting $h(m) = m^2 + X / m$, we differentiate to find $h'(m) = 2 m - X / m^2 = 0$, which has the unique positive root $m_* = (X / 2)^(1/3)$. At $m = m_*$,
    $ h(m_*) = (2^(-2/3) + 2^(1/3)) X^(2/3) = 3 dot.c 2^(-2/3) X^(2/3). $
    Hence the inequality $c_1 X^beta <= c_2 h(m_*) log X$ produces a contradiction as $X -> oo$ if and only if $beta > 2/3$. For any $beta in (1/2, 2/3]$, no choice of $m$ yields a contradiction.
  ]

  #insight-box(title: "Why Cubic vs. Quadratic Cost Is Everything")[
    Compare the two scaling laws side by side:
    - *Naive (uncancelled) cumulative cost $m^3$:* minimizing $m^3 / m + X / m = m^2 + X / m$ forces $m = X^(1/3)$ and stalls at $X^(2/3)$, proving only $beta <= 2/3$.
    - *Divided (cancelled) net cost $m^2$:* minimizing $m^2 / m + X / m = m + X / m$ forces $m = X^(1/2)$ and reaches $X^(1/2)$, proving $beta <= 1/2$ (i.e., the full Generalized Riemann Hypothesis!).

    In fact, the same dichotomy governs the general exponent $alpha$: if the total logarithmic height scales as $m^(1 + 1/theta) + X$, then dividing by $m$ gives $m^(1/theta) + X / m$, whose minimum is $X^(1 / (1 + theta))$ at $m = X^(theta / (1 + theta))$. Reaching the Riemann critical line $1 / (1 + theta) = 1/2$ requires $theta = 1$ (quadratic total cost $m^2$), whereas $theta = 1/2$ (cubic total cost $m^3$) hits the exact wall $1 / (1 + 1/2) = 2/3$!
  ]

  This exact barrier is visibly inscribed in the Lean 4 codebase: the module `BoundAtTwoThreeFamilyFon.lean` (imported directly by `SiegelEisensteinSecondTermHypotheses.lean`) defines `BoundAtTwoThreeFamilyFonAlt`, which packages the sharp $2/3$-level control on the family of forms before the twisting and division step pushes the exponent down from $2/3$ to $1/2$.

  === Breaking the $2/3$ Barrier: Twisting and Algebraic "Division"

  How does one reduce the logarithmic lift cost from $O(m^3)$ down to $O(m^2)$ without sacrificing the order-$m$ multiplicity? Looking back at Theorem 13.8 (the seesaw independence of the Bessel period), the source of the excess $m^3$ cost is immediately transparent: the naive global period of the $m$-fold lift is a *product*
  $ cal(P)(f_m) = cal(B)_(X_0) (f_0; Phi_("base")) dot.c product_(j=1)^m cal(I)_j (mu_j; Phi_j^((perp))), $
  in which the base Bessel period $cal(B)_(X_0) (f_0)$---the sole term that actually probes the prime-power / zero-detection arithmetic---is weighed down by the extraneous product $product_(j=1)^m cal(I)_j (mu_j)$ of auxiliary theta integrals and their associated Siegel–Barnes mass factors! Because $cal(B)_(X_0) (f_0)$ is *independent* of the tuple $underline(mu) = (mu_1, dots.c, mu_m)$, the extraneous factor $product_(j=1)^m cal(I)_j (mu_j)$ is a *common factor* shared across different choices of the auxiliary Hecke characters---or, more subtly, its arithmetic denominator/content varies across $underline(mu)$ while the base period remains fixed.

  Alpöge and Claude resolve the $2/3$ barrier through a two-pronged strategy (`remark.pdf` items 14–15):

  *Mechanism 1: Twisting by auxiliary Hecke characters.*
  Instead of fixing a single tuple $underline(mu) = (mu_1, dots.c, mu_m)$, we allow $underline(mu)$ to range over a large, carefully constructed family $cal(F)_("tw")$ of finite-order (or fixed-infinity-type) Hecke characters of $bb(A)_E^times \/ E^times$. Varying $underline(mu) in cal(F)_("tw")$ accomplishes two things simultaneously:
  1. *Killing spurious main terms and cohomology obstructions.* Certain unwanted terms in the period expansion---including Galois cohomology classes in $H^1 (cal(O)_E [1 \/ ell], bb(Q)_ell \/ bb(Z)_ell (-e))$ (`remark.pdf` item 17)---transform nontrivially under twisting by $mu_j$, whereas the target Bessel period $cal(B)_(X_0) (f_0)$ is invariant. Twisting isolates and annihilates these obstructing classes (leaving only a tiny residual set controlled by a weakened Vandiver-type bound).
  2. *Keeping the archimedean weights bounded.* By using finite-order characters $mu_j$ (or characters with fixed, small infinity type) rather than increasing the archimedean weights at every step, the spectral separation between $mu_1 [t], dots.c, mu_m [t]$ is achieved at the *finite* places rather than at infinity, preventing the archimedean Weyl dimension from blowing up cubically.

  *Mechanism 2: Algebraic "division" via the integral structure ("gcd").*
  Even after fixing the infinity type, each individual choice of $underline(mu) in cal(F)_("tw")$ yields an algebraic number (after normalizing by CM periods via Chowla–Selberg) whose height includes the extraneous factor $product_(j=1)^m cal(I)_j (mu_j)$. One cannot simply divide by $product_(j=1)^m cal(I)_j (mu_j)$ as a complex number without losing *integrality* (which is essential for the Bost slope / Liouville lower bound: a nonzero algebraic integer $alpha$ has $product_v |alpha|_v >= 1$, whereas a rational quotient $alpha / beta$ only satisfies a lower bound weakened by the denominator $beta$).

  The remedy is *gluing together an integral structure across the family of Hecke characters $underline(mu) in cal(F)_("tw")$ to take an arithmetic "gcd"* (`remark.pdf` item 15). Let $cal(O)_L$ be the ring of integers of the number field $L$ generated by the Hecke eigenvalues and period ratios across the family. For each $underline(mu) in cal(F)_("tw")$, the normalized $m$-fold lift period defines an element
  $ alpha(underline(mu)) = alpha_0 dot.c c(underline(mu)) in cal(O)_L, $
  where $alpha_0$ is the character-independent base Bessel period (normalized to be integral up to a controlled denominator) and $c(underline(mu)) = product_(j=1)^m cal(I)_j (mu_j)$ is the auxiliary factor.

  #theorem(title: "Integral Division (GCD Averaging) Across the Twist Family")[
    Let $L$ be a number field with ring of integers $cal(O)_L$, and let $cal(F)_("tw")$ be a finite family of Hecke character tuples $underline(mu) = (mu_1, dots.c, mu_m)$. Suppose that for every $underline(mu) in cal(F)_("tw")$, the normalized global period of the $m$-fold iterated lift takes the factored form
    $ alpha(underline(mu)) = alpha_0 dot.c c(underline(mu)) in cal(O)_L, $
    where $alpha_0 in L$ is independent of $underline(mu)$, and the ideal generated by the auxiliary factors $c(underline(mu))$ across the family satisfies the coprimality / small-gcd condition
    $ frak(g) = sum_(underline(mu) in cal(F)_("tw")) c(underline(mu)) cal(O)_L, quad log op("Nm")_(L \/ bb(Q)) (frak(g)) <= O(m^2 log X). $
    Suppose moreover that the integral structure glued across $cal(F)_("tw")$ admits $cal(O)_L$-linear coefficients $lambda_(underline(mu)) in cal(O)_L$ of controlled archimedean height $log max_(underline(mu)) |lambda_(underline(mu))|_oo <= O(m^2 log X)$ (obtained via approximate orthogonality of the columns of the integral structure and Siegel's lemma) such that
    $ sum_(underline(mu) in cal(F)_("tw")) lambda_(underline(mu)) c(underline(mu)) = g_0 in frak(g) without {0}, quad log |op("Nm")_(L \/ bb(Q)) (g_0)| <= O(m^2 log X). $
    Then the averaged combination
    $ tilde(alpha) = sum_(underline(mu) in cal(F)_("tw")) lambda_(underline(mu)) alpha(underline(mu)) = alpha_0 dot.c g_0 in cal(O)_L $
    retains the full order-$m$ divisibility of $alpha_0$ while reducing the logarithmic height upper bound from $O(m^3 log X)$ to $O((m^2 + X) log X)$, thereby breaking the $2/3$ barrier and reaching the critical exponent $1/2$ at $m approx sqrt(X)$.
  ]

  #proof[
    By construction, every term $lambda_(underline(mu)) alpha(underline(mu))$ lies in the ideal $cal(D)_m cal(O)_L$ generated by the order-$m$ divisibility of the iterated lift, because $alpha(underline(mu))$ is divisible by $cal(D)_m$ for every $underline(mu) in cal(F)_("tw")$ and $lambda_(underline(mu)) in cal(O)_L$. Consequently, the linear combination $tilde(alpha) = sum_(underline(mu)) lambda_(underline(mu)) alpha(underline(mu))$ remains in $cal(D)_m cal(O)_L$. On the other hand, by the factorization $alpha(underline(mu)) = alpha_0 c(underline(mu))$, we have $tilde(alpha) = alpha_0 g_0$. Since $g_0 != 0$, if $alpha_0 != 0$ then $tilde(alpha)$ is a nonzero element of $cal(D)_m cal(O)_L$.

    Estimating the archimedean norm of $tilde(alpha)$ at every embedding $sigma : L arrow.hook bb(C)$ directly from the factored expression $tilde(alpha) = alpha_0 g_0$ (rather than from the triangle inequality on the un-divided terms $alpha(underline(mu))$, which would still carry the $m^3$ cost of $c(underline(mu))$) gives
    $ log |sigma(tilde(alpha))| = log |sigma(alpha_0)| + log |sigma(g_0)|. $
    Because $alpha_0$ is the base Bessel period (whose height depends only on the base group $X_0$ and the quadratic rank-sum $O(m^2)$ from the interlacing/evaluation grid) and $log |sigma(g_0)| <= O(m^2 log X)$ by hypothesis, summing over all embeddings $sigma$ yields the product-formula bound
    $ log cal(D)_m <= [L : bb(Q)]^(-1) sum_sigma log |sigma(tilde(alpha))| <= O((m^2 + X) log X). $
    Applying Proposition 13.3 with $m approx sqrt(X)$ now rules out every zero with $beta > 1/2$.
  ]

  This "division" argument is one of the most striking inventions in the entire proof: it uses the *algebraic* factorization $alpha(underline(mu)) = alpha_0 c(underline(mu))$ (guaranteed by seesaw duality!) to pass to the gcd $g_0 = sum lambda_(underline(mu)) c(underline(mu))$ *inside the ring of integers* $cal(O)_L$, cancelling the $m^3$ height of the individual $c(underline(mu))$ without ever leaving the integral structure! In `remark.pdf` (item 16), the approximate orthogonality of the columns of this integral structure---needed to ensure that the gcd ideal $frak(g)$ has small norm and that $g_0 != 0$---is established via a relative trace formula / Cauchy–Schwarz bound on the norm of a suitably projected Poincaré series.

  == Unitary Base Change, Local Langlands, and Test Vector Assembly

  We now trace how every piece developed in Sections 13.1–13.4 is assembled into the formal Lean 4 proof in `SiegelEisensteinSecondTermHypotheses.lean` and its companion modules. In the formalization, the central theorem of this chapter is `nonempty_hyps_definite_side_of_closed_bound` (and its immediate corollary `every_character_of_theta_integrals_local_matching`), which constructs the complete definite-side hypothesis package `HypsAlt S0.NL DefiniteSideCondition` and deduces `UpperTheory.EveryCharacter` (the Generalized Riemann Hypothesis for every Dirichlet character).

  === Unitary Base Change and Local Langlands Inputs

  The hypothesis bundle `UnitaryGroupThirdPlaceHypotheses` (defined in `ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean`) collects the standard representation-theoretic and automorphic theorems needed to control the spectral transfer $pi |-> pi plus.square mu_j [t]$ at every place. Four pillars stand out:

  + *Unitary base change (`BaseChangeDefiniteUnitaryGroup`).* Associates to every irreducible automorphic representation $pi$ of a totally definite unitary group $U(X_j)(bb(A)_F)$ its global base change $op("BC")(pi)$ on $op("GL")_(n_j) (bb(A)_E)$, matching Satake parameters at all unramified places and $L$-parameters at all archimedean places.
  + *Local Langlands and Bernstein–Zelevinsky classification (`RecTExists`, `BernsteinUnitaryProductIrreducible`, `UnlinkedProductIrreducible`, `BernsteinZelevinskyFiniteness`, `LanglandsClassification`).* At every finite place $v$, the local component $op("BC")_v (pi_v)$ is classified via Zelevinsky segments and Bernstein's theorem that parabolic induction of unitary representations of $op("GL")_k$ is irreducible (`BernsteinUnitaryProductIrreducible`), and that products of unlinked segments are irreducible (`UnlinkedProductIrreducible`). Combined with `DepthZeroJacquetInjective` and `GenericUnitaryDualGL`, this prevents unexpected reducibility or spectral collisions when appending the character block $mu_j [t]$ at ramified places.
  + *Global strong multiplicity one and Galois compatibility (`JacquetShalika`, `ClozelCohomological`, `RegularAlgebraicPurity`, `GaloisRepOfPolarizedCuspidal`, `LocalGlobalAboveL`).* Guarantees that the global base change $op("BC")(pi_m)$ is uniquely determined by its unramified places, is regular algebraic and cohomological (so it carries compatible $ell$-adic Galois representations satisfying local-global compatibility above $ell$), and obeys Ramanujan purity at finite places.
  + *Archimedean representation theory (`DiscreteSeriesCover`, `HarishChandraModules`, `CasselmanWallach`, `FormalDegreeCompactDual`).* Controls the archimedean local components, ensuring rapid decay (`CuspRapidDecay`), Casselman–Wallach globalization of smooth Fréchet representations, and exact formal degree formulas via the compact dual.

  === Explicit Test Vector Assembly: `test_vector_assembly_holds`

  To turn the abstract Rallis inner product formula (Theorem 13.9) and seesaw identity (Theorem 13.8) into quantitative arithmetic bounds, we cannot merely know that *some* Schwartz function $Phi = times.o.big'_v Phi_v$ gives a nonzero theta lift; we must explicitly *assemble* a factorizable test vector whose local doubling zeta integrals $Z_v (s_0, f_v, f'_v, Phi_v, Phi'_v)$ are simultaneously nonzero and quantitatively controlled at every place $v$ of $F$!

  #definition(title: "Admissible Local Test Vector Datum")[
    Fix a global datum $D$ encoding the CM field $E \/ F$, the unitary tower $X_0, dots.c, X_m$, and splitting characters $(chi_j, chi'_j)$. A factorizable Schwartz function $Phi = times.o.big'_v Phi_v in cal(S)(bb(X)(bb(A)_F))$ is an *admissible test vector* for the representation $pi$ and evaluation datum $z$ if:
    + At every unramified finite place $v in.not S$, $Phi_v$ is the characteristic function of the standard self-dual lattice $cal(L)_v$, so that the local doubling integral evaluates to the exact Euler factor $(L_v (s_0 + 1/2, op("BC")(pi_v) times chi_v)) / (b_(n, v) (s_0, chi_v))$.
    + At every ramified finite place $v in S_("fin")$, $Phi_v$ is chosen in the level-plus subgroup test space so that the local zeta integral $Z_v$ is nonzero, lies in the prescribed number field $L$ (rationality of row tests, `RowTest`), and has bounded $v$-adic denominator controlled by the conductor of $pi_v$ and $mu_(j, v)$.
    + At every archimedean place $v | oo$, $Phi_v$ is a Fock-model polynomial vector (`fockF`) matched to the interlacing highest-weight projection, so that $Z_v$ is an explicit nonzero rational multiple of a power of $pi$ (cancelled by the Chowla–Selberg period normalization).
  ]

  In `TestVectorAtDatumOfJoin.lean`, this construction is proved as the theorem `test_vector_assembly_holds` (and its underlying implementation `test_vector_at_datum_of_join`). Let us trace its exact logical structure, which mirrors the mathematical pipeline step by step:

  #theorem(title: "Test Vector Assembly (test_vector_assembly_holds)")[
    Assume:
    - the Siegel set and real Howe duality inputs (`SiegelSetUnitary`, `HoweDualityReal`),
    - Green's cuspidal character input (`GreenCuspidal`),
    - the local theta inputs (`ThetaLocalInputs`), the join datum (`JoinOut`), and the Hecke–Tate functional equation (`HeckeTateFunctionalEquation`), and
    - the three global-local compatibility pillars `ThetaIntegralsAgree`, `LocalMatching`, and `FunctionalsSeparate`.

    Then at every admissible evaluation datum $z$, there exists a factorizable test vector realizing the rational row test property `Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)`.
  ]

  #proof[
    We follow the exact four-stage assembly in `test_vector_at_datum_of_join`:
    + *Twisted square convergence and matching.* From `SiegelSetUnitary` and `ThetaLocalInputs`, `twisted_weil_representation_convergence` ensures absolute convergence of the twisted Weil representation integrals. From `HoweDualityReal`, `ThetaIntegralsAgree`, and `LocalMatching`, the theorems `twisted_square_local_matching` and `twisted_theta_integrals_agree` transport local matching and integral agreement to the twisted square setting (the doubled space $bb(V) = V plus.o (-V)$).
    + *Row properties and nonvanishing of $L$-values.* Combining these three twisted-square facts yields the conjugated row properties (`thetaLift_row_properties_conj`). Simultaneously, applying the Hecke–Tate functional equation together with Phragmén–Lindelöf boundedness of completed Hecke $L$-functions in vertical strips (`completedLBoundedInStrips`) proves nonvanishing of the normalizing Hecke $L$-values (`lNe_of_functionalEquation`).
    + *Local factor ratios and tower compatibility.* Using `FunctionalsSeparate` together with the linear bound for cuspidal theta pair lifts (`twisted_linear_bound` and `thetaPairLift_cuspidal_of_hypotheses`), the map from local test spaces to functionals is injective (`injK_of_separates_linB`). Combining triple existence (`triEx_holds_alt`) with the inductive tower theorem (`tower_alt_bis`) proves `twisted_local_factor_ratio_holds`: the ratio of local zeta integrals matches the predicted algebraic local factor at every place.
    + *Extension field and rationality.* Finally, `theta_lift_extension_field_exists` constructs the finite extension field $L$ containing all twisted period ratios, and `atDat_rowTest_of_exField` (using `GreenCuspidal` and `cuspRapidDecay`) assembles the global test vector satisfying `RowTest`.
  ]

  === Evaluation Grids and Fourier Coefficient Fitting

  Once `test_vector_assembly_holds` supplies the rational row test `hRat : S0.RowRat` (via `rowRatW_of_rowTest`), `SiegelEisensteinSecondTermHypotheses.lean` performs two further constructions before assembling the full definite-side hypothesis bundle:

  + *Fourier coefficient fitting (`fourier_coefficient_fit_of_join_alt`).* Given `ThetaLocalInputs`, `JoinOut`, `HeckeTateFunctionalEquation`, `ThetaIntegralsAgree`, `LocalMatching`, `FunctionalsSeparate`, and the lower bound `LambdaLowerBound_2` (extracted from `ontoX_and_lamLow_of_unitaryGroupHypotheses'`), the theorem `fourier_coefficient_fit_of_join_alt` proves `ConstantFunctionFits Fld`. Mathematically, this guarantees that the constant function (encoding the main term of the explicit formula / zero-mode of the Bessel period) is approximated to within the required error tolerance by a linear combination of the Fourier coefficients of the lifted forms at zero (`fittedFunction_at_zero_close_alt`).
  + *Evaluation grid construction (`evaluation_grid_of_join`).* From the same inputs plus `twisted_weil_representation_convergence`, `twisted_local_factors_match`, and `twisted_square_theta_integrals_eq`, the theorem `evaluation_grid_of_join` produces an explicit threshold $C_(F, 1) in bb(R)$ such that for every $C_F >= C_(F, 1)$, the evaluation grid `GridA CF` is *eventually large* (`EvLgG (GridA CF)`). Inside `EvaluationGridOfJoin.lean`, this proof weaves together:
    - Weil–Deligne parameter existence (`exists_weilDeligne_of_localInputs`),
    - normal forms for characters, phases, and jets (`nfChars`, `nfPhase_of_sumOKK`, `nfJet_holds`),
    - rationality of twist ratios in the number field (`twistRatio_mem_numberField` via `toricRatioConjugates_of_transport`),
    - key finiteness (`keyFin_holds`, `gKeyFin`), ensuring that only finitely many bad keys/exceptions occur outside the evaluation grid.

  === The Master Assembly in `SiegelEisensteinSecondTermHypotheses.lean`

  We can now read the proof of `nonempty_hyps_definite_side_of_closed_bound` and `every_character_of_theta_integrals_local_matching` in `SiegelEisensteinSecondTermHypotheses.lean` as a transparent roadmap of the entire chapter.

  #theorem(title: "Definite-Side Hypothesis Assembly and EveryCharacter")[
    Assume:
    + `P : UnitaryGroupThirdPlaceHypotheses` (including `BaseChangeDefiniteUnitaryGroup`, `DoublingMethodLocalZetaIntegrals`, `SiegelWeilUnitaryConvergent`, `JacquetShalika`, `BernsteinUnitaryProductIrreducible`, and archimedean discrete-series/Casselman–Wallach inputs);
    + `F : ThetaLocalInputs`, `hA : ThetaIntegralsAgree`, `hM : LocalMatching`;
    + `hX : CovolumeBoundOfX` (the covolume upper bound along the tower);
    + `hL : RecTExists` (existence of the local Langlands reciprocity correspondence);
    + the closed $2/3$-family bound `BoundAtTwoThreeFamilyFonAlt` across linked parameter slots.

    Then `HypsAlt S0.NL DefiniteSideCondition` is nonempty (`nonempty_hyps_definite_side_of_closed_bound`). Combining this with Green's regular character bridge (`green_of_regular P.greenRegularCharacters`) and the analytic positivity input `hV : VWin` proves `UpperTheory.EveryCharacter` (`every_character_of_theta_integrals_local_matching`): the Generalized Riemann Hypothesis holds for every Dirichlet character.
  ]

  #proof[
    We trace the exact dependency chain of lines 76–105 of `SiegelEisensteinSecondTermHypotheses.lean`:
    + *Step 1 (Separation).* Apply `functionalsSeparate_of_howeUnram_of_siegelWeil` to `F`, `howeUnram_holds`, and `P.siegelWeilUnitaryConvergent` to obtain `hS : FunctionalsSeparate`.
    + *Step 2 (Test vectors and rationality).* Apply `test_vector_assembly_holds` to `F.siegelSetUnitary`, `F.howeDualityReal`, `P.greenCuspidal`, `F`, `P.litN.join`, `P.litN.fe`, `hA`, `hM`, `hS`, and convert via `rowRatW_of_rowTest` to obtain `hRat : S0.RowRat`.
    + *Step 3 (Fourier fit and evaluation grids).* Apply `fourier_coefficient_fit_of_join_alt` to obtain `hFit : ConstantFunctionFits Fld`, and apply `evaluation_grid_of_join` to obtain the threshold $C_(F, 1)$ with `EvLgG (GridA CF)` for all $C_F >= C_(F, 1)$. Independently, `rowFun_at_gridA_alt` uses `P.discreteSeriesCover`, `P.harishChandraModules`, `P.cuspRapidDecay`, `P.casselmanWallach`, `P.rayClassFieldSt`, and `hFit` to produce a second threshold $C_(F, 0)$ governing the row functions on `GridA`.
    + *Step 4 (Unifying the threshold).* Set $C_* = max(C_(F, 0), C_(F, 1))$. Then `GridA C_*` simultaneously satisfies the large-grid property `hEv : EvLgG (GridA C_*)` and the row-function control `hFun`.
    + *Step 5 (Open orbits and linked bundles).* From `open0_of_unitary_group_hypotheses` and monotonicity under stronger extensions (`open_and_linked_of_stronger_extension_alt`), deduce the open parameter statement `hOpenA`, and feed `hOpenA` together with the covolume bound `hX` into `linked_bundles_l3_of_open_alt` to construct the third-layer linked bundles `hL3`.
    + *Step 6 (Final assembly).* Feed `P`, `hRat`, `hL`, `C_*`, `GridA C_*`, `hEv`, the $2/3$-family bound at `C_*`, `hFun`, and `hL3` into `hypotheses_nonempty_of_unramified_exponents_alt` to inhabit `HypsAlt S0.NL DefiniteSideCondition`. Finally, `every_character_of_green_v_win` combines this nonempty hypothesis bundle with `green_of_regular P.greenRegularCharacters` and `hV : VWin` to conclude `UpperTheory.EveryCharacter`.
  ]

  #lean-note(title: "Lean 4 Formalization: Architecture of SiegelEisensteinSecondTermHypotheses.lean", module: "ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean")[
    The file `SiegelEisensteinSecondTermHypotheses.lean` is remarkably compact---only 108 lines---precisely because it sits at the apex of the theta-lift hierarchy. Its two exported theorems in namespace `UpperTheory.Lit`:
    - `nonempty_hyps_definite_side_of_closed_bound` (lines 76–100), and
    - `every_character_of_theta_integrals_local_matching` (lines 101–105),

    act as the master switchboard connecting all five themes of this chapter: the unitary tower and base change (`P : UnitaryGroupThirdPlaceHypotheses`), the local-global theta compatibility (`hA : ThetaIntegralsAgree`, `hM : LocalMatching`, `hS : FunctionalsSeparate`), the covolume bound along the chain (`hX : CovolumeBoundOfX`), the $2/3$-barrier control (`BoundAtTwoThreeFamilyFonAlt`, bridged by `boundAtTwoThree_linked_of_recT`), and the explicit test-vector and evaluation-grid assembly (`test_vector_assembly_holds`, `fourier_coefficient_fit_of_join_alt`, `evaluation_grid_of_join`). Notice that `HypsAlt` (in `Hyps.lean`) explicitly bundles the resulting integral-structure bounds (`hDivG`, `hMt`, `aPerTw`, `aP10`, `hU : MassRatioUnderVolume`) that carry the proof past the $2/3$ barrier to the critical line $1/2$.
  ]

  Looking back over the entire chapter, the unity of the Alpöge–Claude–Riemann architecture is unmistakable. What begins as a deceptively simple analogy to Stepanov's multiplicity over finite fields---chaining $m approx sqrt(X)$ theta lifts between totally definite unitary groups---forces into harmonious collaboration almost every major pillar of modern automorphic representation theory: the Weil representation and Howe duality, unitary base change and the Bernstein–Zelevinsky classification, Gan–Gross–Prasad interlacing periods, seesaw duality and Bessel periods, the Siegel–Weil formula and the Piatetski-Shapiro–Rallis doubling method, and integral "gcd" division across families of Hecke characters. Each piece enters not for ornament, but to solve a precise quantitative obstruction: theta chaining synthesizes multiplicity $m$; seesaw duality decouples the Bessel period from the auxiliary characters $mu_j$; the Rallis–doubling formula controls the $L^2$-norms; and twisting plus integral division breaks the $2/3$ lift-cost barrier all the way to $1/2$.

  #exercises((
    [
      *Generalizing the optimal chain length.* Suppose a Stepanov-type automorphic construction of chain length $m$ yields a logarithmic divisibility lower bound $log cal(D)_m >= c_1 m^a X^beta$ and a logarithmic height upper bound $log cal(H)_m <= c_2 (m^b + X^c) log X$, where $a, b, c > 0$ with $b > a$. Determine the unique optimal exponent $gamma$ such that $m asymp X^gamma$ minimizes the resulting upper bound on $beta$, and compute the sharp threshold $beta_0 (a, b, c)$ above which a contradiction is obtained. Verify that $(a, b, c) = (1, 2, 1)$ gives $gamma = 1/2, beta_0 = 1/2$, while $(a, b, c) = (1, 3, 1)$ gives $gamma = 1/3, beta_0 = 2/3$.
    ],
    [
      *Quadratic rank sum and the Barnes $G$-function.* For a totally definite Hermitian tower $X_0, X_1, dots.c, X_m$ with $n_j = n_0 + j t$, use Stirling's formula $log Gamma(r) = (r - 1/2) log r - r + O(1)$ to prove the asymptotic expansion
      $ log product_(r=1)^(n) Gamma(r) = 1 / 2 n^2 log n - 3 / 4 n^2 + O(n log n) $
      as $n -> oo$. Deduce that if one naively multiplies the Siegel–Tamagawa masses of *all* intermediate spaces $X_1, dots.c, X_m$ without cancellation, the logarithm scales as $(t^2 / 6) m^3 log m$, whereas cancelling the intermediate masses down to a single space $X_m$ reduces the logarithm to $(t^2 / 2) m^2 log m$.
    ],
    [
      *Weyl branching and interlacing determinants.* Let $V_(underline(b))$ be an irreducible representation of $U(n+1)$ with highest weight $underline(b) = (b_1 >= dots.c >= b_(n+1))$, and let $V_(underline(a))$ be an irreducible representation of $U(n)$ with highest weight $underline(a) = (a_1 >= dots.c >= a_n)$.
      + Using the Weyl character formula for $U(n+1)$ and $U(n)$, give a complete proof that $s_(underline(b)) (z_1, dots.c, z_n, 1) = sum_(underline(a) prec underline(b)) s_(underline(a)) (z_1, dots.c, z_n)$.
      + Show that if $W = V plus.o L_1 plus.o dots.c plus.o L_m$ has codimension $m$ over $V$ (so $U(n) subset.eq U(n+m)$), then $dim_bb(C) op("Hom")_(U(n)) (V_(underline(b)), V_(underline(a)))$ can exceed $1$, and describe the combinatorial condition on $(underline(a), underline(b))$ for nonvanishing in terms of $m$-step interlacing sequences (Gelfand–Tsetlin patterns of depth $m$).
    ],
    [
      *Unramified Howe correspondence at a split place.* Let $v$ be a finite place of $F$ splitting in $E$, so $U(V)(F_v) tilde.equiv op("GL")_n (F_v)$ and $U(W)(F_v) tilde.equiv op("GL")_(n+t) (F_v)$. Let $Phi_v^0 = 1_(M_(n, n+t) (cal(O)_(F_v)))$ be the spherical Schwartz function. Compute the action of the spherical Hecke operator $T_(p, 1) = op("diag")(pi.alt_v, 1, dots.c, 1)$ of $op("GL")_(n+t) (F_v)$ on $Phi_v^0$ under the Weil representation $omega_v$, and verify directly that the induced homomorphism on Satake parameters maps $(alpha_1, dots.c, alpha_n)$ to the $(n+t)$-tuple
      $ (mu_v (pi.alt_v)^(-1) alpha_1, dots.c, mu_v (pi.alt_v)^(-1) alpha_n, mu_v (pi.alt_v) q_v^((t-1)/2), dots.c, mu_v (pi.alt_v) q_v^(-(t-1)/2)). $
    ],
    [
      *Seesaw identity for compact unitary groups.* Let $V_0 = A plus.o L$ and $X = T plus.o L''$ be totally definite Hermitian spaces over $E$, and consider a seesaw diagram $(G_1, H_1)$ and $(G_2, H_2)$ with $G_1 subset.eq G_2$ and $H_2 subset.eq H_1$ inside $op("Sp")(W)$. Prove that the formal seesaw identity $chevron.l theta_Phi (f_1), f_2 chevron.r_(H_2) = chevron.l theta_Phi^* (f_2), f_1 chevron.r_(G_1)$ holds *unconditionally* for all smooth functions $f_1 in C^oo ([G_1])$, $f_2 in C^oo ([H_2])$, and $Phi in cal(S)(bb(X)(bb(A)_F))$ whenever $G_1$ and $H_2$ are totally definite. Where does the argument require modification if $G_1$ is indefinite?
    ],
    [
      *Opposite-norm lines and the partial Fourier transform.* In the setting of Lemma 13.7 (`SeeSawFourier.lean`), let $L = E zeta_1$ and $L'' = E zeta$ satisfy $chevron.l zeta_1, zeta_1 chevron.r_L = -chevron.l zeta, zeta chevron.r_(L'')$. Verify explicitly that $L plus.o L''$ is a split Hermitian plane (contains a nonzero isotropic vector $zeta_1 + zeta$). Show that at a split finite place $v$, the map $beta : W_0 (L, S) -> W_0 (S, L'')$ intertwines the symplectic form on $L times.o S$ with the negative of the symplectic form on $S times.o L''$, and deduce the intertwining identity $M_2 (op("ofRow")(hat(f))) (beta(x)) = M_1 (op("ofCol")(f)) (x)$.
    ],
    [
      *Unramified doubling zeta integral for $n = 1$.* Let $V$ be a one-dimensional Hermitian space ($n = 1$), so $U(V) = U(1)$ and $U(bb(V)) = U(1, 1)$. Let $v$ be an unramified finite place of $F$ splitting in $E$, so $U(V)(F_v) tilde.equiv F_v^times$ and $U(bb(V))(F_v) tilde.equiv op("GL")_2 (F_v)$. Taking $pi_v$ to be an unramified character $eta_v$ of $F_v^times$ and $cal(F)_v$ the normalized spherical section of $I_v (s, chi_v)$, compute the local doubling zeta integral
      $ Z_v (s, 1, 1, cal(F)_v) = integral_(F_v^times) eta_v (g) cal(F)_v (iota(g, 1), s) dif^times g $
      explicitly by decomposing the integral over $|g|_v = q_v^k$ ($k in bb(Z)$), and verify that it equals $(L_v (s + 1/2, eta_v chi_v)) / (L_v (2 s + 1, chi_v))$.
    ],
    [
      *Integral division via Siegel's lemma.* Let $L$ be a number field of degree $d = [L : bb(Q)]$, and let $c_1, dots.c, c_N in cal(O)_L$ be nonzero algebraic integers generating an ideal $frak(g) = (c_1, dots.c, c_N) subset.eq cal(O)_L$. Suppose $max_i H(c_i) <= B$, where $H$ is the absolute multiplicative height, and $op("Nm")_(L \/ bb(Q)) (frak(g)) <= G$. Use the geometry of numbers (Minkowski's theorem / Siegel's lemma) to show that there exist algebraic integers $lambda_1, dots.c, lambda_N in cal(O)_L$ such that $g_0 = sum_(i=1)^N lambda_i c_i != 0$ satisfies a height bound controlled by $G$, $d$, and $N$ (and polynomial in $log B$ when $N$ is large enough relative to the prime factors of $c_i$). Explain why this requires $N$ to grow with the number of bad primes dividing the $c_i$, and why varying $underline(mu)$ over a sufficiently rich twist family $cal(F)_("tw")$ supplies this coprimality.
    ],
    [
      *Nonvanishing at the edge of convergence.* In the Rallis inner product formula (Theorem 13.9) for a tower step $U(X_(j-1)) -> U(X_j)$ with rank increment $t >= 1$, the global $L$-function is evaluated at $s_0 + 1/2 = (t + 1) / 2$. Explain why the case $t = 1$ (where $s_0 + 1/2 = 1$) requires the Jacquet–Shalika nonvanishing theorem on the line $op("Re")(s) = 1$, whereas $t >= 2$ (where $s_0 + 1/2 >= 3/2$) lies strictly inside the half-plane of absolute convergence of the Euler product (assuming Ramanujan purity). Discuss the trade-off between choosing $t = 1$ versus $t >= 2$ in the rank-growth bound $n_j = n_0 + j t$.
    ],
  ))
]
