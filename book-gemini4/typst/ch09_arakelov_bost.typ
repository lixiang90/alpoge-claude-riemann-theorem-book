#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch09() = [
  #chapter(
    "Arakelov Geometry, Hermitian Lattices, and Bost's Slope Inequality",
    short-title: "Arakelov Geometry and Bost's Slope Inequality",
    epigraph: "The theory of slopes for Hermitian vector bundles over the ring of integers of a number field provides an arithmetic counterpart to the Harder–Narasimhan formalism for vector bundles on algebraic curves, turning estimates on heights and covolumes into pure homological inequalities.",
    epigraph-source: "After Jean-Benoît Bost, Périodes et isogénies des variétés abéliennes (1996)",
    overview: [
      In the function-field proof of the Weil conjectures and in Stepanov's elementary method, the key global constraint is the degree bound $m dot.c N_q <= deg(Phi)$: a nonzero section of a line bundle of degree $d$ on a smooth projective curve cannot vanish to order $m$ at more than $d \/ m$ points. Over a number field $K$, the scheme $op("Spec") cal(O)_K$ is affine, so a naive algebraic degree does not exist until one compactifies $op("Spec") cal(O)_K$ by adjoining the archimedean places $v | oo$. Arakelov geometry supplies this compactification. Vector bundles over $op("Spec") cal(O)_K$ become Hermitian vector bundles—or, after restriction of scalars to $bb(Z)$, Euclidean lattices—equipped with an arithmetic degree $hat(op("deg"))$ and slope $hat(mu)$. In this chapter we develop the theory of Hermitian lattices from first principles: we prove the supermodularity of the Arakelov degree, construct the canonical Harder–Narasimhan filtration and its concave slope polygon, and give a complete proof of Jean-Benoît Bost's slope inequality, which serves as the exact arithmetic-geometric analogue of Stepanov's degree bound. We then survey the higher-dimensional Arakelov machinery—arithmetic intersection numbers, the Poincaré–Lelong equation, the arithmetic Hilbert–Samuel theorem, Moriwaki's bigness criterion, and Siegel toroidal compactifications—that supplies the covolume bounds for spaces of automorphic forms used in the sequel, and we document their Lean 4 formalization in `Formalism.HN` and `Development.WeilBound`.
    ],
  )

  == Hermitian Vector Bundles over $op("Spec") cal(O)_K$ and Arithmetic Degree

  Let $C$ be a smooth, projective, geometrically irreducible curve over a finite field $bb(F)_q$, and let $cal(E)$ be a vector bundle of rank $r$ on $C$. Because $C$ is projective, every rational function $f in bb(F)_q (C)^times$ has as many zeros as poles, counted with multiplicity:
  $ sum_(P in C) v_P (f) dot.c deg(P) = 0. $
  This single identity makes the degree $deg(cal(E)) = deg(det cal(E))$ well-defined, additive in short exact sequences, and bounded from above on subbundles. In particular, no nonzero morphism $cal(E) -> cal(F)$ can exist when the smallest Harder–Narasimhan slope of $cal(E)$ exceeds the largest Harder–Narasimhan slope of $cal(F)$.

  When we pass from $C$ to $op("Spec") cal(O)_K$, where $K$ is a number field with ring of integers $cal(O)_K$, the product formula still holds, provided we include the archimedean places $v | oo$:
  $ sum_(frak(p)) v_(frak(p)) (alpha) log N(frak(p)) - sum_(v | oo) epsilon_v log |alpha|_v = 0 quad (alpha in K^times), $
  where $frak(p)$ runs over the nonzero prime ideals of $cal(O)_K$, $N(frak(p)) = \# (cal(O)_K \/ frak(p))$ is the ideal norm, $v$ runs over the archimedean places of $K$, $|dot.c|_v$ is the usual real or complex absolute value, and $epsilon_v = 1$ if $v$ is real while $epsilon_v = 2$ if $v$ is complex. Arakelov's fundamental insight is that to obtain a genuine degree theory over $op("Spec") cal(O)_K$, one must attach a Hermitian metric at each infinite place $v | oo$ to every finitely generated projective $cal(O)_K$-module.

  === Euclidean Lattices and Hermitian Vector Bundles

  We begin with the case $K = bb(Q)$, $cal(O)_K = bb(Z)$, where a Hermitian vector bundle is simply a Euclidean lattice. This case is both concrete and completely general: as we will prove in Proposition 9.6, restriction of scalars from $cal(O)_K$ to $bb(Z)$ reduces the slope theory of Hermitian vector bundles over any number field $K$ to that of Euclidean lattices up to a harmless constant shift.

  #definition(title: "Euclidean Lattice")[
    A _Euclidean lattice_ is a pair $overline(L) = (L, ||dot.c||)$ consisting of a free $bb(Z)$-module $L$ of finite rank $r = op("rk")(L)$ together with a Euclidean norm $||dot.c||$ on the real vector space $L_bb(R) = L times.o_bb(Z) bb(R)$, induced by a positive-definite symmetric bilinear form $chevron.l dot.c, dot.c chevron.r$ on $L_bb(R)$.

    Equivalently—and this is the formulation adopted in `Formalism.HN`—given a ring $R$, an $R$-module $V$, a finite-dimensional real inner product space $E$, and an additive homomorphism $rho : V -> E$, an $R$-submodule $L subset.eq V$ is a _lattice_ with respect to $rho$ (written `IsLat ρ L`) if the restriction $rho|_L$ is injective and the image $op("zl")(rho, L) = rho(L)$ is a discrete subgroup of $E$.
  ]

  The second viewpoint has a substantial practical advantage: it allows us to consider lattices equipped with an additional action of a ring $R$ (such as $cal(O)_K$ or a Hecke algebra) and to speak of $R$-submodules $N subset.eq L$ without changing the ambient inner product space $E$. When $R = bb(Z)$ and $V = E$ with $rho = op("id")_E$, a lattice is simply a discrete subgroup $L subset.eq E$.

  #definition(title: "Covolume, Arakelov Degree, and Slope over Z")[
    Let $overline(L) = (L, ||dot.c||)$ be a Euclidean lattice of rank $r = op("rk")(L)$. Choose a $bb(Z)$-basis $e_1, dots.c, e_r$ of $L$, and form its _Gram matrix_
    $ G(e_1, dots.c, e_r) = (chevron.l e_i, e_j chevron.r)_(1 <= i, j <= r) in op("Mat")_(r times r)(bb(R)). $
    The _covolume_ of $overline(L)$ is
    $ op("covol")(overline(L)) = sqrt(det G(e_1, dots.c, e_r)) > 0, $
    with the convention $op("covol")(0) = 1$ when $r = 0$. The _Arakelov degree_ (or _arithmetic degree_) of $overline(L)$ is
    $ hat(op("deg"))(overline(L)) = -log op("covol")(overline(L)), $
    and when $r >= 1$, the _slope_ of $overline(L)$ is
    $ hat(mu)(overline(L)) = (hat(op("deg"))(overline(L))) / (op("rk")(overline(L))) = -(log op("covol")(overline(L))) / r. $
  ]

  Let us verify immediately that $op("covol")(overline(L))$ is independent of the choice of $bb(Z)$-basis. If $e'_1, dots.c, e'_r$ is another $bb(Z)$-basis of $L$, then $e'_j = sum_(i=1)^r u_(i j) e_i$ for a unimodular matrix $U = (u_(i j)) in op("GL")_r (bb(Z))$. Consequently,
  $ G(e'_1, dots.c, e'_r) = U^T G(e_1, dots.c, e_r) U, $
  and since $det(U) in {plus.minus 1}$, we have $det G(e'_1, dots.c, e'_r) = (det U)^2 det G(e_1, dots.c, e_r) = det G(e_1, dots.c, e_r)$. Moreover, if $L$ spans $E$ over $bb(R)$ (a full-rank lattice), then $op("covol")(overline(L))$ equals the Lebesgue volume of the fundamental parallelepiped $sum_(i=1)^r [0, 1) e_i$ in $E$. In terms of exterior powers, equipping $Lambda^r L_bb(R)$ with the induced Euclidean inner product $chevron.l v_1 and dots.c and v_r, w_1 and dots.c and w_r chevron.r = det(chevron.l v_i, w_j chevron.r)$, we have
  $ op("covol")(overline(L)) = ||e_1 and dots.c and e_r||, quad hat(op("deg"))(overline(L)) = -log ||e_1 and dots.c and e_r||. $
  The minus sign in $hat(op("deg"))(overline(L)) = -log op("covol")(overline(L))$ is dictated by geometry: a lattice with _small_ covolume contains _many_ short nonzero vectors (by Minkowski's convex body theorem), just as a vector bundle of _large_ degree on a curve has _many_ global sections (by Riemann–Roch).

  We now extend this definition to an arbitrary number field $K$ of degree $d = [K : bb(Q)]$.

  #definition(title: "Hermitian Vector Bundle over Spec O_K")[
    A _Hermitian vector bundle_ over $op("Spec") cal(O)_K$ is a pair $overline(E) = (E, {||dot.c||_sigma}_(sigma : K -> bb(C)))$ consisting of:
    1. a finitely generated projective $cal(O)_K$-module $E$ of rank $r = op("rk")_(cal(O)_K) (E)$, and
    2. for each field embedding $sigma : K -> bb(C)$, a Hermitian norm $||dot.c||_sigma$ on the $r$-dimensional complex vector space $E_sigma = E times.o_(cal(O)_K, sigma) bb(C)$, satisfying the compatibility condition $||overline(x)||_(overline(sigma)) = ||x||_sigma$ under complex conjugation (so that for a real embedding $sigma : K -> bb(R)$, $||dot.c||_sigma$ restricts to a Euclidean norm on $E times.o_(cal(O)_K, sigma) bb(R)$).

    Grouping conjugate pairs of complex embeddings into the set of archimedean places $v | oo$ of $K$, we equivalently write $overline(E) = (E, {||dot.c||_v}_(v | oo))$.
  ]

  Because $cal(O)_K$ is a Dedekind domain, a finitely generated projective $cal(O)_K$-module $E$ need not be free when the class group $op("Cl")(K)$ is nontrivial. Nevertheless, $E times.o_(cal(O)_K) K$ is an $r$-dimensional $K$-vector space, so we can always choose $r$ elements $s_1, dots.c, s_r in E$ that are $K$-linearly independent. The $cal(O)_K$-submodule $cal(O)_K s_1 + dots.c + cal(O)_K s_r subset.eq E$ then has finite index in $E$.

  #definition(title: "Arakelov Degree over Spec O_K")[
    Let $overline(E) = (E, {||dot.c||_v}_(v | oo))$ be a Hermitian vector bundle of rank $r >= 1$ over $op("Spec") cal(O)_K$, and let $s_1, dots.c, s_r in E$ be $K$-linearly independent elements. The _Arakelov degree_ of $overline(E)$ is defined by
    $ hat(op("deg"))(overline(E)) = log \# (E \/ (cal(O)_K s_1 + dots.c + cal(O)_K s_r)) - sum_(sigma : K -> bb(C)) log ||s_1 and dots.c and s_r||_sigma, $
    where $||dot.c||_sigma$ on $Lambda^r E_sigma$ is the determinant Hermitian norm induced by $||dot.c||_sigma$ on $E_sigma$. Equivalently, grouping conjugate embeddings by archimedean places $v | oo$ with local degree $epsilon_v in {1, 2}$,
    $ hat(op("deg"))(overline(E))
      &= log \# (E \/ (cal(O)_K s_1 + dots.c + cal(O)_K s_r)) \
      &quad - sum_(v | oo) epsilon_v log ||s_1 and dots.c and s_r||_v. $
    For $E = 0$, we set $hat(op("deg"))(0) = 0$. The _Arakelov slope_ of a nonzero bundle $overline(E)$ is
    $ hat(mu)(overline(E)) = (hat(op("deg"))(overline(E))) / (op("rk")_(cal(O)_K) (E)). $
    Some authors normalize by dividing by $[K : bb(Q)]$, setting $hat(op("deg"))_n (overline(E)) = hat(op("deg"))(overline(E)) \/ [K : bb(Q)]$; we work with the unnormalized degree $hat(op("deg"))$ so that $K = bb(Q)$ agrees verbatim with $-log op("covol")$.
  ]

  #proposition(title: "Well-Definedness of the Arakelov Degree")[
    The quantity $hat(op("deg"))(overline(E))$ is independent of the choice of $K$-linearly independent elements $s_1, dots.c, s_r in E$.
  ]

  #proof[
    Let $s'_1, dots.c, s'_r in E$ be another $K$-basis of $E_K = E times.o_(cal(O)_K) K$. Write $s'_j = sum_(i=1)^r a_(i j) s_i$ with $A = (a_(i j)) in op("GL")_r (K)$, and set $alpha = det(A) in K^times$. Let $M = cal(O)_K s_1 + dots.c + cal(O)_K s_r$ and $M' = cal(O)_K s'_1 + dots.c + cal(O)_K s'_r$.

    At each archimedean embedding $sigma : K -> bb(C)$, exterior multilinearity gives
    $ s'_1 and dots.c and s'_r = sigma(alpha) dot.c (s_1 and dots.c and s_r) quad "in" Lambda^r E_sigma, $
    and therefore
    $ &sum_(sigma : K -> bb(C)) log ||s'_1 and dots.c and s'_r||_sigma - sum_(sigma : K -> bb(C)) log ||s_1 and dots.c and s_r||_sigma \
      &= sum_(sigma : K -> bb(C)) log |sigma(alpha)| = log |N_(K \/ bb(Q))(alpha)|. $

    At the finite places, choose a common sublattice $N subset.eq M inter M'$ of finite index (for instance, $N = c M'$ for a nonzero integer $c$ with $c A in op("Mat")_(r times r)(cal(O)_K)$). By the multiplicativity of finite indices in the towers $N subset.eq M subset.eq E$ and $N subset.eq M' subset.eq E$,
    $ (\# (E \/ M')) / (\# (E \/ M)) = (\# (M \/ N)) / (\# (M' \/ N)). $
    Localizing at each nonzero prime ideal $frak(p)$ of $cal(O)_K$, the modules $M_(frak(p))$ and $M'_(frak(p))$ are free over the discrete valuation ring $cal(O)_(K, frak(p))$, and the transition matrix $A$ satisfies
    $ (\# (M_(frak(p)) \/ N_(frak(p)))) / (\# (M'_(frak(p)) \/ N_(frak(p)))) = N(frak(p))^(v_(frak(p))(det A)) = N(frak(p))^(v_(frak(p))(alpha)). $
    Multiplying over all nonzero primes $frak(p)$ yields
    $ (\# (E \/ M')) / (\# (E \/ M)) = product_(frak(p)) N(frak(p))^(v_(frak(p))(alpha)) = |N_(K \/ bb(Q))(alpha)|, $
    where the last equality is the product formula for $alpha in K^times$. Taking logarithms, the change in $log \# (E \/ M)$ cancels the change in the archimedean sum identically.
  ]

  The structure theorem for finitely generated projective modules over a Dedekind domain states that $E tilde.equiv cal(O)_K^(r-1) plus.o frak(a)$ for some nonzero fractional ideal $frak(a)$ of $K$, whose class in $op("Cl")(K)$ is the Steinitz class of $E$. In particular, for a Hermitian line bundle $overline(L) = (L, {||dot.c||_sigma})$ of rank $1$, picking any nonzero section $s in L$ gives
  $ hat(op("deg"))(overline(L)) = log N(op("div")(s)) - sum_(sigma : K -> bb(C)) log ||s||_sigma, $
  where $op("div")(s)$ is the effective ideal corresponding to the finite quotient $L \/ cal(O)_K s$. For a general rank-$r$ bundle $overline(E)$, passing to the determinant Hermitian line bundle $det overline(E) = (Lambda^r_(cal(O)_K) E, {||dot.c||_sigma})$ gives the exact identity
  $ hat(op("deg"))(overline(E)) = hat(op("deg"))(det overline(E)). $

  #proposition(title: "Restriction of Scalars to Z")[
    Let $overline(E) = (E, {||dot.c||_sigma})$ be a Hermitian vector bundle of rank $r$ over $op("Spec") cal(O)_K$, and let $Delta_K$ be the discriminant of $K$. View $E$ as a free $bb(Z)$-module of rank $r d$ (where $d = [K : bb(Q)]$), and equip $E_bb(R) = E times.o_bb(Z) bb(R)$ with the Euclidean inner product obtained from the canonical embedding
    $ E times.o_bb(Z) bb(R) arrow.hook product_(sigma : K -> bb(C)) E_sigma, quad ||x||^2_(pi_* overline(E)) = sum_(sigma : K -> bb(C)) ||x||^2_sigma. $
    Denote the resulting Euclidean lattice by $pi_* overline(E)$. Then
    $ hat(op("deg"))_bb(Z) (pi_* overline(E)) = hat(op("deg"))_(cal(O)_K) (overline(E)) - r / 2 log |Delta_K|. $
    Consequently, the slope over $bb(Z)$ satisfies
    $ hat(mu)_bb(Z) (pi_* overline(E)) = 1 / d hat(mu)_(cal(O)_K) (overline(E)) - (log |Delta_K|) / (2 d). $
  ]

  #proof[
    Pick $K$-linearly independent elements $s_1, dots.c, s_r in E$, and let $M = cal(O)_K s_1 + dots.c + cal(O)_K s_r subset.eq E$. Because $M subset.eq E$ has finite index $\# (E \/ M)$, the covolume of $M$ in $pi_* overline(E)$ satisfies $op("covol")(M) = \# (E \/ M) dot.c op("covol")(pi_* overline(E))$, hence
    $ hat(op("deg"))_bb(Z) (pi_* overline(E)) = log \# (E \/ M) + hat(op("deg"))_bb(Z) (M). $
    Let $omega_1, dots.c, omega_d$ be a $bb(Z)$-basis of $cal(O)_K$, so that $\{omega_a s_j : 1 <= a <= d, 1 <= j <= r\}$ is a $bb(Z)$-basis of $M$. Under the canonical map $E_bb(R) -> product_sigma E_sigma$, let $u_(sigma, 1), dots.c, u_(sigma, r)$ be an orthonormal basis of $E_sigma$, and write $s_j = sum_(k=1)^r c_(sigma, k j) u_(sigma, k)$ in $E_sigma$. Then the matrix expressing the basis $\{omega_a s_j\}$ in terms of the orthonormal basis $\{u_(sigma, k)\}$ (viewed over $bb(C)$, which preserves the modulus of the determinant) is the block matrix whose $((sigma, k), (a, j))$-entry is $sigma(omega_a) c_(sigma, k j)$.

    Ordering the rows by $(sigma, k)$ and columns by $(a, j)$, this matrix factors as the product of a block-diagonal matrix with blocks $C_sigma = (c_(sigma, k j))$ along the diagonal and the Kronecker product $(sigma(omega_a))_(sigma, a) times.o I_r$. Taking the absolute value of the determinant yields
    $ op("covol")(M)
      &= |det(sigma(omega_a))|^r dot.c product_(sigma : K -> bb(C)) |det(C_sigma)| \
      &= |Delta_K|^(r \/ 2) dot.c product_(sigma : K -> bb(C)) ||s_1 and dots.c and s_r||_sigma. $
    Taking $-log$ gives
    $ hat(op("deg"))_bb(Z) (M) = - r / 2 log |Delta_K| - sum_(sigma : K -> bb(C)) log ||s_1 and dots.c and s_r||_sigma, $
    and adding $log \# (E \/ M)$ yields the claimed formula.
  ]

  Proposition 9.6 explains a crucial architectural feature of the Lean 4 formalization `Formalism.HN`: by studying $R$-submodules of Euclidean lattices (with $R = cal(O)_K$), the Arakelov degree over $cal(O)_K$ and the Euclidean lattice degree over $bb(Z)$ differ only by a linear multiple of the rank, namely $-(log |Delta_K|) / (2 d) dot.c op("rk")_bb(Z)$. As we will see in Section 9.2 (`ShiftInvariance`), adding a constant multiple of the rank shifts all slopes by that constant and leaves the Harder–Narasimhan filtration completely unchanged.

  === Saturated Sublattices, Quotient Metrics, and Dual Lattices

  To formulate exact sequences and quotients in the category of Euclidean lattices, we need the notion of saturation and the quotient metric.

  #definition(title: "Saturated Sublattice and Quotient Metric")[
    Let $overline(L) = (L, ||dot.c||)$ be a Euclidean lattice in an ambient real inner product space $E$.
    1. A sublattice $N subset.eq L$ is _saturated_ in $L$ (written `IsSaturated L N`) if
       $ N = L inter op("span")_bb(R) (N). $
       Equivalently, the quotient abelian group $L \/ N$ is torsion-free. For any sublattice $N subset.eq L$, its _saturation_ in $L$ is the saturated sublattice $overline(N) = L inter op("span")_bb(R)(N)$, which contains $N$ with finite index $[overline(N) : N] < oo$.
    2. Given a saturated sublattice $N subset.eq L$, let $W = op("span")_bb(R)(N) subset.eq E$ and let $pi_(W^perp) : E -> W^perp$ be the orthogonal projection onto $W^perp$. The _quotient lattice_ $overline(L \/ N)$ is the image $Q = pi_(W^perp)(L) subset.eq W^perp$ equipped with the restricted Euclidean norm from $W^perp$. This coincides canonically with the algebraic quotient $L \/ N$ equipped with the quotient norm
       $ ||x + N||_(L \/ N) = inf_(w in W) ||x - w|| = ||pi_(W^perp)(x)||. $
  ]

  In `Formalism.F`, this quotient lattice is defined directly as `quot L N`, the image of $L$ under the orthogonal projection onto $(op("span")_bb(R)(N))^perp$.

  #proposition(title: "Index Formula and Additivity in Exact Sequences")[
    Let $overline(L)$ be a Euclidean lattice in $E$.
    1. (_Index Formula_) If $N subset.eq L$ is a sublattice of the same rank as $L$, then $[L : N] < oo$ and
       $ hat(op("deg"))(overline(N)) = hat(op("deg"))(overline(L)) - log [L : N] <= hat(op("deg"))(overline(L)), $
       with equality if and only if $N = L$.
    2. (_Exact Sequence Additivity_, `DegQuot`) If $N subset.eq L$ is a saturated sublattice, then $Q = pi_(W^perp)(L)$ is a discrete lattice in $W^perp$, and
       $ op("rk")(L) = op("rk")(N) + op("rk")(Q), quad hat(op("deg"))(overline(L)) = hat(op("deg"))(overline(N)) + hat(op("deg"))(overline(Q)). $
  ]

  #proof[
    For (1), let $e_1, dots.c, e_r$ be a $bb(Z)$-basis of $L$ and $f_1, dots.c, f_r$ a $bb(Z)$-basis of $N$, with $f_j = sum_i a_(i j) e_i$ for an integer matrix $A = (a_(i j))$ of nonzero determinant. By the Smith normal form, $|det A| = [L : N]$. Since $G(f) = A^T G(e) A$, we have $op("covol")(N) = |det A| dot.c op("covol")(L) = [L : N] dot.c op("covol")(L)$, and taking $-log$ gives (1).

    For (2), since $L \/ N$ is finitely generated and torsion-free, it is free of rank $s = op("rk")(L) - op("rk")(N)$. Choose a $bb(Z)$-basis $e_1, dots.c, e_k$ of $N$ and lift a $bb(Z)$-basis of $L \/ N$ to elements $e_(k+1), dots.c, e_(k+s) in L$, so that $e_1, dots.c, e_(k+s)$ is a $bb(Z)$-basis of $L$. Let $q_j = pi_(W^perp)(e_(k+j))$ for $1 <= j <= s$. Because $e_(k+j) - q_j in W = op("span")_bb(R)(e_1, dots.c, e_k)$, we can write
    $ e_(k+j) = q_j + sum_(i=1)^k c_(i j) e_i $
    for real scalars $c_(i j)$. Thus the transition matrix from the $bb(R)$-basis $(e_1, dots.c, e_k, q_1, dots.c, q_s)$ to $(e_1, dots.c, e_(k+s))$ is upper-unitriangular (determinant $1$). Since $q_1, dots.c, q_s in W^perp$ are orthogonal to $e_1, dots.c, e_k in W$, the Gram matrix of $(e_1, dots.c, e_k, q_1, dots.c, q_s)$ is block-diagonal:
    $ G(e_1, dots.c, e_k, q_1, dots.c, q_s) = mat(G(e_1, dots.c, e_k), 0; 0, G(q_1, dots.c, q_s)). $
    In particular, $det G(q_1, dots.c, q_s) > 0$, so $q_1, dots.c, q_s$ are $bb(R)$-linearly independent, which implies that $Q = bb(Z) q_1 + dots.c + bb(Z) q_s$ is discrete of rank $s$ in $W^perp$, and
    $ op("covol")(L)
      &= sqrt(det G(e_1, dots.c, e_(k+s))) \
      &= sqrt(det G(e_1, dots.c, e_k)) dot.c sqrt(det G(q_1, dots.c, q_s)) \
      &= op("covol")(N) dot.c op("covol")(Q). $
    Taking $-log$ yields $hat(op("deg"))(overline(L)) = hat(op("deg"))(overline(N)) + hat(op("deg"))(overline(Q))$.
  ]

  Next, we introduce the dual lattice, which corresponds to the dual vector bundle $cal(E)^or = op("Hom")(cal(E), cal(O))$ and reverses the signs of all slopes.

  #definition(title: "Dual Lattice, Formalism.HN.dualZ")[
    Let $overline(L)$ be a Euclidean lattice in an inner product space $E$, and let $V_L = op("span")_bb(R)(L) subset.eq E$. The _dual lattice_ of $overline(L)$ is
    $ L^or = { y in V_L : chevron.l y, x chevron.r in bb(Z) "for all" x in L }, $
    equipped with the restricted inner product from $E$.
  ]

  In `Formalism.HN.dualZ`, this is written precisely as the intersection of `Submodule.span ℝ L` (restricted to $bb(Z)$-scalars) with the preimages of $bb(Z) subset.eq bb(R)$ under the inner product functionals `innerSL ℝ x` for $x in L$.

  #proposition(title: "Properties of the Dual Lattice")[
    Let $overline(L)$ be a Euclidean lattice of rank $r$ in $E$. Then:
    1. $L^or$ is a Euclidean lattice in $V_L$ of rank $r$, with $(L^or)^or = L$.
    2. $op("covol")(L^or) = op("covol")(L)^(-1)$, so $hat(op("deg"))(overline(L)^or) = -hat(op("deg"))(overline(L))$ and (for $r >= 1$) $hat(mu)(overline(L)^or) = -hat(mu)(overline(L))$.
    3. If $N subset.eq L$ is a saturated sublattice, then its annihilator
       $ N^perp_L = { y in L^or : chevron.l y, x chevron.r = 0 "for all" x in N } = L^or inter op("span")_bb(R)(N)^perp $
       is a saturated sublattice of $L^or$ that is canonically isometric to $(L \/ N)^or$, and the quotient lattice $L^or \/ N^perp_L$ is canonically isometric to $N^or$.
  ]

  #proof[
    Choose a $bb(Z)$-basis $e_1, dots.c, e_r$ of $L$, and let $e_1^*, dots.c, e_r^* in V_L$ be the unique dual $bb(R)$-basis satisfying $chevron.l e_i^*, e_j chevron.r = delta_(i j)$. Clearly $y = sum_i c_i e_i^* in V_L$ lies in $L^or$ if and only if $c_j = chevron.l y, e_j chevron.r in bb(Z)$ for all $j$, so $L^or = bb(Z) e_1^* + dots.c + bb(Z) e_r^*$ is discrete of rank $r$. Since the dual of the dual basis is $e_1, dots.c, e_r$, we have $(L^or)^or = L$. Moreover, the Gram matrices satisfy $G(e_1^*, dots.c, e_r^*) = G(e_1, dots.c, e_r)^(-1)$, because if $e_i^* = sum_k b_(i k) e_k$, then $delta_(i j) = sum_k b_(i k) G_(k j)$, so $B = G^(-1)$ and $G(e^*) = B G B^T = G^(-1)$. Taking determinants and square roots yields $op("covol")(L^or) = op("covol")(L)^(-1)$, proving (1) and (2).

    For (3), let $W = op("span")_bb(R)(N)$. Clearly $N^perp_L = L^or inter W^perp$ is saturated in $L^or$. For any $y in W^perp inter V_L$ and $x in L$, we have $chevron.l y, x chevron.r = chevron.l y, pi_(W^perp)(x) chevron.r$, so $y in N^perp_L$ if and only if $chevron.l y, q chevron.r in bb(Z)$ for all $q in pi_(W^perp)(L) = L \/ N$; hence $N^perp_L = (L \/ N)^or$ as subsets of $W^perp$, which is an isometry. Finally, the orthogonal projection $pi_W : V_L -> W$ has kernel $W^perp inter V_L = op("span")_bb(R)(N^perp_L)$. For $y in L^or$ and $x in N subset.eq W$, $chevron.l pi_W (y), x chevron.r = chevron.l y, x chevron.r in bb(Z)$, so $pi_W (L^or) subset.eq N^or$. Conversely, since $N$ is saturated in $L$, any $bb(Z)$-basis of $N$ extends to a $bb(Z)$-basis of $L$, so any $bb(Z)$-linear functional on $N$ extends to a $bb(Z)$-linear functional on $L$; hence $pi_W (L^or) = N^or$, giving an isometry $L^or \/ N^perp_L tilde.equiv N^or$.
  ]

  #example(title: "Rank-One Bundles and a Diagonal Rank-Two Lattice")[
    1. Over $bb(Z)$, every rank-one Euclidean lattice has the form $overline(L)_a = (bb(Z), ||n|| = a |n|)$ for a positive real number $a > 0$. Its covolume is $a$, its Arakelov degree and slope are both $-log a$, and its dual is $overline(L)_(1 \/ a)$ of degree $+log a$.
    2. Consider the rank-two lattice $overline(L) = bb(Z) (a, 0) plus.o bb(Z) (0, b) subset.eq bb(R)^2$ with $0 < a <= b$ and the standard Euclidean norm. Its covolume is $a b$, so $hat(op("deg"))(overline(L)) = -log a - log b$ and $hat(mu)(overline(L)) = -(log a + log b) \/ 2$. Any nonzero vector $(m a, n b) in L$ has norm at least $a$, with equality for $plus.minus (a, 0)$, so the rank-one sublattice $N = bb(Z)(a, 0)$ achieves the maximum possible slope $-log a$, while the quotient $L \/ N tilde.equiv bb(Z)(0, b)$ has slope $-log b$. If $a < b$, then $hat(mu)(N) = -log a > hat(mu)(overline(L)) > -log b = hat(mu)(L \/ N)$, showing that $overline(L)$ is not semistable and that $0 subset.neq N subset.neq L$ is its canonical filtration.
  ]

  == Supermodularity and the Harder–Narasimhan Filtration

  On an algebraic curve $C$, the degree of vector bundles is _modular_ on subbundles: if $A, B subset.eq E$ are subbundles of a vector bundle $E$, then $deg(A) + deg(B) = deg(A + B) + deg(A inter B)$ (at least after taking saturations, and with an inequality $deg(A) + deg(B) <= deg(A + B) + deg(A inter B)$ for general coherent subsheaves). Remarkably, in Arakelov geometry the equality becomes an inequality even for saturated sublattices—and it goes in the _favorable_ direction! This phenomenon, known as _supermodularity of the Arakelov degree_, is the engine that drives the entire Harder–Narasimhan theory.

  === Supermodularity of the Arakelov Degree

  Before proving supermodularity, we isolate a fundamental determinant inequality for linear contractions between Euclidean spaces, which will serve double duty here and in Bost's slope inequality.

  #lemma(title: "Gram Determinant Monotonicity, Formalism.F.GramDetLe")[
    Let $E, F$ be real inner product spaces, let $v_1, dots.c, v_r in E$ and $w_1, dots.c, w_r in F$, and let $C >= 0$ be a real number such that
    $ ||sum_(i=1)^r c_i w_i||_F <= C dot.c ||sum_(i=1)^r c_i v_i||_E quad "for all" (c_1, dots.c, c_r) in bb(R)^r. $
    Then the Gram determinants satisfy
    $ det G(w_1, dots.c, w_r) <= C^(2 r) det G(v_1, dots.c, v_r). $
  ]

  #proof[
    If $v_1, dots.c, v_r$ are linearly dependent over $bb(R)$, then there exist $c_1, dots.c, c_r in bb(R)$, not all zero, with $sum_i c_i v_i = 0$. The hypothesis forces $sum_i c_i w_i = 0$, so both Gram determinants vanish and the inequality holds trivially.

    Assume therefore that $v_1, dots.c, v_r$ are linearly independent, and let $V_0 = op("span")_bb(R)(v_1, dots.c, v_r) subset.eq E$. There is a unique linear map $T : V_0 -> F$ sending $v_i |-> w_i$, and the hypothesis states that $||T(x)||_F <= C ||x||_E$ for all $x in V_0$. Let $u_1, dots.c, u_r$ be an orthonormal basis of $V_0$, and write $v_j = sum_(i=1)^r p_(i j) u_i$ with $P = (p_(i j)) in op("GL")_r (bb(R))$. Then $G(v_1, dots.c, v_r) = P^T P$, so $det G(v_1, dots.c, v_r) = (det P)^2$, while $G(w_1, dots.c, w_r) = P^T G(T u_1, dots.c, T u_r) P$, so
    $ det G(w_1, dots.c, w_r)
      &= (det P)^2 det G(T u_1, dots.c, T u_r) \
      &= det G(v_1, dots.c, v_r) dot.c det G(T u_1, dots.c, T u_r). $
    By Hadamard's inequality for the positive semidefinite matrix $G(T u_1, dots.c, T u_r)$,
    $ det G(T u_1, dots.c, T u_r) <= product_(i=1)^r ||T u_i||_F^2 <= product_(i=1)^r (C ||u_i||_E)^2 = C^(2 r). $
    Multiplying by $det G(v_1, dots.c, v_r)$ completes the proof.
  ]

  With Lemma 9.12 in hand, we can now prove supermodularity in complete generality—for arbitrary (not necessarily saturated) sublattices $A, B subset.eq L$.

  #theorem(title: "Supermodularity of the Arakelov Degree, DegSupermod")[
    Let $overline(L)$ be a Euclidean lattice in an inner product space $E$, and let $A, B subset.eq L$ be any two sublattices. Then:
    1. $op("rk")(A + B) + op("rk")(A inter B) = op("rk")(A) + op("rk")(B)$, and
    2. $hat(op("deg"))(overline(A)) + hat(op("deg"))(overline(B)) <= hat(op("deg"))(overline(A + B)) + hat(op("deg"))(overline(A inter B))$.
  ]

  #proof[
    The rank identity (1) is immediate from the short exact sequence of free abelian groups
    $ &0 -> A inter B -> A plus.o B -> A + B -> 0, \
      &x |-> (x, -x), quad (a, b) |-> a + b. $

    For (2), set $C = A inter B$ and let $W = op("span")_bb(R)(C) subset.eq E$. We first verify the crucial subspace identity
    $ op("span")_bb(R)(A) inter op("span")_bb(R)(B) = W. $
    Indeed, let $U_A = op("span")_bb(Q)(A)$ and $U_B = op("span")_bb(Q)(B)$ inside the finite-dimensional $bb(Q)$-vector space $U_L = op("span")_bb(Q)(L)$. If $v in U_A inter U_B$, then clearing denominators produces a positive integer $n$ such that $n v in A$ and $n v in B$, hence $n v in A inter B = C$ and $v in op("span")_bb(Q)(C)$. Thus $U_A inter U_B = op("span")_bb(Q)(C)$. Because $L$ is discrete in $E$, a $bb(Q)$-basis of $U_L$ is $bb(R)$-linearly independent in $E$, so extension of scalars $- times.o_bb(Q) bb(R)$ is exact and commutes with finite intersections; hence $op("span")_bb(R)(A) inter op("span")_bb(R)(B) = op("span")_bb(R)(C) = W$.

    Now define the saturated intersections with $W$:
    $ tilde(A) = A inter W, quad tilde(B) = B inter W, quad tilde(S) = (A + B) inter W. $
    Notice that $C = tilde(A) inter tilde(B) subset.eq tilde(A), tilde(B) subset.eq tilde(A) + tilde(B) subset.eq tilde(S)$, and all five lattices span $W$ over $bb(R)$, so they all have the same rank $op("rk")(C)$. By the second isomorphism theorem for abelian groups,
    $ (tilde(A) + tilde(B)) \/ tilde(B) tilde.equiv tilde(A) \/ (tilde(A) inter tilde(B)) = tilde(A) \/ C, $
    so the finite indices satisfy $[tilde(A) + tilde(B) : tilde(B)] = [tilde(A) : C]$. Applying Proposition 9.8(1) twice gives
    $ hat(op("deg"))(tilde(A)) - hat(op("deg"))(C)
      &= log [tilde(A) : C] = log [tilde(A) + tilde(B) : tilde(B)] \
      &= hat(op("deg"))(tilde(A) + tilde(B)) - hat(op("deg"))(tilde(B)). $
    Since $tilde(A) + tilde(B) subset.eq tilde(S)$ has finite index, Proposition 9.8(1) also gives $hat(op("deg"))(tilde(A) + tilde(B)) <= hat(op("deg"))(tilde(S))$, and therefore
    $ hat(op("deg"))(tilde(A)) + hat(op("deg"))(tilde(B)) <= hat(op("deg"))(tilde(S)) + hat(op("deg"))(C). $

    Next, let $pi : E -> W^perp$ be the orthogonal projection onto $W^perp$. Because $tilde(A)$, $tilde(B)$, and $tilde(S)$ are saturated in $A$, $B$, and $A + B$ respectively, Proposition 9.8(2) gives
    $ hat(op("deg"))(A) = hat(op("deg"))(tilde(A)) + hat(op("deg"))(pi(A)), $
    $ hat(op("deg"))(B) = hat(op("deg"))(tilde(B)) + hat(op("deg"))(pi(B)), $
    $ hat(op("deg"))(A + B) = hat(op("deg"))(tilde(S)) + hat(op("deg"))(pi(A + B)). $
    Observe that $pi(A + B) = pi(A) + pi(B)$, and because $op("span")_bb(R)(A) inter op("span")_bb(R)(B) = W = ker(pi)$, the real spans $V_1 = op("span")_bb(R)(pi(A))$ and $V_2 = op("span")_bb(R)(pi(B))$ satisfy $V_1 inter V_2 = {0}$ inside $W^perp$. Hence $pi(A)$ is saturated in $pi(A) + pi(B)$, and the orthogonal projection $pi_(V_1^perp)$ maps $pi(A) + pi(B)$ onto $pi_(V_1^perp)(pi(B))$ with kernel $pi(A)$. By Proposition 9.8(2) once more,
    $ hat(op("deg"))(pi(A + B)) = hat(op("deg"))(pi(A)) + hat(op("deg"))(pi_(V_1^perp)(pi(B))). $
    Since $pi_(V_1^perp)$ is an orthogonal projection, it is $1$-Lipschitz ($||pi_(V_1^perp)(x)|| <= ||x||$ for all $x$). Applying Lemma 9.12 with $C = 1$ to a $bb(Z)$-basis of $pi(B)$ yields $op("covol")(pi_(V_1^perp)(pi(B))) <= op("covol")(pi(B))$, and hence
    $ hat(op("deg"))(pi_(V_1^perp)(pi(B))) >= hat(op("deg"))(pi(B)). $
    Therefore $hat(op("deg"))(pi(A)) + hat(op("deg"))(pi(B)) <= hat(op("deg"))(pi(A + B))$. Adding this to our inequality on $W$ gives
    $ hat(op("deg"))(A) + hat(op("deg"))(B) <= hat(op("deg"))(A + B) + hat(op("deg"))(A inter B), $
    completing the proof.
  ]

  Notice where the inequality in Theorem 9.13 comes from geometrically: two sources of strictness can occur. At the finite places, $tilde(A) + tilde(B)$ can be a proper finite-index sublattice of $(A + B) inter W$; at the archimedean place, $pi(A)$ and $pi(B)$ need not be orthogonal in $W^perp$, so the parallelepiped spanned by $pi(A)$ and $pi(B)$ has volume at most the product of their individual volumes (shrinking by the sine of the principal angles between $V_1$ and $V_2$). Both effects _decrease_ the covolume of $A + B$ and therefore _increase_ its Arakelov degree!

  === Maximal and Minimal Slopes

  We now introduce the extremal slopes $mu_max (overline(L))$ and $mu_min (overline(L))$ and establish their basic finiteness and characterization properties (`MuMaxLeMin` and `MuChar` in `Formalism.F` and `Formalism.HN`).

  #definition(title: "Maximal Slope, Minimal Slope, and Semistability")[
    Let $overline(L)$ be a nonzero Euclidean lattice (or an $R$-lattice `IsLat ρ L` with $L != 0$).
    1. The _maximal slope_ of $overline(L)$ is
       $ mu_max (overline(L)) = sup { hat(mu)(overline(N)) : 0 != N subset.eq L }. $
    2. The _minimal slope_ of $overline(L)$ is
       $ mu_min (overline(L)) = inf { hat(mu)(overline(L \/ N)) : N subset.neq L "saturated" }. $
    3. We say that $overline(L)$ is _semistable_ if $hat(mu)(overline(N)) <= hat(mu)(overline(L))$ for every nonzero sublattice $N subset.eq L$, i.e., if $mu_max (overline(L)) = hat(mu)(overline(L))$.
  ]

  In the $R$-module setting of `Formalism.HN`, the supremum in $mu_max (rho, L)$ is taken over nonzero $R$-submodules $N subset.eq L$, and the infimum in $mu_min (rho, L)$ is taken over proper saturated $R$-submodules $N subset.neq L$. All arguments below apply verbatim in this generality because $R$-submodules are closed under sum and intersection.

  Why is $mu_max (overline(L))$ finite, and why is it actually attained by a sublattice? Both facts follow from the discreteness of $L$ in $E$.

  #lemma(title: "Upper Bound on Maximal Slope via Shortest Vector, MuMaxLeMin")[
    Let $overline(L)$ be a nonzero Euclidean lattice of rank $r$, and let $lambda_1 (overline(L)) = min_(x in L without {0}) ||x|| > 0$ be the length of a shortest nonzero vector in $L$. Then for every nonzero sublattice $N subset.eq L$,
    $ hat(mu)(overline(N)) <= -log lambda_1 (overline(L)) + 1 / 2 log op("rk")(N) <= -log lambda_1 (overline(L)) + 1 / 2 log r. $
    In particular, $mu_max (overline(L)) <= -log lambda_1 (overline(L)) + (1 \/ 2) log r < +oo$.
  ]

  #proof[
    Let $N subset.eq L$ be a nonzero sublattice of rank $k = op("rk")(N) <= r$, and identify $op("span")_bb(R)(N)$ isometrically with $bb(R)^k$ via an orthonormal basis. Consider the open hypercube
    $ Q_R = (-R, R)^k subset.eq bb(R)^k, quad R = (lambda_1 (overline(L))) / sqrt(k). $
    Every point $x = (x_1, dots.c, x_k) in Q_R$ satisfies $||x|| = sqrt(sum_(i=1)^k x_i^2) < sqrt(k R^2) = lambda_1 (overline(L))$. Since every nonzero vector in $N subset.eq L$ has norm at least $lambda_1 (overline(L))$, the convex, centrally symmetric body $Q_R$ contains no nonzero point of $N$. By Minkowski's convex body theorem,
    $ op("vol")(Q_R) = (2 R)^k <= 2^k op("covol")(overline(N)), $
    and hence $op("covol")(overline(N)) >= R^k = lambda_1 (overline(L))^k k^(-k \/ 2)$. Taking $-log$ and dividing by $k$ gives
    $ hat(mu)(overline(N)) = -(log op("covol")(overline(N))) / k
      &<= -log lambda_1 (overline(L)) + 1 / 2 log k \
      &<= -log lambda_1 (overline(L)) + 1 / 2 log r. $
  ]

  In fact, an even stronger finiteness property holds: for every real number $M$, there are only _finitely many_ sublattices $N subset.eq L$ with $hat(op("deg"))(overline(N)) >= M$. Indeed, for each fixed rank $k in {1, dots.c, r}$, the exterior power $Lambda^k L$ is a discrete lattice in the Euclidean space $Lambda^k E$. Every rank-$k$ sublattice $N subset.eq L$ with $bb(Z)$-basis $v_1, dots.c, v_k$ determines a nonzero decomposable vector $plus.minus v_1 and dots.c and v_k in Lambda^k L$ of norm $op("covol")(overline(N)) = e^(-hat(op("deg"))(overline(N)))$. If $hat(op("deg"))(overline(N)) >= M$, then $||v_1 and dots.c and v_k|| <= e^(-M)$. Because $Lambda^k L$ is discrete, the closed ball of radius $e^(-M)$ in $Lambda^k E$ contains only finitely many points of $Lambda^k L$. Each nonzero decomposable vector $omega in Lambda^k L$ uniquely determines the $k$-dimensional subspace $W = {x in E : x and omega = 0}$, hence uniquely determines the saturated sublattice $overline(N) = L inter W$, and the index $[overline(N) : N] = ||omega|| \/ op("covol")(overline(N))$ is bounded above by $e^(-M) \/ op("covol")(overline(N))$, leaving only finitely many sublattices $N subset.eq overline(N)$ of bounded index.

  This finiteness immediately yields the complete characterization of $mu_max$ and $mu_min$.

  #proposition(title: "Characterization of Extremal Slopes, MuChar")[
    Let $overline(L)$ be a nonzero Euclidean lattice. Then:
    1. For every $theta in bb(R)$, $mu_max (overline(L)) <= theta$ if and only if $hat(op("deg"))(overline(N)) <= theta dot.c op("rk")(N)$ for all sublattices $N subset.eq L$.
    2. For every $theta in bb(R)$, $theta <= mu_min (overline(L))$ if and only if
       $ theta dot.c (op("rk")(L) - op("rk")(N)) <= hat(op("deg"))(overline(L)) - hat(op("deg"))(overline(N)) $
       for all sublattices $N subset.eq L$.
    3. There exists a nonzero saturated sublattice $N subset.eq L$ such that $hat(mu)(overline(N)) = mu_max (overline(L))$.
    4. $mu_min (overline(L)) <= hat(mu)(overline(L)) <= mu_max (overline(L))$, and equality holds in either inequality if and only if $overline(L)$ is semistable.
    5. Under duality, $mu_max (overline(L)^or) = -mu_min (overline(L))$ and $mu_min (overline(L)^or) = -mu_max (overline(L))$.
  ]

  #proof[
    Statement (1) is immediate from the definition of $mu_max (overline(L))$ (noting that for $N = 0$, both sides of $hat(op("deg"))(0) <= theta dot.c 0$ are $0$).

    For (2), if $theta <= mu_min (overline(L))$ and $N subset.eq L$ is any sublattice, let $overline(N) = L inter op("span")_bb(R)(N)$ be its saturation. Then $op("rk")(overline(N)) = op("rk")(N)$ and $hat(op("deg"))(overline(N)) >= hat(op("deg"))(N)$ by Proposition 9.8(1). If $overline(N) = L$, the desired inequality is $0 <= hat(op("deg"))(L) - hat(op("deg"))(N)$, which holds by Proposition 9.8(1). If $overline(N) != L$, then by Proposition 9.8(2) and the definition of $mu_min (overline(L))$,
    $ theta <= mu_min (overline(L)) <= hat(mu)(overline(L \/ overline(N))) = (hat(op("deg"))(L) - hat(op("deg"))(overline(N))) / (op("rk")(L) - op("rk")(overline(N))) <= (hat(op("deg"))(L) - hat(op("deg"))(N)) / (op("rk")(L) - op("rk")(N)). $
    Multiplying through by $op("rk")(L) - op("rk")(N) > 0$ gives the forward implication; the converse follows directly by specializing to saturated $N subset.neq L$.

    For (3), pick any nonzero $N_0 subset.eq L$ and let $theta_0 = hat(mu)(N_0)$. Any sublattice $N subset.eq L$ with $hat(mu)(N) >= theta_0$ satisfies $hat(op("deg"))(N) >= op("rk")(N) theta_0 >= min(0, op("rk")(L) theta_0)$. By the finiteness property proved above, there are only finitely many such sublattices $N subset.eq L$, so the supremum $mu_max (overline(L))$ is attained by some nonzero $N subset.eq L$. Replacing $N$ by its saturation $overline(N)$ can only increase $hat(op("deg"))(N)$ without changing $op("rk")(N)$, so $hat(mu)(overline(N)) = mu_max (overline(L))$ as well.

    For (4), taking $N = L$ in the definition of $mu_max$ and $N = 0$ in the definition of $mu_min$ gives $mu_min (overline(L)) <= hat(mu)(overline(L)) <= mu_max (overline(L))$. If $overline(L)$ is semistable, then for every proper saturated $N subset.neq L$, $hat(op("deg"))(N) <= hat(mu)(L) op("rk")(N)$, so $hat(op("deg"))(L \/ N) = hat(op("deg"))(L) - hat(op("deg"))(N) >= hat(mu)(L)(op("rk")(L) - op("rk")(N))$, whence $mu_min (overline(L)) >= hat(mu)(overline(L))$, forcing equality; the converse is analogous.

    Finally, (5) follows from Proposition 9.10(3): the map $N |-> N^perp_L = (L \/ N)^or$ is an order-reversing bijection between proper saturated sublattices of $L$ and nonzero saturated sublattices of $L^or$, with $hat(mu)(N^perp_L) = -hat(mu)(L \/ N)$. Taking suprema gives $mu_max (overline(L)^or) = -mu_min (overline(L))$, and applying this to $L^or$ (using $(L^or)^or = L$) gives $mu_min (overline(L)^or) = -mu_max (overline(L))$.
  ]

  === The Canonical Harder–Narasimhan Filtration

  We can now construct the Harder–Narasimhan filtration of any Euclidean lattice. The key step is the existence and uniqueness of a _maximal destabilizing sublattice_.

  #lemma(title: "Maximal Destabilizing Sublattice")[
    Let $overline(L)$ be a nonzero Euclidean lattice. Among all nonzero sublattices $N subset.eq L$ satisfying $hat(mu)(overline(N)) = mu_max (overline(L))$, there is a unique one of maximum rank, denoted $L_1$. Moreover:
    1. $L_1$ is saturated in $L$ and semistable with $hat(mu)(overline(L)_1) = mu_max (overline(L))$.
    2. $L_1$ contains every nonzero sublattice $N subset.eq L$ with $hat(mu)(overline(N)) = mu_max (overline(L))$.
    3. If $L_1 != L$, then $mu_max (overline(L \/ L_1)) < mu_max (overline(L))$.
  ]

  #proof[
    Let $mu_1 = mu_max (overline(L))$. By Proposition 9.16(3), the set $cal(S) = {N subset.eq L : N != 0, hat(mu)(overline(N)) = mu_1}$ is nonempty. Pick $L_1 in cal(S)$ of maximum rank.

    We first show that $cal(S)$ is closed under taking sums. Let $A, B in cal(S)$. By Theorem 9.13 (`DegSupermod`),
    $ &hat(op("deg"))(A + B) + hat(op("deg"))(A inter B) \
      &>= hat(op("deg"))(A) + hat(op("deg"))(B) \
      &= mu_1 (op("rk")(A) + op("rk")(B)) = mu_1 (op("rk")(A + B) + op("rk")(A inter B)). $
    On the other hand, Proposition 9.16(1) gives $hat(op("deg"))(A + B) <= mu_1 op("rk")(A + B)$ and $hat(op("deg"))(A inter B) <= mu_1 op("rk")(A inter B)$. Adding these two upper bounds forces equality in both; in particular, $hat(op("deg"))(A + B) = mu_1 op("rk")(A + B)$, so $A + B in cal(S)$.

    Now for any $N in cal(S)$, we have $L_1 + N in cal(S)$, so $op("rk")(L_1 + N) <= op("rk")(L_1)$ by maximality of $op("rk")(L_1)$. Also $L_1$ is saturated in $L$ (since its saturation $overline(L_1)$ lies in $cal(S)$ and has the same rank, forcing $hat(op("deg"))(overline(L_1)) = hat(op("deg"))(L_1)$ and thus $overline(L_1) = L_1$). Since $L_1 subset.eq L_1 + N$ have the same rank and $L_1$ is saturated in $L$, we must have $L_1 + N = L_1$, i.e., $N subset.eq L_1$. This proves uniqueness, saturation, and (2). Semistability of $L_1$ is immediate because $mu_max (overline(L)_1) <= mu_max (overline(L)) = hat(mu)(overline(L)_1)$.

    Finally, suppose $L_1 != L$, and let $Q subset.eq L \/ L_1$ be any nonzero saturated sublattice. Its preimage $M subset.eq L$ is a saturated sublattice strictly containing $L_1$, so $op("rk")(M) > op("rk")(L_1)$ and hence $hat(mu)(overline(M)) < mu_1$ by maximality of $op("rk")(L_1)$. By Proposition 9.8(2),
    $ hat(op("deg"))(overline(Q)) = hat(op("deg"))(overline(M)) - hat(op("deg"))(overline(L)_1) < mu_1 op("rk")(M) - mu_1 op("rk")(L_1) = mu_1 op("rk")(Q), $
    so $hat(mu)(overline(Q)) < mu_1$. Since $mu_max (overline(L \/ L_1))$ is attained by some nonzero saturated sublattice $Q$, we conclude that $mu_max (overline(L \/ L_1)) < mu_1$.
  ]

  Iterating Lemma 9.17 produces the canonical Harder–Narasimhan filtration.

  #theorem(title: "Existence and Uniqueness of the Harder–Narasimhan Filtration")[
    Let $overline(L)$ be a Euclidean lattice of rank $r >= 1$. There exists a unique filtration by saturated sublattices
    $ 0 = L_0 subset.neq L_1 subset.neq L_2 subset.neq dots.c subset.neq L_k = L $
    such that:
    1. each successive quotient $overline(L_i \/ L_(i-1))$ ($1 <= i <= k$), equipped with the quotient metric, is semistable; and
    2. the slopes $mu_i = hat(mu)(overline(L_i \/ L_(i-1)))$ are strictly decreasing:
       $ mu_1 > mu_2 > dots.c > mu_k. $
    Moreover, $mu_1 = mu_max (overline(L))$ and $mu_k = mu_min (overline(L))$.
  ]

  #proof[
    _Existence._ We induct on $r = op("rk")(L)$. Let $L_1 subset.eq L$ be the maximal destabilizing sublattice from Lemma 9.17. If $L_1 = L$, then $0 subset.neq L$ is the desired filtration with $k = 1$ and $mu_1 = hat(mu)(overline(L))$. If $L_1 != L$, then $overline(L \/ L_1)$ is a Euclidean lattice of strictly smaller rank $r - op("rk")(L_1) >= 1$. By the induction hypothesis, $overline(L \/ L_1)$ admits a Harder–Narasimhan filtration
    $ 0 = Q_0 subset.neq Q_1 subset.neq dots.c subset.neq Q_(k-1) = L \/ L_1 $
    with semistable quotients of strictly decreasing slopes $mu_2 > dots.c > mu_k$. Pulling back $Q_j$ along the quotient map $L -> L \/ L_1$ yields saturated sublattices $L_1 = L'_1 subset.neq L_2 subset.neq dots.c subset.neq L_k = L$ with $overline(L_i \/ L_(i-1)) tilde.equiv overline(Q_(i-1) \/ Q_(i-2))$ isometrically (since orthogonal projections compose cleanly when the subspaces are nested: $(W_i^perp) inter W_(i-1)^perp = W_i^perp$). By Lemma 9.17(3), $mu_2 = mu_max (overline(L \/ L_1)) < mu_1$, so $mu_1 > mu_2 > dots.c > mu_k$.

    _Extremal slopes._ By construction, $mu_1 = mu_max (overline(L))$. To see that $mu_k = mu_min (overline(L))$, note first that $L_(k-1) subset.neq L$ is saturated, so $mu_min (overline(L)) <= hat(mu)(overline(L \/ L_(k-1))) = mu_k$. We prove the reverse inequality $mu_min (overline(L)) >= mu_k$ by induction on the filtration length $k$.
    For $k = 1$, $overline(L)$ is semistable, so $mu_min (overline(L)) = mu_1$ by Proposition 9.16(4). For $k >= 2$, we verify the criterion of Proposition 9.16(2): we must show that for every sublattice $N subset.eq L$,
    $ hat(op("deg"))(L) - hat(op("deg"))(N) >= mu_k (op("rk")(L) - op("rk")(N)). $
    By Proposition 9.8(2) applied to $N inter L_1 subset.eq N$ (saturated in $N$ since $L_1$ is saturated in $L$), the quotient $N \/ (N inter L_1)$ maps injectively into $L \/ L_1$ with norm $<= 1$ (since $op("span")_bb(R)(N inter L_1) subset.eq op("span")_bb(R)(L_1)$, orthogonal projection onto $op("span")_bb(R)(L_1)^perp$ factors through projection onto $op("span")_bb(R)(N inter L_1)^perp$). By Lemma 9.12 with $C = 1$,
    $ hat(op("deg"))(N \/ (N inter L_1)) <= hat(op("deg"))(pi_(L_1^perp)(N)). $
    Since $pi_(L_1^perp)(N) subset.eq L \/ L_1$ and by induction $mu_min (overline(L \/ L_1)) = mu_k$, Proposition 9.16(2) applied to $L \/ L_1$ gives
    $ hat(op("deg"))(L \/ L_1) - hat(op("deg"))(pi_(L_1^perp)(N)) >= mu_k (op("rk")(L \/ L_1) - op("rk")(pi_(L_1^perp)(N))). $
    Meanwhile, since $L_1$ is semistable of slope $mu_1 > mu_k$, we have $hat(op("deg"))(L_1) - hat(op("deg"))(N inter L_1) >= mu_1 (op("rk")(L_1) - op("rk")(N inter L_1)) >= mu_k (op("rk")(L_1) - op("rk")(N inter L_1))$. Adding these two inequalities and using $hat(op("deg"))(N) = hat(op("deg"))(N inter L_1) + hat(op("deg"))(N \/ (N inter L_1))$ yields
    $ hat(op("deg"))(L) - hat(op("deg"))(N) >= mu_k (op("rk")(L) - op("rk")(N)), $
    proving $mu_min (overline(L)) = mu_k$.

    _Uniqueness._ Suppose $0 = M_0 subset.neq M_1 subset.neq dots.c subset.neq M_l = L$ is any filtration satisfying (1) and (2) with slopes $nu_1 > nu_2 > dots.c > nu_l$. By the extremal slope argument just proved, we have $mu_min (overline(M_j)) = nu_j$ and $mu_max (overline(L \/ M_j)) = nu_(j+1)$ (by induction on $l$). Let us show that $M_1 = L_1$; uniqueness then follows by induction on rank. Since $M_1$ is semistable, $hat(mu)(M_1) = nu_1$. On the other hand, for any nonzero $N subset.eq L$, the exact same calculation as above applied to the filtration $M_bullet$ shows
    $ hat(op("deg"))(N)
      &= sum_(j=1)^l hat(op("deg"))((N inter M_j) \/ (N inter M_(j-1))) \
      &<= sum_(j=1)^l nu_j (op("rk")(N inter M_j) - op("rk")(N inter M_(j-1))) <= nu_1 op("rk")(N), $
    with strict inequality whenever $N$ is not contained in $M_1$ (since then some term with $j >= 2$ has positive rank and $nu_j < nu_1$). Therefore $mu_max (overline(L)) = nu_1$, and any sublattice achieving $mu_max (overline(L))$ is contained in $M_1$. Thus $M_1$ is the unique maximal destabilizing sublattice $L_1$.
  ]

  === The Harder–Narasimhan Polygon and Threshold Formulation

  Theorem 9.18 admits an extraordinarily clean reformulation in terms of a real threshold parameter $theta in bb(R)$ and a concave piecewise-linear polygon. This is precisely the formulation formalized in `Formalism.HN` (`HNStep`, `HNSlopes`, `HNExtreme`).

  #definition(title: "Threshold Filtration, Slope List, and HN Polygon")[
    Let $overline(L)$ be a Euclidean lattice of rank $r$, with Harder–Narasimhan filtration $0 = L_0 subset.neq L_1 subset.neq dots.c subset.neq L_k = L$ and slopes $mu_1 > mu_2 > dots.c > mu_k$.
    1. For each real threshold $theta in bb(R)$, define
       $ op("hnStep")(overline(L), theta) = sum_(N subset.eq L, N != 0, mu_min (N) >= theta) N. $
    2. Define the non-increasing _slope list_ $op("slopeList")(overline(L)) : {0, 1, dots.c, r - 1} -> bb(R)$ by listing each slope $mu_i$ with multiplicity $op("rk")(L_i \/ L_(i-1))$, equivalently
       $ op("slopeList")(overline(L))(j) = sup { theta in bb(R) : j < op("rk")(op("hnStep")(overline(L), theta)) }. $
    3. Define the _Harder–Narasimhan polygon_ $op("hnPoly")(overline(L)) : {0, 1, dots.c, r} -> bb(R)$ by
       $ op("hnPoly")(overline(L), m) = sum_(j=0)^(m-1) op("slopeList")(overline(L))(j), $
       extended piecewise linearly to $[0, r]$.
  ]

  Let us check how `hnStep`, `slopeList`, and `hnPoly` match the discrete filtration $L_0 subset.neq L_1 subset.neq dots.c subset.neq L_k$.

  #proposition(title: "Properties of the HN Threshold and Polygon, HNStep & HNSlopes")[
    Let $overline(L)$ be a Euclidean lattice of rank $r$ with Harder–Narasimhan filtration $0 = L_0 subset.neq dots.c subset.neq L_k = L$ and slopes $mu_1 > dots.c > mu_k$.
    1. For every $theta in bb(R)$, $op("hnStep")(overline(L), theta) = L_i$, where $i in {0, 1, dots.c, k}$ is the largest index such that $mu_i >= theta$ (with $i = 0$ if $theta > mu_1$). In particular, $op("hnStep")(overline(L), theta)$ is saturated in $L$, satisfies $mu_min (op("hnStep")(overline(L), theta)) >= theta$ whenever it is nonzero, contains every nonzero $N subset.eq L$ with $mu_min (N) >= theta$, and satisfies
       $ hat(op("deg"))(N) - hat(op("deg"))(op("hnStep")(overline(L), theta)) < theta dot.c (op("rk")(N) - op("rk")(op("hnStep")(overline(L), theta))) $
       for every sublattice $N$ strictly containing $op("hnStep")(overline(L), theta)$.
    2. The function $op("slopeList")(overline(L))$ is antitone (non-increasing), satisfies
       $ \# { j in {0, dots.c, r - 1} : op("slopeList")(overline(L))(j) >= theta } = op("rk")(op("hnStep")(overline(L), theta)), $
       and sums to the Arakelov degree: $sum_(j=0)^(r-1) op("slopeList")(overline(L))(j) = hat(op("deg"))(overline(L))$.
    3. (_Concave Envelope Property_) For every sublattice $N subset.eq L$, the point $(op("rk")(N), hat(op("deg"))(N))$ lies on or below the Harder–Narasimhan polygon:
       $ hat(op("deg"))(overline(N)) <= op("hnPoly")(overline(L), op("rk")(N)), $
       with equality for every step $N = op("hnStep")(overline(L), theta) = L_i$.
  ]

  #proof[
    For (1), let $i$ be the largest index with $mu_i >= theta$ (or $i = 0$ if $theta > mu_1$). Since $L_i$ has Harder–Narasimhan slopes $mu_1 > dots.c > mu_i >= theta$, we have $mu_min (L_i) = mu_i >= theta$ (when $i >= 1$). Conversely, if $N subset.eq L$ is nonzero with $mu_min (N) >= theta$, suppose for contradiction that $N$ is not contained in $L_i$. Let $m > i$ be the smallest index with $N subset.eq L_m$; then $N inter L_(m-1) subset.neq N$ is saturated in $N$, and $N \/ (N inter L_(m-1))$ maps injectively with norm $<= 1$ into the semistable quotient $L_m \/ L_(m-1)$ of slope $mu_m < theta$. Hence
    $ theta <= mu_min (N) <= hat(mu)(N \/ (N inter L_(m-1))) <= mu_max (L_m \/ L_(m-1)) = mu_m < theta, $
    a contradiction. Thus $N subset.eq L_i$, proving $op("hnStep")(overline(L), theta) = L_i$. For any $N$ strictly containing $L_i$, the quotient $N \/ L_i$ injects with norm $<= 1$ into $L \/ L_i$, whose maximal slope is $mu_(i+1) < theta$; thus $hat(op("deg"))(N) - hat(op("deg"))(L_i) = hat(op("deg"))(N \/ L_i) <= mu_(i+1) (op("rk")(N) - op("rk")(L_i)) < theta (op("rk")(N) - op("rk")(L_i))$.

    Statement (2) follows directly from (1), since $op("rk")(L_i) = sum_(a=1)^i op("rk")(L_a \/ L_(a-1))$ and $hat(op("deg"))(L) = sum_(a=1)^k op("rk")(L_a \/ L_(a-1)) mu_a$.

    For (3), let $N subset.eq L$ be any sublattice of rank $m = op("rk")(N)$. As in the uniqueness proof of Theorem 9.18, set $d_a = op("rk")(N inter L_a) - op("rk")(N inter L_(a-1))$ for $1 <= a <= k$. Then $0 <= d_a <= op("rk")(L_a \/ L_(a-1))$, $sum_(a=1)^k d_a = m$, and
    $ hat(op("deg"))(overline(N)) <= sum_(a=1)^k d_a mu_a. $
    Since $mu_1 > mu_2 > dots.c > mu_k$, the maximum of $sum_(a=1)^k d_a mu_a$ subject to $0 <= d_a <= op("rk")(L_a \/ L_(a-1))$ and $sum_a d_a = m$ is achieved greedily by taking the $m$ largest entries of $op("slopeList")(overline(L))$, which equals $op("hnPoly")(overline(L), m)$. Equality holds at $N = L_i$ because $d_a = op("rk")(L_a \/ L_(a-1))$ for $a <= i$ and $d_a = 0$ for $a > i$.
  ]

  Geometrically, $op("hnPoly")(overline(L))$ is the _upper convex hull_ (concave envelope) of the finite set of points $\{(op("rk")(N), hat(op("deg"))(overline(N))) : N subset.eq L\}$ in the plane $bb(R)^2$, starting at $(0, 0)$ and ending at $(r, hat(op("deg"))(overline(L)))$. Its vertices are precisely the points $(op("rk")(L_i), hat(op("deg"))(overline(L)_i))$ of the Harder–Narasimhan filtration, and the slopes of its segments are $mu_1 > mu_2 > dots.c > mu_k$.

  #figure(
    caption: [The Harder–Narasimhan polygon $op("hnPoly")(overline(L))$ as the concave upper envelope of $(op("rk")(N), hat(op("deg"))(overline(N)))$ for sublattices $N subset.eq L$.],
    block(
      width: 82%,
      inset: 10pt,
      fill: gtm-tint,
      stroke: 0.5pt + gtm-rule,
      radius: 2pt,
    )[
      #align(center)[
        #box(width: 270pt, height: 128pt)[
          // Axes
          #place(top + left, dx: 24pt, dy: 105pt)[#line(length: 230pt, stroke: 0.7pt + gtm-navy)]
          #place(top + left, dx: 24pt, dy: 12pt)[#line(length: 93pt, angle: 90deg, stroke: 0.7pt + gtm-navy)]
          // Axis labels
          #place(top + left, dx: 256pt, dy: 100pt)[#text(size: 8.5pt)[$op("rk")$]]
          #place(top + left, dx: 6pt, dy: 2pt)[#text(size: 8.5pt)[$hat(op("deg"))$]]
          // HN polygon segments
          #place(top + left, dx: 24pt, dy: 105pt)[#line(end: (60pt, -57pt), stroke: 1.5pt + gtm-accent)]
          #place(top + left, dx: 84pt, dy: 48pt)[#line(end: (85pt, -26pt), stroke: 1.5pt + gtm-accent)]
          #place(top + left, dx: 169pt, dy: 22pt)[#line(end: (70pt, 14pt), stroke: 1.5pt + gtm-accent)]
          // Dashed secant from (0,0) to (r, deg L)
          #place(top + left, dx: 24pt, dy: 105pt)[#line(end: (215pt, -69pt), stroke: (paint: gtm-rule, thickness: 0.7pt, dash: "dashed"))]
          // Vertices
          #place(top + left, dx: 21.5pt, dy: 102.5pt)[#circle(radius: 2.5pt, fill: gtm-navy)]
          #place(top + left, dx: 81.5pt, dy: 45.5pt)[#circle(radius: 2.5pt, fill: gtm-navy)]
          #place(top + left, dx: 166.5pt, dy: 19.5pt)[#circle(radius: 2.5pt, fill: gtm-navy)]
          #place(top + left, dx: 236.5pt, dy: 33.5pt)[#circle(radius: 2.5pt, fill: gtm-navy)]
          // Sublattice dots below the polygon
          #place(top + left, dx: 54pt, dy: 88pt)[#circle(radius: 1.8pt, fill: luma(120))]
          #place(top + left, dx: 112pt, dy: 64pt)[#circle(radius: 1.8pt, fill: luma(120))]
          #place(top + left, dx: 140pt, dy: 50pt)[#circle(radius: 1.8pt, fill: luma(120))]
          #place(top + left, dx: 196pt, dy: 52pt)[#circle(radius: 1.8pt, fill: luma(120))]
          // Labels
          #place(top + left, dx: 14pt, dy: 110pt)[#text(size: 8pt)[$L_0$]]
          #place(top + left, dx: 74pt, dy: 33pt)[#text(size: 8pt)[$L_1$]]
          #place(top + left, dx: 164pt, dy: 7pt)[#text(size: 8pt)[$L_2$]]
          #place(top + left, dx: 234pt, dy: 21pt)[#text(size: 8pt)[$L_3 = L$]]
          #place(top + left, dx: 40pt, dy: 63pt)[#text(size: 8pt, fill: gtm-accent)[$mu_1$]]
          #place(top + left, dx: 122pt, dy: 23pt)[#text(size: 8pt, fill: gtm-accent)[$mu_2$]]
          #place(top + left, dx: 204pt, dy: 17pt)[#text(size: 8pt, fill: gtm-accent)[$mu_3$]]
          #place(top + left, dx: 132pt, dy: 74pt)[#text(size: 7.5pt, fill: luma(90))[$(op("rk")(N), hat(op("deg"))(N))$]]
        ]
      ]
    ],
  )

  Before moving to Bost's slope inequality, we record the behavior of Harder–Narasimhan invariants under metric shifts (`ShiftInvariance`), which is the exact tool needed to translate between $cal(O)_K$-bundles and $bb(Z)$-lattices via Proposition 9.6.

  #proposition(title: "Shift Invariance, ShiftInvariance")[
    Let $L$ be an $R$-submodule of $V$ equipped with two lattice embeddings $rho : V -> E$ and $rho_2 : V -> E_2$ such that for a constant $c in bb(R)$ and every $R$-submodule $N subset.eq L$,
    $ op("rk")(rho_2, N) = op("rk")(rho, N), quad hat(op("deg"))(rho_2, N) = hat(op("deg"))(rho, N) + c dot.c op("rk")(rho, N). $
    (For example, scaling the Euclidean norm by $e^(-c)$ achieves this.) Then $rho$ and $rho_2$ have the same saturated submodules, and for $L != 0$:
    $ mu_max (rho_2, L) = mu_max (rho, L) + c, quad mu_min (rho_2, L) = mu_min (rho, L) + c, $
    $ op("hnStep")(rho_2, L, theta + c) &= op("hnStep")(rho, L, theta), \
      op("hnPoly")(rho_2, L, m) &= op("hnPoly")(rho, L, m) + c dot.c min(m, op("rk")(rho, L)). $
  ]

  #proof[
    Because $op("rk")(rho_2, N) = op("rk")(rho, N)$ for all $N subset.eq L$, a submodule $N subset.eq L$ is saturated with respect to $rho$ if and only if no strictly larger submodule of $L$ has the same rank, which is identical for $rho_2$. For every nonzero $N subset.eq L$, $hat(mu)(rho_2, N) = hat(mu)(rho, N) + c$, and for every proper saturated $N subset.neq L$, $hat(mu)(rho_2, L \/ N) = hat(mu)(rho, L \/ N) + c$. Taking suprema and infima yields the shifts of $mu_max$, $mu_min$, `hnStep`, `slopeList`, and `hnPoly` immediately.
  ]

  == Bost's Slope Inequality

  In algebraic geometry, the Harder–Narasimhan filtration acquires its full force when combined with the homological vanishing principle: if $cal(E)$ and $cal(F)$ are vector bundles on a smooth projective curve $C$ and $mu_min (cal(E)) > mu_max (cal(F))$, then $op("Hom")(cal(E), cal(F)) = 0$. In Arakelov geometry, a morphism $phi : overline(E) -> overline(F)$ of Hermitian vector bundles does not preserve metrics automatically; instead, it distorts archimedean norms by at most its operator norm $C = ||phi||_(op("op"))$. In his landmark 1996 and 2001 papers on periods, isogenies, and algebraic foliations, Jean-Benoît Bost discovered that the exact arithmetic analogue of the curve vanishing principle holds with the single additive error term $+ log C$.

  === Statement and Proof of Bost's Slope Inequality

  We first record the injective special case (`Formalism.F.SlopeInequality`), which follows in three lines from Gram determinant monotonicity (Lemma 9.12).

  #corollary(title: "Injective Slope Inequality, Formalism.F.SlopeInequality")[
    Let $overline(L)$ and $overline(M)$ be Euclidean lattices in inner product spaces $E$ and $F$ with $L != 0$, and let $phi : L -> M$ be an injective $bb(Z)$-linear map. Suppose $C > 0$ satisfies
    $ ||phi(x)||_F <= C dot.c ||x||_E quad "for all" x in L. $
    Then
    $ hat(mu)(overline(L)) <= hat(mu)(overline(phi(L))) + log C <= mu_max (overline(M)) + log C. $
  ]

  #proof[
    Let $e_1, dots.c, e_r$ be a $bb(Z)$-basis of $L$. Because $phi : L -> M$ is injective and $L, M$ are discrete, $phi$ extends uniquely to an $bb(R)$-linear map $phi_bb(R) : op("span")_bb(R)(L) -> op("span")_bb(R)(M)$ satisfying $||phi_bb(R)(x)||_F <= C ||x||_E$ for all $x in op("span")_bb(R)(L)$ (by density of $bb(Q)$ in $bb(R)$ and continuity). Applying Lemma 9.12 to $v_i = e_i$ and $w_i = phi(e_i)$ yields
    $ det G(phi(e_1), dots.c, phi(e_r)) <= C^(2 r) det G(e_1, dots.c, e_r). $
    Taking square roots gives $op("covol")(overline(phi(L))) <= C^r op("covol")(overline(L))$. Applying $-log$ and dividing by $r = op("rk")(L) = op("rk")(phi(L))$ gives
    $ hat(mu)(overline(L)) <= hat(mu)(overline(phi(L))) + log C <= mu_max (overline(M)) + log C, $
    since $phi(L)$ is a nonzero sublattice of $M$.
  ]

  We now establish Bost's slope inequality in its full generality (`Formalism.HN.SlopeIneq`), allowing $phi$ to have a nontrivial kernel and working over any base ring $R$ (including $R = bb(Z)$ and $R = cal(O)_K$).

  #theorem(title: "Bost's Slope Inequality, Formalism.HN.SlopeIneq")[
    Let $R$ be a ring, let $L subset.eq V$ and $M subset.eq W$ be $R$-lattices with respect to additive embeddings $rho : V -> E$ and $rho' : W -> F$ into finite-dimensional real inner product spaces $E$ and $F$. Let $phi : L -> M$ be an $R$-linear map, and suppose $C > 0$ satisfies
    $ ||rho'(phi(x))||_F <= C dot.c ||rho(x)||_E quad "for all" x in L. $
    Then:
    1. If $phi != 0$, then
       $ mu_min (rho, L) - log C <= mu_min (rho', op("im")(phi)) $
       and in particular
       $ mu_min (rho, L) <= mu_max (rho', M) + log C. $
    2. If $phi$ is injective and $L != 0$, then
       $ mu_max (rho, L) <= mu_max (rho', M) + log C. $
  ]

  #proof[
    We first prove (2). Suppose $phi$ is injective and $L != 0$. For every nonzero $R$-submodule $N subset.eq L$, the restriction $phi|_N : N -> M$ is an injective $bb(Z)$-linear map of Euclidean lattices (identifying $N$ with $rho(N)$ and $M$ with $rho'(M)$) satisfying $||rho'(phi(x))||_F <= C ||rho(x)||_E$ for all $x in N$. By Corollary 9.22,
    $ hat(mu)(rho, N) <= hat(mu)(rho', phi(N)) + log C <= mu_max (rho', M) + log C, $
    where the second inequality holds because $phi(N)$ is a nonzero $R$-submodule of $M$. Taking the supremum over all nonzero $R$-submodules $N subset.eq L$ yields $mu_max (rho, L) <= mu_max (rho', M) + log C$.

    Now we prove (1). Assume $phi != 0$, and let $I = op("im")(phi) subset.eq M$, which is a nonzero $R$-submodule of $M$. To prove $mu_min (rho, L) - log C <= mu_min (rho', I)$, let $J subset.neq I$ be any proper saturated $R$-submodule of $I$; we must show that
    $ mu_min (rho, L) - log C <= hat(mu)(overline(I \/ J)). $
    Consider the preimage $N = phi^(-1)(J) subset.eq L$. Because $phi$ is $R$-linear and surjective onto $I$, $N$ is a proper $R$-submodule of $L$. We claim that $N$ is saturated in $L$. Indeed, let $x in L$ satisfy $m x in N$ for some nonzero integer $m$; then $m phi(x) = phi(m x) in J$, and since $J$ is saturated in $I$ (so $I \/ J$ is torsion-free), we must have $phi(x) in J$, hence $x in N$. Thus $L \/ N$ is torsion-free, so $N$ is saturated in $L$.

    Let $W_N = op("span")_bb(R)(rho(N)) subset.eq E$ and $W_J = op("span")_bb(R)(rho'(J)) subset.eq F$, with orthogonal projections $pi_(W_N^perp) : E -> W_N^perp$ and $pi_(W_J^perp) : F -> W_J^perp$. Because $phi : L -> I$ induces an isomorphism of $R$-modules $overline(phi) : L \/ N -> I \/ J$, it induces an injective $bb(Z)$-linear map of quotient Euclidean lattices
    $ overline(phi) : pi_(W_N^perp)(rho(L)) -> pi_(W_J^perp)(rho'(I)), quad pi_(W_N^perp)(rho(x)) |-> pi_(W_J^perp)(rho'(phi(x))). $
    We claim that $overline(phi)$ has operator norm at most $C$ with respect to the quotient metrics! To see this, extend $phi$ by $bb(R)$-linearity to $phi_bb(R) : op("span")_bb(R)(rho(L)) -> op("span")_bb(R)(rho'(I))$; by continuity and density of $bb(Q)$ in $bb(R)$, we still have $||phi_bb(R)(v)||_F <= C ||v||_E$ for all $v in op("span")_bb(R)(rho(L))$, and clearly $phi_bb(R)(W_N) subset.eq W_J$. Now let $x in L$ and decompose $rho(x) = w + u$ with $w in W_N$ and $u = pi_(W_N^perp)(rho(x)) in W_N^perp$. Since $phi_bb(R)(w) in W_J = ker(pi_(W_J^perp))$ and orthogonal projection onto $W_J^perp$ is $1$-Lipschitz, we obtain
    $ ||pi_(W_J^perp)(rho'(phi(x)))||_F
      &= ||pi_(W_J^perp)(phi_bb(R)(w) + phi_bb(R)(u))||_F \
      &= ||pi_(W_J^perp)(phi_bb(R)(u))||_F <= ||phi_bb(R)(u)||_F \
      &<= C ||u||_E = C ||pi_(W_N^perp)(rho(x))||_E. $

    Applying Corollary 9.22 to the injective map $overline(phi) : overline(L \/ N) -> overline(I \/ J)$ gives
    $ hat(mu)(overline(L \/ N)) <= hat(mu)(overline(I \/ J)) + log C. $
    Since $N subset.neq L$ is a proper saturated $R$-submodule of $L$, the definition of $mu_min (rho, L)$ gives $mu_min (rho, L) <= hat(mu)(overline(L \/ N))$, and therefore
    $ mu_min (rho, L) - log C <= hat(mu)(overline(I \/ J)). $
    Taking the infimum over all proper saturated $R$-submodules $J subset.neq I$ yields $mu_min (rho, L) - log C <= mu_min (rho', I)$.

    Finally, by Proposition 9.16(4) applied to $I$ and the definition of $mu_max (rho', M)$,
    $ mu_min (rho, L) - log C <= mu_min (rho', I) <= hat(mu)(rho', I) <= mu_max (rho', M), $
    which gives $mu_min (rho, L) <= mu_max (rho', M) + log C$.
  ]

  For a Hermitian vector bundle $overline(E) = (E, {||dot.c||_v}_(v | oo))$ over a number field $K$, if $phi : overline(E) -> overline(F)$ is a morphism of $cal(O)_K$-modules with local operator norms $||phi_v|| <= C_v$ at each archimedean place $v | oo$, then one can rescale the metrics at each infinite place (or apply the exterior power inequality directly at each place $v | oo$) to obtain the multi-place form of Bost's slope inequality:
  $ mu_min (overline(E)) <= mu_max (overline(F)) + sum_(v | oo) epsilon_v log C_v. $
  When all local operator norms satisfy $||phi_v|| <= C$, passing to the $bb(Z)$-lattices $pi_* overline(E)$ and $pi_* overline(F)$ via Proposition 9.6 immediately recovers this bound from Theorem 9.23, since the discriminant shifts $-(log |Delta_K|) \/ (2 d)$ on both sides cancel out identically.

  The following immediate corollary packages Bost's slope inequality into the two forms most frequently invoked in Diophantine geometry and automorphic multiplicity bounds.

  #corollary(title: "Vanishing Criterion and Filtered Bost Slope Inequality")[
    1. (_Vanishing Criterion_) Let $phi : overline(E) -> overline(F)$ be a morphism of Euclidean lattices with operator norm $<= C$ ($C > 0$). If
       $ mu_min (overline(E)) > mu_max (overline(F)) + log C, $
       then $phi = 0$.
    2. (_Filtered Slope Inequality_) Let $overline(E)$ be a Euclidean lattice equipped with a finite decreasing filtration by saturated sublattices
       $ E = F^0 supset.eq F^1 supset.eq dots.c supset.eq F^m = 0. $
       Suppose that for each $0 <= i < m$ there is an injective morphism $phi_i : overline(F^i \/ F^(i+1)) -> overline(G)_i$ into a Euclidean lattice $overline(G)_i$ with operator norm $<= C_i$ ($C_i > 0$). Then
       $ hat(op("deg"))(overline(E)) <= sum_(i=0)^(m-1) op("rk")(F^i \/ F^(i+1)) dot.c (mu_max (overline(G)_i) + log C_i). $
  ]

  #proof[
    Part (1) is the contrapositive of Theorem 9.23(1). For part (2), repeated application of Proposition 9.8(2) gives
    $ hat(op("deg"))(overline(E)) = sum_(i=0)^(m-1) hat(op("deg"))(overline(F^i \/ F^(i+1))). $
    For each index $i$ with $F^i \/ F^(i+1) != 0$, Corollary 9.22 applied to the injective map $phi_i : overline(F^i \/ F^(i+1)) -> overline(G)_i$ yields
    $ hat(op("deg"))(overline(F^i \/ F^(i+1)))
      &= op("rk")(F^i \/ F^(i+1)) dot.c hat(mu)(overline(F^i \/ F^(i+1))) \
      &<= op("rk")(F^i \/ F^(i+1)) dot.c (mu_max (overline(G)_i) + log C_i). $
    Summing over $i = 0, dots.c, m - 1$ gives the desired inequality.
  ]

  === Why Bost's Slope Inequality Is Arithmetic Stepanov

  In the proof of the Riemann Hypothesis over finite fields via Stepanov's method (Chapters 2–3), the heart of the argument is the elementary degree bound $m dot.c N_q <= deg(Phi)$ for a nonzero auxiliary polynomial $Phi$ vanishing to order at least $m$ at each of $N_q$ rational points. It is illuminating to see that Bost's slope inequality is not merely _inspired_ by this bound—it is its exact arithmetic-geometric generalization.

  #insight-box(title: "Bost's Slope Inequality as the Arithmetic Analogue of Stepanov's Bound")[
    Compare the geometric setup on a smooth projective curve $C \/ bb(F)_q$ with the arithmetic setup over $op("Spec") cal(O)_K$:

    #table(
      columns: (1fr, 1.35fr, 1.45fr),
      inset: 6pt,
      stroke: 0.4pt + gtm-rule,
      fill: (x, y) => if y == 0 { gtm-tint } else { white },
      [*Feature*], [*Stepanov's Method on $C \/ bb(F)_q$*], [*Bost's Method over $op("Spec") cal(O)_K$*],
      [Base space], [Projective curve $C$ over $bb(F)_q$], [Compactified base $overline(op("Spec") cal(O)_K)$],
      [Auxiliary object], [Line bundle $cal(O)_C (d)$ or bundle $cal(E)$], [Hermitian lattice $overline(E) = (H^0 (cal(X), cal(L)^(times.o D)), ||dot.c||)$],
      [Evaluation map], [$op("ev") : cal(O)_C (d) -> plus.o_(j=1)^(N_q) cal(O)_(m P_j)$], [$phi : overline(E) -> overline(F)$ (jets, periods, or theta lifts)],
      [Vanishing order / norm], [Order of vanishing $m$ at $N_q$ points], [Archimedean operator norm $||phi|| <= C$ (or Schwarz lemma decay $e^(-m c)$)],
      [Global constraint], [$m dot.c N_q <= deg(Phi)$], [$mu_min (overline(E)) <= mu_max (overline(F)) + log C$],
      [Contradiction mechanism], [$m dot.c N_q > d ==> Phi equiv 0$], [$mu_min (overline(E)) > mu_max (overline(F)) + log C ==> phi = 0$],
    )

    To see the correspondence even more sharply, suppose $Phi in H^0(C, cal(O)_C (d))$ is a nonzero section vanishing to order $>= m$ at points $P_1, dots.c, P_(N_q)$. Then multiplication by $Phi$ defines a nonzero morphism of line bundles
    $ cal(O)_C (m sum_(j=1)^(N_q) P_j) -> cal(O)_C (d). $
    Because line bundles are semistable of slope equal to their degree, the curve slope inequality $mu_min (cal(E)) <= mu_max (cal(F))$ reads literally
    $ m dot.c N_q = deg(cal(O)_C (m sum P_j)) <= deg(cal(O)_C (d)) = d. $
    In the arithmetic setting of Alpöge and Claude's proof, $overline(E)$ is a Hermitian lattice of integral automorphic forms (or sections of a Hermitian line bundle on an arithmetic model of a Shimura variety), and $phi : overline(E) -> overline(F)$ is an evaluation or representation-theoretic comparison map whose archimedean norm $C$ is tightly controlled by Schwarz-type decay estimates (or analytic bounds on theta kernels). In place of the single number $d = deg(Phi)$, we need a _lower bound_ on $hat(op("deg"))(overline(E))$—equivalently, an _upper bound_ on the covolume $op("covol")(overline(E))$—and an _upper bound_ on $mu_max (overline(F))$. When the filtered Bost slope inequality (Corollary 9.24(2)) is applied to the vanishing filtration $F^i$ by order of vanishing at a point or cusp, the archimedean Schwarz lemma supplies a factor $C_i approx R^(-i)$ at filtration step $i$, turning the sum of $log C_i$ into a negative linear term $-i log R$ that plays the exact role of $-m dot.c N_q$ in Stepanov's method!
  ]

  == Arithmetic Hilbert–Samuel, Moriwaki Bigness, and Toroidal Compactifications

  To deploy Bost's slope inequality on a space of global sections $E_k = H^0(cal(X), cal(L)^(times.o k))$—most notably, spaces of integral Siegel modular forms of weight $k$—we must estimate its Arakelov degree $hat(op("deg"))(overline(E)_k) = -log op("covol")(overline(E)_k)$ as $k -> oo$. Over a curve $C$, the Riemann–Roch theorem determines the dimension and degree of $H^0(C, cal(L)^(times.o k))$ in terms of the intersection number $deg(cal(L))$. On a higher-dimensional arithmetic variety $cal(X) -> op("Spec") cal(O)_K$, the corresponding engine is higher-dimensional Arakelov intersection theory, culminating in the arithmetic Hilbert–Samuel theorem, Moriwaki's bigness criterion, and their extension to Siegel toroidal compactifications with logarithmically singular Petersson metrics. In this section we survey these four pillars as they are used and formalized in the proof.

  === Arithmetic Intersection Theory and the Poincaré–Lelong Equation

  Let $K$ be a number field. An _arithmetic variety_ of relative dimension $d$ (hence absolute Krull dimension $d + 1$) is an integral, flat, projective scheme $pi : cal(X) -> op("Spec") cal(O)_K$ whose generic fiber $cal(X)_K$ is smooth over $K$. Its set of complex points $cal(X)(bb(C)) = union.sq_(sigma : K -> bb(C)) cal(X)_sigma (bb(C))$ is a compact complex manifold of complex dimension $d$, equipped with the antiholomorphic involution $F_oo$ induced by complex conjugation.

  #definition(title: "Hermitian Line Bundle and First Chern Form")[
    A _Hermitian line bundle_ $overline(cal(L)) = (cal(L), ||dot.c||)$ on an arithmetic variety $cal(X)$ consists of a line bundle $cal(L)$ on $cal(X)$ together with a smooth (or, more generally, continuous or singular plurisubharmonic) Hermitian metric $||dot.c||$ on the holomorphic line bundle $cal(L)_bb(C)$ over $cal(X)(bb(C))$ that is invariant under $F_oo$.

    On any open chart where $cal(L)_bb(C)$ admits a nowhere-vanishing holomorphic frame $s$, the _first Chern form_ (or _curvature form_) of $overline(cal(L))$ is the smooth real $(1, 1)$-form
    $ c_1 (overline(cal(L))) = (1) / (2 pi i) partial overline(partial) log ||s||^(-2) = -d d^c log ||s||^2, $
    where $d^c = (i \/ 4 pi)(overline(partial) - partial)$ so that $d d^c = (i \/ 2 pi) partial overline(partial)$. We say that $overline(cal(L))$ is _positively curved_ (resp. _semipositively curved_) if the $(1, 1)$-form $c_1 (overline(cal(L)))$ is strictly positive (resp. positive semidefinite) at every point of $cal(X)(bb(C))$.
  ]

  The fundamental bridge between algebraic divisors and differential forms on $cal(X)(bb(C))$ is the Poincaré–Lelong equation.

  #theorem(title: "Poincaré–Lelong Equation")[
    Let $overline(cal(L)) = (cal(L), ||dot.c||)$ be a smooth Hermitian line bundle on $cal(X)$, and let $s$ be a nonzero meromorphic section of $cal(L)_bb(C)$ with divisor $op("div")(s)$ on $cal(X)(bb(C))$. Then, as currents of bidegree $(1, 1)$ on $cal(X)(bb(C))$,
    $ d d^c [-log ||s||^2] + delta_(op("div")(s)) = [c_1 (overline(cal(L)))], $
    where $delta_(op("div")(s))$ is the current of integration along the analytic cycle $op("div")(s)$. Equivalently, for every smooth $(d - 1, d - 1)$-form $eta$ on $cal(X)(bb(C))$,
    $ integral_(cal(X)(bb(C))) (-log ||s||^2) dot.c d d^c eta + integral_(op("div")(s)) eta = integral_(cal(X)(bb(C))) eta and c_1 (overline(cal(L))). $
  ]

  In the Gillet–Soulé arithmetic intersection theory, the _arithmetic Chow group_ $hat(op("CH"))^p (cal(X))$ consists of pairs $(Z, g_Z)$ of codimension-$p$ algebraic cycles $Z$ on $cal(X)$ and Green currents $g_Z$ on $cal(X)(bb(C))$ satisfying $d d^c g_Z + delta_Z = [omega_Z]$ for a smooth $(p, p)$-form $omega_Z$, modulo arithmetic rational equivalence $(op("div")(f), [-log |f|^2])$. By the Poincaré–Lelong equation, every smooth Hermitian line bundle $overline(cal(L))$ defines a canonical arithmetic first Chern class
  $ hat(c)_1 (overline(cal(L))) = (op("div")(s), [-log ||s||^2]) in hat(op("CH"))^1 (cal(X)), $
  which is independent of the choice of nonzero rational section $s$.

  Gillet and Soulé constructed an associative, commutative intersection pairing on $hat(op("CH"))^bullet (cal(X))_bb(Q)$ together with an arithmetic degree map $hat(op("deg")) : hat(op("CH"))^(d+1)(cal(X)) -> bb(R)$. In particular, given Hermitian line bundles $overline(cal(L))_0, dots.c, overline(cal(L))_d$ on $cal(X)$, their _arithmetic intersection number_
  $ hat(c)_1 (overline(cal(L))_0) dot.c hat(c)_1 (overline(cal(L))_1) dots.c hat(c)_1 (overline(cal(L))_d) in bb(R) $
  is characterized inductively by the height formula: if $s$ is a nonzero rational section of $cal(L)_0$ whose divisor $op("div")(s)$ meets the generic fiber properly, then
  $ &hat(c)_1 (overline(cal(L))_0) dots.c hat(c)_1 (overline(cal(L))_d) \
    &= hat(op("deg"))(overline(cal(L))_1 dots.c overline(cal(L))_d |_(op("div")(s))) \
    &quad - integral_(cal(X)(bb(C))) log ||s|| dot.c c_1 (overline(cal(L))_1) and dots.c and c_1 (overline(cal(L))_d). $
  When $d = 0$ and $cal(X) = op("Spec") cal(O)_K$, this reduces directly to $hat(op("deg"))(overline(cal(L))_0) = log N(op("div")(s)) - sum_(sigma : K -> bb(C)) log ||s||_sigma$ from Section 9.1. When $overline(cal(L))_0 = dots.c = overline(cal(L))_d = overline(cal(L))$, we write $hat(c)_1 (overline(cal(L)))^(d+1)$ for the top arithmetic self-intersection number.

  === The Arithmetic Hilbert–Samuel Theorem

  Fix a smooth positive volume form $mu$ on $cal(X)(bb(C))$ (invariant under $F_oo$). For each positive integer $k$, the space of global sections $E_k = H^0(cal(X), cal(L)^(times.o k))$ is a finitely generated projective $cal(O)_K$-module, which becomes a Hermitian vector bundle $overline(E)_k$ when equipped with the $L^2$-Hermitian norm
  $ ||s||^2_(L^2, sigma) = integral_(cal(X)_sigma (bb(C))) ||s(x)||^(2)_sigma d mu_sigma (x) $
  at each embedding $sigma : K -> bb(C)$. Alternatively, one may equip $E_k$ with the supremum norm $||s||_(oo, sigma) = sup_(x in cal(X)_sigma (bb(C))) ||s(x)||_sigma$ (which is a Banach norm rather than a Hermitian norm, though by Gromov's ratio / John's ellipsoid theorem it is comparable to $||dot.c||_(L^2)$ up to a factor polynomial in $k$, shifting the Arakelov degree by at most $O(k^d log k)$).

  In classical algebraic geometry, the asymptotic Riemann–Roch (Hilbert–Samuel) theorem asserts that for an ample line bundle $cal(L)$ on a $d$-dimensional projective variety $X$,
  $ op("rk") H^0(X, cal(L)^(times.o k)) = (c_1 (cal(L))^d) / (d!) k^d + O(k^(d-1)) quad (k -> oo). $
  The arithmetic Hilbert–Samuel theorem, originally proved by Gillet and Soulé (1992) by combining their arithmetic Riemann–Roch theorem with the Bismut–Vasserot analytic torsion asymptotics, and subsequently given more elementary proofs by Abbes–Bouche (1995) and Zhang (1995), gives the exact arithmetic counterpart for the Arakelov degree $hat(op("deg"))(overline(E)_k)$.

  #theorem(title: "Arithmetic Hilbert–Samuel Theorem, ArithHilbertSamuel")[
    Let $cal(X) -> op("Spec") cal(O)_K$ be an arithmetic variety of relative dimension $d$, and let $overline(cal(L))$ be a smooth Hermitian line bundle on $cal(X)$ such that:
    1. $cal(L)$ is ample on $cal(X)$ (or more generally, $cal(L)_K$ is ample and $cal(L)$ is relatively nef), and
    2. the curvature form $c_1 (overline(cal(L)))$ is strictly positive on $cal(X)(bb(C))$.
    Then as $k -> oo$, the Arakelov degree of the $L^2$-Hermitian vector bundle $overline(E)_k = (H^0(cal(X), cal(L)^(times.o k)), ||dot.c||_(L^2))$ satisfies
    $ hat(op("deg"))(overline(E)_k) = (hat(c)_1 (overline(cal(L)))^(d+1)) / ((d + 1)!) k^(d+1) + o(k^(d+1)). $
    In particular, the slope $hat(mu)(overline(E)_k)$ grows linearly in $k$:
    $ hat(mu)(overline(E)_k) = (hat(c)_1 (overline(cal(L)))^(d+1)) / ((d + 1) dot.c [K : bb(Q)] dot.c c_1 (cal(L)_K)^d) dot.c k + o(k). $
  ]

  Notice the remarkable sign and scaling in Theorem 9.27: the leading term of $hat(op("deg"))(overline(E)_k)$ is _independent_ of the choice of smooth volume form $mu$ on $cal(X)(bb(C))$ (changing $mu$ by a positive smooth function $f$ changes $||s||_(L^2)$ by a bounded factor, altering $hat(op("deg"))(overline(E)_k)$ by $O(op("rk")(E_k)) = O(k^d) = o(k^(d+1))$). Moreover, by comparing $L^2$-norms with sup-norms, one obtains the same asymptotic for the arithmetic Euler characteristic $hat(chi)_(sup)(overline(cal(L))^(times.o k))$, and therefore a precise upper bound on the covolume $op("covol")(overline(E)_k) = exp(-hat(op("deg"))(overline(E)_k))$.

  === Moriwaki's Bigness Criterion, Nadel Vanishing, and Kawamata–Viehweg

  In practice—especially on moduli spaces such as toroidal compactifications of Siegel modular varieties—the natural Hermitian line bundle (the Hodge bundle $overline(omega)$) is _not_ ample, only _nef and big_! Furthermore, one frequently needs to know not merely the asymptotic degree $hat(op("deg"))(overline(E)_k)$, but that $overline(E)_k$ actually possesses _many small nonzero sections_ ($||s||_oo <= 1$), i.e., that $overline(cal(L))$ is _arithmetically big_.

  Recall that for a Hermitian line bundle $overline(cal(L))$ on $cal(X)$, the _arithmetic volume_ (introduced by Moriwaki and Yuan) is defined by
  $ hat(op("vol"))(overline(cal(L))) = limsup_(k -> oo) ((d + 1)!) / (k^(d+1)) log \# { s in H^0(cal(X), cal(L)^(times.o k)) : ||s||_oo <= 1 }, $
  and $overline(cal(L))$ is called _arithmetically big_ if $hat(op("vol"))(overline(cal(L))) > 0$. By Minkowski's first theorem, if $hat(op("deg"))(overline(E)_k) >= c k^(d+1)$ with $c > 0$ for large $k$, then $overline(E)_k$ contains exponentially many small sections (of norm $<= 1$), so positive asymptotic Arakelov degree implies arithmetic bigness.

  Similarly, $overline(cal(L))$ is called _arithmetically nef_ (or _semipositive_ in Zhang's sense) if:
  1. $c_1 (overline(cal(L))) >= 0$ as a $(1, 1)$-form on $cal(X)(bb(C))$ (semipositivity at infinity), and
  2. for every closed $1$-dimensional integral subscheme $C subset.eq cal(X)$ (whether vertical or horizontal), $hat(op("deg"))(overline(cal(L))|_C) >= 0$.

  Moriwaki (2008, 2009) and Yuan (2008, building on Siu's bigness criterion in algebraic geometry) extended the arithmetic Hilbert–Samuel theorem from ample to nef-and-big Hermitian line bundles.

  #theorem(title: "Moriwaki's Bigness Criterion, MoriwakiBigTheorem")[
    Let $cal(X) -> op("Spec") cal(O)_K$ be an arithmetic variety of relative dimension $d$, and let $overline(cal(L))$ be an arithmetically nef Hermitian line bundle on $cal(X)$. If the top arithmetic self-intersection number is strictly positive,
    $ hat(c)_1 (overline(cal(L)))^(d+1) > 0, $
    then $overline(cal(L))$ is arithmetically big; in fact, its arithmetic volume equals its top self-intersection number:
    $ hat(op("vol"))(overline(cal(L))) = hat(c)_1 (overline(cal(L)))^(d+1) > 0. $
    More generally, if $overline(cal(L))$ and $overline(cal(M))$ are both arithmetically nef, then Yuan's arithmetic Siu inequality gives
    $ hat(op("vol"))(overline(cal(L)) times.o overline(cal(M))^(-1)) >= hat(c)_1 (overline(cal(L)))^(d+1) - (d + 1) hat(c)_1 (overline(cal(L)))^d dot.c hat(c)_1 (overline(cal(M))). $
  ]

  Two classical complex-analytic and algebraic vanishing theorems play an indispensable supporting role in passing from ample to nef-and-big bundles and in handling singular Hermitian metrics:

  - _Kawamata–Viehweg vanishing._ On a smooth complex projective variety $X$, if $L$ is a nef and big line bundle (or $bb(Q)$-divisor whose fractional part has simple normal crossings support), then $H^q (X, K_X times.o L) = 0$ for all $q > 0$. This vanishing ensures that exact sequences of sheaves on $X$ remain exact on global sections for high tensor powers, allowing the arithmetic Hilbert–Samuel induction to pass from $cal(X)$ to a hyperplane section $cal(Y) subset.eq cal(X)$ without obstruction from higher cohomology.
  - _Nadel vanishing._ When a Hermitian metric $h = e^(-phi)$ on $L$ has singularities (so the local weight $phi$ is only plurisubharmonic rather than smooth), one associates to $phi$ its _multiplier ideal sheaf_ $cal(I)(phi) subset.eq cal(O)_X$, consisting of germs of holomorphic functions $f$ such that $|f|^2 e^(-2 phi)$ is locally integrable. If the curvature current $i partial overline(partial) phi$ dominates a strictly positive $(1, 1)$-form $epsilon omega$, then Nadel's vanishing theorem asserts that
    $ H^q (X, K_X times.o L times.o cal(I)(phi)) = 0 quad "for all" q > 0. $
    In Arakelov geometry, Nadel vanishing (derived from Hörmander's $L^2$-estimates for the $overline(partial)$-operator) allows one to lift small sections from subvarieties and control the singularities of metrics near boundary divisors, bridging smooth Arakelov theory to the logarithmically singular metrics arising on Shimura varieties.

  === Siegel Toroidal Compactifications and Covolume Bounds

  We now specialize to the arithmetic varieties that lie at the heart of the Alpöge–Claude proof: the moduli spaces of principally polarized abelian varieties and their toroidal compactifications.

  Let $g >= 1$ and $N >= 3$ be integers, and let $cal(A)_(g, N)$ be the fine moduli scheme over $bb(Z)[1/N, zeta_N]$ (or its integral model over $bb(Z)$) parametrizing principally polarized abelian schemes $pi : cal(G) -> cal(A)_(g, N)$ of relative dimension $g$ with symplectic level-$N$ structure. Its complex points form the Siegel modular variety
  $ cal(A)_(g, N)(bb(C)) tilde.equiv Gamma_g (N) backslash frak(H)_g, $
  where $frak(H)_g = { Z in op("Mat")_(g times g)(bb(C)) : Z^T = Z, op("Im")(Z) > 0 }$ is the Siegel upper half-space of genus $g$ (complex dimension $d = g(g + 1) \/ 2$) and $Gamma_g (N) = ker(op("Sp")_(2 g)(bb(Z)) -> op("Sp")_(2 g)(bb(Z) \/ N bb(Z)))$ is the principal congruence subgroup of level $N$.

  The _Hodge bundle_ on $cal(A)_(g, N)$ is the determinant line bundle
  $ omega = det(pi_* Omega^1_(cal(G) \/ cal(A)_(g, N))) $
  of the rank-$g$ bundle of invariant $1$-forms on the universal abelian scheme. Global sections of $omega^(times.o k)$ over $cal(A)_(g, N)(bb(C))$ are Siegel modular forms of genus $g$, weight $k$, and level $Gamma_g (N)$: holomorphic functions $f : frak(H)_g -> bb(C)$ satisfying
  $ &f((A Z + B)(C Z + D)^(-1)) = det(C Z + D)^k f(Z) \
    &quad "for all" mat(A, B; C, D) in Gamma_g (N) $
  (together with holomorphicity at the cusps when $g = 1$; for $g >= 2$, holomorphicity at the cusps is automatic by the Koecher principle).

  Over $cal(A)_(g, N)(bb(C))$, the Hodge bundle $omega$ carries the canonical _Petersson (or Faltings) Hermitian metric_: for a section $f$ of $omega^(times.o k)$,
  $ ||f(Z)||^2_(op("Pet")) = |f(Z)|^2 dot.c (det op("Im")(Z))^k. $
  However, $cal(A)_(g, N)$ is _not_ projective! To apply Arakelov geometry, we must compactify it. By the fundamental theorem of Faltings and Chai (1990), for any smooth, projective, $op("GL")_g (bb(Z))$-admissible polyhedral cone decomposition $Sigma$ of the cone of positive semidefinite symmetric $g times g$ matrices, there exists a smooth projective _toroidal compactification_
  $ cal(A)_(g, N) arrow.hook overline(cal(A))_(g, N)^Sigma $
  over $bb(Z)[1/N, zeta_N]$ (with a semistable boundary divisor $D = overline(cal(A))_(g, N)^Sigma without cal(A)_(g, N)$ having simple normal crossings), such that:
  1. the universal abelian scheme $cal(G)$ extends to a semi-abelian scheme over $overline(cal(A))_(g, N)^Sigma$, and consequently the Hodge bundle $omega$ extends to a line bundle (still denoted $omega$) on $overline(cal(A))_(g, N)^Sigma$;
  2. $omega$ is _nef and big_ on $overline(cal(A))_(g, N)^Sigma$ (it is the pullback of the ample line bundle on the minimal Satake–Baily–Borel compactification $cal(A)_(g, N)^*$); and
  3. for $g >= 2$, $H^0(overline(cal(A))_(g, N)^Sigma, omega^(times.o k)) = H^0(cal(A)_(g, N), omega^(times.o k))$ is precisely the space of integral Siegel modular forms of weight $k$.

  There is one subtle analytic obstacle: as $Z$ approaches the boundary divisor $D$ (for instance, as $op("Im")(Z) -> oo$ in a cusp chart $q = e^(2 pi i Z)$), the factor $det op("Im")(Z) = (2 pi)^(-g) det(-log |q|)$ blows up _logarithmically_! Thus the Petersson metric $||dot.c||_(op("Pet"))$ on $omega$ is not smooth on $overline(cal(A))_(g, N)^Sigma$—it is a _pre-log-singular_ (or _log-singular_) Hermitian metric in the sense of Burgos Gil, Kramer, and Kühn (2005, 2007). Remarkably, logarithmic singularities are mild enough that all Chern forms $c_1 (overline(omega))^m$ are locally integrable on $overline(cal(A))_(g, N)^Sigma (bb(C))$ and satisfy the Poincaré–Lelong equation in the sense of currents, so the arithmetic intersection number $hat(c)_1 (overline(omega))^(d + 1)$ remains finite and well-defined!

  #theorem(title: "Siegel Toroidal Integrals and Covolume Bounds")[
    Let $overline(cal(A))_(g, N)^Sigma$ be a smooth projective toroidal compactification of $cal(A)_(g, N)$ of relative dimension $d = g(g + 1) \/ 2$, and let $overline(omega) = (omega, ||dot.c||_(op("Pet")))$ be the Hodge bundle equipped with the Petersson metric.
    1. (_Log-Singular Integrability_, `SiegelToroidalIntegralHolds`) The curvature form $c_1 (overline(omega))$ and its wedge powers $c_1 (overline(omega))^m$ ($1 <= m <= d$) extend as locally integrable currents across the boundary divisor $D$, and the arithmetic intersection pairing $hat(c)_1 (overline(omega))^(d + 1) in bb(R)$ is finite and independent of the choice of admissible cone decomposition $Sigma$.
    2. (_Covolume Bound for Spaces of Automorphic Forms_, `CovolumeBoundOfX`) Equipping the lattice $M_k = H^0(overline(cal(A))_(g, N)^Sigma, omega^(times.o k))$ of integral Siegel modular forms of weight $k$ with the Petersson $L^2$-metric (or sup-norm metric on a compact Siegel domain), the arithmetic Hilbert–Samuel theorem for log-singular nef-and-big bundles yields an explicit asymptotic lower bound on the Arakelov degree:
       $ hat(op("deg"))(overline(M)_k) = -log op("covol")(overline(M)_k) >= c_(g, N) dot.c k^(d + 1) - O(k^d log k) $
       as $k -> oo$, with an explicit constant $c_(g, N) = hat(c)_1 (overline(omega))^(d + 1) \/ ((d + 1)!)$ controlled by the Faltings height of the universal abelian variety and special values of $zeta'(-2 j + 1) \/ zeta(-2 j + 1)$.
  ]

  This covolume bound is the exact geometric input needed by Bost's slope inequality: it guarantees that the lattice $overline(M)_k$ of integral automorphic forms has a large positive Arakelov degree (and hence, on its semistable quotients or after twisting, a large minimal slope $mu_min$), which can then be played against the archimedean operator norm $log C$ of period, Fourier, or theta-lift evaluation maps.

  == Lean 4 Formalization

  One of the striking engineering achievements of the `lean-rh` repository is the complete, self-contained formalization of both the lattice-theoretic Harder–Narasimhan / Bost slope formalism and the higher-dimensional Arakelov geometry infrastructure. Below we summarize the exact module layout, definitions, and theorem statements in the repository.

  #lean-note(
    title: "Lean 4 Formalization: Harder–Narasimhan Theory, Bost's Slope Inequality, and Arakelov Geometry",
    module: "Formalism.LatticeSlopes, Formalism.HN, Development.AbelianVarietyTheory, Development.WeilBound",
  )[
    The Arakelov and slope-theoretic infrastructure in `lean-rh` is organized into three layers:

    1. *Euclidean Lattice Slopes* (`src/Formalism/LatticeSlopes/Statement.lean`, namespace `Formalism.F`):
       For a finite-dimensional real inner product space `E` and a `ℤ`-submodule `L : Submodule ℤ E`, the file defines `covol L` as `Real.sqrt (Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L i : L) : E))).det` (when `DiscreteTopology L`), `rk L := Module.finrank ℤ L`, `deg L := -Real.log (covol L)`, `slope L := deg L / (rk L : ℝ)`, `muMax L := sSup (slopes L)`, `IsSaturated L N`, and the orthogonal-projection quotient `quot L N`. Its core statements include:
       - `CovolEqGram`, `CovolPos`, `CovolBasic`, `CovolEqCovolume` (identifying `covol L` with Mathlib's `ZLattice.covolume L`),
       - `GramDetLe` (Lemma 9.12), `SlopeInequality` (Corollary 9.22),
       - `DegQuot` (Proposition 9.8(2)), `MuMaxMono`, `OrthSum`, and `MuMaxLeMin` (Lemma 9.15).

    2. *Harder–Narasimhan Filtration and Bost's Slope Inequality* (`src/Formalism/HarderNarasimhan/Statement.lean`, namespace `Formalism.HN`):
       Rather than fixing $R = bb(Z)$ and $V = E$, `Formalism.HN` generalizes to an arbitrary ring `R`, an `R`-module `V`, a finite-dimensional real inner product space `E`, and an additive map `ρ : V →+ E`. A submodule `L : Submodule R V` satisfies `IsLat ρ L` when `Set.InjOn ρ L` and `DiscreteTopology (zl ρ L)`, where `zl ρ L` is the `ℤ`-submodule image of `L` in `E`. This allows the exact same theorems to apply to $bb(Z)$-lattices, $cal(O)_K$-bundles, and Hecke-stable submodules! The module defines `deg`, `rk`, `slope`, `IsSat`, `muMax`, `muMin`, `hnStep`, `slopeList`, `hnPoly`, and `dualZ`, and states and proves:
       - `DegSupermod` (Theorem 9.13): supermodularity `deg ρ A + deg ρ B ≤ deg ρ (A ⊔ B) + deg ρ (A ⊓ B)` and rank modularity;
       - `MuChar` (Proposition 9.16): universal characterizations of `muMax` and `muMin` and attainment of `muMax` on a saturated submodule;
       - `HNStep`, `HNSlopes`, `HNExtreme` (Theorem 9.18 & Proposition 9.20): saturation, maximality, antitone slope list, and the concave polygon upper envelope `deg ρ N ≤ hnPoly ρ L (rk ρ N)`;
       - `SlopeIneq` (Theorem 9.23): Bost's slope inequality for both nonzero and injective `R`-linear maps `φ : L →ₗ[R] M` with norm bound `C > 0`;
       - `HNSum`: preservation of `θ ≤ muMin` under finite suprema and exact formulas for orthogonal direct sums;
       - `ShiftInvariance` (Proposition 9.21): behavior of `muMax`, `muMin`, `hnStep`, and `hnPoly` under linear shifts `deg ρ₂ N = deg ρ N + c * rk ρ N`.

    3. *Higher-Dimensional Arakelov Geometry and Toroidal Covolume Bounds*:
       - `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`: formalizes `ArithHilbertSamuel` (in `SmallSecTensTriv.lean`, `ArithHilbertSamuelNefOfAmple.lean`, and `ArithHilbertSamuelOfPrincipalisation.lean`), passing from ample to nef-and-big bundles via principalization.
       - `Development/WeilBound/CoreStatements/TemperedRepresentationTheory/`: contains `PoincareLelong/`, `ArakelovCycleHeights/` (cycle height formulas and metric extensions), `NefDivisors/`, and `ChernDegreeComplex/`.
       - `Development/WeilBound/CoreStatements/AbelianHeightsDuality/ArakelovSingularities/`: handles singular Hermitian metrics, gluing, and pullbacks, feeding into `CovolumeBoundOfX` (in `LiftLambdaBound.lean`), `MoriwakiBigTheorem`, and `SiegelToroidalIntegralHolds`.

    Here are the verbatim Lean 4 statements of `DegSupermod` and `SlopeIneq` from `Formalism/HarderNarasimhan/Statement.lean`:

    ```lean
    def DegSupermod : Prop :=
      ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        (ρ : V →+ E) (L A B : Submodule R V),
        IsLat ρ L → A ≤ L → B ≤ L →
        rk ρ (A ⊔ B) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B ∧
        deg ρ A + deg ρ B ≤ deg ρ (A ⊔ B) + deg ρ (A ⊓ B)

    def SlopeIneq : Prop :=
      ∀ (R V W E F : Type*) [Ring R] [AddCommGroup V] [Module R V]
        [AddCommGroup W] [Module R W] [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
        (ρ : V →+ E) (ρ' : W →+ F) (L : Submodule R V) (M : Submodule R W),
        IsLat ρ L → IsLat ρ' M →
        ∀ (φ : L →ₗ[R] M) (C : ℝ), 0 < C →
        (∀ x : L, ‖ρ' (φ x : W)‖ ≤ C * ‖ρ (x : V)‖) →
        (φ ≠ 0 → muMin ρ L - Real.log C ≤ muMin ρ' ((LinearMap.range φ).map M.subtype) ∧
          muMin ρ L ≤ muMax ρ' M + Real.log C) ∧
        (Function.Injective φ → L ≠ ⊥ → muMax ρ L ≤ muMax ρ' M + Real.log C)
    ```
  ]

  #exercises((
    [
      Let $K$ be a number field and let $frak(a) subset.eq K$ be a nonzero fractional ideal of $cal(O)_K$. Equip $frak(a)$ with the canonical Hermitian metric $||x||_sigma = |sigma(x)|$ at each embedding $sigma : K -> bb(C)$, forming a Hermitian line bundle $overline(frak(a))$ over $op("Spec") cal(O)_K$. Compute $hat(op("deg"))(overline(frak(a)))$ in terms of the ideal norm $N(frak(a))$, and verify directly from Proposition 9.6 that the covolume of $frak(a)$ in the Minkowski embedding $K times.o_bb(Q) bb(R) arrow.hook bb(C)^([K : bb(Q)])$ is $N(frak(a)) |Delta_K|^(1 \/ 2)$.
    ],
    [
      Consider the rank-$3$ Euclidean lattice $overline(L) = bb(Z) e_1 + bb(Z) e_2 + bb(Z) e_3 subset.eq bb(R)^3$ generated by
      $ e_1 = (1, 0, 0), quad e_2 = (1 \/ 2, 2, 0), quad e_3 = (0, 1, 3) $
      with the standard Euclidean inner product on $bb(R)^3$. Compute $op("covol")(overline(L))$, $hat(op("deg"))(overline(L))$, $hat(mu)(overline(L))$, the Harder–Narasimhan filtration $0 = L_0 subset.neq L_1 subset.neq dots.c subset.neq L_k = L$, the slope list $op("slopeList")(overline(L))$, and the vertices of $op("hnPoly")(overline(L))$.
    ],
    [
      (_Sums and Orthogonal Direct Sums_, `Formalism.HN.HNSum`) Let $overline(L)$ be a Euclidean lattice.
      (a) Suppose $A_1, dots.c, A_m subset.eq L$ are nonzero sublattices satisfying $mu_min (overline(A)_i) >= theta$ for all $1 <= i <= m$. Using Theorem 9.13 (`DegSupermod`) or Theorem 9.23 (`SlopeIneq`), prove that $mu_min (overline(A_1 + dots.c + A_m)) >= theta$.
      (b) Suppose $A, B subset.eq L$ are nonzero sublattices that are mutually orthogonal: $chevron.l x, y chevron.r = 0$ for all $x in A$ and $y in B$. Prove that $hat(op("deg"))(overline(A + B)) = hat(op("deg"))(overline(A)) + hat(op("deg"))(overline(B))$, $mu_max (overline(A + B)) = max(mu_max (overline(A)), mu_max (overline(B)))$, and $mu_min (overline(A + B)) = min(mu_min (overline(A)), mu_min (overline(B)))$.
    ],
    [
      (_Duality of the Harder–Narasimhan Polygon_) Let $overline(L)$ be a Euclidean lattice of rank $r >= 1$ with Harder–Narasimhan filtration $0 = L_0 subset.neq L_1 subset.neq dots.c subset.neq L_k = L$ and slopes $mu_1 > mu_2 > dots.c > mu_k$. Using Proposition 9.10(3), prove that the Harder–Narasimhan filtration of the dual lattice $overline(L)^or$ is
      $ 0 = L_k^perp subset.neq L_(k-1)^perp subset.neq dots.c subset.neq L_1^perp subset.neq L_0^perp = L^or, $
      with slopes $-mu_k > -mu_(k-1) > dots.c > -mu_1$, and show that for every $0 <= m <= r$,
      $ op("hnPoly")(overline(L)^or, m) = op("hnPoly")(overline(L), r - m) - hat(op("deg"))(overline(L)). $
    ],
    [
      (_Tensor Products and Stability_) Let $overline(L)$ and $overline(M)$ be Euclidean lattices, and equip their tensor product $L times.o_bb(Z) M$ with the induced inner product $chevron.l x_1 times.o y_1, x_2 times.o y_2 chevron.r = chevron.l x_1, x_2 chevron.r dot.c chevron.l y_1, y_2 chevron.r$.
      (a) Prove that $hat(mu)(overline(L) times.o overline(M)) = hat(mu)(overline(L)) + hat(mu)(overline(M))$.
      (b) If $op("rk")(M) = 1$, deduce from Proposition 9.21 (`ShiftInvariance`) that $mu_max (overline(L) times.o overline(M)) = mu_max (overline(L)) + hat(mu)(overline(M))$ and $mu_min (overline(L) times.o overline(M)) = mu_min (overline(L)) + hat(mu)(overline(M))$.
      (c) (_Challenge_) Using the canonical identification $L times.o_bb(Z) M tilde.equiv op("Hom")_bb(Z) (L^or, M)$ and Bost's slope inequality (Theorem 9.23) together with the relation between the Hilbert–Schmidt norm and operator norm on $op("Hom")(L^(or)_bb(R), M_bb(R))$, prove that for any two nonzero Euclidean lattices $overline(L), overline(M)$ of ranks $r, s$,
      $ mu_max (overline(L) times.o overline(M)) <= mu_max (overline(L)) + mu_max (overline(M)) + 1 / 2 log min(r, s). $
    ],
    [
      (_Refining `MuMaxLeMin` via Hermite's Constant_) Recall that Hermite's constant $gamma_k$ is the supremum of $lambda_1 (overline(N))^2 \/ op("covol")(overline(N))^(2 \/ k)$ over all rank-$k$ Euclidean lattices $overline(N)$. Show that for any Euclidean lattice $overline(L)$ of rank $r$,
      $ mu_max (overline(L)) <= -log lambda_1 (overline(L)) + 1 / 2 max_(1 <= k <= r) log gamma_k. $
      Using Minkowski's bound $gamma_k <= 4 omega_k^(-2 \/ k)$ (where $omega_k = pi^(k \/ 2) \/ Gamma(k \/ 2 + 1)$ is the volume of the unit ball in $bb(R)^k$), compare this bound asymptotically with Lemma 9.15 as $r -> oo$.
    ],
    [
      (_Siegel's Lemma from Bost's Slope Inequality_) Let $A in op("Mat")_(m times n)(bb(Z))$ be an integer matrix with $1 <= m < n$, viewed as a linear map $phi : bb(Z)^n -> bb(Z)^m$ between standard Euclidean lattices. Suppose the operator norm of $A$ satisfies $||A||_(op("op")) <= C$ (with $C >= 1$). Set $K = ker(phi) subset.eq bb(Z)^n$.
      (a) Show that $hat(op("deg"))(overline(K)) >= -m log C$ by applying Proposition 9.8(2) and Corollary 9.22 to the induced injection $bb(Z)^n \/ K arrow.hook bb(Z)^m$.
      (b) Combine part (a) with Minkowski's first theorem (Lemma 9.15) to deduce the existence of a nonzero integer vector $x in ker(A)$ satisfying
      $ ||x|| <= sqrt(n - m) dot.c C^(m \/ (n - m)). $
      Compare this with the classical Bombieri–Vaaler version of Siegel's lemma.
    ],
    [
      (_Liouville's Inequality via Bost's Slope Inequality_) Let $alpha in bb(R)$ be an algebraic number of degree $d >= 2$ with minimal polynomial $P(X) = a_d X^d + dots.c + a_0 in bb(Z)[X]$ ($a_d > 0$). For a rational number $p \/ q$ ($q >= 1$, $gcd(p, q) = 1$), consider the evaluation map $phi : bb(Z) -> bb(Z)$ sending $1 |-> q^d P(p \/ q)$ equipped with suitable rescaled metrics, or the rank-$1$ lattice $cal(O)_K$ evaluated at $p - q alpha$. Use Theorem 9.23 to derive an explicit lower bound of the form $|alpha - p \/ q| >= c(alpha) q^(-d)$ for all $p \/ q != alpha$.
    ],
    [
      (_Arithmetic Hilbert–Samuel on $bb(P)^1_bb(Z)$_) Let $cal(X) = bb(P)^1_bb(Z)$ with homogeneous coordinates $[X_0 : X_1]$, and equip $cal(L) = cal(O)(1)$ with the Fubini–Study Hermitian metric $||s||_(op("FS"))([z_0 : z_1]) = |s(z_0, z_1)| \/ sqrt(|z_0|^2 + |z_1|^2)$.
      (a) Compute the first Chern form $c_1 (overline(cal(L)))$ on $bb(P)^1 (bb(C))$ and verify that $integral_(bb(P)^1 (bb(C))) c_1 (overline(cal(L))) = 1$.
      (b) Using the section $s = X_0$ and the inductive height formula from Section 9.4.1, prove that the top arithmetic self-intersection number is
      $ hat(c)_1 (overline(cal(L)))^2 = 1 / 2. $
      (c) For each $k >= 1$, compute the $L^2$-norms of the monomial basis $X_0^j X_1^(k-j)$ ($0 <= j <= k$) of $H^0(bb(P)^1_bb(Z), cal(O)(k))$ with respect to the Fubini–Study area form $mu = c_1 (overline(cal(L)))$, show that the monomials are pairwise orthogonal, and verify directly using Stirling's formula that
      $ hat(op("deg"))(H^0(bb(P)^1_bb(Z), cal(O)(k)), ||dot.c||_(L^2))
        &= 1 / 4 k^2 + O(k log k) \
        &= (hat(c)_1 (overline(cal(L)))^2) / (2!) k^2 + o(k^2), $
      confirming Theorem 9.27 explicitly!
    ],
  ))
]
