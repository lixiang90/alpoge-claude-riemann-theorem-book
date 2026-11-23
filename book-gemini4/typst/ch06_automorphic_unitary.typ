#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch06() = [
  #chapter(
    [Automorphic Forms on Totally Definite Unitary Groups and $op("GL")_n$],
    short-title: "Automorphic Forms on Unitary Groups",
    epigraph: "The theory of automorphic forms on definite unitary groups is the point at which harmonic analysis turns into finite-dimensional linear algebra, without losing a single drop of arithmetic depth.",
    epigraph-source: "After Clozel and Labesse",
    overview: [
      In the previous chapters we developed the analytic machinery of $L$-functions, explicit formulas, and the spectral theory of automorphic forms on classical spaces. To carry out the arithmetic half of the Alpöge–Claude–Riemann proof, we now pivot to a remarkably concrete class of reductive groups: _totally definite unitary groups_ $U(X)$ associated to Hermitian spaces over CM fields. Because $U(X)$ is compact at every archimedean place, its adelic double coset quotients are finite sets, its spaces of algebraic automorphic forms are finite-dimensional vector spaces with no continuous spectrum, and its Petersson inner product is a finite weighted sum. Yet through quadratic base change $op("BC"): U(n) -> op("GL")_n / K$, these finite-dimensional spaces transmit their Hecke eigenvalues directly into the cuspidal and isobaric spectrum of $op("GL")_n (bb(A)_K)$. This chapter develops both sides of that bridge: the arithmetic of Hermitian spaces and definite unitary groups (Sections 6.1–6.2), the local and global representation theory of $op("GL")_n$ via Flath's theorem, the Bernstein–Zelevinsky classification, and Shalika multiplicity one (Section 6.3), and the global bridge of Clozel purity, unitary base change, and Caraiani's local-global compatibility for Galois representations (Section 6.4), followed by a map to the Lean 4 formalization (Section 6.5).
    ],
    label-name: "ch:automorphic-unitary",
  )

  // ==========================================================================
  // Section 6.1
  // ==========================================================================
  == CM Fields, Hermitian Spaces, and Unitary Groups

  The arithmetic geometry of unitary groups begins with a quadratic extension of number fields possessing a canonical involution that behaves like complex conjugation at every archimedean place.

  #definition(title: "CM Field")[
    A number field $K$ is called a _CM field_ if it is a totally imaginary quadratic extension of a totally real number field $K_0$. Equivalently, $[K : K_0] = 2$, every embedding $K_0 arrow.hook bb(C)$ has image contained in $bb(R)$, and no embedding $K arrow.hook bb(C)$ has image contained in $bb(R)$. The unique nontrivial element of $op("Gal")(K / K_0)$ is denoted $c$ (or $x |-> overline(x)$) and is called _complex conjugation_; it commutes with every embedding $iota : K arrow.hook bb(C)$ in the sense that $iota(c(x)) = overline(iota(x))$.
  ]

  The simplest CM fields are the imaginary quadratic fields $K = bb(Q)(sqrt(-d))$ ($d > 0$) over $K_0 = bb(Q)$, and the cyclotomic fields $K = bb(Q)(zeta_m)$ ($m >= 3$) over their maximal totally real subfields $K_0 = bb(Q)(zeta_m + zeta_m^(-1))$. More generally, if $K_0$ is any totally real field and $E$ is an imaginary quadratic field, the compositum $K = K_0 E$ is a CM field with maximal totally real subfield $K_0$.

  Let $Sigma_(K_0)$ denote the set of places of $K_0$, partitioned into archimedean places $v | oo$ and finite places $v < oo$. For each $v in Sigma_(K_0)$, the algebra $K_v = K times.o_(K_0) K_(0,v)$ falls into one of four regimes:
  1. _Archimedean_ ($v | oo$): $K_(0,v) tilde.equiv bb(R)$ and $K_v tilde.equiv bb(C)$, with $c$ acting as ordinary complex conjugation. Every infinite place of $K_0$ is nonsplit in $K$.
  2. _Finite split_ ($v = w w^c$): $K_v tilde.equiv K_w times K_(w^c) tilde.equiv K_(0,v) times K_(0,v)$, with $c$ acting by swapping the two coordinates: $c(x, y) = (y, x)$.
  3. _Finite inert_: $K_v / K_(0,v)$ is the unique unramified quadratic extension of the nonarchimedean local field $K_(0,v)$, with $c$ generating $op("Gal")(K_v / K_(0,v))$.
  4. _Finite ramified_: $K_v / K_(0,v)$ is a ramified quadratic extension of $K_(0,v)$, with $c$ generating $op("Gal")(K_v / K_(0,v))$.

  By local class field theory, each place $v in Sigma_(K_0)$ carries a quadratic character
  $ omega_(K_v / K_(0,v)) : K_(0,v)^times -> {plus.minus 1} $
  whose kernel is the norm subgroup $op("Nm")_(K_v / K_(0,v))(K_v^times)$. When $v$ splits in $K$, $omega_(K_v / K_(0,v)) = 1$ is trivial; when $v | oo$, $omega_(K_v / K_(0,v)) = op("sgn")_v$ is the sign character on $bb(R)^times$; when $v$ is inert, $omega_(K_v / K_(0,v))(x) = (-1)^(v(x))$. By Artin reciprocity, the product of all local characters is trivial on global elements:
  $ product_(v in Sigma_(K_0)) omega_(K_v / K_(0,v))(a) = 1 quad forall a in K_0^times. $

  === Hermitian Spaces and Unitary Groups

  #definition(title: "Hermitian Space and Unitary Group")[
    Let $K / K_0$ be a CM extension. A _Hermitian space_ of dimension $n$ over $K / K_0$ is a pair $(V, h)$ consisting of an $n$-dimensional $K$-vector space $V$ and a map $h : V times V -> K$ such that:
    1. $h$ is $K$-linear in the first variable: $h(alpha x + beta y, z) = alpha h(x, z) + beta h(y, z)$ for all $alpha, beta in K$ and $x, y, z in V$;
    2. $h$ is _Hermitian symmetric_: $h(y, x) = c(h(x, y))$ for all $x, y in V$ (hence $c$-semilinear in the second variable);
    3. $h$ is _nondegenerate_: if $h(x, y) = 0$ for all $y in V$, then $x = 0$.

    The _unitary group_ $U(V) = U(V, h)$ is the algebraic group over $K_0$ whose functor of points on any commutative $K_0$-algebra $R$ is
    $ U(V)(R) = \{ & g in op("GL")_(K times.o_(K_0) R)(V times.o_(K_0) R) : \
      & h(g x, g y) = h(x, y) quad forall x, y in V times.o_(K_0) R \}. $
  ]

  Choosing a $K$-basis $e_1, dots.c, e_n$ of $V$, the Hermitian form is represented by an invertible Hermitian matrix $H = (h(e_i, e_j)) in op("GL")_n (K)$ satisfying $H^* := c(H^t) = H$. A change of basis $P in op("GL")_n (K)$ replaces $H$ by $P H P^*$, whose determinant changes by $det(P) c(det(P)) = op("Nm")_(K / K_0)(det P)$. Notice also that $c(det H) = det(H^*) = det(H)$, so $det(H) in K_0^times$. Thus the _determinant_ (or _discriminant_)
  $ det(V, h) := det(H) in K_0^times / op("Nm")_(K / K_0)(K^times) $
  is a well-defined isometry invariant of $(V, h)$. In coordinates, $U(V)(R) = { g in op("GL")_n (K times.o_(K_0) R) : g H g^* = H }$.

  Because $U(V)$ becomes isomorphic to $op("GL")_n$ after base change from $K_0$ to $K$, it is a connected reductive algebraic group over $K_0$ of dimension $n^2$ and rank $n$; it is an outer form of $op("GL")_n$ whenever $n >= 2$. Let us examine its group of local points $U(V)(K_(0,v))$ at every place $v$ of $K_0$.

  #proposition(title: "Local Structure of Unitary Groups")[
    Let $(V, h)$ be an $n$-dimensional Hermitian space over $K / K_0$, and let $v in Sigma_(K_0)$.
    1. _Archimedean place_ ($v | oo$): By Sylvester's law of inertia, there exist unique nonnegative integers $p_v, q_v$ with $p_v + q_v = n$ such that $(V_v, h_v)$ is isometric to $bb(C)^n$ with diagonal form $op("diag")(1, dots.c, 1, -1, dots.c, -1)$ ($p_v$ copies of $+1$ and $q_v$ copies of $-1$). The pair $(p_v, q_v)$ is the _signature_ of $(V, h)$ at $v$, and
       $ U(V)(K_(0,v)) tilde.equiv U(p_v, q_v). $
       In particular, $U(V)(K_(0,v))$ is compact if and only if $(p_v, q_v) = (n, 0)$ or $(0, n)$, in which case $U(V)(K_(0,v)) tilde.equiv U(n)$.
    2. _Finite split place_ ($v = w w^c$): Choosing one of the two places $w | v$ yields a canonical isomorphism
       $ U(V)(K_(0,v)) tilde.equiv op("GL")_n (K_w) tilde.equiv op("GL")_n (K_(0,v)). $
       Replacing $w$ by $w^c$ composes this isomorphism with the outer automorphism $g |-> H (g^t)^(-1) H^(-1)$ (which is conjugate to $g |-> (g^t)^(-1)$).
    3. _Finite nonsplit place_ ($v < oo$ inert or ramified): The isometry class of $(V_v, h_v)$ is completely determined by $n$ and the local discriminant $det(V_v, h_v) in K_(0,v)^times / op("Nm")_(K_v / K_(0,v))(K_v^times) tilde.equiv {plus.minus 1}$. Thus there are precisely two isometry classes of $n$-dimensional Hermitian spaces over $K_v / K_(0,v)$.
  ]

  #proof[
    Part (1) is standard linear algebra over $bb(C)$: diagonalizing the Hermitian matrix $H_v$ by a unitary change of basis and rescaling each eigenvector by $|lambda_i|^(-1/2)$ puts $H_v$ in the form $op("diag")(I_(p_v), -I_(q_v))$. The group $U(p_v, q_v)$ is compact precisely when the quadratic form $x |-> h_v (x, x)$ is definite.

    For part (2), write $K_v = K_w times K_(w^c)$ with $c(a, b) = (b, a)$. Accordingly, $V_v = V_w plus.o V_(w^c)$ and any $g in op("GL")_(K_v)(V_v)$ decomposes as $g = (g_1, g_2)$ with $g_1 in op("GL")(V_w)$ and $g_2 in op("GL")(V_(w^c))$. The Hermitian form $h_v$ induces a nondegenerate $K_(0,v)$-bilinear pairing $B : V_w times V_(w^c) -> K_(0,v)$ by taking the first component of $h_v (x, y)$ for $x in V_w, y in V_(w^c)$. The condition $h_v (g x, g y) = h_v (x, y)$ is equivalent to $B(g_1 x, g_2 y) = B(x, y)$ for all $x, y$, which determines $g_2$ uniquely as the transpose-inverse of $g_1$ with respect to $B$. Hence the projection $(g_1, g_2) |-> g_1$ is an isomorphism $U(V)(K_(0,v)) ->^tilde op("GL")(V_w) tilde.equiv op("GL")_n (K_(0,v))$.

    For part (3), by Gram–Schmidt orthogonalization over $K_v$ (valid since $op("char")(K_v) != 2$), $(V_v, h_v)$ has an orthogonal basis with diagonal entries $a_1, dots.c, a_n in K_(0,v)^times$. Every $2$-dimensional Hermitian space with $a_1, a_2 in K_(0,v)^times$ represents all elements of $K_(0,v)^times$? Let us be precise: an element $b in K_(0,v)^times$ is represented by $a_1 x overline(x) + a_2 y overline(y)$ if and only if the quaternion algebra $(-a_1 a_2, b)_(K_(0,v))$ or rather the binary norm form represents $b$. Since $K_(0,v)$ is a nonarchimedean local field, every ternary (in fact, every $3$-variable) Hermitian form is isotropic, and every binary Hermitian form of discriminant $-1 in K_(0,v)^times / op("Nm")(K_v^times)$ is a hyperbolic plane $bb(H)$ representing all of $K_(0,v)$. Inductively, $(V_v, h_v)$ splits off hyperbolic planes until only a $1$-dimensional or $2$-dimensional anisotropic kernel remains; in fact, a $2$-dimensional Hermitian space over $K_v / K_(0,v)$ is already uniquely determined by its discriminant, because $x |-> x overline(x)$ has index $2$ in $K_(0,v)^times$ and the sum of two cosets of a subgroup of index $2$ in a local field covers $K_(0,v)^times$. By Witt cancellation, two nondegenerate Hermitian spaces of the same dimension over $K_v / K_(0,v)$ are isometric if and only if they have the same discriminant in $K_(0,v)^times / op("Nm")(K_v^times) tilde.equiv bb(Z) / 2 bb(Z)$.
  ]

  #definition(title: "Totally Definite Hermitian Space and Unitary Group")[
    A Hermitian space $(X, h)$ of dimension $n$ over a CM extension $K / K_0$ is called _totally definite_ (or _totally positive definite_) if its signature at every archimedean place $v | oo$ of $K_0$ is $(n, 0)$ (so $h_v (x, x) > 0$ for all nonzero $x in X_v$). The associated algebraic group $U(X)$ over $K_0$ is called a _totally definite unitary group_. Its group of real points is the compact Lie group
    $ U(X)(K_(0, oo)) = product_(v | oo) U(X)(K_(0,v)) tilde.equiv product_(v | oo) U(n). $
  ]

  At a finite nonsplit place $v$, the two local isometry classes of $n$-dimensional Hermitian spaces correspond to two local unitary groups. When $n$ is odd, scaling the Hermitian form $h$ by a non-norm $u in K_(0,v)^times without op("Nm")(K_v^times)$ changes $det(h)$ by $u^n equiv u mod op("Nm")(K_v^times)$ without changing the unitary group $U(V_v, u h) = U(V_v, h)$; hence for odd $n$ there is only _one_ isomorphism class of unitary groups over $K_(0,v)$, and it is always quasi-split! When $n = 2m$ is even, scaling $h$ by $u$ multiplies $det(h)$ by $u^(2m) = (u^m)^2 in op("Nm")(K_v^times)$, leaving the discriminant invariant; the two isometry classes yield two non-isomorphic local unitary groups: the _quasi-split_ group $U(V_v^+)$ (when $(-1)^m det(V_v) in op("Nm")(K_v^times)$, i.e., $V_v tilde.equiv bb(H)^m$ is a sum of $m$ hyperbolic planes) and the _non-quasi-split_ inner form $U(V_v^-)$ (when $(-1)^m det(V_v) in.not op("Nm")(K_v^times)$, which has Witt index $m - 1$).

  === Landherr's Theorem and the Hasse Principle

  To construct totally definite unitary groups with prescribed local behavior—for instance, quasi-split at all finite nonsplit places, or ramified at a controlled set of places matching a given theta correspondence—we need the local-global classification of Hermitian spaces over number fields, proved by W. Landherr in 1936.

  For a local Hermitian space $(V_v, h_v)$ of dimension $n$ over $K_v / K_(0,v)$, define its _local Hasse–Landherr invariant_ $epsilon_v (V_v, h_v) in {plus.minus 1}$ by
  $ epsilon_v (V_v, h_v) := omega_(K_v / K_(0,v))((-1)^(n(n-1)/2) det(V_v, h_v)). $
  Let us evaluate this sign in each local regime:
  - If $v$ splits in $K$, then $omega_(K_v / K_(0,v)) = 1$, so $epsilon_v (V_v, h_v) = 1$.
  - If $v | oo$ has signature $(p_v, q_v)$, then $det(V_v, h_v) = (-1)^(q_v)$ up to positive reals, so
    $ epsilon_v (V_v, h_v) = (-1)^(n(n-1)/2 + q_v). $
    In particular, for a totally positive definite space ($q_v = 0$ for all $v | oo$), we have $epsilon_v (V_v, h_v) = (-1)^(n(n-1)/2)$ at each of the $d = [K_0 : bb(Q)]$ infinite places.
  - If $v < oo$ is inert and $(V_v, h_v)$ contains a self-dual $cal(O)_(K_v)$-lattice, then $det(V_v, h_v) in cal(O)_(K_(0,v))^times subset.eq op("Nm")(K_v^times)$, so $epsilon_v (V_v, h_v) = 1$.

  #theorem(title: "Landherr's Theorem and the Hermitian Hasse Principle")[
    Let $K / K_0$ be a quadratic extension of number fields, and let $n >= 1$.
    1. _(Hermitian Hasse Principle)_ Two $n$-dimensional nondegenerate Hermitian spaces $(V, h)$ and $(V', h')$ over $K / K_0$ are globally isometric if and only if $(V_v, h_v) tilde.equiv (V'_v, h'_v)$ for every place $v in Sigma_(K_0)$.
    2. _(Landherr's Existence Theorem)_ Let ${(V_v, h_v)}_(v in Sigma_(K_0))$ be a collection of $n$-dimensional local Hermitian spaces over $K_v / K_(0,v)$ such that $epsilon_v (V_v, h_v) = 1$ for all but finitely many places $v$. Then there exists a global Hermitian space $(V, h)$ over $K / K_0$ with $(V times.o_(K_0) K_(0,v), h_v) tilde.equiv (V_v, h_v)$ for all $v in Sigma_(K_0)$ if and only if
       $ product_(v in Sigma_(K_0)) epsilon_v (V_v, h_v) = 1. $
  ]

  #proof[
    We outline the classical reduction to the Hasse norm theorem and the Hasse–Minkowski theorem for quadratic forms. For (1), observe first that if $n = 1$, two forms $a x overline(y)$ and $b x overline(y)$ ($a, b in K_0^times$) are isometric if and only if $a b^(-1) in op("Nm")_(K / K_0)(K^times)$. By the Hasse norm theorem for the cyclic (quadratic) extension $K / K_0$, an element of $K_0^times$ is a global norm if and only if it is a local norm at every place $v in Sigma_(K_0)$, establishing the $n = 1$ case.

    For $n >= 2$, we argue by induction on $n$ using the _trace quadratic form_ $q_h (x) := h(x, x)$ on $V$, viewed as a $2n$-dimensional quadratic space over $K_0$. If $(V, h)$ and $(V', h')$ are locally isometric at all places $v$, then $q_h$ and $q_(h')$ are locally isometric quadratic forms over $K_0$, hence globally isometric by the Hasse–Minkowski theorem. In particular, pick any nonzero $a in K_0^times$ represented by $q_h$ (and hence by $q_(h')$). Then there exist $x in V$ and $x' in V'$ with $h(x, x) = a = h'(x', x')$. Decomposing $V = K x plus.o (K x)^perp$ and $V' = K x' plus.o (K x')^perp$, Witt cancellation for local Hermitian spaces implies that $(K x)^perp$ and $(K x')^perp$ are locally isometric at every place $v$. By the induction hypothesis, they are globally isometric, whence $(V, h) tilde.equiv (V', h')$.

    For (2), necessity of the product formula follows immediately from Artin reciprocity: if $(V, h)$ exists globally with determinant $D in K_0^times$, then
    $ product_v epsilon_v (V_v, h_v) = product_v omega_(K_v / K_(0,v))((-1)^(n(n-1)/2) D) = 1. $
    Conversely, given local spaces ${(V_v, h_v)}_v$ satisfying $product_v epsilon_v (V_v, h_v) = 1$, choose a finite set $S$ of places containing all archimedean places, all places ramified in $K / K_0$, and all places where $epsilon_v (V_v, h_v) = -1$. By weak approximation and Dirichlet's theorem on primes in arithmetic progressions (or Chebotarev's density theorem applied to $K / K_0$), one constructs a diagonal Hermitian form $h = op("diag")(a_1, dots.c, a_n)$ matching the archimedean signatures $(p_v, q_v)$ at all $v | oo$ and having determinant $D = a_1 dots.c a_n$ whose local norm class $omega_(K_v / K_(0,v))((-1)^(n(n-1)/2) D)$ agrees with $epsilon_v (V_v, h_v)$ at every place $v$. Since local Hermitian spaces are completely classified by dimension, signature (at $v | oo$), and $epsilon_v$ (at $v < oo$), the resulting global space $(V, h)$ realizes every $(V_v, h_v)$.
  ]

  #corollary(title: "Existence of Totally Definite Unitary Groups")[
    Let $K / K_0$ be a CM extension with $d = [K_0 : bb(Q)]$, and let $n >= 1$.
    1. There exists a totally definite Hermitian space $(X, h)$ of dimension $n$ over $K / K_0$ whose unitary group $U(X)$ is quasi-split at every finite place $v$ of $K_0$ if and only if either $n$ is odd, or $n$ is even and $d n / 2$ is even (equivalently, $(-1)^(d n(n-1)/2) = 1$).
    2. In all cases—even when $n equiv 2 mod 4$ and $d$ is odd—there exists a totally definite Hermitian space $(X, h)$ of dimension $n$ over $K / K_0$ that is quasi-split at all finite places outside a single chosen finite inert place $v_0$ of $K_0$.
  ]

  #proof[
    For a totally positive definite space, $q_v = 0$ at all $d$ infinite places, so $product_(v | oo) epsilon_v = (-1)^(d n(n-1)/2)$. At a finite nonsplit place $v$, the quasi-split unitary group of even dimension $n = 2m$ corresponds to $epsilon_v = omega_(K_v / K_(0,v))((-1)^(m(2m-1)) dot.c (-1)^m) = omega_(K_v / K_(0,v))(1) = 1$. Hence if $n$ is even, being quasi-split at all finite places forces $product_(v < oo) epsilon_v = 1$, which by Landherr's theorem is compatible with total definiteness if and only if $(-1)^(d n(n-1)/2) = 1$. If instead this sign is $-1$, choosing a single finite inert place $v_0$ and setting $epsilon_(v_0) = -1$ (the non-quasi-split inner form at $v_0$) restores the product to $+1$. For odd $n$, every local unitary group at a finite place is quasi-split regardless of $epsilon_v$, so one can always choose a single finite inert place $v_0$ to absorb any sign $(-1)^(d n(n-1)/2)$ without losing quasi-splitness at $v_0$.
  ]

  #remark[
    In the Lean 4 formalization of the Alpöge–Claude–Riemann theorem, Landherr's theorem and the Hermitian Hasse principle are formalized as `HermitianHassePrinciple` (in `Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds` and `Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HermitianHassePrinciple`) and `LandherrAndLandherrSt` (in `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt`). They guarantee that the global Hermitian spaces required to stage the chained theta lifts—definite at infinity and locally prescribed at the bad primes—actually exist over $K / K_0$.
  ]

  #example(title: "Totally Definite Unitary Groups over Imaginary Quadratic Fields")[
    Take $K_0 = bb(Q)$ ($d = 1$) and $K = bb(Q)(i)$, with $h(x, y) = sum_(j=1)^n x_j overline(y_j)$ on $X = K^n$. Then $(X, h)$ is totally positive definite of determinant $1$. For $n = 1$, $U(X)(bb(Q)) = { z in bb(Q)(i)^times : z overline(z) = 1 }$, and $U(X)(bb(R)) = U(1) = S^1$. For $n = 2$, $epsilon_oo = (-1)^1 = -1$, so $U(X)$ cannot be quasi-split at every finite prime! Indeed, $det(h) = 1$ has $omega_(bb(Q)_p (i) / bb(Q)_p)(-1) = (-1)^((p-1)/2)$ for odd primes $p$; at $p = 2$, $2$ ramifies in $bb(Q)(i)$ and $-1 in.not op("Nm")(bb(Q)_2 (i)^times)$ since $x^2 + y^2 equiv -1 mod 4$ has no solution, so $epsilon_2 = -1$ while $epsilon_p = 1$ for all odd $p$. Thus $U(X)$ is non-quasi-split at the single finite prime $p = 2$ and quasi-split at all odd primes, in exact agreement with Landherr's product formula $epsilon_oo epsilon_2 = (-1)(-1) = 1$. Moreover, $op("SU")(X)$ is isomorphic to the norm-$1$ group of the Hamilton quaternion algebra $B_(2, oo)$ ramified at ${2, oo}$.
  ]

  // ==========================================================================
  // Section 6.2
  // ==========================================================================
  == Adelic Automorphic Forms on Totally Definite Unitary Groups

  Let $G = U(X)$ be a totally definite unitary group of rank $n$ over a totally real field $K_0$ (associated to a CM extension $K / K_0$). Write $bb(A)_(K_0) = K_(0, oo) times bb(A)_(K_0, f)$ for the adele ring of $K_0$, where $K_(0, oo) = K_0 times.o_bb(Q) bb(R) tilde.equiv bb(R)^d$ and $bb(A)_(K_0, f)$ is the ring of finite adeles. Accordingly, the adelic group splits as
  $ G(bb(A)_(K_0)) = G(K_(0, oo)) times G(bb(A)_(K_0, f)), $
  where $G(K_(0, oo)) tilde.equiv product_(v | oo) U(n)$ is a _compact_ Lie group, and $G(bb(A)_(K_0, f))$ is a totally disconnected locally compact topological group (the restricted direct product $product'_v G(K_(0,v))$ with respect to the open compact subgroups $G(cal(O)_(K_(0,v)))$ defined by a choice of $cal(O)_K$-lattice $Lambda subset.eq X$).

  The global points $G(K_0)$ embed diagonally into $G(bb(A)_(K_0))$ as a discrete subgroup. The single most decisive geometric property of totally definite unitary groups is that their adelic quotients are _compact_, and their finite-adelic double coset spaces are _finite_.

  #theorem(title: "Finiteness of Double Cosets for Totally Definite Unitary Groups")[
    Let $G = U(X)$ be a totally definite unitary group over $K_0$, and let $K_f subset.eq G(bb(A)_(K_0, f))$ be any open compact subgroup.
    1. The double coset space
       $ X(K_f) := G(K_0) backslash G(bb(A)_(K_0, f)) / K_f $
       is a _finite set_.
    2. For every $g_f in G(bb(A)_(K_0, f))$, the arithmetic stabilizer
       $ Gamma_(g_f) := G(K_0) inter g_f K_f g_f^(-1) $
       (intersection taken inside $G(bb(A)_(K_0, f))$) is a _finite group_.
    3. There exists an open normal subgroup $K'_f subset.eq K_f$ (for instance, any _neat_ open compact subgroup, such as a principal congruence subgroup of sufficiently deep level) such that $Gamma_(g_f) = {1}$ for all $g_f in G(bb(A)_(K_0, f))$.
  ]

  #proof[
    First, since $G$ is a reductive algebraic group over $K_0$ that is anisotropic over $K_0$ (in fact, $G(K_(0, oo))$ is compact, so $G$ contains no nontrivial $K_0$-split torus, and its center $Z_G tilde.equiv U(1)_(K / K_0)$ is also anisotropic over $K_0$), Borel's compactness theorem (Borel–Harish-Chandra) asserts that the adelic quotient $G(K_0) backslash G(bb(A)_(K_0))$ is compact.

    Now consider the open subgroup $U := G(K_(0, oo)) times K_f subset.eq G(bb(A)_(K_0))$. The double coset space $G(K_0) backslash G(bb(A)_(K_0)) / U$ is naturally in bijection with $X(K_f) = G(K_0) backslash G(bb(A)_(K_0, f)) / K_f$. Since the orbits $G(K_0) g U$ form a partition of the compact space $G(K_0) backslash G(bb(A)_(K_0))$ into pairwise disjoint open subsets, there can be only finitely many of them. Thus $X(K_f)$ is finite, proving (1).

    For (2), embed $Gamma_(g_f)$ diagonally into $G(bb(A)_(K_0))$. Its image lies in the intersection
    $ G(K_0) inter (G(K_(0, oo)) times g_f K_f g_f^(-1)). $
    Here $G(K_0)$ is discrete in $G(bb(A)_(K_0))$, while $G(K_(0, oo)) times g_f K_f g_f^(-1)$ is compact (because _both_ the archimedean factor $G(K_(0, oo))$ and the finite factor $g_f K_f g_f^(-1)$ are compact!). The intersection of a discrete subset and a compact subset in a Hausdorff topological group is finite.

    For (3), let $g_1, dots.c, g_h in G(bb(A)_(K_0, f))$ be a complete set of representatives for the finite set $X(K_f)$. The union $union.big_(i=1)^h (Gamma_(g_i) without {1})$ is a finite set of nontrivial elements of $G(K_0)$. Since $G(bb(A)_(K_0, f))$ is Hausdorff and has a neighborhood basis of the identity consisting of open compact subgroups, we may choose an open normal subgroup $K'_f subset.eq K_f$ small enough that $g_i K'_f g_i^(-1)$ avoids every nontrivial element of $Gamma_(g_i)$ for all $1 <= i <= h$. For any $g_f = gamma g_i k_f$ ($gamma in G(K_0), k_f in K_f$), normality of $K'_f$ in $K_f$ gives
    $ G(K_0) inter g_f K'_f g_f^(-1) = gamma (G(K_0) inter g_i K'_f g_i^(-1)) gamma^(-1) = {1}. $
  ]

  #insight-box(title: "Automorphic Forms Without Analysis")[
    Compare $X(K_f)$ for a totally definite unitary group with the modular curve $Y_0 (N) = Gamma_0 (N) backslash frak(H)$ for $op("GL")_2 (bb(Q))$. On $op("GL")_2 (bb(Q))$, the archimedean group $op("GL")_2 (bb(R))$ is noncompact, $Y_0 (N)$ is a noncompact Riemann surface with cusps, automorphic forms satisfy differential equations (holomorphy or Laplace eigenfunction equations) and moderate growth conditions, and $L^2$ has both a cuspidal spectrum and a continuous spectrum of Eisenstein series.

    On a totally definite unitary group $U(X)$, _every single analytic subtlety disappears_:
    - There are no cusps and no proper parabolic subgroups over $K_0$, so every automorphic form is automatically "cuspidal" in the sense that $L^2(G(K_0) backslash G(bb(A)_(K_0)))$ decomposes discretely with finite multiplicities.
    - The double coset space $X(K_f)$ is a finite set of points—a "$0$-dimensional Shimura variety."
    - Automorphic forms of fixed weight and level form a finite-dimensional vector space, Hecke operators are finite matrices, and the Petersson inner product is a finite sum.
    Yet, as we will see in Section 6.4, the Hecke eigenvalues occurring in these finite-dimensional spaces are rich enough to capture the arithmetic of cohomological automorphic representations of $op("GL")_n (bb(A)_K)$!
  ]

  === Algebraic Automorphic Forms of Weight $lambda$

  By the theorem of the highest weight for the compact connected Lie group $U(n)$, the irreducible finite-dimensional continuous (equivalently, algebraic) complex representations of $U(n)$ are parametrized by _dominant weights_
  $ bb(Z)^n_+ := { a = (a_1, a_2, dots.c, a_n) in bb(Z)^n : a_1 >= a_2 >= dots.c >= a_n }. $
  For each $a in bb(Z)^n_+$, let $W_a$ denote the irreducible algebraic representation of $U(n)$ of highest weight $a$ (with respect to the standard diagonal maximal torus $T tilde.equiv U(1)^n$ and upper-triangular Borel subgroup of $op("GL")_n (bb(C))$). For example:
  - $a = (0, dots.c, 0)$ gives the trivial representation $bb(C)$;
  - $a = (1, 0, dots.c, 0)$ gives the standard $n$-dimensional representation $bb(C)^n$;
  - $a = (k, 0, dots.c, 0)$ ($k >= 0$) gives the symmetric power $op("Sym")^k (bb(C)^n)$;
  - $a = (1, dots.c, 1) = (1^n)$ gives the $1$-dimensional determinant representation $det$.

  Its dimension is given by the Weyl dimension formula:
  $ dim_bb(C) W_a = product_(1 <= i < j <= n) (a_i - a_j + j - i) / (j - i), $
  and its contragredient (dual) representation is $W_a^or tilde.equiv W_(a^or)$, where $a^or = (-a_n, -a_(n-1), dots.c, -a_1)$.

  For the product group $G(K_(0, oo)) tilde.equiv product_(v | oo) U(n)$, a dominant weight is a tuple $lambda = (lambda_v)_(v | oo) in (bb(Z)^n_+)^(op("Hom")(K_0, bb(R)))$, and the corresponding irreducible representation is the external tensor product
  $ W_lambda := times.o.big_(v | oo) W_(lambda_v). $
  We denote the action of $g_oo in G(K_(0, oo))$ on $W_lambda$ by $rho_lambda (g_oo)$, and we equip $W_lambda$ with a $G(K_(0, oo))$-invariant positive-definite Hermitian inner product $chevron.l dot.c, dot.c chevron.r_(W_lambda)$ (unique up to positive scalar by Schur's lemma).

  #definition(title: "Algebraic Automorphic Forms on Totally Definite Unitary Groups")[
    Let $lambda$ be a dominant weight for $G(K_(0, oo))$ and $K_f subset.eq G(bb(A)_(K_0, f))$ an open compact subgroup. The space of _algebraic automorphic forms of weight $lambda$ and level $K_f$_ on $G = U(X)$ is
    $ cal(A)_lambda (G, K_f) := \{ & f : G(bb(A)_(K_0, f)) -> W_lambda bar.v f(gamma g_f k_f) = rho_lambda (gamma_oo) f(g_f) \
      & quad forall gamma in G(K_0), g_f in G(bb(A)_(K_0, f)), k_f in K_f \}, $
    where $gamma_oo$ denotes the image of $gamma in G(K_0)$ in $G(K_(0, oo))$.

    Passing to the direct limit over all open compact subgroups $K_f$ gives the space of _all algebraic automorphic forms of weight $lambda$_:
    $ cal(A)_lambda (G) := lim_(-> K_f) cal(A)_lambda (G, K_f) = union.big_(K_f) cal(A)_lambda (G, K_f), $
    which is a smooth representation of $G(bb(A)_(K_0, f))$ under right translation: $(g dot.c f)(x) = f(x g)$.
  ]

  Let us check the equivalence with the classical adelic definition of automorphic forms as scalar-valued functions on $G(K_0) backslash G(bb(A)_(K_0))$. Given $f in cal(A)_lambda (G, K_f)$ and a functional $ell in W_lambda^or$, the scalar function
  $ phi_(f, ell)(g_oo, g_f) := ell(rho_lambda (g_oo)^(-1) f(g_f)) $
  satisfies $phi_(f, ell)(gamma g_oo, gamma g_f k_f) = ell(rho_lambda (g_oo)^(-1) rho_lambda (gamma_oo)^(-1) rho_lambda (gamma_oo) f(g_f)) = phi_(f, ell)(g_oo, g_f)$. Thus $phi_(f, ell)$ is a smooth function on $G(K_0) backslash G(bb(A)_(K_0)) / K_f$, and as $ell$ varies over $W_lambda^or$, the map $ell |-> phi_(f, ell)$ identifies
  $ cal(A)_lambda (G, K_f) tilde.equiv op("Hom")_(G(K_(0, oo)))(W_lambda^or, C^oo (G(K_0) backslash G(bb(A)_(K_0)) / K_f)). $

  #proposition(title: "Explicit Finite-Dimensional Decomposition")[
    Let ${g_1, dots.c, g_h} subset.eq G(bb(A)_(K_0, f))$ be a complete set of representatives for the finite double coset space $X(K_f) = G(K_0) backslash G(bb(A)_(K_0, f)) / K_f$. Evaluation at $g_1, dots.c, g_h$ induces an isomorphism of complex vector spaces
    $ cal(A)_lambda (G, K_f) ->^tilde plus.o.big_(i=1)^h W_lambda^(Gamma_(g_i)), quad f |-> (f(g_1), dots.c, f(g_h)), $
    where $W_lambda^(Gamma_(g_i)) = { w in W_lambda : rho_lambda (gamma_oo) w = w text(" for all ") gamma in Gamma_(g_i) }$. In particular:
    1. $dim_bb(C) cal(A)_lambda (G, K_f) = sum_(i=1)^h dim_bb(C) W_lambda^(Gamma_(g_i)) < oo$;
    2. If $K_f$ is neat (so $Gamma_(g_i) = {1}$ for all $i$), then $dim_bb(C) cal(A)_lambda (G, K_f) = |X(K_f)| dot.c dim_bb(C) W_lambda$;
    3. The representation $cal(A)_lambda (G)$ of $G(bb(A)_(K_0, f))$ is _admissible_ (since $cal(A)_lambda (G)^(K_f) = cal(A)_lambda (G, K_f)$ is finite-dimensional for every open compact $K_f$).
  ]

  #proof[
    For any $f in cal(A)_lambda (G, K_f)$ and $gamma in Gamma_(g_i) = G(K_0) inter g_i K_f g_i^(-1)$, write $gamma = g_i k g_i^(-1)$ with $k in K_f$. Then $rho_lambda (gamma_oo) f(g_i) = f(gamma g_i) = f(g_i k) = f(g_i)$, so $f(g_i) in W_lambda^(Gamma_(g_i))$. Conversely, given any tuple $(w_1, dots.c, w_h) in plus.o.big_(i=1)^h W_lambda^(Gamma_(g_i))$, any element of $G(bb(A)_(K_0, f))$ can be written as $g = gamma g_i k$ with a unique index $i$, and setting $f(gamma g_i k) := rho_lambda (gamma_oo) w_i$ is well-defined precisely because if $gamma g_i k = gamma' g_i k'$, then $(gamma')^(-1) gamma = g_i k' k^(-1) g_i^(-1) in Gamma_(g_i)$ fixes $w_i$. The remaining statements follow immediately from Theorem 6.9.
  ]

  === Petersson Inner Product and Semisimplicity

  Because $X(K_f)$ is finite and every stabilizer $Gamma_(g_i)$ is finite, the Petersson inner product on $cal(A)_lambda (G, K_f)$ is simply a finite weighted sum—no convergence checks are required!

  #definition(title: "Petersson Inner Product")[
    For $f_1, f_2 in cal(A)_lambda (G, K_f)$, define
    $ chevron.l f_1, f_2 chevron.r_("Pet") := sum_(i=1)^h 1 / (|Gamma_(g_i)|) chevron.l f_1 (g_i), f_2 (g_i) chevron.r_(W_lambda). $
  ]

  Let us check that this pairing is independent of the choice of representatives $g_i$: if $g'_i = gamma g_i k$ with $gamma in G(K_0)$ and $k in K_f$, then $|Gamma_(g'_i)| = |gamma Gamma_(g_i) gamma^(-1)| = |Gamma_(g_i)|$, and by $G(K_(0, oo))$-invariance of $chevron.l dot.c, dot.c chevron.r_(W_lambda)$,
  $ chevron.l f_1 (gamma g_i k), f_2 (gamma g_i k) chevron.r_(W_lambda)
    &= chevron.l rho_lambda (gamma_oo) f_1 (g_i), rho_lambda (gamma_oo) f_2 (g_i) chevron.r_(W_lambda) \
    &= chevron.l f_1 (g_i), f_2 (g_i) chevron.r_(W_lambda). $
  Moreover, if $K'_f subset.eq K_f$ is a smaller open compact subgroup, dividing by $[K_f : K'_f]$ (or equivalently normalizing by the Haar measure $op("vol")(K_f)$) makes the inner product compatible with the inclusion $cal(A)_lambda (G, K_f) arrow.hook cal(A)_lambda (G, K'_f)$ and invariant under the right translation action of $G(bb(A)_(K_0, f))$! Indeed, $chevron.l f_1, f_2 chevron.r_("Pet")$ is proportional to the adelic Haar integral
  $ integral_(G(K_0) backslash G(bb(A)_(K_0))) chevron.l rho_lambda (g_oo)^(-1) f_1 (g_f), rho_lambda (g_oo)^(-1) f_2 (g_f) chevron.r_(W_lambda) thin d g. $

  #proposition(title: "Complete Reducibility of " + $cal(A)_lambda (G)$)[
    The Petersson inner product is positive-definite and $G(bb(A)_(K_0, f))$-invariant on $cal(A)_lambda (G)$. Consequently, $cal(A)_lambda (G)$ is a semisimple unitary representation of $G(bb(A)_(K_0, f))$ and decomposes as an orthogonal direct sum of irreducible admissible representations with finite multiplicities:
    $ cal(A)_lambda (G) tilde.equiv plus.o.big_(pi_f) pi_f^(plus.o m(pi_f, lambda)), quad m(pi_f, lambda) < oo. $
    In terms of automorphic representations of $G(bb(A)_(K_0))$, $m(pi_f, lambda)$ is the multiplicity of $pi = W_lambda^or times.o pi_f$ in $L^2 (G(K_0) backslash G(bb(A)_(K_0)))$.
  ]

  #proof[
    For any open compact subgroup $K_f$, the space $cal(A)_lambda (G, K_f)$ is a finite-dimensional Hilbert space under $chevron.l dot.c, dot.c chevron.r_("Pet")$. Any $G(bb(A)_(K_0, f))$-invariant subspace $V subset.eq cal(A)_lambda (G)$ has an orthogonal complement $V^perp$ with $V^(K_f) plus.o (V^perp)^(K_f) = cal(A)_lambda (G, K_f)$ for every $K_f$, so $V plus.o V^perp = cal(A)_lambda (G)$. By admissibility, every nonzero invariant subspace contains an irreducible subrepresentation (choose $K_f$ with $V^(K_f) != 0$ and take a minimal nonzero subspace of the finite-dimensional space $V^(K_f)$ invariant under the Hecke algebra $cal(H)(G(bb(A)_(K_0, f)), K_f)$). By Zorn's lemma (or induction on $dim cal(A)_lambda (G, K_f)$ for each $K_f$), $cal(A)_lambda (G)$ decomposes as a direct sum of irreducibles, and for each irreducible $pi_f$ with $pi_f^(K_f) != 0$, its multiplicity satisfies $m(pi_f, lambda) <= dim cal(A)_lambda (G, K_f) < oo$.
  ]

  === Hecke Operators and Satake Parameters

  Fix a finite set $S$ of places of $K_0$ containing all archimedean places, all places ramified in $K / K_0$, and all finite places where $K_f = product_(v < oo) K_v$ fails to be a hyperspecial maximal compact subgroup of $G(K_(0,v))$. For every finite place $v in.not S$, the local group $G(K_(0,v))$ is unramified and $K_v$ is hyperspecial.

  The _local spherical Hecke algebra_ at $v in.not S$ is the convolution algebra
  $ cal(H)_v := cal(H)(G(K_(0,v)), K_v) = C_c^oo (K_v backslash G(K_(0,v)) / K_v), $
  with multiplication $(phi_1 * phi_2)(x) = integral_(G(K_(0,v))) phi_1 (y) phi_2 (y^(-1) x) thin d y$, where the Haar measure $d y$ is normalized so that $op("vol")(K_v) = 1$. It acts on $cal(A)_lambda (G, K_f)$ by
  $ (T_phi f)(g_f) := integral_(G(K_(0,v))) phi(y) f(g_f y) thin d y = sum_(j=1)^r c_j f(g_f y_j), $
  where for the characteristic function $phi = bold(1)_(K_v gamma K_v)$ of a double coset $K_v gamma K_v = union.sq.big_(j=1)^r y_j K_v$, the operator is simply the finite sum $(T_(K_v gamma K_v) f)(g_f) = sum_(j=1)^r f(g_f y_j)$.

  A fundamental fact of $p$-adic harmonic analysis (the Satake isomorphism) is that $cal(H)_v$ is a _commutative_ finitely generated $bb(C)$-algebra. Let us make this completely explicit in the two unramified cases—split and inert—because both play a central role in unitary base change.

  ==== Case 1: Unramified Split Places ($v = w w^c$)

  Here $G(K_(0,v)) tilde.equiv op("GL")_n (K_(0,v))$ and $K_v tilde.equiv op("GL")_n (cal(O)_(K_(0,v)))$. Let $pi.alt_v$ be a uniformizer of $K_(0,v)$ and $q_v = |cal(O)_(K_(0,v)) / (pi.alt_v)|$ the cardinality of the residue field. For each $1 <= j <= n$, let $T_v^((j)) in cal(H)_v$ be the characteristic function of the double coset
  $ K_v op("diag")(underbrace(pi.alt_v "," dots.c "," pi.alt_v, j), underbrace(1 "," dots.c "," 1, n - j)) K_v. $
  By the Cartan decomposition, $cal(H)_v = bb(C)[T_v^((1)), dots.c, T_v^((n)), (T_v^((n)))^(-1)]$.

  #theorem(title: "Satake Isomorphism for " + $op("GL")_n$)[
    Let $F = K_(0,v)$ be a nonarchimedean local field with uniformizer $pi.alt$ and residue cardinality $q$. The _Satake transform_ $cal(S) : cal(H)(op("GL")_n (F), op("GL")_n (cal(O)_F)) -> bb(C)[X_1^(plus.minus 1), dots.c, X_n^(plus.minus 1)]^(S_n)$, defined on $phi in cal(H)_v$ by
    $ (cal(S) phi)(X_1, dots.c, X_n) = sum_(a in bb(Z)^n) (delta_B (t_a)^(-1/2) integral_(N(F)) phi(t_a u) thin d u) X_1^(a_1) dots.c X_n^(a_n) $
    (where $t_a = op("diag")(pi.alt^(a_1), dots.c, pi.alt^(a_n))$ and $delta_B (t_a) = product_(i=1)^n q^(-(n + 1 - 2i) a_i)$ is the modulus character of the upper-triangular Borel subgroup $B = T N$), is an isomorphism of $bb(C)$-algebras. Under this isomorphism, the $j$-th Hecke operator maps to the $j$-th elementary symmetric polynomial up to a normalizing power of $q$:
    $ cal(S)(T_v^((j))) = q^(j(n - j)/2) e_j (X_1, dots.c, X_n), quad 1 <= j <= n. $
  ]

  Consequently, every algebra homomorphism $chi : cal(H)_v -> bb(C)$—in particular, the system of Hecke eigenvalues of an unramified irreducible representation $pi_v$ of $op("GL")_n (K_(0,v))$—is uniquely determined by an unordered $n$-tuple of nonzero complex numbers
  $ {alpha_(v,1), dots.c, alpha_(v,n)} subset.eq bb(C)^times, $
  called the _Satake parameters_ of $pi_v$, via the identity
  $ chi(T_v^((j))) = q_v^(j(n - j)/2) e_j (alpha_(v,1), dots.c, alpha_(v,n)). $
  Equivalently, the _Hecke polynomial_ of $pi_v$ is
  $ P_v (X) := product_(i=1)^n (X - alpha_(v,i)) = sum_(j=0)^n (-1)^j q_v^(-j(n - j)/2) chi(T_v^((j))) X^(n - j). $
  In terms of parabolic induction (Section 6.3), $pi_v$ is the unique unramified subquotient of the normalized principal series $op("Ind")_(B(F))^(op("GL")_n (F))(chi_1 times.square dots.c times.square chi_n)$, where $chi_i$ is the unramified character sending $pi.alt_v |-> alpha_(v,i)$.

  ==== Case 2: Unramified Inert Places ($v$ inert in $K / K_0$)

  Now suppose $v$ is inert in $K / K_0$, so $K_v / K_(0,v)$ is the unramified quadratic extension with residue field of size $q_v^2$. Put $m := floor(n / 2)$. Since $G(K_(0,v))$ is quasi-split, we may choose a basis in which the Hermitian form is the anti-diagonal matrix $J_n$ with $1$'s on the anti-diagonal. The maximal $K_(0,v)$-split torus $A subset.eq G(K_(0,v))$ consists of diagonal matrices
  $ a(t_1, dots.c, t_m) = op("diag")(t_1, dots.c, t_m, [1], t_m^(-1), dots.c, t_1^(-1)), quad t_i in K_(0,v)^times, $
  where the middle entry $1$ is present when $n = 2m + 1$ is odd and omitted when $n = 2m$ is even. The relative Weyl group is the hyperoctahedral group $W_m = ({plus.minus 1})^m times.r S_m$, acting by permutations and inversions $X_i |-> X_i^(-1)$.

  By Satake's theorem for quasi-split reductive groups, the Satake transform identifies the spherical Hecke algebra $cal(H)_v$ at an inert place $v$ with
  $ cal(H)(U_n (K_(0,v)), K_v) ->^tilde bb(C)[X_1^(plus.minus 1), dots.c, X_m^(plus.minus 1)]^(W_m). $
  Thus an unramified representation $pi_v$ of $U_n (K_(0,v))$ is determined by an unordered $m$-tuple of pairs ${beta_(v,1)^(plus.minus 1), dots.c, beta_(v,m)^(plus.minus 1)} subset.eq bb(C)^times$. Its _local unramified base change_ $op("BC")(pi_v)$ to $op("GL")_n (K_v)$ (whose residue field has cardinality $q_w = q_v^2$) is the unramified representation of $op("GL")_n (K_v)$ with Satake parameters
  $ cases(
    {beta_(v,1), dots.c, beta_(v,m), beta_(v,m)^(-1), dots.c, beta_(v,1)^(-1)} & text("if ") n = 2m,
    {beta_(v,1), dots.c, beta_(v,m), 1, beta_(v,m)^(-1), dots.c, beta_(v,1)^(-1)} & text("if ") n = 2m + 1,
  ) $
  which is manifestly conjugate self-dual! (For twisted base change $op("BC")_chi$ by a conjugate-self-dual unramified character $chi$ of $K_v^times$, one twists by $chi(pi.alt_v) = plus.minus 1$.)

  Let $bb(T)^S subset.eq op("End")_bb(C)(cal(A)_lambda (G, K_f))$ denote the commutative subalgebra generated by the local spherical Hecke algebras $cal(H)_v$ for all $v in.not S$.

  #proposition(title: "Spectral Decomposition Under the Unramified Hecke Algebra")[
    For every $v in.not S$ and every $phi in cal(H)_v$, the adjoint of $T_phi$ with respect to the Petersson inner product on $cal(A)_lambda (G, K_f)$ is $T_(phi^*)$, where $phi^*(g) = overline(phi(g^(-1)))$. In particular, at a split place $v$, the adjoint of $T_v^((j))$ is $T_v^((n - j)) (T_v^((n)))^(-1)$, so every $T_phi in bb(T)^S$ is a _normal operator_. Consequently, $cal(A)_lambda (G, K_f)$ admits an orthogonal basis of simultaneous Hecke eigenforms for $bb(T)^S$.
  ]

  #proof[
    By $G(bb(A)_(K_0, f))$-invariance of the Petersson inner product, for all $f_1, f_2 in cal(A)_lambda (G, K_f)$ we have
    $ chevron.l T_phi f_1, f_2 chevron.r_("Pet")
      &= integral_(G(K_(0,v))) phi(y) chevron.l y dot.c f_1, f_2 chevron.r_("Pet") thin d y \
      &= integral_(G(K_(0,v))) phi(y) chevron.l f_1, y^(-1) dot.c f_2 chevron.r_("Pet") thin d y. $
    Substituting $z = y^(-1)$ and using unimodularity of the reductive group $G(K_(0,v))$ gives
    $ chevron.l T_phi f_1, f_2 chevron.r_("Pet") = integral_(G(K_(0,v))) chevron.l f_1, overline(phi(z^(-1))) z dot.c f_2 chevron.r_("Pet") thin d z = chevron.l f_1, T_(phi^*) f_2 chevron.r_("Pet"). $
    Since $cal(H)_v$ is commutative and closed under $phi |-> phi^*$, $T_phi$ commutes with its adjoint $T_phi^* = T_(phi^*)$, i.e., $T_phi$ is normal. A commuting family of normal operators on a finite-dimensional Hilbert space is simultaneously unitarily diagonalizable.
  ]

  // ==========================================================================
  // Section 6.3
  // ==========================================================================
  == Automorphic Representations of $op("GL")_n$, Flath's Theorem, and Bernstein–Zelevinsky Classification

  To pass from the concrete finite-dimensional spaces $cal(A)_lambda (G, K_f)$ to the global arithmetic of $L$-functions and Galois representations, we must understand the local and global representation theory of the general linear group $op("GL")_n$. In contrast to definite unitary groups, $op("GL")_n$ is split at every place, has a rich parabolic subgroup structure, and satisfies remarkable multiplicity-one and classification theorems.

  === Smooth Admissible Representations and Flath's Theorem

  Let $F$ be a nonarchimedean local field with ring of integers $cal(O)_F$, uniformizer $pi.alt$, and residue field of order $q$, and let $G = op("GL")_n (F)$ (or more generally the $F$-points of a reductive group).

  #definition(title: "Smooth and Admissible Representations")[
    A complex representation $(pi, V)$ of $G$ is called:
    - _smooth_ if every vector $v in V$ has an open stabilizer in $G$ (equivalently, $V = union.big_K V^K$ as $K$ ranges over open compact subgroups of $G$);
    - _admissible_ if it is smooth and $dim_bb(C) V^K < oo$ for every open compact subgroup $K subset.eq G$.

    The _contragredient_ (or _smooth dual_) of a smooth representation $(pi, V)$ is the space $tilde(V) = (V^or)_("sm")$ of smooth linear functionals on $V$, with action $(tilde(pi)(g) ell)(v) = ell(pi(g^(-1)) v)$.
  ]

  By a foundational theorem of Jacquet and Bernstein, every irreducible smooth representation of a $p$-adic reductive group is automatically admissible, and satisfies Schur's lemma: $op("End")_G (V) = bb(C)$. In particular, the center $Z(G) tilde.equiv F^times$ acts on any irreducible smooth representation $pi$ of $op("GL")_n (F)$ by a smooth character $omega_pi : F^times -> bb(C)^times$, called the _central character_ of $pi$.

  Globally, let $E$ be a number field and $G$ a connected reductive group over $E$. Fix a collection of compact open subgroups $K_v subset.eq G(E_v)$ for all finite places $v$ that are hyperspecial for almost all $v$. Given a family of irreducible smooth representations $(pi_v, V_v)$ of $G(E_v)$ ($v < oo$) such that $V_v^(K_v) != 0$ for almost all $v$, and a choice of nonzero _spherical vector_ $e_v in V_v^(K_v)$ for almost all $v$, the _restricted tensor product_
  $ times.o.big'_v (V_v, e_v) := lim_(-> S) (times.o.big_(v in S) V_v) $
  is the direct limit over finite sets of places $S$ via the transition maps $w |-> w times.o (times.o.big_(v in S' without S) e_v)$. It carries a natural smooth action of $G(bb(A)_(E, f))$.

  #theorem(title: "Flath's Restricted Tensor Product Theorem, 1979")[
    Let $G$ be a connected reductive group over a number field $E$, and let $(pi, V)$ be an irreducible admissible representation of $G(bb(A)_(E, f))$ (or an irreducible admissible $(frak(g)_oo, K_oo) times G(bb(A)_(E, f))$-module). Then:
    1. For every place $v$ of $E$, there exists an irreducible admissible representation $(pi_v, V_v)$ of $G(E_v)$ (a $(frak(g)_v, K_v)$-module if $v | oo$), unramified ($V_v^(K_v) != 0$) for almost all finite $v$, such that
       $ pi tilde.equiv times.o.big'_v pi_v. $
    2. Each local component $pi_v$ is uniquely determined up to isomorphism by $pi$.
  ]

  #proof[
    We explain the finite-adelic case (the archimedean factor separates by the same mechanism). Choose an open compact subgroup $K = product_(v < oo) K_v subset.eq G(bb(A)_(E, f))$ such that $V^K != 0$ and $K_v$ is hyperspecial for all $v in.not S$. The global Hecke algebra $cal(H)(G(bb(A)_(E, f)), K)$ is the algebraic restricted tensor product $times.o.big'_v cal(H)(G(E_v), K_v)$ (with unit $bold(1)_(K_v)$ for $v in.not S$).

    Since $V$ is irreducible and admissible, $V^K$ is a finite-dimensional irreducible module over $cal(H)(G(bb(A)_(E, f)), K)$. For each $v in.not S$, the spherical Hecke algebra $cal(H)_v = cal(H)(G(E_v), K_v)$ is commutative and lies in the center of $cal(H)(G(bb(A)_(E, f)), K)$ (since elements at distinct places commute). By Schur's lemma, $cal(H)_v$ acts on $V^K$ by a scalar character $chi_v : cal(H)_v -> bb(C)$. By the Satake isomorphism, $chi_v$ uniquely determines an irreducible unramified representation $pi_v$ of $G(E_v)$ with $dim pi_v^(K_v) = 1$, spanned by a vector $e_v$.

    At the finitely many ramified places $v in S$, $V^K$ is a finite-dimensional irreducible module over the tensor product $times.o.big_(v in S) cal(H)(G(E_v), K_v)$, which by the Burnside–Wedderburn theorem factors uniquely as $times.o.big_(v in S) M_v$, where each $M_v$ is an irreducible $cal(H)(G(E_v), K_v)$-module corresponding to a unique irreducible smooth representation $pi_v$ of $G(E_v)$ with $pi_v^(K_v) tilde.equiv M_v$. Thus $V^K tilde.equiv times.o.big_(v in S) pi_v^(K_v) times.o times.o.big'_(v in.not S) bb(C) e_v = (times.o.big'_v pi_v)^K$ as modules over the global Hecke algebra. By the bijective correspondence between irreducible admissible representations with $K$-fixed vectors and irreducible $cal(H)(G(bb(A)_(E, f)), K)$-modules, we conclude $pi tilde.equiv times.o.big'_v pi_v$. Uniqueness of each $pi_v$ follows because $pi_v$ is recovered from the $G(E_v)$-action on any irreducible $G(E_v)$-subquotient of $pi$.
  ]

  Flath's theorem is the structural backbone of the entire Langlands program: it allows us to decompose any global automorphic representation $pi$ of $U(X)(bb(A)_(K_0))$ or $op("GL")_n (bb(A)_K)$ into local components $pi_v$, and to define global $L$-functions as Euler products $L(s, pi) = product_v L(s, pi_v)$.

  === Parabolic Induction, Supercuspidals, and Bernstein–Zelevinsky Classification

  Now specialize to $G = op("GL")_n (F)$ over a nonarchimedean local field $F$. For a composition $n = n_1 + dots.c + n_r$, let $P = M N subset.eq op("GL")_n (F)$ be the standard upper block-triangular parabolic subgroup with Levi subgroup $M tilde.equiv op("GL")_(n_1)(F) times dots.c times op("GL")_(n_r)(F)$ and unipotent radical $N$. Let $delta_P : P -> bb(R)_(> 0)$ be the modulus character $delta_P (m n) = |det(op("Ad")(m)|_(op("Lie")(N)))|_F$.

  Given smooth representations $pi_i$ of $op("GL")_(n_i)(F)$ ($1 <= i <= r$), their _normalized parabolic induction_ is the smooth representation of $op("GL")_n (F)$ denoted by the Bernstein–Zelevinsky product
  $ pi_1 times dots.c times pi_r := op("Ind")_P^(op("GL")_n (F))(pi_1 times.square dots.c times.square pi_r), $
  consisting of locally constant functions $f : op("GL")_n (F) -> V_1 times.o dots.c times.o V_r$ such that
  $ f(m n g) &= delta_P (m)^(1/2) (pi_1 (m_1) times.o dots.c times.o pi_r (m_r)) f(g), \
    & quad m = (m_1, dots.c, m_r) in M, n in N, g in op("GL")_n (F), $
  with $op("GL")_n (F)$ acting by right translation. The factor $delta_P^(1/2)$ ensures that parabolic induction preserves unitarity: if each $pi_i$ is unitary, then $pi_1 times dots.c times pi_r$ is unitary.

  The left adjoint of parabolic induction is the _normalized Jacquet functor_ $r_(M, G)(pi) := delta_P^(-1/2) times.o pi_N$, where $pi_N = V / op("span"){ pi(u) v - v : u in N, v in V }$ is the space of $N$-coinvariants. Frobenius reciprocity reads
  $ op("Hom")_G (pi, pi_1 times dots.c times pi_r) tilde.equiv op("Hom")_M (r_(M, G)(pi), pi_1 times.square dots.c times.square pi_r). $

  #definition(title: "Supercuspidal Representation")[
    An irreducible smooth representation $rho$ of $op("GL")_n (F)$ is called _supercuspidal_ if $r_(M, G)(rho) = 0$ for every proper standard parabolic subgroup $P = M N subset.neq op("GL")_n (F)$. Equivalently, $rho$ does not occur as a subquotient of any properly parabolically induced representation, or equivalently, all matrix coefficients of $rho$ are compactly supported modulo the center $Z(op("GL")_n (F))$.
  ]

  By Jacquet's subrepresentation theorem, every irreducible smooth representation $pi$ of $op("GL")_n (F)$ embeds into a parabolically induced representation $rho_1 times dots.c times rho_r$ for some supercuspidal representations $rho_i$ of $op("GL")_(d_i)(F)$ ($sum d_i = n$); the multiset ${rho_1, dots.c, rho_r}$ is uniquely determined by $pi$ and is called the _supercuspidal support_ of $pi$.

  To classify _all_ irreducible smooth representations of $op("GL")_n (F)$ in terms of supercuspidals, Bernstein and Zelevinsky introduced the combinatorial language of _segments_. Write $nu(g) := |det(g)|_F$ for the unramified norm character on $op("GL")_d (F)$.

  #definition(title: "Segments and Multisegments")[
    1. A _segment_ of length $k >= 1$ is a finite set of equivalence classes of supercuspidal representations of $op("GL")_d (F)$ of the form
       $ Delta = [rho, rho nu^(k-1)] := { rho, rho nu, rho nu^2, dots.c, rho nu^(k-1) }, $
       where $rho$ is an irreducible supercuspidal representation of $op("GL")_d (F)$.
    2. Two segments $Delta_1$ and $Delta_2$ are called _linked_ if $Delta_1 union Delta_2$ is again a segment, and neither $Delta_1 subset.eq Delta_2$ nor $Delta_2 subset.eq Delta_1$.
    3. If $Delta_1 = [rho_1, rho_1 nu^(k_1 - 1)]$ and $Delta_2 = [rho_2, rho_2 nu^(k_2 - 1)]$ are linked, we say $Delta_1$ _precedes_ $Delta_2$ (written $Delta_1 prec Delta_2$) if $rho_2 = rho_1 nu^j$ for some integer $1 <= j <= k_1$.
    4. A _multisegment_ is a finite multiset $frak(m) = {Delta_1, dots.c, Delta_r}$ of segments. Its _degree_ is $deg(frak(m)) = sum_(i=1)^r k_i d_i$.
  ]

  For a single segment $Delta = [rho, rho nu^(k-1)]$, the parabolically induced representation
  $ I(Delta) := rho times rho nu times dots.c times rho nu^(k-1) $
  of $op("GL")_(k d)(F)$ has a unique irreducible quotient, denoted $L(Delta)$ (also called the _generalized Steinberg representation_ $op("St")_k (rho)$), and a unique irreducible subrepresentation, denoted $Z(Delta)$. For instance, when $d = 1$ and $rho = nu^(-(k-1)/2)$ on $op("GL")_1 (F) = F^times$, the representation $Z(Delta)$ is the trivial representation $bold(1)_(op("GL")_k (F))$, while $L(Delta) = op("St")_k$ is the classical Steinberg representation of $op("GL")_k (F)$.

  The generalized Steinberg representations $L(Delta)$ are precisely the _essentially square-integrable_ (or _discrete series_) representations of $op("GL")_n (F)$: $L(Delta)$ is square-integrable modulo center if and only if its central character is unitary, which occurs precisely when the segment $Delta$ is centered on the unitary axis (i.e., $rho nu^((k-1)/2)$ is unitary).

  #theorem(title: "Bernstein–Zelevinsky Classification, 1977–1980")[
    Let $frak(m) = {Delta_1, dots.c, Delta_r}$ be a multisegment of degree $n$, ordered so that $Delta_i$ does not precede $Delta_j$ whenever $i < j$ (such an ordering always exists because $prec$ is a strict partial order).
    1. The parabolically induced representation
       $ I(frak(m)) := L(Delta_1) times L(Delta_2) times dots.c times L(Delta_r) $
       has a _unique irreducible quotient_, denoted $L(frak(m))$ (the _Langlands quotient_ of $frak(m)$).
    2. The map $frak(m) |-> L(frak(m))$ is a _bijection_ between multisegments of degree $n$ and isomorphism classes of irreducible smooth representations of $op("GL")_n (F)$.
    3. _(Genericity criterion)_ Fix a nontrivial additive character $psi : F -> bb(C)^times$, and extend it to a generic character $psi_N$ of the upper-triangular unipotent subgroup $N_0 subset.eq op("GL")_n (F)$ via $psi_N (u) = psi(sum_(i=1)^(n-1) u_(i, i+1))$. An irreducible representation $pi = L(frak(m))$ is _generic_ (meaning $op("Hom")_(N_0)(pi, psi_N) != 0$) if and only if _no two segments in $frak(m)$ are linked_. In that case, the induced representation $L(Delta_1) times dots.c times L(Delta_r)$ is already irreducible, so $L(frak(m)) = I(frak(m))$.
    4. _(Temperedness criterion)_ An irreducible representation $L(frak(m))$ is _tempered_ (its matrix coefficients lie in $L^(2 + epsilon)(op("GL")_n (F) / Z)$ for all $epsilon > 0$) if and only if every segment $Delta_i in frak(m)$ is unitary (i.e., $L(Delta_i)$ is unitary discrete series). In particular, every tempered representation is generic and of the form $L(Delta_1) times dots.c times L(Delta_r)$ with each $L(Delta_i)$ unitary discrete series.
  ]

  #remark(title: "Speh Representations and Tadić's Classification of the Unitary Dual")[
    When $delta = L(Delta)$ is a unitary discrete series representation of $op("GL")_d (F)$ and $m >= 1$, the multisegment
    $ frak(m)_(delta, m) = { Delta nu^(-(m-1)/2), Delta nu^(-(m-3)/2), dots.c, Delta nu^((m-1)/2) } $
    yields an irreducible unitary representation $u(delta, m) := L(frak(m)_(delta, m))$ of $op("GL")_(m d)(F)$, called a _Speh representation_. For $m >= 2$, the segments in $frak(m)_(delta, m)$ are linked, so $u(delta, m)$ is _non-generic_ and _non-tempered_. By Tadić's classification (1986), every irreducible unitary representation of $op("GL")_n (F)$ is an irreducible parabolic induction of Speh representations $u(delta, m)$ and complementary series $u(delta, m) nu^alpha times u(delta, m) nu^(-alpha)$ ($0 < alpha < 1/2$). In particular, every _generic_ irreducible unitary representation of $op("GL")_n (F)$ is a product of unitary discrete series and complementary series $delta nu^alpha times delta nu^(-alpha)$ with $0 < alpha < 1/2$. Speh representations appear globally in the _residual spectrum_ of $op("GL")_n$ (Moeglin–Waldspurger) and as base changes of non-tempered automorphic representations of unitary groups (cf. `NarrowSpeh` in Section 6.5).
  ]

  === Archimedean Representations and Casselman–Wallach Globalization

  At an archimedean place $v | oo$ of a number field $E$, $G_v = op("GL")_n (bb(R))$ or $op("GL")_n (bb(C))$ is a real Lie group with maximal compact subgroup $K_v = O(n)$ or $U(n)$ and complexified Lie algebra $frak(g)_v$. Harish-Chandra's algebraic approach studies the category of admissible finitely generated $(frak(g)_v, K_v)$-modules (Harish-Chandra modules), which are purely algebraic objects. However, global automorphic forms and theta lifts are smooth functions of moderate growth—analytic objects carrying Fréchet topologies. The bridge between the algebraic and analytic worlds is the Casselman–Wallach theorem.

  #theorem(title: "Casselman–Wallach Globalization Theorem, 1989")[
    Let $G$ be a real reductive Lie group with maximal compact subgroup $K$. Let $cal(M)_(op("SF"))(G)$ denote the category of smooth Fréchet representations of $G$ of moderate growth and finite length, and let $cal(M)_(op("HC"))(frak(g), K)$ denote the category of Harish-Chandra $(frak(g), K)$-modules of finite length. The functor
    $ V |-> V_(K"-fin") $
    taking a smooth Fréchet representation to its dense subspace of $K$-finite vectors is an _equivalence of categories_. In particular, every finite-length Harish-Chandra module admits a canonical smooth Fréchet globalization $V^oo$, and continuous $G$-intertwining maps between smooth globalizations coincide with $(frak(g), K)$-module homomorphisms.
  ]

  The Langlands classification at archimedean places parallels the Bernstein–Zelevinsky classification: every irreducible $(frak(g), K)$-module is the unique irreducible quotient $J(P, sigma, nu)$ of a standard module induced from a tempered representation $sigma$ of a Levi subgroup $M$ twisted by a strictly positive character $nu$. For $op("GL")_n (bb(C))$, every parabolic subgroup reduces to the Borel subgroup $B$ (there are no discrete series on $op("GL")_m (bb(C))$ for $m >= 2$!), so every irreducible representation is a subquotient of a principal series $op("Ind")_B^(op("GL")_n (bb(C)))(chi_1 times.square dots.c times.square chi_n)$ where each character of $bb(C)^times$ has the form
  $ chi_j (z) = z^(a_j) overline(z)^(b_j) = (z / |z|)^(a_j - b_j) |z|^(a_j + b_j), quad a_j, b_j in bb(C), thin a_j - b_j in bb(Z). $

  === Cuspidal Automorphic Representations of $op("GL")_n$ and Multiplicity One

  Let $K$ be a number field. An automorphic form $phi$ on $op("GL")_n (K) backslash op("GL")_n (bb(A)_K)$ with unitary central character $omega$ is called _cuspidal_ if for every proper standard parabolic subgroup $P = M N subset.neq op("GL")_n$, its constant term along $N$ vanishes identically:
  $ integral_(N(K) backslash N(bb(A)_K)) phi(n g) thin d n = 0 quad forall g in op("GL")_n (bb(A)_K). $
  Cuspidal forms are rapidly decreasing on Siegel domains and therefore lie in the Hilbert space $L^2_("cusp")(op("GL")_n (K) backslash op("GL")_n (bb(A)_K), omega)$, which decomposes discretely with finite multiplicities into irreducible unitary representations—the _cuspidal automorphic representations_ of $op("GL")_n (bb(A)_K)$.

  The Fourier expansion of a cuspidal form on $op("GL")_n$ (Piatetski-Shapiro and Shalika) expresses $phi$ in terms of its global Whittaker function
  $ W_phi (g) := integral_(N_0 (K) backslash N_0 (bb(A)_K)) phi(u g) overline(psi_(N_0)(u)) thin d u, $
  where $psi_(N_0)(u) = psi(sum_(i=1)^(n-1) u_(i, i+1))$ for a nontrivial additive character $psi : bb(A)_K / K -> bb(C)^times$. Because $phi != 0$ implies $W_phi != 0$, every cuspidal automorphic representation of $op("GL")_n (bb(A)_K)$ is _globally generic_, and hence every local component $pi_v$ is generic! Combined with local uniqueness of Whittaker models (Gelfand–Kazhdan and Shalika: $dim op("Hom")_(N_0 (K_v))(pi_v, psi_(N_0, v)) <= 1$), this yields three cornerstones of the theory of $op("GL")_n$.

  #theorem(title: "Multiplicity One, Strong Multiplicity One, and Jacquet–Shalika Bounds")[
    Let $K$ be a number field.
    1. _(Multiplicity One — Shalika, 1974)_ Every irreducible cuspidal automorphic representation $pi$ of $op("GL")_n (bb(A)_K)$ occurs with multiplicity _one_ in $L^2_("cusp")(op("GL")_n (K) backslash op("GL")_n (bb(A)_K), omega_pi)$, and every local component $pi_v$ is generic.
    2. _(Strong Multiplicity One — Jacquet–Shalika, 1981)_ Let $pi = times.o.big'_v pi_v$ and $pi' = times.o.big'_v pi'_v$ be irreducible cuspidal automorphic representations of $op("GL")_n (bb(A)_K)$. If $pi_v tilde.equiv pi'_v$ for all but finitely many places $v$ of $K$, then $pi = pi'$ (equality of subspaces of $L^2_("cusp")$).
    3. _(Jacquet–Shalika Bounds, 1981)_ If $pi$ is a unitary cuspidal automorphic representation of $op("GL")_n (bb(A)_K)$, then at every unramified finite place $v$, the Satake parameters $alpha_(v,1), dots.c, alpha_(v,n)$ satisfy the strict inequality
       $ q_v^(-1/2) < |alpha_(v,i)| < q_v^(1/2), quad 1 <= i <= n. $
  ]

  #proof[
    We sketch the core ideas. For (1), if $pi$ appeared with multiplicity $>= 2$ in $L^2_("cusp")$, we would obtain two linearly independent global Whittaker functionals on $pi$. By Flath's theorem $pi tilde.equiv times.o.big'_v pi_v$ and local uniqueness of Whittaker models ($dim op("Hom")_(N_0 (K_v))(pi_v, psi_v) = 1$), the space of global Whittaker functionals on $pi$ is $1$-dimensional, so some nontrivial linear combination of the two embeddings would have identically zero Whittaker function, contradicting the Piatetski-Shapiro–Shalika Fourier expansion for nonzero cusp forms.

    For (2) and (3), the key tool is the Rankin–Selberg $L$-function $L(s, pi times tilde(pi)')$, which converges absolutely for $op("Re")(s) > 1$ and admits a meromorphic continuation to $bb(C)$ with a simple pole at $s = 1$ if and only if $pi tilde.equiv pi'$ (and is holomorphic at $s = 1$ otherwise). For a single unitary cuspidal $pi$, the Euler product $L^S (s, pi times tilde(pi)) = product_(v in.not S) product_(i,j) (1 - alpha_(v,i) overline(alpha_(v,j)) q_v^(-s))^(-1)$ has nonnegative Dirichlet coefficients and converges for $op("Re")(s) > 1$; if some $|alpha_(v,i)| >= q_v^(1/2)$, then the local factor $(1 - |alpha_(v,i)|^2 q_v^(-s))^(-1)$ would have a pole in $op("Re")(s) >= 1$, contradicting the convergence of the partial Euler product on $op("Re")(s) > 1$ (and its known holomorphy/simple pole structure). If $pi_v tilde.equiv pi'_v$ for $v in.not S$, then $L^S (s, pi times tilde(pi)') = L^S (s, pi times tilde(pi))$ has a pole at $s = 1$, forcing $pi tilde.equiv pi'$, and hence $pi = pi'$ by (1).
  ]

  The _Generalized Ramanujan–Petersson Conjecture_ predicts that for every unitary cuspidal automorphic representation $pi$ of $op("GL")_n (bb(A)_K)$, every local component $pi_v$ is _tempered_—in particular, $|alpha_(v,i)| = 1$ at all unramified places $v$. While this conjecture remains open in full generality, Section 6.4 shows that it is a _theorem_ for regular algebraic conjugate self-dual cuspidal (RACSDC) representations—and it is precisely this theorem that powers the Weil bound in the Alpöge–Claude–Riemann proof.

  // ==========================================================================
  // Section 6.4
  // ==========================================================================
  == Cohomological Representations, Clozel Purity, and Unitary Base Change

  We now assemble the three global pillars connecting totally definite unitary groups $U(X)$ to $op("GL")_n (bb(A)_K)$ and $ell$-adic Galois representations: Clozel's purity lemma, quadratic base change, and Caraiani's local-global compatibility.

  === Regular Algebraic Conjugate Self-Dual Cuspidal (RACSDC) Representations

  Let $K / K_0$ be a CM field. Complex conjugation $c in op("Gal")(K / K_0)$ acts on $op("GL")_n (bb(A)_K)$ entrywise; for any representation $Pi$ of $op("GL")_n (bb(A)_K)$, define the conjugate representation $Pi^c (g) := Pi(c(g))$.

  #definition(title: "RACSDC Automorphic Representation")[
    An irreducible cuspidal automorphic representation $Pi = times.o.big'_w Pi_w$ of $op("GL")_n (bb(A)_K)$ is called _regular algebraic conjugate self-dual cuspidal_ (abbreviated _RACSDC_) if:
    1. _(Conjugate self-dual)_ $Pi^c tilde.equiv Pi^or$;
    2. _(Regular algebraic / cohomological)_ For every archimedean place $w | oo$ of $K$, the representation $Pi_w$ of $op("GL")_n (bb(C))$ is cohomological for an irreducible algebraic representation $W_(lambda_w)^or$ of $op("GL")_n (bb(C))$ (where $lambda_w = (lambda_(w,1) >= dots.c >= lambda_(w,n)) in bb(Z)^n_+$). Concretely, $Pi_w$ is isomorphic to the irreducible principal series
       $ Pi_w tilde.equiv op("Ind")_(B(bb(C)))^(op("GL")_n (bb(C)))(chi_1 times.square dots.c times.square chi_n), quad chi_j (z) = z^(a_(w,j)) overline(z)^(b_(w,j)), $
       where $a_(w,j), b_(w,j) in bb(Z) + (n - 1)/2$ (the $C$-algebraic / half-integral shift, so that $a_(w,j) + (n-1)/2 in bb(Z)$ and $b_(w,j) + (n-1)/2 in bb(Z)$), the $a_(w,j)$ are pairwise distinct, and the $b_(w,j)$ are pairwise distinct.
  ]

  In terms of the highest weight $lambda_w = (lambda_(w,1) >= dots.c >= lambda_(w,n))$ and the half-sum of positive roots $rho_n = ((n-1)/2, (n-3)/2, dots.c, -(n-1)/2)$, the infinitesimal character of $W_(lambda_w)^or$ has Harish-Chandra parameters $(lambda_(w,j) + (n + 1 - 2j)/2)_(j=1)^n$ (and conjugate parameters determined by $lambda_(w^c)$). Notice that the shift $(n-1)/2$ is half-integral when $n$ is even and integral when $n$ is odd; this is why Clozel distinguishes between _$L$-algebraic_ ($a_(w,j), b_(w,j) in bb(Z)$) and _$C$-algebraic_ ($a_(w,j), b_(w,j) in bb(Z) + (n-1)/2$) normalizations, which differ by twisting by $|det|^((n-1)/2)$.

  A remarkable rigidity phenomenon governs the archimedean exponents $a_(w,j)$ and $b_(w,j)$ of regular algebraic cuspidal representations: they are forced to be _pure_ of a single weight.

  #theorem(title: "Clozel's Purity Lemma, 1990")[
    Let $Pi$ be a regular algebraic cuspidal automorphic representation of $op("GL")_n (bb(A)_K)$ over a CM field $K$ (or any number field $K$) with archimedean parameters $chi_(w,j)(z) = z^(a_(w,j)) overline(z)^(b_(w,j))$ at each $w | oo$. Suppose $Pi$ is essentially conjugate self-dual, i.e., $Pi^c tilde.equiv Pi^or times.o |det|^w$ for some $w in bb(Z)$ (or more generally, $Pi$ is algebraic and unitary up to a twist $|det|^(w/2)$). Then for every archimedean place $w | oo$ and every $1 <= j <= n$,
    $ a_(w,j) + b_(w,j) = w. $
    In particular, if $Pi$ is RACSDC ($Pi^c tilde.equiv Pi^or$), then $w = 0$ (so $a_(w,j) + b_(w,j) = 0$ in the unitary normalization, meaning $Pi_w$ is _tempered_ at every infinite place, and $a_(w,j) + b_(w,j) = n - 1$ after twisting by $|det|^{(n-1)/2}$ to the $L$-algebraic normalization).
  ]

  #proof[
    By twisting $Pi$ by $|det|^(-w/2)$, we reduce to the case where $Pi$ is unitary (in particular, $Pi^c tilde.equiv Pi^or$ implies the central character of $Pi$ is unitary on $bb(R)_(> 0)$ embedded diagonally, so $Pi$ is already unitary). Since $Pi$ is cuspidal, every archimedean component $Pi_w$ is both _unitary_ and _generic_.

    Recall from the classification of unitary generic representations of $op("GL")_n (bb(C))$ (Vogan / Tadić) that any irreducible unitary generic principal series $op("Ind")_B^(op("GL")_n (bb(C)))(chi_1 times.square dots.c times.square chi_n)$ with $chi_j (z) = (z / |z|)^(m_j) |z|^(s_j)$ ($m_j = a_j - b_j in bb(Z)$, $s_j = a_j + b_j in bb(C)$) must have all exponents $s_j$ real and lying in the strict strip
    $ -1 < op("Re")(s_j) < 1, $
    with every nonzero $s_j$ paired with $-s_j$ having the _same_ angular exponent $m_j$ (a complementary series pair). Wait: here $a_j, b_j in bb(Z) + (n-1)/2$ implies that
    $ s_j = a_j + b_j in bb(Z)! $
    The only integer strictly between $-1$ and $1$ is $0$! Therefore $s_j = a_(w,j) + b_(w,j) = 0$ for every $w | oo$ and every $1 <= j <= n$.
  ]

  Look at how short and lethal that proof is: the combination of _algebraicity_ ($a_j + b_j in bb(Z)$) and _unitary genericity_ ($|op("Re")(a_j + b_j)| < 1$) leaves literally no integer available except $0$! In particular, every RACSDC representation is automatically tempered at every archimedean place.

  === Isobaric Sums and Unitary Base Change

  Not every automorphic representation of a totally definite unitary group $U(X)$ transfers to a _cuspidal_ representation of $op("GL")_n (bb(A)_K)$—some transfer to sums of lower-rank cuspidal representations (endoscopic transfers). To state the unitary base change theorem cleanly, we recall Langlands' notion of an _isobaric sum_.

  #definition(title: "Isobaric Automorphic Representation")[
    Let $Pi_1, dots.c, Pi_r$ be irreducible cuspidal automorphic representations of $op("GL")_(n_1)(bb(A)_K), dots.c, op("GL")_(n_r)(bb(A)_K)$ with $n_1 + dots.c + n_r = n$. Their _isobaric sum_
    $ Pi = Pi_1 plus.square Pi_2 plus.square dots.c plus.square Pi_r $
    is the unique irreducible automorphic representation of $op("GL")_n (bb(A)_K)$ whose local component at every place $w$ is the Langlands quotient of $Pi_(1,w) times dots.c times Pi_(r,w)$ (ordered by decreasing real parts of central character exponents). In particular, at every place $w$ where all $Pi_(i,w)$ are unramified, the Satake parameters of $Pi_w$ are the multiset union of the Satake parameters of $Pi_(1,w), dots.c, Pi_(r,w)$, and the partial $L$-function factors as
    $ L^S (s, Pi) = product_(i=1)^r L^S (s, Pi_i). $
  ]

  By the Jacquet–Shalika classification theorem for isobaric sums, the unordered multiset ${Pi_1, dots.c, Pi_r}$ is uniquely determined by the local components $Pi_w$ at almost all places $w$. More generally, if we allow each $Pi_i$ to be an irreducible representation in the _discrete spectrum_ $L^2_("disc")(op("GL")_(n_i)(K) backslash op("GL")_(n_i)(bb(A)_K))$—which by the Moeglin–Waldspurger theorem consists of global Speh representations $op("MW")(sigma_i, m_i)$ built from cuspidal representations $sigma_i$—we obtain the full discrete-to-isobaric spectrum needed to house base change of arbitrary (possibly non-tempered) unitary automorphic representations.

  Let us now describe the $L$-group mechanism behind quadratic base change from $G = U(X)$ to $op("Res")_(K / K_0) op("GL")_n$. The Langlands dual group of $U(X)$ over $K_0$ is the semidirect product
  $ {}^L U(X) = op("GL")_n (bb(C)) times.r op("Gal")(K / K_0), $
  where the nontrivial element $c in op("Gal")(K / K_0)$ acts on $op("GL")_n (bb(C))$ by the pinned outer automorphism
  $ theta(g) := Phi_n (g^t)^(-1) Phi_n^(-1), quad (Phi_n)_(i, j) = (-1)^(i-1) delta_(i, n + 1 - j). $
  Meanwhile, the $L$-group of $op("Res")_(K / K_0) op("GL")_n$ is
  $ {}^L (op("Res")_(K / K_0) op("GL")_n) = (op("GL")_n (bb(C)) times op("GL")_n (bb(C))) times.r op("Gal")(K / K_0), $
  where $c$ swaps the two copies of $op("GL")_n (bb(C))$: $c(g_1, g_2) = (g_2, g_1)$.

  There are two natural $L$-homomorphisms ${}^L U(X) -> {}^L (op("Res")_(K / K_0) op("GL")_n)$:
  1. _Standard base change_ $op("BC")$: sends $(g, 1) |-> (g, theta(g), 1)$ and $(1, c) |-> (I_n, I_n, c)$.
  2. _Twisted base change_ $op("BC")_chi$: given a Hecke character $chi : bb(A)_K^times / K^times -> bb(C)^times$ whose restriction to $bb(A)_(K_0)^times$ is the quadratic character $omega_(K / K_0)$ (note that $chi$ is conjugate self-dual: $chi^c = chi^(-1)$), one modifies the image of $c$ by a cocycle built from $chi$, which corresponds on $op("GL")_n (bb(A)_K)$ to twisting by $chi$ when $n$ is even (and is necessary in the even-dimensional case to make the base change of a $C$-algebraic representation $L$-algebraic, or vice versa).

  For a totally definite unitary group $G = U(X)$, the Arthur–Selberg trace formula—dramatically simplified by the compactness of $G(K_0) backslash G(bb(A)_(K_0))$—was used by Labesse (2011) (for cohomological/regular weights, building on Clozel and Kottwitz) and in complete generality by Mok (2015) and Kaletha–Minguez–Shin–White (2014) to establish global quadratic base change.

  #theorem(title: "Unitary Base Change — Labesse, Mok, Kaletha–Minguez–Shin–White")[
    Let $K / K_0$ be a CM extension, let $G = U(X)$ be a totally definite unitary group of rank $n$ over $K_0$, and let $pi = pi_oo times.o pi_f$ be an irreducible automorphic representation of $G(bb(A)_(K_0))$ with $pi_oo tilde.equiv W_lambda^or$ for a dominant weight $lambda = (lambda_v)_(v | oo)$. Then there exists a unique conjugate self-dual isobaric automorphic representation
    $ Pi = op("BC")(pi) = Pi_1 plus.square Pi_2 plus.square dots.c plus.square Pi_r $
    of $op("GL")_n (bb(A)_K)$ (where each $Pi_i$ is a conjugate self-dual discrete-spectrum automorphic representation of $op("GL")_(n_i)(bb(A)_K)$, and in fact cuspidal whenever $Pi_w$ is regular algebraic) such that:
    1. _(Split places)_ For every finite place $v = w w^c$ of $K_0$ that splits in $K$, under the isomorphism $G(K_(0,v)) tilde.equiv op("GL")_n (K_w)$ of Proposition 6.3,
       $ Pi_w tilde.equiv pi_v quad text("and") quad Pi_(w^c) tilde.equiv pi_v^or. $
    2. _(Unramified inert places)_ For every finite place $v$ inert in $K / K_0$ at which $pi_v$ is unramified (with unique place $w | v$ of $K$), $Pi_w$ is the local unramified base change of $pi_v$ described in Section 6.2.
    3. _(Archimedean places)_ For every archimedean place $w | v | oo$ of $K$, the infinitesimal character of $Pi_w$ coincides with that of $W_(lambda_v)^or$ (with $a_(w,j) = lambda_(v,j) + (n + 1 - 2j)/2$ and $b_(w,j) = -a_(w,j)$). In particular, if $Pi_i$ is cuspidal, it is automatically regular algebraic (up to the standard shift)!
  ]

  #insight-box(title: "Why Definite Unitary Groups Plus Base Change Is So Powerful")[
    Notice what happens when we combine Section 6.2 with Theorem 6.27:
    - On the unitary group $G = U(X)$, constructing automorphic forms of weight $lambda$ is completely elementary—any nonzero vector in the finite-dimensional space $cal(A)_lambda (G, K_f) tilde.equiv plus.o.big_(i=1)^h W_lambda^(Gamma_(g_i))$ decomposes into Hecke eigenforms! Even better, theta lifts from smaller groups into $U(X)$ land directly in $cal(A)_lambda (G, K_f)$ and are tested for nonvanishing by finite Petersson inner products.
    - Once we have an irreducible automorphic representation $pi$ of $U(X)(bb(A)_(K_0))$, base change produces a conjugate self-dual isobaric representation $Pi = op("BC")(pi) = Pi_1 plus.square dots.c plus.square Pi_r$ of $op("GL")_n (bb(A)_K)$ whose split local components are _literally identical_ to those of $pi$ ($Pi_w tilde.equiv pi_v$).
    - And once we are on $op("GL")_n (bb(A)_K)$ with RACSDC summands $Pi_i$, the full arsenal of Galois representations and Deligne's purity theorem kicks in!
  ]

  === Galois Representations and Local-Global Compatibility

  The culminating arithmetic theorem of this chapter attaches $ell$-adic Galois representations to RACSDC automorphic representations of $op("GL")_n (bb(A)_K)$ and matches them with the Local Langlands Correspondence at _every_ finite place $w divides.not ell$.

  Recall that for a nonarchimedean local field $F$, the _Local Langlands Correspondence_ for $op("GL")_n (F)$ (proved by Harris–Taylor and Henniart in 2000–2001) is a canonical bijection
  $ op("rec")_F : op("Irr")(op("GL")_n (F)) ->^tilde op("WD")_n (F) $
  between isomorphism classes of irreducible smooth representations of $op("GL")_n (F)$ and isomorphism classes of $n$-dimensional Frobenius-semisimple Weil–Deligne representations $(r, N)$ of the Weil group $W_F$, preserving $L$-factors and $epsilon$-factors of pairs. On the Galois side, given a continuous representation $rho : op("Gal")(overline(F) / F) -> op("GL")_n (overline(bb(Q))_ell)$ (with $ell$ different from the residue characteristic of $F$), Grothendieck's $ell$-adic monodromy theorem associates a Weil–Deligne representation $op("WD")(rho) = (r, N)$, whose Frobenius-semisimplification is denoted $op("WD")(rho)^(op("F-ss"))$.

  #theorem(title: "Galois Representations and Strong Local-Global Compatibility — Clozel, Harris–Taylor, Shin, Chenevier–Harris, Caraiani")[
    Let $K$ be a CM field, and let $Pi$ be a RACSDC automorphic representation of $op("GL")_n (bb(A)_K)$ of weight $lambda$. For every prime $ell$ and every field isomorphism $iota : overline(bb(Q))_ell ->^tilde bb(C)$, there exists a unique (up to isomorphism) continuous semisimple Galois representation
    $ rho_(Pi, iota) : op("Gal")(overline(K) / K) -> op("GL")_n (overline(bb(Q))_ell) $
    such that:
    1. _(Conjugate self-duality)_ $rho_(Pi, iota)^c tilde.equiv rho_(Pi, iota)^or times.o epsilon_ell^(1 - n)$, where $epsilon_ell$ is the $ell$-adic cyclotomic character.
    2. _(Unramified compatibility)_ At every finite place $w divides.not ell$ where $Pi_w$ is unramified, $rho_(Pi, iota)$ is unramified at $w$, and the characteristic polynomial of geometric Frobenius $op("Frob")_w$ matches the Satake parameters of $Pi_w$ (normalized by $q_w^((n-1)/2)$):
       $ det(X dot.c I_n - iota(rho_(Pi, iota)(op("Frob")_w))) = product_(j=1)^n (X - q_w^((n-1)/2) alpha_(w,j)). $
    3. _(Strong local-global compatibility — Caraiani, 2012)_ At _every_ finite place $w divides.not ell$ of $K$ (ramified or unramified!),
       $ op("WD")(rho_(Pi, iota)|_(G_(K_w)))^(op("F-ss")) tilde.equiv iota^(-1) op("rec")_(K_w)(Pi_w times.o |det|_w^((1 - n)/2)). $
       In particular, the monodromy operator $N$ on the Galois side matches the segment structure (Steinberg / Bernstein–Zelevinsky nilpotent orbit) on the automorphic side!
    4. _(De Rham and Hodge–Tate weights at $w | ell$)_ For every place $w | ell$, $rho_(Pi, iota)|_(G_(K_w))$ is de Rham (and crystalline if $Pi_w$ is unramified and $K_w / bb(Q)_ell$ is unramified), with Hodge–Tate weights determined explicitly by $lambda_w$.
  ]

  #corollary(title: "Ramanujan–Petersson / Temperedness for RACSDC Representations")[
    Let $Pi$ be a RACSDC automorphic representation of $op("GL")_n (bb(A)_K)$. Then for _every_ place $w$ of $K$ (archimedean or nonarchimedean), the local component $Pi_w$ is _tempered_. In particular, at every unramified finite place $w$, all Satake parameters of $Pi_w$ lie on the unit circle:
    $ |alpha_(w,j)| = 1, quad 1 <= j <= n. $
  ]

  #proof[
    At archimedean places $w | oo$, temperedness is already Clozel's Purity Lemma (Theorem 6.25). For a finite place $w < oo$, choose a prime $ell$ coprime to the residue characteristic of $w$. Because $rho_(Pi, iota)$ is constructed in the $ell$-adic étale cohomology of unitary Shimura varieties (Kottwitz, Harris–Taylor, Shin), Deligne's purity theorem (Weil II) implies that the Weil–Deligne representation $op("WD")(rho_(Pi, iota)|_(G_(K_w)))^(op("F-ss"))$ is _pure of weight $n - 1$_: every eigenvalue of $op("Frob")_w$ on the $k$-th graded piece of the monodromy filtration has complex absolute value $q_w^((n - 1 + k)/2)$. Under Caraiani's local-global compatibility (Theorem 6.28(3)), twisting by $|det|_w^((1 - n)/2)$ shifts the weight from $n - 1$ to $0$. By the Local Langlands Correspondence, a Weil–Deligne representation $(r, N)$ is pure of weight $0$ if and only if its corresponding irreducible representation $Pi_w = op("rec")_(K_w)^(-1)(r, N)$ of $op("GL")_n (K_w)$ is _tempered_ (all segments in its Bernstein–Zelevinsky multisegment are centered on the unitary axis). At unramified places ($N = 0$), this says precisely $|alpha_(w,j)| = 1$.
  ]

  This corollary is the ultimate payoff of the chapter. In the chapters that follow, the Alpöge–Claude–Riemann proof will construct automorphic forms on totally definite unitary groups via chained theta lifts, transfer them to $op("GL")_n (bb(A)_K)$ via unitary base change, and invoke `galoisLocalGlobalStrong_recParameter` (Caraiani's strong local-global compatibility) to deduce temperedness—eliminating any possible failure of the Weil/Ramanujan bound that could otherwise arise from an off-line zero of a Dirichlet $L$-function.

  // ==========================================================================
  // Section 6.5
  // ==========================================================================
  == Lean 4 Formalization

  In the Lean 4 codebase `lean-rh`, the theory developed in this chapter is organized into four tightly interconnected layers: Hermitian spaces and Landherr's theorem, real/adelic representation theory of $op("GL")_n$, quadratic base change identities from totally definite unitary groups, and the attachment of $ell$-adic Galois representations with strong local-global compatibility.

  #lean-note(title: "Lean 4 Formalization: Unitary Groups, GL_n, Base Change, and Galois Representations", module: "CompanionTheory & Development")[
    The main results of Chapter 6 correspond to the following modules and declarations in `lean-rh/src/`:

    - *Hermitian Hasse Principle & Landherr's Theorem (Section 6.1)*:
      - `Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds` and `Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HermitianHassePrinciple`: formalizes `GlobalTheory.Published.HermitianHassePrinciple` (proved via `hermitianHassePrinciple_holds` and re-exported as `PositivityTheory.Stage1.PM.hermitianHassePrinciple`).
      - `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt`: establishes the Landherr classification and existence of global Hermitian spaces with prescribed archimedean signatures and local invariants at finite places.

    - *Harish-Chandra Modules, Real Groups, and Spectral Geometry (Sections 6.2–6.3)*:
      - `CompanionTheory` (`AutomorphicTheory`, `HarishChandraModules`, `RealGroups`, `SpectralGeometry`, `ThickeningEstimates`): provides the analytic and algebraic backbone for real reductive groups, $(frak(g), K)$-modules, Bessel and orbital integral estimates, and spectral decomposition on compact and arithmetic quotients.

    - *Representation Theory of $op("GL")_n$ (Section 6.3)*:
      - `Development.WeilBound.RepresentationTheoryGL`: a comprehensive library containing `GenericUnitaryGL`, `JacquetShalikaBounds`, `DiscreteSeries`, `HolomorphicDiscreteSeries`, `EisensteinSeries`, `EisensteinResidues`, `ResidualSpectrum`, `UnitaryDualProof`, `CasimirAlgebra`, `ConstantTermFiniteness`, `FormalDegree`, and `ArchimedeanBaseChange`. Together these formalize the local unitary dual of $op("GL")_n$, Jacquet–Shalika bounds, constant-term finiteness, and archimedean base change parameters.

    - *Unitary Base Change Identities (Section 6.4)*:
      - `Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities`: formalizes quadratic base change from totally definite unitary groups to isobaric automorphic representations of $op("GL")_n (bb(A)_K)$. Key files include `DefiniteNHolds.lean` (proving `UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN`), `BaseChangeNB.lean` (`baseChangeNB`), `FrameMatching/` (Hecke eigenvalue finiteness and word bounds), `RealTraceClifford/`, `Narrow.lean`, `NarrowSpeh.lean` (ruling out or controlling non-tempered Speh summands), `SplitComp.lean` (matching split local components $Pi_w tilde.equiv pi_v$), and `USideFree.lean`.

    - *Galois Representations and Local-Global Compatibility (Section 6.4)*:
      - `Development.AutomorphicArithmetic.Foundations.GaloisRepresentations`: formalizes the construction and local-global compatibility of $ell$-adic Galois representations attached to RACSDC automorphic representations. Key subdirectories include `IntegralStructures/RowSrc.lean` (exporting the headline theorem `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`, which packages Caraiani's strong local-global compatibility with the Local Langlands `rec` parameter), `BaseChangeDescent/`, `SphericalGaloisCompatibility/`, `HeckeGaloisCriteria/`, `DefiniteTraceForms/`, `CrystallineTowers/`, `CharpolyFromTrace/`, `KunnethLefschetz/`, and `WeightCharacters/`.
  ]

  Notice an important architectural lesson from the formalization: in `BaseChangeIdentities`, the base change theorem `baseChangeN` is proved by matching Hecke eigenvalues on finite-dimensional spaces of automorphic forms on totally definite unitary groups (`FrameMatching` and `DefiniteNHolds.lean`) against isobaric sums on $op("GL")_n$, with dedicated modules (`NarrowSpeh.lean`, `SplitComp.lean`) tracking the exact local components at split places and controlling Speh representations. In `GaloisRepresentations`, `galoisLocalGlobalStrong_recParameter` then converts that automorphic datum into the strong Weil–Deligne compatibility needed to enforce temperedness and feed directly into the final character-box conclusion (`Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`).

  // ==========================================================================
  // Exercises
  // ==========================================================================
  #exercises((
    [
      Let $K_0 = bb(Q)(sqrt(5))$ and $K = K_0 (i) = bb(Q)(sqrt(5), i)$. Verify that $K / K_0$ is a CM extension with $d = [K_0 : bb(Q)] = 2$. Using Landherr's theorem (Theorem 6.5), determine for each $n >= 1$ whether there exists a totally definite Hermitian space of dimension $n$ over $K / K_0$ whose unitary group is quasi-split at _every_ finite place of $K_0$.
    ],
    [
      Let $K = bb(Q)(sqrt(-D))$ be an imaginary quadratic field of discriminant $-D < 0$, and let $(X, h)$ be the $1$-dimensional totally definite Hermitian space $X = K$, $h(x, y) = x overline(y)$. Compute the finite double coset space $X(K_f) = U(X)(bb(Q)) backslash U(X)(bb(A)_(bb(Q), f)) / K_f$ for the maximal open compact subgroup $K_f = product_p U(X)(bb(Z)_p)$, and show that its cardinality is related to the class number $h_K$ of $K$ (specifically, identify $X(K_f)$ with the subgroup of squares or the genus quotient in $op("Cl")(K)$ via Hilbert's Theorem 90).
    ],
    [
      Let $G = U(X)$ be a totally definite unitary group over $K_0$, and let $K_f subset.eq G(bb(A)_(K_0, f))$ be an open compact subgroup.
      (a) Give an explicit example (with $K = bb(Q)(i)$, $n = 1$ or $n = 2$) where $Gamma_(g_f) = G(K_0) inter g_f K_f g_f^(-1)$ is nontrivial, and compute $dim_bb(C) cal(A)_lambda (G, K_f)$ for $lambda = (k)$ ($k in bb(Z)$) in the $n = 1$ case.
      (b) Prove that if $K_f = product_v K_v$ is a principal congruence subgroup of level $N >= 3$ (meaning every matrix in $K_v$ is congruent to $I_n$ modulo $N cal(O)_(K_v)$ for all $v | N$), then every element of finite order in $G(K_0) inter g_f K_f g_f^(-1)$ is the identity (Minkowski's theorem), so $K_f$ is neat.
    ],
    [
      For $G = op("GL")_2 (F)$ over a nonarchimedean local field $F$ with uniformizer $pi.alt$ and residue field of order $q$, decompose the double coset $K op("diag")(pi.alt, 1) K$ (where $K = op("GL")_2 (cal(O)_F)$) into $q + 1$ left cosets $y_j K$. Using the definition of the Satake transform in Theorem 6.14, compute $cal(S)(T^((1)))$ and $cal(S)(T^((2)))$ directly and verify the formula $cal(S)(T^((1))) = q^(1/2)(X_1 + X_2)$ and $cal(S)(T^((2))) = X_1 X_2$.
    ],
    [
      Let $v$ be an unramified inert place of $K / K_0$, and consider the quasi-split unitary group $U_3 (K_(0,v))$ defined by the anti-diagonal form $J_3$.
      (a) Verify that the maximal $K_(0,v)$-split torus is $A = { op("diag")(t, 1, t^(-1)) : t in K_(0,v)^times }$ and that the relative Weyl group has order $2$, acting by $t |-> t^(-1)$.
      (b) Describe the spherical Hecke algebra $cal(H)(U_3 (K_(0,v)), K_v) tilde.equiv bb(C)[X + X^(-1)]$ and compute the Satake parameters of the local unramified base change $op("BC")(pi_v)$ on $op("GL")_3 (K_v)$ in terms of the eigenvalue of the generator $T_v$ corresponding to $X + X^(-1)$.
    ],
    [
      Let $F$ be a nonarchimedean local field and $rho$ a unitary supercuspidal representation of $op("GL")_2 (F)$. Consider the three multisegments of degree $6$:
      $ frak(m)_1 &= { [rho, rho nu], [rho nu^(-1)] }, quad frak(m)_2 = { [rho nu^(-1/2), rho nu^(1/2)], [rho] }, \
        frak(m)_3 &= { [rho nu^(-1), rho nu] }. $
      For each $frak(m)_i$:
      (a) Determine whether $L(frak(m)_i)$ is generic;
      (b) Determine whether $L(frak(m)_i)$ is tempered;
      (c) Determine whether $L(frak(m)_i)$ is discrete series (square-integrable modulo center).
    ],
    [
      Prove that if $Pi = Pi_1 plus.square dots.c plus.square Pi_r$ is a conjugate self-dual isobaric automorphic representation of $op("GL")_n (bb(A)_K)$ ($Pi^c tilde.equiv Pi^or$) with each $Pi_i$ cuspidal, then the involution $sigma |-> (sigma^c)^or$ permutes the multiset ${Pi_1, dots.c, Pi_r}$. Give an example of a conjugate self-dual isobaric sum $Pi_1 plus.square Pi_2$ on $op("GL")_2 (bb(A)_K)$ where _neither_ $Pi_1$ nor $Pi_2$ is individually conjugate self-dual, and explain why such pairs can still arise via base change from $U(2)$.
    ],
    [
      Verify directly from the formulas for ${}^L U(n)$ and ${}^L (op("Res")_(K / K_0) op("GL")_n)$ in Section 6.4 that the map
      $ & op("BC") : {}^L U(n) -> {}^L (op("Res")_(K / K_0) op("GL")_n), \
        & quad (g, 1) |-> (g, theta(g), 1), quad (1, c) |-> (I_n, I_n, c) $
      is a well-defined group homomorphism (where $theta(g) = Phi_n (g^t)^(-1) Phi_n^(-1)$). Show that for a diagonal matrix $t = op("diag")(t_1, dots.c, t_n) in op("GL")_n (bb(C))$, one has $theta(t) = op("diag")(t_n^(-1), dots.c, t_1^(-1))$, and deduce the Satake parameter formula for local unramified base change at both split and inert places.
    ],
    [
      Let $Pi$ be a RACSDC automorphic representation of $op("GL")_n (bb(A)_K)$ with associated $ell$-adic Galois representation $rho_(Pi, iota)$. Using Theorem 6.28(2) and Corollary 6.29, show that for every finite place $w divides.not ell$ where $Pi_w$ is unramified, the Frobenius trace satisfies the sharp Weil bound
      $ |iota(op("tr")(rho_(Pi, iota)(op("Frob")_w)))| <= n dot.c q_w^((n - 1)/2). $
      Explain what bound one would obtain if one knew only the Jacquet–Shalika bound (Theorem 6.23(3)) instead of Caraiani's local-global compatibility and Deligne's Weil II.
    ],
  ))
]
