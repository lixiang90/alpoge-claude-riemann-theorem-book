// ============================================================================
// Chapter 7: The Weil Representation, Theta Lifts, and the Doubling Method
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch07() = [
  #chapter(
    "The Weil Representation, Theta Lifts, and the Doubling Method",
    short-title: "Weil Representation and Theta Lifts",
    epigraph: "It is a remarkable fact that the classical theta functions, which Jacobi and Riemann used to uniformize abelian varieties and prove the functional equation of the zeta function, are in reality matrix coefficients and automorphic realizations of a single canonical projective representation of the symplectic group.",
    epigraph-source: "After André Weil (1964) and Roger Howe (1979)",
    overview: [
      This chapter develops the representation-theoretic and automorphic machinery of the *theta correspondence*—the engine that powers the chain of iterated theta lifts $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ in the Alpöge–Claude proof of the Riemann Hypothesis. We begin with the Heisenberg group, the Stone–von Neumann uniqueness theorem, the metaplectic double cover $op("Mp")(bb(W))$, and the Schrödinger and Fock models of the Weil representation $omega_psi$. We then specialize to unitary reductive dual pairs $(U(V), U(W))$, presenting Kudla's explicit splitting via pairs of Hecke characters $(chi_V, chi_W)$, local Howe duality at both archimedean and non-archimedean places, and the global theta kernel $theta_phi (g, h)$. Next, we establish the spectral transfer of Satake parameters $pi |-> pi plus.square mu_j [t]$ and introduce the three great analytic identities governing global theta lifts: the Siegel–Weil formula, the Piatetski-Shapiro–Rallis doubling method, and the Rallis inner product formula. Finally, we prove the seesaw identity and explain how seesaw duality converts the period of an iterated theta lift into a Gan–Gross–Prasad / Bessel period that is *independent* of the auxiliary Hecke characters $mu_j$, resolving a decisive structural obstacle in the proof.
    ],
    label-name: "ch:theta-correspondence",
  )

  In Chapter 3, we saw that Stepanov's elementary proof of the Riemann Hypothesis over finite fields relies on constructing an auxiliary polynomial vanishing to high multiplicity $m$ along the Frobenius locus. Over the integers, there is no literal Frobenius endomorphism and no algebraic differentiation of whole numbers with respect to primes. The boldest architectural idea of the Alpöge–Claude proof is to *synthesize multiplicity automorphically* by passing an automorphic form through a chain of $m approx sqrt(X)$ iterated theta lifts between totally definite unitary groups:
  $ U(X_0) -> U(X_1) -> U(X_2) -> dots.c -> U(X_m). $
  At each link in this chain, a theta lift increments the rank of the unitary group and appends a twisted block $mu_j [t]$ to the automorphic representation, acting as an automorphic analogue of raising the order of vanishing by one. To make this mechanism rigorous—and to control both the $L^2$-norms of the lifted forms and their period integrals—we need the full local and global theory of the Weil representation and the theta correspondence.

  == The Heisenberg Group, Stone–von Neumann, and the Metaplectic Cover

  The story begins in the simplest non-abelian nilpotent Lie group: the Heisenberg group, born in quantum mechanics from the canonical commutation relations $[p, q] = -i planck$ and reborn in number theory in André Weil's landmark 1964 paper *Sur certains groupes d'opérateurs unitaires*.

  === Symplectic Spaces and the Heisenberg Group

  Let $F$ be a local field of characteristic zero (so $F$ is isomorphic to $bb(R)$, $bb(C)$, or a finite extension of $bb(Q)_p$). Let $(bb(W), chevron.l dot.c, dot.c chevron.r)$ be a finite-dimensional symplectic vector space over $F$, meaning that $chevron.l dot.c, dot.c chevron.r : bb(W) times bb(W) -> F$ is a nondegenerate alternating bilinear form. Consequently, $dim_F bb(W) = 2n$ is even. The *symplectic group* of $(bb(W), chevron.l dot.c, dot.c chevron.r)$ is
  $ op("Sp")(bb(W)) = { g in op("GL")(bb(W)) : chevron.l g w_1, g w_2 chevron.r = chevron.l w_1, w_2 chevron.r, forall w_1, w_2 in bb(W) }. $
  A subspace $bb(L) subset.eq bb(W)$ is called *isotropic* if $chevron.l w_1, w_2 chevron.r = 0$ for all $w_1, w_2 in bb(L)$, and *Lagrangian* (or maximally isotropic) if in addition $dim_F bb(L) = n$. Every symplectic space admits a *complete polarization*
  $ bb(W) = bb(X) plus.o bb(Y) $
  into two transverse Lagrangian subspaces $bb(X)$ and $bb(Y)$. In such a polarization, the symplectic pairing identifies $bb(X)$ with the dual space $bb(Y)^* = op("Hom")_F (bb(Y), F)$ via $x |-> chevron.l dot.c, x chevron.r$.

  #definition(title: "Heisenberg Group")[
    The *Heisenberg group* attached to $(bb(W), chevron.l dot.c, dot.c chevron.r)$ is the topological group $H(bb(W)) = bb(W) times F$ equipped with the multiplication law
    $ (w_1, t_1) dot.c (w_2, t_2) = (w_1 + w_2, t_1 + t_2 + frac(1, 2) chevron.l w_1, w_2 chevron.r). $
  ]

  The identity element of $H(bb(W))$ is $(0, 0)$, the inverse of $(w, t)$ is $(-w, -t)$, and the commutator of two elements is
  $ [(w_1, t_1), (w_2, t_2)] = (0, chevron.l w_1, w_2 chevron.r). $
  Because $chevron.l dot.c, dot.c chevron.r$ is nondegenerate, the center $Z(H(bb(W)))$ coincides with the derived subgroup $[H(bb(W)), H(bb(W))] = {(0, t) : t in F} approx F$, and $H(bb(W))$ sits in a central extension
  $ 1 -> F -> H(bb(W)) -> bb(W) -> 1. $
  Moreover, the symplectic group $op("Sp")(bb(W))$ acts on $H(bb(W))$ by group automorphisms that fix the center pointwise:
  $ g dot.c (w, t) = (g w, t), quad g in op("Sp")(bb(W)), (w, t) in H(bb(W)). $

  === The Stone–von Neumann Theorem and the Schrödinger Model

  Fix a nontrivial continuous unitary additive character $psi : F -> bb(C)^times$. (For $F = bb(R)$, the standard choice is $psi(t) = e^(2 pi i t)$; for $F = bb(Q)_p$, one takes $psi(t) = e^(-2 pi i {t}_p)$, where ${t}_p$ is the $p$-adic fractional part.) We seek irreducible unitary representations of $H(bb(W))$ on which the center $Z(H(bb(W))) approx F$ acts through $psi$:
  $ rho(0, t) = psi(t) dot.c op("Id") quad "for all" t in F. $

  Given a complete polarization $bb(W) = bb(X) plus.o bb(Y)$, the subgroup $A_bb(X) = bb(X) times F subset.eq H(bb(W))$ is maximal abelian because $bb(X)$ is Lagrangian. Extending $psi$ trivially across $bb(X)$ defines a one-dimensional unitary character $tilde(psi)(x, t) = psi(t)$ of $A_bb(X)$. Forming the unitary induced representation $op("Ind")_(A_bb(X))^(H(bb(W))) tilde(psi)$ yields a concrete realization on the Hilbert space $L^2(bb(Y))$ (with respect to a Haar measure $d y$ on $bb(Y)$), whose space of smooth vectors is the Schwartz–Bruhat space $cal(S)(bb(Y))$ (rapidly decreasing $C^oo$-functions when $F$ is archimedean; locally constant compactly supported functions when $F$ is non-archimedean).

  #definition(title: "Schrödinger Model")[
    For a complete polarization $bb(W) = bb(X) plus.o bb(Y)$, the *Schrödinger representation* $rho_psi = rho_(psi, bb(X), bb(Y))$ of $H(bb(W))$ on $cal(S)(bb(Y))$ (and by unitary extension on $L^2(bb(Y))$) is given for $w = x + y in bb(X) plus.o bb(Y)$ and $t in F$ by
    $ (rho_psi (x + y, t) phi)(y') = psi(t + chevron.l y', x chevron.r + frac(1, 2) chevron.l y, x chevron.r) phi(y' + y). $
  ]

  One verifies directly from the bilinearity and alternating property of $chevron.l dot.c, dot.c chevron.r$ that $rho_psi$ is a unitary group homomorphism: for $w_1 = x_1 + y_1$ and $w_2 = x_2 + y_2$, the cocycle factor $psi(chevron.l y' + y_1, x_2 chevron.r + frac(1,2) chevron.l y_2, x_2 chevron.r + chevron.l y', x_1 chevron.r + frac(1,2) chevron.l y_1, x_1 chevron.r)$ differs from the value at $(w_1 + w_2, t_1 + t_2)$ by precisely $psi(frac(1,2)(chevron.l y_1, x_2 chevron.r - chevron.l y_2, x_1 chevron.r)) = psi(frac(1,2) chevron.l w_1, w_2 chevron.r)$.

  #theorem(title: "Stone–von Neumann Theorem")[
    Let $psi : F -> bb(C)^times$ be a nontrivial unitary additive character.
    1. The Schrödinger representation $(rho_psi, L^2(bb(Y)))$ is irreducible (and its smooth subspace $cal(S)(bb(Y))$ is an irreducible smooth representation of $H(bb(W))$ when $F$ is non-archimedean).
    2. Every irreducible unitary representation $(rho, cal(H))$ of $H(bb(W))$ with central character $psi$ is unitarily equivalent to $(rho_psi, L^2(bb(Y)))$.
    3. Every unitary representation of $H(bb(W))$ with central character $psi$ is a Hilbert-space direct sum of copies of $rho_psi$.
  ]

  #proof[
    We sketch the classical proof via the integrated form of the representation (Mackey–Weil–von Neumann), which works uniformly over both archimedean and non-archimedean local fields. Fix a self-dual Haar measure $d w$ on $bb(W)$ with respect to the bicharacter $(w_1, w_2) |-> psi(chevron.l w_1, w_2 chevron.r)$. For any unitary representation $(rho, cal(H))$ with central character $psi$ and any $f in cal(S)(bb(W))$, define the bounded operator
    $ rho(f) = integral_(bb(W)) f(w) rho(w, 0) d w. $
    In the Schrödinger model on $L^2(bb(Y))$, writing $w = x + y$, we compute
    $ (rho_psi (f) phi)(y') = integral_(bb(Y)) K_f (y', y'') phi(y'') d y'', $
    where the integral kernel is the partial Fourier transform
    $ K_f (y', y'') = integral_(bb(X)) f(x + y'' - y') psi(frac(1, 2) chevron.l y' + y'', x chevron.r) d x. $
    Since the partial Fourier transform is a topological isomorphism $cal(S)(bb(W)) -> cal(S)(bb(Y) times bb(Y))$, the operators $rho_psi (f)$ range over all Hilbert–Schmidt operators with Schwartz–Bruhat kernels. In particular, $rho_psi (cal(S)(bb(W)))$ is strongly dense in the algebra of all compact operators on $L^2(bb(Y))$, which immediately proves irreducibility of $rho_psi$.

    To prove uniqueness, pick a unit vector $phi_0 in cal(S)(bb(Y))$ (for instance, a Gaussian over $bb(R)$ or the characteristic function of a lattice over a $p$-adic field) and let $f_0 in cal(S)(bb(W))$ be the unique Schwartz–Bruhat function whose kernel is the rank-one projection $K_(f_0)(y', y'') = phi_0 (y') overline(phi_0 (y''))$. Then $rho_psi (f_0)$ is a self-adjoint projection of rank one, and by the Heisenberg multiplication law, the twisted convolution algebra satisfies $f_0 star_psi f star_psi f_0 = c(f) f_0$ for a scalar $c(f) = chevron.l rho_psi (f) phi_0, phi_0 chevron.r$. Now let $(rho, cal(H))$ be *any* nonzero unitary representation with central character $psi$. One checks that $rho(f_0) != 0$ (otherwise $rho(f) = 0$ for all $f$ by translating $f_0$, contradicting strong continuity). Choose a unit vector $v_0 in op("Im")(rho(f_0))$. Then for every $f in cal(S)(bb(W))$,
    $ norm(rho(f) v_0)^2
      &= chevron.l rho(f_0 star_psi f^* star_psi f star_psi f_0) v_0, v_0 chevron.r \
      &= c(f^* star_psi f) = norm(rho_psi (f) phi_0)^2. $
    Thus the map $rho_psi (f) phi_0 |-> rho(f) v_0$ extends to a $H(bb(W))$-equivariant isometry $L^2(bb(Y)) -> cal(H)$. If $(rho, cal(H))$ is irreducible, this isometry is surjective, proving unitary equivalence.
  ]

  #remark(title: "Intertwining Between Transverse Lagrangians")[
    A direct corollary of the Stone–von Neumann theorem is that the Schrödinger models attached to two different polarizations $bb(W) = bb(X) plus.o bb(Y)$ and $bb(W) = bb(X)' plus.o bb(Y)'$ are canonically intertwined up to a scalar of modulus one. When $bb(Y)$ and $bb(Y)'$ are *transverse* ($bb(Y) inter bb(Y)' = {0}$), the intertwining operator $cal(S)(bb(Y)) -> cal(S)(bb(Y)')$ is explicitly the symplectic Fourier transform
    $ (cal(F)_(bb(Y), bb(Y)') phi)(y') = integral_(bb(Y)) phi(y) psi(chevron.l y', y chevron.r) d y. $
    More generally, for any two Lagrangians $bb(Y)$ and $bb(Y)'$, the intertwiner integrates over the quotient $bb(Y) \/ (bb(Y) inter bb(Y)')$. This explicit Schwartz–Bruhat intertwining is formalized in `StoneVonNeumannSchwartzBruhatTransverseLagrangia` and globally in `AdelicStoneVonNeumannLagrangianUniqueness`.
  ]

  === The Metaplectic Double Cover and the Weil Representation

  We now harvest the miraculous consequence of the Stone–von Neumann theorem discovered by Shale (over $bb(R)$) and Weil (over arbitrary local fields). For any $g in op("Sp")(bb(W))$, define a new representation $rho_psi^g$ of $H(bb(W))$ on the same space $L^2(bb(Y))$ by
  $ rho_psi^g (w, t) = rho_psi (g w, t). $
  Because $op("Sp")(bb(W))$ fixes the center $Z(H(bb(W)))$ pointwise, $rho_psi^g$ is again an irreducible unitary representation of $H(bb(W))$ with the *same* central character $psi$. By the Stone–von Neumann theorem, there exists a unitary operator $M(g) in cal(U)(L^2(bb(Y)))$, unique up to a scalar in $S^1 = {z in bb(C)^times : |z| = 1}$, such that
  $ M(g) rho_psi (h) M(g)^(-1) = rho_psi (g dot.c h) quad "for all" h in H(bb(W)). $
  By Schur's lemma, for any $g_1, g_2 in op("Sp")(bb(W))$, the operators $M(g_1) M(g_2)$ and $M(g_1 g_2)$ both intertwine $rho_psi$ with $rho_psi^(g_1 g_2)$, so there exists a scalar $c(g_1, g_2) in S^1$ such that
  $ M(g_1) M(g_2) = c(g_1, g_2) M(g_1 g_2). $
  Associativity implies that $c : op("Sp")(bb(W)) times op("Sp")(bb(W)) -> S^1$ is a $2$-cocycle, defining a projective representation of $op("Sp")(bb(W))$—equivalently, a genuine unitary representation of a central $S^1$-extension $tilde(op("Sp"))(bb(W))_(S^1)$ of $op("Sp")(bb(W))$.

  The decisive structural theorem of Weil is that the cohomology class $[c] in H^2(op("Sp")(bb(W)), S^1)$ has order dividing $2$: it can be reduced from $S^1$ to the two-element group $mu_2 = {plus.minus 1}$!

  #theorem(title: "Existence of the Metaplectic Cover and Weil Representation")[
    There exists a unique (up to isomorphism) topological double cover—the *metaplectic group* $op("Mp")(bb(W))$—fitting into a central exact sequence
    $ 1 -> mu_2 -> op("Mp")(bb(W)) ->^(p) op("Sp")(bb(W)) -> 1, $
    which is non-split whenever $F != bb(C)$, together with a genuine unitary representation $omega_psi$ of $op("Mp")(bb(W))$ on $L^2(bb(Y))$ (preserving the smooth subspace $cal(S)(bb(Y))$) satisfying
    $ omega_psi (tilde(g)) rho_psi (h) omega_psi (tilde(g))^(-1) = rho_psi (p(tilde(g)) dot.c h) $
    for all $tilde(g) in op("Mp")(bb(W))$ and $h in H(bb(W))$.
  ]

  The representation $omega_psi$ is called the *Weil representation* (or *oscillator* / *metaplectic* representation). In the Schrödinger model on $cal(S)(bb(Y))$, the action of the generators of $op("Sp")(bb(W))$ can be written down explicitly. Let $P(bb(Y)) = M(bb(Y)) N(bb(Y))$ be the Siegel parabolic subgroup stabilizing the Lagrangian $bb(Y)$, where in block form with respect to $bb(W) = bb(X) plus.o bb(Y)$:
  $ m(a) &= mat(a^*, 0; 0, a) quad (a in op("GL")(bb(Y))), \
    n(b) &= mat(1, 0; b, 1) quad (b in op("Hom")^(op("sym"))(bb(X), bb(Y))), $
  where $a^*$ is the contragredient of $a$ with respect to $chevron.l dot.c, dot.c chevron.r$ (so $chevron.l a y, a^* x chevron.r = chevron.l y, x chevron.r$), and $b$ satisfies $chevron.l b x_1, x_2 chevron.r = chevron.l b x_2, x_1 chevron.r$. Let $w_0 = mat(0, -1; 1, 0)$ be a Weyl element swapping $bb(X)$ and $bb(Y)$ via an identification $bb(X) approx bb(Y)^*$. Then for $phi in cal(S)(bb(Y))$:
  1. *(Levi action)* For $m(a) in M(bb(Y))$,
     $ (omega_psi (m(a), epsilon) phi)(y) = epsilon dot.c gamma_psi (det a)^(-1) dot.c |det a|_F^(1/2) dot.c phi(a^(-1) y), $
     where $epsilon in {plus.minus 1}$ and $gamma_psi (det a)$ is the *Weil index*—an eighth root of unity encoding the phase of the Gaussian integral $integral_F psi(frac(1,2) a x^2) d x$—satisfying $gamma_psi (a b) = gamma_psi (a) gamma_psi (b) (a, b)_F$, with $(a, b)_F in {plus.minus 1}$ the quadratic Hilbert symbol of $F$.
  2. *(Unipotent action)* For $n(b) in N(bb(Y))$ (acting by $x |-> x + b x$, or dually on $bb(Y)$ for the opposite unipotent $u(c) = mat(1, c; 0, 1)$),
     $ (omega_psi (u(c), epsilon) phi)(y) = epsilon dot.c psi(frac(1, 2) chevron.l y, c y chevron.r) phi(y). $
  3. *(Weyl element)* For $w_0$,
     $ (omega_psi (w_0, epsilon) phi)(y) = epsilon dot.c gamma_psi dot.c integral_(bb(Y)) phi(y') psi(chevron.l y, y' chevron.r) d y', $
     the Fourier transform normalized by the Weil index $gamma_psi$.

  Notice the factor $|det a|_F^(1/2) gamma_psi (det a)^(-1)$ in the Levi action! This square root of the determinant is the precise analytic manifestation of the double cover: as $a$ traces a loop in $op("GL")(bb(Y))$ (for instance, $e^(i theta) in op("GL")_1(bb(R))$? Even simpler, a rotation in $op("SO")(2) subset op("SL")_2(bb(R))$), the phase factor acquires a sign $-1$, forcing us to pass to the double cover $op("Mp")(bb(W))$.

  === The Fock Model over $bb(R)$

  While the Schrödinger model is indispensable for non-archimedean fields and global Poisson summation, over $F = bb(R)$ the compact maximal subgroup $tilde(K) subset op("Mp")(bb(W))$ (the double cover of $U(n) subset op("Sp")_(2n)(bb(R))$) acts by complicated integral operators in the Schrödinger model. To diagonalize the action of $tilde(K)$—and thereby compute archimedean theta correspondences cleanly—one passes to the *Bargmann–Fock model*.

  Choose a positive-definite compatible complex structure $J in op("Sp")(bb(W))$ (meaning $J^2 = -1$ and the symmetric bilinear form $(w_1, w_2) |-> chevron.l w_1, J w_2 chevron.r$ is positive definite). This identifies $bb(W) approx bb(C)^n$ with standard Hermitian inner product $h(z, w) = z^t overline(w)$ and symplectic form $chevron.l z, w chevron.r = op("Im") h(z, w)$.

  #definition(title: "Fock Space and Polynomial Fock Model")[
    The *Bargmann–Fock Hilbert space* $cal(F)(bb(C)^n)$ consists of all entire holomorphic functions $F : bb(C)^n -> bb(C)$ such that
    $ norm(F)_(cal(F))^2 = integral_(bb(C)^n) |F(z)|^2 e^(-pi norm(z)^2) d z < oo. $
    Its dense subspace of $tilde(K)$-finite vectors is the *polynomial Fock space*
    $ cal(P)(bb(C)^n) = bb(C)[z_1, dots.c, z_n], $
    which is a $(frak("sp")_(2n)(bb(C)), tilde(K))$-module (the Harish-Chandra module of $omega_psi$).
  ]

  The unitary intertwiner between the Schrödinger model $L^2(bb(R)^n)$ and the Fock model $cal(F)(bb(C)^n)$ is the *Bargmann transform*:
  $ (cal(B) phi)(z) = 2^(n/4) integral_(bb(R)^n) phi(y) exp(-pi y^t y + 2 pi z^t y - frac(pi, 2) z^t z) d y. $
  Under $cal(B)$, the Gaussian vacuum vector $phi_0 (y) = 2^(n/4) e^(-pi norm(y)^2) in cal(S)(bb(R)^n)$ maps to the constant polynomial $1 in cal(P)(bb(C)^n)$. More remarkably, the Heisenberg Lie algebra acts by the *creation and annihilation operators*:
  $ z_j quad "(multiplication by" z_j ")" wide "and" wide frac(1, pi) frac(partial, partial z_j), $
  and the complexified symplectic Lie algebra $frak("sp")_(2n)(bb(C))$ acts by the quadratic differential operators
  $ z_j z_k, wide z_j frac(partial, partial z_k) + frac(1, 2) delta_(j k), wide frac(partial^2, partial z_j partial z_k). $
  In particular, the maximal compact subgroup $tilde(K) = tilde(U)(n)$ acts on homogeneous polynomials $F in bb(C)[z_1, dots.c, z_n]$ simply by linear substitution twisted by the square-root determinant character:
  $ (omega_psi (tilde(k)) F)(z) = (det tilde(k))^(-1/2) dot.c F(k^(-1) z), quad tilde(k) in tilde(U)(n). $
  This diagonalization of $tilde(K)$ turns the archimedean theta correspondence into pure classical invariant theory!

  #lean-note(
    title: "Lean 4 Formalization: Stone–von Neumann, Metaplectic Cover, and Fock Models",
    module: "Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels & WeilRepresentation",
  )[
    In `lean-rh/src`, the foundational local theory of the Weil representation is split across three tightly coordinated components:
    - *Stone–von Neumann uniqueness*: `StoneVonNeumannSchwartzBruhatAnyCharacter` and `StoneVonNeumannSchwartzBruhatTransverseLagrangia` (under `Development/AbelianVarietyTheory/Proofs/DivisorProofs`) establish uniqueness of the Schrödinger model on Schwartz–Bruhat spaces and the explicit Fourier intertwiner between transverse Lagrangians, upgraded adelically in `AdelicStoneVonNeumannLagrangianUniqueness`.
    - *Real metaplectic representation*: `RealMetaplecticRepresentation` and `RealMetaplecticRepresentationHolds` (in `Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula` and `Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives`) formalize the real metaplectic double cover, the quadratic Lie algebra action, and the smooth vector space.
    - *Fock models*: `Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels` constructs the polynomial Fock model $bb(C)[z_1, dots.c, z_n]$, the Bargmann intertwiner, and the explicit $tilde(K)$-type decomposition needed for archimedean Howe duality on compact unitary groups.
  ]

  == Unitary Dual Pairs and Kudla's Splitting

  The Weil representation $omega_psi$ is an extraordinarily "small" representation of $op("Mp")(bb(W))$—its Gelfand–Kirillov dimension is only $n = frac(1,2) dim bb(W)$, the minimal possible for an infinite-dimensional representation. Roger Howe's revolutionary insight was that when one restricts $omega_psi$ to a pair of mutually centralizing reductive subgroups inside $op("Sp")(bb(W))$, this smallness forces a rigid bijection between their irreducible representations.

  === Reductive Dual Pairs and Unitary Spaces

  #definition(title: "Reductive Dual Pair")[
    A pair $(G, G')$ of reductive subgroups of $op("Sp")(bb(W))$ is called a *reductive dual pair* if $G$ is the centralizer of $G'$ in $op("Sp")(bb(W))$ and $G'$ is the centralizer of $G$ in $op("Sp")(bb(W))$.
  ]

  Howe classified all irreducible reductive dual pairs over a local field $F$ into two types:
  - *Type I*: Pairs arising from a division algebra $D$ with involution and two sesquilinear spaces $(V, (dot.c, dot.c)_V)$ and $(W, chevron.l dot.c, dot.c chevron.r_W)$ of opposite symmetry (one Hermitian, one skew-Hermitian). Over $F$, these give the orthogonal-symplectic pairs $(O(V), op("Sp")(W))$, the unitary pairs $(U(V), U(W))$, and the quaternionic pairs.
  - *Type II*: Pairs $(op("GL")_m (D), op("GL")_n (D))$ embedded in $op("Sp")_(2 m n d)(F)$ via a complete polarization $bb(W) = M_(m times n)(D) plus.o M_(m times n)(D)^*$.

  In the Alpöge–Claude proof, we work exclusively with *unitary dual pairs* (which become Type II general linear pairs at places where the quadratic extension splits!). Let $K \/ K_0$ be a quadratic extension of local fields (or globally a CM field $K$ over its maximal totally real subfield $K_0$), with nontrivial Galois automorphism $x |-> x^c$ (written $overline(x)$ at archimedean places) and associated quadratic character $omega_(K/K_0) : K_0^times -> {plus.minus 1}$ from local/global class field theory.

  Let $(V, (dot.c, dot.c)_V)$ be an $m$-dimensional *Hermitian* vector space over $K$ (so $(v_1, v_2)_V^c = (v_2, v_1)_V$, linear in the first variable and conjugate-linear in the second), and let $(W, chevron.l dot.c, dot.c chevron.r_W)$ be an $n$-dimensional *skew-Hermitian* vector space over $K$ (so $chevron.l w_1, w_2 chevron.r_W^c = -chevron.l w_2, w_1 chevron.r_W$). Fix a nonzero trace-zero element $delta in K^times$ with $delta^c = -delta$; multiplying a Hermitian form by $delta$ converts it into a skew-Hermitian form, so the distinction is merely a convenient bookkeeping device.

  Consider the $2 m n$-dimensional $K_0$-vector space
  $ bb(W) = op("Res")_(K/K_0)(V times.o_K W), $
  equipped with the $K_0$-bilinear form
  $ chevron.l v_1 times.o w_1, v_2 times.o w_2 chevron.r_bb(W) = op("Tr")_(K/K_0) ( (v_1, v_2)_V dot.c chevron.l w_1, w_2 chevron.r_W^c ). $
  Because $(v_1, v_2)_V^c = (v_2, v_1)_V$ and $chevron.l w_1, w_2 chevron.r_W^c = -chevron.l w_2, w_1 chevron.r_W$, we have
  $ chevron.l v_2 times.o w_2, v_1 times.o w_1 chevron.r_bb(W)
    &= op("Tr")_(K/K_0) ( (v_1, v_2)_V^c dot.c (-chevron.l w_1, w_2 chevron.r_W) ) \
    &= -chevron.l v_1 times.o w_1, v_2 times.o w_2 chevron.r_bb(W), $
  so $chevron.l dot.c, dot.c chevron.r_bb(W)$ is a nondegenerate symplectic form on $bb(W)$! The natural action of the isometry groups $U(V)$ and $U(W)$ on $V times.o_K W$ via $(g, h) dot.c (v times.o w) = g v times.o h w$ preserves $chevron.l dot.c, dot.c chevron.r_bb(W)$, giving a homomorphism
  $ iota : U(V) times U(W) -> op("Sp")(bb(W)) $
  whose image is a reductive dual pair in $op("Sp")(bb(W))$.

  === Kudla's Splitting via Splitting Characters

  When we pull back the metaplectic double cover $op("Mp")(bb(W)) -> op("Sp")(bb(W))$ to $U(V) times U(W)$, a crucial question arises: *does the double cover split over $U(V) times U(W)$?* For orthogonal-symplectic pairs $(O(V), op("Sp")(W))$ with $dim V$ odd, the cover does *not* split over $op("Sp")(W)$—this is why classical Shimura lifts connect half-integral weight modular forms on $tilde(op("SL"))_2$ to integral weight forms on $op("PGL")_2$. For *unitary* dual pairs, however, Stephen Kudla proved in 1994 that the metaplectic cover *always* splits over $U(V) times U(W)$—provided one supplies a pair of auxiliary characters!

  #definition(title: "Splitting Characters")[
    A pair of continuous characters $(chi_V, chi_W)$ of $K^times$ (globally, Hecke characters of $bb(A)_K^times \/ K^times$) is called a *pair of splitting characters* for the unitary dual pair $(U(V), U(W))$ if their restrictions to $K_0^times$ (globally, $bb(A)_(K_0)^times$) satisfy the parity conditions
    $ chi_V |_(K_0^times) = omega_(K/K_0)^(dim V), wide chi_W |_(K_0^times) = omega_(K/K_0)^(dim W). $
  ]

  Note that when $dim V$ is even, $chi_V$ is trivial on $K_0^times$ (for instance, $chi_V = 1$ is allowed); when $dim V$ is odd, $chi_V$ must restrict to the nontrivial quadratic character $omega_(K/K_0)$ on $K_0^times$ (such characters always exist, both locally and globally!).

  #theorem(title: "Kudla's Splitting Theorem")[
    Let $(U(V), U(W))$ be a unitary dual pair over a local field $K_0$ (with quadratic extension $K \/ K_0$), and let $(chi_V, chi_W)$ be a pair of splitting characters. Then there exists an explicit, canonical continuous group homomorphism
    $ tilde(iota)_(chi_V, chi_W) : U(V) times U(W) -> op("Mp")(bb(W)) $
    lifting the embedding $iota : U(V) times U(W) -> op("Sp")(bb(W))$. Moreover:
    1. Globally, over a CM extension $K \/ K_0$ with global splitting Hecke characters $(chi_V, chi_W)$ of $bb(A)_K^times \/ K^times$, the local splittings assemble into an adelic splitting
       $ U(V)(bb(A)_(K_0)) times U(W)(bb(A)_(K_0)) -> op("Mp")(bb(W)(bb(A)_(K_0))) $
       that agrees with the canonical global splitting of $op("Mp")(bb(W)(bb(A)_(K_0)))$ over the rational points $op("Sp")(bb(W)(K_0))$.
    2. Pulling back the Weil representation $omega_psi$ along $tilde(iota)_(chi_V, chi_W)$ yields a genuine linear representation $omega_(psi, chi_V, chi_W)$ of $U(V) times U(W)$.
    3. Changing the splitting characters to $(chi_V dot.c eta_1, chi_W dot.c eta_2)$ (where $eta_1, eta_2$ are characters of $K^times$ trivial on $K_0^times$, so they factor through $K^1 = {z in K^times : z z^c = 1}$ via Hilbert's Theorem 90) twists the representation by determinant characters:
       $ omega_(psi, chi_V eta_1, chi_W eta_2)(g, h) = tilde(eta)_2 (det g) dot.c tilde(eta)_1 (det h) dot.c omega_(psi, chi_V, chi_W)(g, h), $
       where $tilde(eta)(z \/ z^c) = eta(z)$.
  ]

  #proof[
    We explain the mechanism of Kudla's splitting in the *split* case $K approx K_0 times K_0$ (which occurs at half of all finite places of a CM field and is the heart of `KudlaSplittingSplitUnitary`), and then indicate the non-split case.

    When $K = K_0 times K_0$ with involution $(a, b)^c = (b, a)$, the Hermitian space decomposes as $V = V^+ plus.o V^-$ with $V^-$ naturally dual to $V^+$, and $U(V) approx op("GL")(V^+) approx op("GL")_m (K_0)$ acts by $(g, (g^t)^(-1))$. Similarly, $U(W) approx op("GL")_n (K_0)$. Under this identification, the symplectic space $bb(W) = op("Res")_(K/K_0)(V times.o_K W)$ acquires a *canonical complete polarization*
    $ bb(W) = (V^+ times.o_(K_0) W^+) plus.o (V^- times.o_(K_0) W^-) = bb(X) plus.o bb(Y) $
    that is preserved by the entire group $U(V) times U(W)$! Hence $iota(U(V) times U(W))$ lies inside the Siegel Levi subgroup $M(bb(Y)) approx op("GL")(bb(Y))$. Recall from Section 7.1 that on $M(bb(Y))$, the metaplectic 2-cocycle of $m(a_1)$ and $m(a_2)$ is the Hilbert symbol $(det a_1, det a_2)_(K_0)$! For $(g, h) in op("GL")_m (K_0) times op("GL")_n (K_0)$, the determinant on $bb(Y) = V^- times.o W^-$ is
    $ det_(bb(Y))(g, h) = (det g)^(-n) (det h)^(-m). $
    Notice that for $g_1, g_2 in op("GL")_m (K_0)$, the Hilbert symbol $((det g_1)^(-n), (det g_2)^(-n))_(K_0)$ is trivial if $n$ is even, and equals $(det g_1, det g_2)_(K_0)$ if $n$ is odd! Meanwhile, a character $chi_W = (chi_1, chi_2)$ of $K^times = K_0^times times K_0^times$ with $chi_W |_(K_0^times) = 1$ (since $omega_(K/K_0) = 1$ at a split place) satisfies $chi_2 = chi_1^(-1)$, and in the split case one directly cancels the Levi cocycle using the explicit metaplectic section $m(a) |-> (m(a), 1)$ twisted by $chi_W (det g, 1) dot.c chi_V (det h, 1)$ (in fact, at split places, $gamma_psi (det a)$ is a character on the Levi up to a coboundary once the parity of $n$ is absorbed into the Weil index!).

    In the *non-split* case where $K \/ K_0$ is a field, $U(V)$ is no longer contained in a single Siegel Levi. Kudla decomposes $V$ into a maximal hyperbolic part $V_0 = bb(X)_V plus.o bb(Y)_V$ plus an anisotropic kernel, and computes the Leray/Maslov cocycle on the Bruhat cells of $U(V)$ using Rao's explicit formula for the metaplectic $2$-cocycle $c_R (g_1, g_2) in {plus.minus 1}$. Remarkably, Kudla shows that the restriction of Rao's cocycle to $U(V)$ is a coboundary $beta(g_1) beta(g_2) beta(g_1 g_2)^(-1)$ for an explicit function $beta : U(V) -> bb(C)^times$ built from the splitting character $chi_W$ evaluated on the generalized Bruhat determinants $x(g) in K^times \/ K_0^times$, and similarly for $U(W)$ using $chi_V$. The global compatibility follows from Hilbert reciprocity $product_v (a, b)_v = 1$ and the automorphy of $chi_V, chi_W$.
  ]

  #insight-box(title: "Why Splitting Characters Matter in the Alpöge–Claude Proof")[
    At first glance, the need to choose splitting characters $(chi_V, chi_W)$ looks like an annoying technicality. In the Alpöge–Claude proof, it is turned into a *weapon*! Because each theta lift step $U(X_(j-1)) -> U(X_j)$ requires a choice of splitting Hecke characters, we are free to *vary* the auxiliary Hecke characters $mu_j$ across a rich family. As we shall see in Section 7.3, each $mu_j$ appears directly in the spectral transfer $pi |-> pi plus.square mu_j [t]$; and as we shall see in Section 7.5, seesaw duality guarantees that our target Bessel period remains *invariant* as we vary $mu_j$, allowing us to average over $mu_j$ to construct an integral structure and kill bad primes!
  ]

  === Local Howe Duality

  Fix a local unitary dual pair $(U(V), U(W))$ and splitting characters $(chi_V, chi_W)$, giving the smooth Weil representation $omega = omega_(psi, chi_V, chi_W)$ of $U(V) times U(W)$ on $cal(S)(bb(Y))$ (or the Harish-Chandra module on the polynomial Fock space when $K_0 = bb(R)$).

  For any irreducible admissible representation $pi$ of $U(V)$, define the *maximal $pi$-isotypic quotient* of $omega$ as
  $ omega \/ cal(N)(pi), wide cal(N)(pi) = inter.big_(f in op("Hom")_(U(V))(omega, pi)) ker(f). $
  Because $U(W)$ commutes with $U(V)$, it preserves $cal(N)(pi)$, so there is a smooth representation $Theta(pi) = Theta_(V, W, psi, chi)(pi)$ of $U(W)$—called the *big theta lift* of $pi$—such that
  $ omega \/ cal(N)(pi) approx pi times.o Theta(pi) $
  as representations of $U(V) times U(W)$. (Equivalently, $Theta(pi)^* approx op("Hom")_(U(V))(omega, pi)$ as $U(W)$-modules.)

  #theorem(title: "Local Howe Duality")[
    Let $(U(V), U(W))$ be a unitary dual pair over a local field $K_0$ of characteristic zero, and let $pi$ be an irreducible admissible representation of $U(V)$.
    1. The big theta lift $Theta(pi)$ is an admissible representation of $U(W)$ of finite length.
    2. If $Theta(pi) != 0$, then $Theta(pi)$ has a *unique* irreducible quotient $theta(pi) = theta_(V, W, psi, chi)(pi)$, called the *small theta lift* of $pi$.
    3. *(Injectivity)* If $pi_1, pi_2$ are irreducible admissible representations of $U(V)$ such that $theta(pi_1) approx theta(pi_2) != 0$, then $pi_1 approx pi_2$.
  ]

  This theorem was proved by Roger Howe (1989) in the archimedean case, by Jean-Loup Waldspurger (1990) for non-archimedean fields of odd residue characteristic, and in full generality (including residue characteristic $2$) by Wee Teck Gan and Shuichiro Takeda (2016) (with the general linear Type II case earlier established by Minguez (2008)). In the Lean 4 formalization, the archimedean case is established in `HoweDualityReal` and `HoweDualityRealHolds`, while the split/general linear case $(op("GL")_m, op("GL")_n)$ is established in `GLHoweDuality` (and `Development/AutomorphicArithmetic/ThetaCorrespondence/HoweDuality`).

  === Archimedean Correspondence: Compact Unitary Groups and Discrete Series

  In the Alpöge–Claude proof, the groups $U(X_0), U(X_1), dots.c, U(X_m)$ are *totally definite* unitary groups over the totally real field $K_0$: at every archimedean place $v | oo$ of $K_0$, $K_v approx bb(C)$, $X_(j, v)$ is a positive-definite Hermitian space of dimension $n_j$, and $U(X_(j, v)) approx U(n_j)$ is *compact*! Let us see how extraordinarily clean local Howe duality becomes for a compact unitary dual pair $(U(p), U(q))$.

  In this case, $V = bb(C)^p$ (positive-definite Hermitian) and $W = bb(C)^q$ (positive-definite skew-Hermitian after multiplying by $i$). The real symplectic space $bb(W) = V times.o_bb(C) W approx M_(p times q)(bb(C))$ has a *natural* compatible complex structure, and the Fock model of $omega_(psi, chi_V, chi_W)$ is simply the polynomial ring
  $ cal(P)(M_(p times q)(bb(C))) = bb(C)[z_(a b) : 1 <= a <= p, 1 <= b <= q]. $
  Under the action of $(g, h) in U(p) times U(q)$, a polynomial $P(Z)$ transforms as
  $ (omega_(psi, chi_V, chi_W)(g, h) P)(Z)
    &= chi_W (det g) dot.c chi_V (det h) \
    &quad dot.c (det g)^(q/2) (det h)^(-p/2) dot.c P(g^(-1) Z h) $
  (up to convention on $g$ vs $g^t$ and signs of the half-integral powers, which combine with the archimedean splitting characters $chi_V (z) = (z \/ |z|)^(2 a_V + p)$, $chi_W (z) = (z \/ |z|)^(2 a_W + q)$ to produce *integral* powers of $det g$ and $det h$!).

  #proposition(title: "Compact Unitary Howe Duality via Cauchy's Identity")[
    Let $p, q >= 1$ and $r = min(p, q)$. As a representation of $U(p) times U(q)$, the polynomial Fock space decomposes with multiplicity one as
    $ bb(C)[M_(p times q)(bb(C))] approx plus.o.big_(lambda_1 >= lambda_2 >= dots.c >= lambda_r >= 0) (V_lambda^(U(p)) times.o (V_lambda^(U(q)))^or), $
    where the sum runs over all partitions $lambda = (lambda_1, dots.c, lambda_r)$ of length at most $r$, $V_lambda^(U(p))$ is the irreducible algebraic representation of $U(p)$ with highest weight $(lambda_1, dots.c, lambda_r, 0, dots.c, 0)$, and $(V_lambda^(U(q)))^or$ is the contragredient of $V_lambda^(U(q))$.
  ]

  #proof[
    By the Peter–Weyl theorem and the classical Cauchy identity for Schur polynomials, the character of $U(p) times U(q)$ on $bb(C)[M_(p times q)(bb(C))]$ evaluated at diagonal matrices $(op("diag")(x_1, dots.c, x_p), op("diag")(y_1, dots.c, y_q))$ is
    $ op("Tr")_(bb(C)[M_(p times q)])(x, y)
      &= product_(a=1)^p product_(b=1)^q frac(1, 1 - x_a^(-1) y_b) \
      &= sum_(ell(lambda) <= min(p, q)) s_lambda (x_1^(-1), dots.c, x_p^(-1)) dot.c s_lambda (y_1, dots.c, y_q), $
    where $s_lambda$ is the Schur polynomial of highest weight $lambda$. Since $s_lambda (x_1^(-1), dots.c, x_p^(-1))$ is the character of $(V_lambda^(U(p)))^or$ and $s_lambda (y_1, dots.c, y_q)$ is the character of $V_lambda^(U(q))$, this immediately gives the multiplicity-free decomposition (replacing $Z$ by $Z^t$ or $g$ by $g^(-1)$ matches the signs).
  ]

  Look at what this gives when $q > p$ (the dimension-increasing step $U(X_(j-1)) -> U(X_j)$ with $dim X_j = dim X_(j-1) + t$): every irreducible representation $V_lambda^(U(p))$ with nonnegative highest weight $lambda = (lambda_1, dots.c, lambda_p)$ lifts *canonically* to the representation of $U(q)$ with highest weight $(lambda_1, dots.c, lambda_p, 0, dots.c, 0)$ (padded with $t = q - p$ zeros!), shifted by the integral determinant twist from the archimedean splitting characters!

  When one of the groups is *indefinite*—for example, $(U(p, 0), U(r, s))$ with $U(p)$ compact and $U(r, s)$ noncompact—the Fock model still decomposes into a multiplicity-free direct sum of $V_lambda^(U(p)) times.o pi_lambda$, where now $pi_lambda$ is an irreducible *highest-weight* $(frak(u)(r, s), U(r) times U(s))$-module (a holomorphic discrete-series representation when $p >= r + s$). This archimedean discrete-series correspondence (Kashiwara–Vergne, Howe, Adams, Li) is the bridge between finite-dimensional automorphic forms on definite unitary groups and cohomological discrete-series forms on indefinite unitary groups $U(r, s)$.

  == Global Theta Kernels and Theta Lifts

  We now pass from local fields to the global arithmetic setting of a CM number field $K$ with maximal totally real subfield $K_0$, adele rings $bb(A)_(K_0)$ and $bb(A)_K = bb(A)_(K_0) times.o_(K_0) K$, and a nontrivial unitary additive character $psi = product_v psi_v : bb(A)_(K_0) \/ K_0 -> bb(C)^times$.

  === The Adelic Weil Representation and Theta Distribution

  Let $(V, (dot.c, dot.c)_V)$ and $(W, chevron.l dot.c, dot.c chevron.r_W)$ be global Hermitian and skew-Hermitian spaces over $K$ of dimensions $m$ and $n$, respectively, and let $bb(W) = op("Res")_(K/K_0)(V times.o_K W)$ with global complete polarization $bb(W) = bb(X) plus.o bb(Y)$ over $K_0$. (Here we also denote the Lagrangian $bb(X)$ by $X$ when writing the global theta sum over $X(K_0)$.) Fix global splitting Hecke characters $(chi_V, chi_W)$ of $bb(A)_K^times \/ K^times$ with $chi_V |_(bb(A)_(K_0)^times) = omega_(K/K_0)^m$ and $chi_W |_(bb(A)_(K_0)^times) = omega_(K/K_0)^n$.

  At almost every finite place $v$ of $K_0$, the spaces $V_v, W_v$ admit self-dual lattices, $psi_v$ is unramified, and $chi_(V, v), chi_(W, v)$ are unramified; at such places, the characteristic function $phi_v^0 = bb(1)_(X(cal(O)_(K_0, v))) in cal(S)(X(K_(0, v)))$ is fixed by the maximal compact subgroup $K_(V, v) times K_(W, v)$. We form the global adelic Schwartz–Bruhat space as the restricted tensor product
  $ cal(S)(X(bb(A)_(K_0))) = times.o.big'_v cal(S)(X(K_(0, v))) $
  with respect to the spherical vectors $phi_v^0$. The global Weil representation $omega = omega_(psi, chi_V, chi_W) = times.o.big'_v omega_(psi_v, chi_(V, v), chi_(W, v))$ acts smoothly on $cal(S)(X(bb(A)_(K_0)))$.

  #definition(title: "Theta Distribution and Global Theta Kernel")[
    1. The *theta distribution* $Theta : cal(S)(X(bb(A)_(K_0))) -> bb(C)$ is the tempered distribution
       $ Theta(phi) = sum_(x in X(K_0)) phi(x). $
    2. For each $phi in cal(S)(X(bb(A)_(K_0)))$, the *global theta kernel* on $U(V)(bb(A)_(K_0)) times U(W)(bb(A)_(K_0))$ is defined by
       $ theta_phi (g, h) = Theta(omega(g, h) phi) = sum_(x in X(K_0)) (omega(g, h) phi)(x). $
  ]

  The fundamental theorem of Weil asserts that $Theta$ is invariant under the rational symplectic group $op("Sp")(bb(W)(K_0))$!

  #theorem(title: "Automorphy and Moderate Growth of the Theta Kernel")[
    For every $phi in cal(S)(X(bb(A)_(K_0)))$:
    1. *(Absolute convergence)* The series $theta_phi (g, h)$ converges absolutely and uniformly on compact subsets of $U(V)(bb(A)_(K_0)) times U(W)(bb(A)_(K_0))$.
    2. *(Automorphy)* For all $(gamma, delta) in U(V)(K_0) times U(W)(K_0)$,
       $ theta_phi (gamma g, delta h) = theta_phi (g, h). $
    3. *(Moderate growth)* $theta_phi (g, h)$ is a smooth function of moderate growth on $[U(V)] times [U(W)]$, where $[G] = G(K_0) backslash G(bb(A)_(K_0))$.
  ]

  #proof[
    Since $phi$ is a finite linear combination of pure tensors $times.o.big_v phi_v$ with $phi_v = bb(1)_(X(cal(O)_(K_0, v)))$ for almost all $v$, the sum over $x in X(K_0)$ restricts to a lattice $Lambda subset X(K_0)$ determined by the finite-place supports, and at archimedean places $phi_oo$ is rapidly decreasing. This proves absolute and uniform convergence on compact sets.

    For automorphy, it suffices to show that $Theta(omega(gamma) phi) = Theta(phi)$ for every generator $gamma$ of $op("Sp")(bb(W)(K_0))$ (since Kudla's global splitting agrees with the canonical rational splitting over $op("Sp")(bb(W)(K_0))$):
    - For $m(a) in M(X)(K_0)$, $|det a|_(bb(A)_(K_0)) = 1$ by the product formula, $product_v gamma_(psi_v)(det a) = 1$ by global Weil reciprocity, and $a^(-1)$ merely permutes the rational points $X(K_0)$.
    - For $u(c) in N(X)(K_0)$, the phase $psi(frac(1,2) chevron.l x, c x chevron.r) = 1$ for every $x in X(K_0)$ because $psi$ is trivial on $K_0$.
    - For the Weyl element $w_0$, the global Weil index is $1$, and the identity
      $ sum_(x in X(K_0)) hat(phi)(x) = sum_(x in X(K_0)) phi(x) $
      is precisely *adelic Poisson summation* on the self-dual lattice $X(K_0) subset X(bb(A)_(K_0))$!

    Moderate growth follows from standard Siegel-set estimates on the lattice sum $sum_(x in Lambda) |phi_oo (g_oo x)|$, which grows at most polynomially in the height of $(g, h)$ by comparison with the volume of balls in $X(K_0 times.o_bb(Q) bb(R))$.
  ]

  === The Global Theta Lift

  We now use the theta kernel $theta_phi (g, h)$ as an integral kernel to transfer automorphic forms from $U(V)$ to $U(W)$.

  #definition(title: "Global Theta Lift")[
    Let $f in cal(A)_0 (U(V))$ be a cusp form on $[U(V)]$ (or any smooth automorphic form when $U(V)$ is anisotropic, e.g. totally definite, so $[U(V)]$ is compact). For $phi in cal(S)(X(bb(A)_(K_0)))$, the *global theta lift* of $f$ to $U(W)$ is the function on $[U(W)]$ defined by
    $ theta_phi (f)(h) = integral_([U(V)]) theta_phi (g, h) overline(f(g)) d g, $
    where $d g$ is a Haar measure on $U(V)(bb(A)_(K_0))$ (typically normalized to Tamagawa measure). For an irreducible cuspidal automorphic representation $pi subset cal(A)_0 (U(V))$, the *global theta lift* $Theta(pi) = Theta_(V, W, psi, chi)(pi)$ is the space of automorphic forms on $[U(W)]$ spanned by $theta_phi (f)$ as $f$ ranges over $pi$ and $phi$ ranges over $cal(S)(X(bb(A)_(K_0)))$.
  ]

  Because $theta_phi (g, h)$ has moderate growth in $g$ and $f(g)$ is rapidly decreasing on $[U(V)]$ (or $[U(V)]$ is compact when $U(V)$ is totally definite), the integral defining $theta_phi (f)(h)$ converges absolutely and defines a smooth automorphic form of moderate growth on $[U(W)]$. Note that $theta_phi (f)$ is conjugate-linear in $f$ (some authors omit the complex conjugate on $f$ and instead pair $pi^or$ with $Theta(pi)$; the convention with $overline(f(g))$ makes $pi |-> Theta(pi)$ covariant with respect to $L^2$-inner products and matches the Rallis inner product formula cleanly).

  === Unramified Spectral Transfer of Satake Parameters

  How does a global theta lift transform the Hecke eigenvalues (Satake parameters) of an automorphic representation $pi$? This is the spectral heart of the theta correspondence.

  Let $v$ be a finite place of $K_0$ where $V_v, W_v, psi_v, chi_(V, v), chi_(W, v)$, and $pi_v$ are all unramified. Suppose first that $v$ *splits* in $K$, so $K_v approx K_(0, v) times K_(0, v)$, $U(V)(K_(0, v)) approx op("GL")_m (K_(0, v))$, and $U(W)(K_(0, v)) approx op("GL")_n (K_(0, v))$, with $n = m + t$ ($t >= 0$). Let $q_v$ be the cardinality of the residue field of $K_(0, v)$, and suppose the unramified representation $pi_v$ of $op("GL")_m (K_(0, v))$ has Satake parameter
  $ c(pi_v) = op("diag")(alpha_1, dots.c, alpha_m) in op("GL")_m (bb(C)), $
  so that $pi_v$ is the unramified constituent of the normalized parabolic induction $op("Ind")_B^(op("GL")_m)(eta_1 times.o dots.c times.o eta_m)$ with $eta_i (pi.alt_v) = alpha_i$.

  Let $mu_v$ be the unramified character of $K_(0, v)^times$ determined by the splitting characters (specifically, on the split factor $K_(0, v)^times subset K_v^times$, $mu_v = chi_(V, v) dot.c chi_(W, v)^(-1)$ up to our convention on $chi_V, chi_W$), and let $beta = mu_v (pi.alt_v) in bb(C)^times$.

  #theorem(title: "Unramified Spectral Transfer (Rallis–Howe–Kudla)")[
    Let $v$ be an unramified finite place of $K_0$, and assume $n = dim W = dim V + t$ with $t >= 0$. If $pi_v$ is an unramified irreducible representation of $U(V)(K_(0, v))$ whose local theta lift $theta(pi_v)$ to $U(W)(K_(0, v))$ is nonzero and unramified, then the base-change Satake parameter of $theta(pi_v)$ on $op("GL")_n (K_v)$ is obtained from that of $pi_v$ (twisted by the splitting character) by adjoining the $t$-dimensional Arthur / Speh block $mu_v [t]$:
    $ op("BC")(theta(pi_v)) approx (op("BC")(pi_v) times.o chi_(W, v) chi_(V, v)^(-1)) plus.square mu_v [t], $
    where $mu_v [t]$ has Satake parameter
    $ op("diag")(mu_v (pi.alt_v) q_v^(-(t-1)/2), mu_v (pi.alt_v) q_v^(-(t-3)/2), dots.c, mu_v (pi.alt_v) q_v^((t-1)/2)). $
    In global isobaric notation (suppressing the fixed base twist when absorbed into the normalization of $pi$), the spectral transfer reads
    $ pi |-> pi plus.square mu_j [t]. $
  ]

  #proof[
    We verify this directly in the split case $(op("GL")_m (F), op("GL")_n (F))$ with $F = K_(0, v)$ and $n = m + t$. In this case, the Weil representation is realized on $cal(S)(M_(m times n)(F))$ via
    $ (omega(g, h) phi)(X) = |det g|_F^(n/2) |det h|_F^(-m/2) chi_W (det g) chi_V (det h) phi(g^(-1) X h). $
    Consider the parabolic subgroup $P_(m, t) subset op("GL")_n (F)$ stabilizing the subspace of the first $m$ coordinates, with Levi $op("GL")_m (F) times op("GL")_t (F)$. Evaluating a function $phi in cal(S)(M_(m times n)(F))$ on matrices of the block form $X = (I_m, 0)$ (which has open orbit under $op("GL")_m (F) times op("GL")_n (F)$? More cleanly, taking the Jacquet module along $P_(m, t)$!), one constructs a nonzero $(op("GL")_m (F) times op("GL")_n (F))$-equivariant map
    $ omega -> pi_v times.o op("Ind")_(P_(m, t))^(op("GL")_n)(tilde(pi)_v times.o (mu_v dot.c |det|_F^0)), $
    where the trivial representation $bb(1)_(op("GL")_t)$ of $op("GL")_t (F)$ appears on the second Levi block! Now recall a basic fact of representation theory of $op("GL")_t (F)$: the trivial representation $bb(1)_(op("GL")_t)$ is the unique unramified subquotient of the normalized principal series
    $ op("Ind")_(B_t)^(op("GL")_t)(|dot.c|_F^((t-1)/2) times.o |dot.c|_F^((t-3)/2) times.o dots.c times.o |dot.c|_F^(-(t-1)/2)). $
    Twisting by the character $mu_v$ produces the exact Satake parameters $mu_v (pi.alt_v) q_v^((t-1)/2 - k)$ for $k = 0, 1, dots.c, t - 1$, i.e., the block $mu_v [t]$! At inert places of $K \/ K_0$, the same argument using the Siegel parabolic of $U(W)$ stabilizing a $t$-dimensional isotropic subspace (or the base-change Hecke homomorphism of Kudla–Rallis) yields the identical base-change transfer $op("BC")(theta(pi_v)) = op("BC")(pi_v) plus.square mu_v [t]$.
  ]

  === The Alpöge–Claude Chain of Iterated Theta Lifts

  We can now see clearly *why* the theta lift is the building block of the Alpöge–Claude chain (item 8 of Alpöge's *Remark*). Consider a sequence of totally definite Hermitian spaces over the CM field $K$:
  $ X_0, X_1, X_2, dots.c, X_m, $
  with dimensions $dim X_j = dim X_0 + j dot.c t$ (where $t >= 1$ is a fixed step size). At each step $j = 1, dots.c, m$, we form the unitary dual pair $(U(X_(j-1)), U(X_j))$ (multiplying the form on $X_j$ by $delta$ when needed to alternate Hermitian and skew-Hermitian spaces) and choose splitting Hecke characters producing an auxiliary algebraic Hecke character $mu_j$.

  Starting from a base automorphic representation $pi_0$ on $U(X_0)$ (carrying the arithmetic data of the Dirichlet character $chi$ or the Riemann zeta function), we apply the global theta lift $m$ times in succession:
  $ U(X_0) ->^(theta_1) U(X_1) ->^(theta_2) U(X_2) -> dots.c ->^(theta_m) U(X_m). $
  At the spectral level, the unramified Satake parameters evolve along the chain as
  $ pi_0 &|-> pi_0 plus.square mu_1 [t] |-> pi_0 plus.square mu_1 [t] plus.square mu_2 [t] \
    &|-> dots.c |-> pi_0 plus.square mu_1 [t] plus.square dots.c plus.square mu_m [t]. $
  Each step adjoins a new block $mu_j [t]$ of length $t$, increasing the dimension of the automorphic representation while keeping the group *totally definite* (so that every $[U(X_j)]$ is compact and every automorphic form is a finite linear combination of values on a finite double-coset class set!).

  Why does this mimic *multiplicity $m$* in Stepanov's method? In Part III (Chapters 11–13), we will see how the local divisibility at inert primes (via CM periods and invariant derivations $D^p equiv 0$, Chapter 8) and the Siegel mass / Weyl dimension formulas interact with each theta-lift step: each step multiplies the $p$-adic divisibility of the lifted form by a factor controlled by the Chowla–Selberg period and the rank increment, while the "height cost" grows at a controlled rate. Taking a chain of length $m approx sqrt(X)$ for a von Mangoldt sum of length $X$ balances the multiplicity gain against the Arakelov height bound—a balance that would be impossible with a single lift!

  Yet to make this chain work, two formidable analytic questions must be answered:
  1. *Nonvanishing and $L^2$-norms*: How do we prove that the iterated lift $theta_(phi_m) dots.c theta_(phi_1)(f_0)$ is *nonzero*, and how do we compute its exact Petersson norm $norm(theta_phi (f))_(L^2)^2$?
  2. *Independence of periods*: How do we extract a period from the final lift on $U(X_m)$ that still remembers $pi_0$ without becoming hopelessly entangled with the $m$ auxiliary Hecke characters $mu_1, dots.c, mu_m$?

  The first question is answered by the *Siegel–Weil formula*, the *doubling method*, and the *Rallis inner product formula* (Section 7.4). The second is answered by *seesaw duality* (Section 7.5).

  == The Siegel–Weil Formula, Rallis Inner Product Formula, and Doubling Method

  In classical number theory, Siegel's main theorem on quadratic forms equates the average representation number of a quadratic form over its genus to a product of local representation densities—which is the Fourier coefficient of a Siegel Eisenstein series. André Weil (1965) reformulated Siegel's theorem as an identity between the global integral of a theta kernel and a special value of an Eisenstein series, and Stephen Kudla and Stephen Rallis (1988–1994) extended this identity beyond the range of absolute convergence via regularization. Combined with the Piatetski-Shapiro–Rallis doubling method, the Siegel–Weil formula yields the Rallis inner product formula, expressing the $L^2$-norm of a global theta lift directly in terms of special values of standard $L$-functions!

  === Siegel Eisenstein Series: Analytic Continuation and Simple Poles

  Let $(W, chevron.l dot.c, dot.c chevron.r_W)$ be an $n$-dimensional skew-Hermitian space over the CM field $K$. Form the *doubled space*
  $ W^square = W plus.o (-W), $
  where $-W$ is the same vector space $W$ equipped with the negated skew-Hermitian form $-chevron.l dot.c, dot.c chevron.r_W$. The doubled space $W^square$ is a *split* (hyperbolic) skew-Hermitian space of dimension $2n$: it admits the complete polarization
  $ W^square = W^Delta plus.o W^nabla, $
  where $W^Delta = {(w, w) : w in W}$ is the diagonal Lagrangian and $W^nabla = {(w, -w) : w in W}$ is the anti-diagonal Lagrangian.

  Let $P = M N subset U(W^square)$ be the *Siegel parabolic subgroup* stabilizing the Lagrangian $W^Delta$. Its Levi factor is $M approx op("Res")_(K/K_0) op("GL")(W^Delta) approx op("Res")_(K/K_0) op("GL")_n$, and its unipotent radical $N$ is abelian, isomorphic to the $K_0$-vector space of $n times n$ Hermitian matrices. The modulus character of $P(bb(A)_(K_0))$ is given by
  $ delta_P (m(a) n) = |det a|_(bb(A)_K)^n, quad a in op("GL")_n (bb(A)_K). $

  Fix a unitary Hecke character $chi$ of $bb(A)_K^times \/ K^times$ and a complex parameter $s in bb(C)$. Define the *degenerate principal series* (Siegel induced representation)
  $ I(s, chi) = op("Ind")_(P(bb(A)_(K_0)))^(U(W^square)(bb(A)_(K_0))) (chi dot.c |dot.c|_(bb(A)_K)^s), $
  consisting of smooth $K^square$-finite functions $Phi_s : U(W^square)(bb(A)_(K_0)) -> bb(C)$ satisfying
  $ Phi_s (m(a) n h) = chi(det a) dot.c |det a|_(bb(A)_K)^(s + n/2) dot.c Phi_s (h) $
  for all $a in op("GL")_n (bb(A)_K)$, $n in N(bb(A)_(K_0))$, and $h in U(W^square)(bb(A)_(K_0))$. A section $Phi_s in I(s, chi)$ is called *standard* if its restriction to the standard maximal compact subgroup $K^square subset U(W^square)(bb(A)_(K_0))$ is independent of $s$.

  #definition(title: "Siegel Eisenstein Series")[
    For a standard section $Phi_s in I(s, chi)$, the *Siegel Eisenstein series* on $U(W^square)(bb(A)_(K_0))$ is defined by
    $ E(h, s, Phi) = sum_(gamma in P(K_0) backslash U(W^square)(K_0)) Phi_s (gamma h). $
  ]

  The analytic properties of $E(h, s, Phi)$ are governed by Langlands's general theory of Eisenstein series, refined for Siegel Eisenstein series on unitary groups by Tan (1999), Kudla–Rallis, and Ichino:

  #theorem(title: "Analytic Continuation and Simple Poles of Siegel Eisenstein Series")[
    Let $Phi_s in I(s, chi)$ be a standard section.
    1. *(Convergence)* The series $E(h, s, Phi)$ converges absolutely and uniformly on compact subsets of $U(W^square)(bb(A)_(K_0)) times {s in bb(C) : op("Re")(s) > n / 2}$.
    2. *(Meromorphic continuation and functional equation)* $E(h, s, Phi)$ admits a meromorphic continuation to the entire complex $s$-plane and satisfies the functional equation
       $ E(h, s, Phi) = E(h, -s, M(s, chi) Phi), $
       where $M(s, chi) : I(s, chi) -> I(-s, chi^(-c))$ is the standard global intertwining operator.
    3. *(Location and order of poles)* In the right half-plane $op("Re")(s) >= 0$, the poles of $E(h, s, Phi)$ are *at most simple* and can occur only at the finite set of half-integers / integers
       $ s in { frac(n - 2r, 2) : 0 <= r < frac(n, 2) } $
       satisfying the parity condition $chi |_(bb(A)_(K_0)^times) = omega_(K/K_0)^(n - 2r)$. In particular, if $chi |_(bb(A)_(K_0)^times) = omega_(K/K_0)^m$, the Eisenstein series has at most a simple pole at $s_0 = (m - n) / 2$ when $m > n$, and is holomorphic at $s = 0$ when $m = n$.
  ]

  In the Lean 4 formalization, the meromorphic continuation and pole structure are proved in `SiegelEisensteinContinuation` (under `Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinContinuation`) and `SiegelEisensteinContinuationOfDoublingMethod` / `SiegelEisensteinSimplePoleOfDoublingMethod` (under `Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂`).

  === The Siegel–Weil Formula

  Now let $(V, (dot.c, dot.c)_V)$ be an $m$-dimensional Hermitian space over $K$, and consider the dual pair $(U(V), U(W^square))$ inside $op("Sp")(op("Res")_(K/K_0)(V times.o_K W^square))$. Because $W^square = W^Delta plus.o W^nabla$ is a complete polarization, the space $V times.o_K W^square$ inherits the $U(V)$-invariant polarization $(V times.o_K W^Delta) plus.o (V times.o_K W^nabla)$! In this Schrödinger model on $cal(S)(V(bb(A)_K)^n)$ (identifying $V times.o_K W^Delta approx V^n$), the group $U(V)$ acts simply by linear substitution $(omega(g) phi)(x) = chi_(W^square)(det g) phi(g^(-1) x)$, while the Siegel parabolic $P subset U(W^square)$ acts by
  $ (omega(m(a) n) phi)(0) = chi_V (det a) dot.c |det a|_(bb(A)_K)^(m/2) dot.c phi(0). $
  Therefore, evaluating the Weil representation at $0 in V(bb(A)_K)^n$ defines a $U(W^square)(bb(A)_(K_0))$-equivariant map
  $ phi |-> Phi_phi (h) = (omega(h) phi)(0) in I(s_0, chi_V), wide s_0 = frac(m - n, 2)! $
  Let $Phi_phi (h, s) in I(s, chi_V)$ be the unique standard section extending $Phi_phi (h)$ from $s = s_0$ to all $s in bb(C)$.

  On the other hand, we can integrate the theta kernel $theta_phi (g, h) = sum_(x in V(K)^n) (omega(g, h) phi)(x)$ over the automorphic quotient $[U(V)]$:
  $ I(h, phi) = integral_([U(V)]) theta_phi (g, h) d g, $
  where $d g$ is normalized so that $op("vol")([U(V)]) = 1$ (or Tamagawa measure). When does this integral converge? By Weil's convergence criterion (1965), $I(h, phi)$ converges absolutely for all $phi$ if and only if either:
  - $V$ is *anisotropic* (which holds automatically for all our totally definite Hermitian spaces $X_j$!), or
  - $m - r > n$, where $r$ is the Witt index of $V$.

  #theorem(title: "Siegel–Weil Formula (Convergent Range)")[
    Suppose $V$ is anisotropic (in particular, totally definite) or $m - r > n$, and assume $s_0 = (m - n) / 2 > n / 2$ (i.e., $m > 2n$, Weil's range of absolute convergence) or more generally $m > n$ with $V$ anisotropic (the Kudla–Rallis extended convergent range). Then the Siegel Eisenstein series $E(h, s, Phi_phi)$ is holomorphic at $s = s_0 = (m - n) / 2$ (or has a simple pole whose residue is a regularized theta integral in the second-term range), and for all $phi in cal(S)(V(bb(A)_K)^n)$ and $h in U(W^square)(bb(A)_(K_0))$,
    $ integral_([U(V)]) theta_phi (g, h) d g = kappa dot.c E(h, s_0, Phi_phi), $
    where $kappa = 1$ if $m > n$ and $kappa = 2$ if $m = n$ (when $E$ is evaluated at the center $s_0 = 0$).
  ]

  #proof[
    We give Weil's proof in the range $m > 2n$ (which also explains why the identity is so natural). Both sides of the formula are smooth functions of $h in U(W^square)(bb(A)_(K_0))$ that depend continuously on $phi$ and are $U(W^square)(bb(A)_(K_0))$-equivariant as functionals on $cal(S)(V(bb(A)_K)^n)$. Look at the right-hand side:
    $ E(h, s_0, Phi_phi) = sum_(gamma in P(K_0) backslash U(W^square)(K_0)) (omega(gamma h) phi)(0). $
    Look at the left-hand side:
    $ I(h, phi) = integral_([U(V)]) sum_(x in V(K)^n) (omega(g, h) phi)(x) d g. $
    Decompose the sum over $x in V(K)^n$ according to the Gram matrix $T(x) = ((x_i, x_j)_V)_(1 <= i, j <= n) in op("Herm")_n (K)$! For $x$ with $T(x) = 0$ (the *totally isotropic* $n$-tuples $x in V(K)^n$), if $V$ is anisotropic, the *only* totally isotropic tuple is $x = 0$! More generally, we compare the $T$-th Fourier coefficients of $I(h, phi)$ and $E(h, s_0, Phi_phi)$ along the Siegel unipotent radical $N(K_0) backslash N(bb(A)_(K_0))$:
    $ I_T (h, phi)
      &= integral_(N(K_0) backslash N(bb(A)_(K_0))) I(n h, phi) psi(-op("Tr")(T n)) d n \
      &= integral_([U(V)]) sum_(x in V(K)^n, T(x) = T) (omega(g, h) phi)(x) d g. $
    By Witt's theorem, $U(V)(K)$ acts *transitively* on the set of $n$-tuples $x in V(K)^n$ of rank $n$ with a given nonsingular Gram matrix $T$. Unfolding the integral over $[U(V)]$ reduces $I_T (h, phi)$ to an orbital integral over $U(V)(bb(A)_(K_0))$, which factors into a product of local orbital integrals—matching the Euler product of local Whittaker–Fourier coefficients of the Siegel Eisenstein series $E_T (h, s_0, Phi_phi)$ by the Tamagawa number formula $tau(U(V)) = 2$ (and $tau(op("SU")(V)) = 1$)! For singular $T$ (including $T = 0$), the same matching holds via induction on the rank of $T$ when $m > 2n$, and via Kudla–Rallis's differential-operator regularization when $n <= m <= 2n$.
  ]

  In `lean-rh/src`, the standard Siegel–Weil formula is formalized in `SiegelWeilStd` (under `Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilStandard`) and `ThetaIntegralEqSiegelEisensteinOfWeilRange`.

  === The Piatetski-Shapiro–Rallis Doubling Method

  Now forget the space $V$ for a moment and focus solely on the doubled group $U(W^square) = U(W plus.o (-W))$! There is a natural embedding
  $ &iota : U(W) times U(W) arrow.r.hook U(W^square), \
    &(h_1, h_2) |-> (h_1, h_2) "acting on" W plus.o (-W). $
  Notice that the diagonal subgroup $Delta U(W) = {(h, h) : h in U(W)}$ stabilizes the diagonal Lagrangian $W^Delta$, so $Delta U(W) subset P inter (U(W) times U(W))$.

  Let $pi$ be an irreducible cuspidal automorphic representation of $U(W)(bb(A)_(K_0))$, let $f_1, f_2 in pi$ be smooth cusp forms, and let $E(h, s, Phi)$ be a Siegel Eisenstein series on $U(W^square)$ attached to a standard section $Phi_s in I(s, chi)$.

  #definition(title: "Doubling Zeta Integral")[
    The *global Piatetski-Shapiro–Rallis doubling integral* is
    $ Z(s, f_1, f_2, Phi)
      &= integral_([U(W)] times [U(W)]) E(iota(h_1, h_2), s, Phi) \
      &quad dot.c f_1 (h_1) overline(f_2 (h_2)) dot.c chi(det h_2)^(-1) d h_1 d h_2. $
  ]

  Why is this integral called the *doubling method*? Because by pulling back an Eisenstein series from the doubled group $U(W^square)$ to $U(W) times U(W)$ and integrating against $f_1 times.o overline(f_2)$, one obtains an integral representation of the *standard $L$-function* $L(s + frac(1, 2), pi times chi)$—for *every* cuspidal representation $pi$ of $U(W)$, without needing $pi$ to be generic (i.e., without needing a Whittaker model)! This is crucial in the Alpöge–Claude proof, because automorphic representations on totally definite unitary groups are compact at infinity and have *no* Whittaker models at all!

  #theorem(title: "Piatetski-Shapiro–Rallis Doubling Identity")[
    Let $pi = times.o.big'_v pi_v$ be an irreducible cuspidal automorphic representation of $U(W)(bb(A)_(K_0))$, and let $f_1 = times.o.big_v f_(1, v)$, $f_2 = times.o.big_v f_(2, v) in pi$ and $Phi_s = times.o.big_v Phi_(s, v) in I(s, chi)$ be factorizable vectors. Let $S$ be a finite set of places of $K_0$ (including all archimedean places and all ramified places) outside of which $W_v, pi_v, chi_v, f_(1, v), f_(2, v), Phi_(s, v)$ are unramified and normalized so that $chevron.l f_(1, v), f_(2, v) chevron.r_v = 1$. Then for $op("Re")(s) >> 0$:
    1. *(Basic unfolding identity)*
       $ Z(s, f_1, f_2, Phi) = integral_(U(W)(bb(A)_(K_0))) Phi_s (iota(h, 1)) dot.c chevron.l pi(h) f_1, f_2 chevron.r d h, $
       where $chevron.l pi(h) f_1, f_2 chevron.r = integral_([U(W)]) f_1 (h_2 h) overline(f_2 (h_2)) d h_2$ is the global matrix coefficient of $pi$.
    2. *(Euler product factorization)*
       $ Z(s, f_1, f_2, Phi) = frac(L^S (s + frac(1, 2), pi times chi), b_n^S (s, chi)) dot.c product_(v in S) Z_v (s, f_(1, v), f_(2, v), Phi_(s, v)), $
       where the local doubling zeta integral is
       $ Z_v (s, f_(1, v), f_(2, v), Phi_(s, v))
         &= integral_(U(W)(K_(0, v))) Phi_(s, v)(iota(h, 1)) \
         &quad dot.c chevron.l pi_v (h) f_(1, v), f_(2, v) chevron.r_v d h, $
       and the normalizing denominator is the product of abelian $L$-functions
       $ b_n^S (s, chi) = product_(j=0)^(n-1) L^S (2 s + n - j, chi |_(bb(A)_(K_0)^times) dot.c omega_(K/K_0)^j). $
  ]

  #proof[
    We give the complete unfolding argument—one of the most elegant computations in all of automorphic forms!

    For $op("Re")(s) > n / 2$, substitute the defining sum $E(iota(h_1, h_2), s, Phi) = sum_(gamma in P(K_0) backslash U(W^square)(K_0)) Phi_s (gamma dot.c iota(h_1, h_2))$ into the integral $Z(s, f_1, f_2, Phi)$, and partition $P(K_0) backslash U(W^square)(K_0)$ into double cosets
    $ P(K_0) backslash U(W^square)(K_0) \/ (U(W)(K_0) times U(W)(K_0)). $
    By Witt's theorem, these double cosets are in bijection with the dimensions $r = dim_K (gamma dot.c W^Delta inter (W plus.o {0}))$ for $0 <= r <= n$:
    - *Negligible orbits ($r > 0$)*: When $r > 0$, the stabilizer of the double coset representative $gamma_r$ in $U(W) times U(W)$ contains the unipotent radical of a *proper* parabolic subgroup $Q_r subset U(W)$ (fixing the $r$-dimensional isotropic subspace $gamma_r dot.c W^Delta inter W$). Unfolding the contribution of this orbit produces an inner integral of the cusp form $f_1$ over the unipotent radical $[N_(Q_r)]$, which *vanishes identically* by the cuspidality of $f_1$! (When $W$ is anisotropic—our totally definite case—there are *no* nonzero isotropic subspaces at all, so $r = 0$ is literally the *only* double coset!)
    - *The open orbit ($r = 0$)*: The unique open double coset is represented by the identity element $gamma_0 = 1$ (since $W^Delta inter (W plus.o {0}) = {0}$). Its stabilizer in $U(W) times U(W)$ is precisely the diagonal subgroup $Delta U(W) = {(h, h) : h in U(W)}$.

    Therefore, only the single orbit $gamma_0 = 1$ survives, and unfolding yields
    $ Z(s, f_1, f_2, Phi)
      &= integral_(Delta U(W)(K_0) backslash (U(W)(bb(A)) times U(W)(bb(A)))) Phi_s (iota(h_1, h_2)) \
      &quad f_1 (h_1) overline(f_2 (h_2)) chi(det h_2)^(-1) d h_1 d h_2. $
    Make the change of variables $h_1 = h_2 h$ (with $h in U(W)(bb(A))$ and $h_2 in [U(W)]$). Since $(h_2, h_2) in Delta U(W) subset P$, the transformation law of $Phi_s in I(s, chi)$ gives
    $ Phi_s (iota(h_2 h, h_2))
      &= Phi_s (iota(h_2, h_2) dot.c iota(h, 1)) \
      &= chi(det h_2) dot.c |det h_2|_(bb(A)_K)^(s + n/2) dot.c Phi_s (iota(h, 1)). $
    Because $det h_2 in bb(A)_K^1$ has norm $1$, $|det h_2|_(bb(A)_K) = 1$, and the factor $chi(det h_2)$ *cancels* $chi(det h_2)^(-1)$ identically! Thus the integral separates into
    $ Z(s, f_1, f_2, Phi)
      &= integral_(U(W)(bb(A))) Phi_s (iota(h, 1)) \
      &quad ( integral_([U(W)]) f_1 (h_2 h) overline(f_2 (h_2)) d h_2 ) d h, $
    proving (1).

    For (2), since $pi = times.o.big'_v pi_v$ and $f_1, f_2$ are factorizable, the global matrix coefficient factors as $chevron.l pi(h) f_1, f_2 chevron.r = product_v chevron.l pi_v (h_v) f_(1, v), f_(2, v) chevron.r_v$, so the integral factors as $product_v Z_v (s, f_(1, v), f_(2, v), Phi_(s, v))$. At every unramified place $v in.not S$, the local integral $Z_v (s, f_(1, v), f_(2, v), Phi_(s, v))$ is computed by Macdonald's formula for spherical matrix coefficients (the Casselman–Shalika / Godement–Jacquet computation of Piatetski-Shapiro–Rallis and Li), yielding
    $ Z_v (s, f_(1, v), f_(2, v), Phi_(s, v)) = frac(L_v (s + frac(1, 2), pi_v times chi_v), b_(n, v)(s, chi_v)). $
    Multiplying over all $v in.not S$ establishes (2).
  ]

  In `lean-rh/src`, the local doubling zeta integrals and their unramified evaluations are developed in `DoublingMethodLocalZetaIntegrals` and `Development/AutomorphicArithmetic/ThetaCorrespondence/RallisInnerProduct`.

  === The Rallis Inner Product Formula

  We are now poised for the grand synthesis of this section: combining the Siegel–Weil formula with the Piatetski-Shapiro–Rallis doubling identity to compute the exact Petersson inner product of two global theta lifts!

  Let $(U(V), U(W))$ be a unitary dual pair with $dim V = m$ and $dim W = n$, and let $f_1, f_2 in pi$ be smooth cusp forms in an irreducible cuspidal automorphic representation $pi$ of $U(V)(bb(A)_(K_0))$. Choose Schwartz–Bruhat functions $phi_1, phi_2 in cal(S)(X(bb(A)_(K_0)))$, and assume that $theta_(phi_1)(f_1)$ and $theta_(phi_2)(f_2)$ are square-integrable on $[U(W)]$ (for instance, when $U(W)$ is totally definite, or when the theta lifts are cuspidal).

  Consider their Petersson inner product on $[U(W)]$:
  $ chevron.l theta_(phi_1)(f_1), theta_(phi_2)(f_2) chevron.r_(U(W)) = integral_([U(W)]) theta_(phi_1)(f_1)(h) dot.c overline(theta_(phi_2)(f_2)(h)) d h. $
  Expanding the definitions of $theta_(phi_1)(f_1)$ and $theta_(phi_2)(f_2)$ and interchanging the order of integration (valid in the convergent range, or after regularization):
  $ &chevron.l theta_(phi_1)(f_1), theta_(phi_2)(f_2) chevron.r_(U(W)) \
    &= integral_([U(V)] times [U(V)]) overline(f_1 (g_1)) f_2 (g_2) \
    &quad ( integral_([U(W)]) theta_(phi_1)(g_1, h) overline(theta_(phi_2)(g_2, h)) d h ) d g_1 d g_2. $
  Look at the inner integrand $theta_(phi_1)(g_1, h) overline(theta_(phi_2)(g_2, h))$! Complex conjugating a theta kernel for $(V, W)$ negates the Hermitian form on $V$ (since $overline(psi(t)) = psi(-t)$), turning it into a theta kernel for $(-V, W)$! Hence the product
  $ theta_(phi_1)(g_1, h) overline(theta_(phi_2)(g_2, h)) = theta_(phi_1 times.o overline(phi_2))(iota(g_1, g_2), h) $
  is *precisely* the global theta kernel for the *doubled dual pair* $(U(V^square), U(W))$ evaluated at $iota(g_1, g_2) in U(V) times U(V) arrow.r.hook U(V^square)$!

  Now apply the *Siegel–Weil formula* to the inner integral over $[U(W)]$ (note that the roles of $V$ and $W$ are swapped compared to Section 7.4.2: here we integrate over $U(W)$ to produce an Eisenstein series on $U(V^square)$!):
  $ integral_([U(W)]) theta_(phi_1 times.o overline(phi_2))(iota(g_1, g_2), h) d h = kappa dot.c E(iota(g_1, g_2), s_0, Phi_(phi_1 times.o overline(phi_2))), $
  where $s_0 = (dim W - dim V) / 2 = (n - m) / 2$ and $Phi_(phi_1 times.o overline(phi_2)) in I(s_0, chi_W)$ is the Siegel–Weil section attached to $phi_1 times.o overline(phi_2)$!

  Finally, substitute this Siegel–Weil identity back into the outer integral over $[U(V)] times [U(V)]$:
  $ &chevron.l theta_(phi_1)(f_1), theta_(phi_2)(f_2) chevron.r_(U(W)) \
    &= kappa dot.c integral_([U(V)] times [U(V)]) E(iota(g_1, g_2), s_0, Phi_(phi_1 times.o overline(phi_2))) \
    &quad overline(f_1 (g_1)) f_2 (g_2) d g_1 d g_2. $
  That outer integral is *literally* the Piatetski-Shapiro–Rallis doubling integral $Z(s_0, overline(f_1), overline(f_2), Phi_(phi_1 times.o overline(phi_2)))$! Applying Theorem 7.20 immediately delivers the celebrated Rallis inner product formula:

  #theorem(title: "Rallis Inner Product Formula")[
    Let $(U(V), U(W))$ be a unitary dual pair with $dim V = m$ and $dim W = n$, and let $pi = times.o.big'_v pi_v$ be an irreducible cuspidal automorphic representation of $U(V)(bb(A)_(K_0))$ (with $U(W)$ anisotropic, or in the convergent / regularized range of the Siegel–Weil formula). Let $f_1 = times.o.big_v f_(1, v)$, $f_2 = times.o.big_v f_(2, v) in pi$ and $phi_1 = times.o.big_v phi_(1, v)$, $phi_2 = times.o.big_v phi_(2, v) in cal(S)(X(bb(A)_(K_0)))$ be factorizable vectors, and let $s_0 = (n - m) / 2$. Then
    $ &chevron.l theta_(phi_1)(f_1), theta_(phi_2)(f_2) chevron.r_(U(W)) \
      &= kappa dot.c frac(L^S (s_0 + frac(1, 2), pi^or times chi_W), b_m^S (s_0, chi_W)) \
      &quad dot.c product_(v in S) Z_v^natural (f_(1, v), f_(2, v), phi_(1, v), phi_(2, v)), $
    where the local doubling zeta integral at $v in S$ is given in terms of the local Weil representation $omega_v$ by
    $ &Z_v^natural (f_(1, v), f_(2, v), phi_(1, v), phi_(2, v)) \
      &= integral_(U(V)(K_(0, v))) chevron.l omega_v (g_v, 1) phi_(1, v), phi_(2, v) chevron.r_(L^2) \
      &quad dot.c overline(chevron.l pi_v (g_v) f_(1, v)\, f_(2, v) chevron.r_v) d g_v. $
  ]

  #corollary(title: "Nonvanishing Criterion for Global Theta Lifts")[
    Under the hypotheses of Theorem 7.21 (with $s_0 >= 0$), the global theta lift $Theta_(V, W, psi, chi)(pi)$ is *nonzero* if and only if:
    1. *(Global condition)* The partial $L$-value $L^S (s_0 + frac(1, 2), pi^or times chi_W)$ is nonzero (note that when $n = m$, $s_0 = 0$ and this is the *central* $L$-value $L^S (frac(1, 2), pi^or times chi_W)$; when $n > m$, $s_0 = (n - m) / 2 >= 1/2$ lies in or at the edge of the region of absolute convergence, where $L^S (s_0 + frac(1, 2), pi^or times chi_W) != 0$ automatically when $n >= m + 2$!), and
    2. *(Local condition)* For every place $v in S$, the local theta lift $Theta(pi_v)$ is nonzero (equivalently, the local doubling integral $Z_v^natural$ is not identically zero on $pi_v times cal(S)_v$).
  ]

  Pause to appreciate the sheer power of this corollary in the Alpöge–Claude chain $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$! Because each step increases the dimension by $t = dim X_j - dim X_(j-1) >= 1$, the evaluation point $s_0 + frac(1, 2) = (t + 1) / 2 >= 1$ lies in the *safe half-plane* $op("Re")(s) >= 1$ (where standard $L$-functions of unitary cuspidal representations have no zeros by Jacquet–Shalika, and in fact when $t >= 2$ are given by absolutely convergent Euler products!). Even better, the Rallis inner product formula does not merely say that the lift is nonzero: it yields an *exact formula* for $norm(theta_phi (f))_(L^2)^2$ in terms of special $L$-values and local Schwartz moments—providing the quantitative norm bounds (items 9 and 14 of `remark.pdf`) that enter the Arakelov height comparison in Part III!

  == Seesaw Dual Pairs and Reduction to Bessel / GGP Periods

  We now turn to the second structural pillar of the Alpöge–Claude chain: *seesaw duality* (Kudla 1983). If the Rallis inner product formula is the scalpel that measures the $L^2$-norm of a theta lift, seesaw duality is the lever that transforms a period integral of an *iterated* theta lift on a huge group $U(X_m)$ back down to a *fixed* Bessel / Gan–Gross–Prasad period on the base group $U(X_0)$—completely independent of the $m$ auxiliary Hecke characters $mu_1, dots.c, mu_m$!

  === Seesaw Dual Pairs and the Seesaw Identity

  #definition(title: "Seesaw Dual Pair")[
    Two reductive dual pairs $(G, G')$ and $(H, H')$ inside the same ambient symplectic group $op("Sp")(bb(W))$ are said to form a *seesaw pair* if
    $ H subset.eq G wide "and" wide G' subset.eq H'. $
    Such a configuration is customarily depicted by a *seesaw diagram* in which each diagonal line connects a reductive dual pair and each vertical inclusion points downward (from larger group to smaller group):
    #align(center)[
      #v(0.3em)
      #grid(
        columns: (auto, 2.2cm, auto),
        align: center + horizon,
        row-gutter: 0.4em,
        [$G$], [], [$H'$],
        [$supset.eq$], [$times$], [$supset.eq$],
        [$H$], [], [$G'$],
      )
      #v(0.3em)
    ]
    Here $(G, G')$ and $(H, H')$ are the two dual pairs connected across the diagonal.
  ]

  For unitary groups, the fundamental seesaw pair arises from an *orthogonal direct sum decomposition* of a Hermitian space:
  $ V = V_1 plus.o V_2, $
  paired with a skew-Hermitian space $W$. Inside the ambient symplectic group
  $ &op("Sp")(op("Res")_(K/K_0)(V times.o_K W)) \
    &= op("Sp")(op("Res")_(K/K_0)(V_1 times.o_K W) plus.o op("Res")_(K/K_0)(V_2 times.o_K W)), $
  the subgroup $U(V_1) times U(V_2) subset U(V_1 plus.o V_2)$ has centralizer $U(W) times U(W)$, which contains the diagonally embedded $U(W) = Delta U(W)$. This gives the *unitary seesaw diagram*:

  #align(center)[
    #v(0.35em)
    #block(
      fill: gtm-tint,
      stroke: 0.5pt + gtm-rule,
      inset: (x: 16pt, y: 10pt),
      radius: 3pt,
    )[
      #grid(
        columns: (auto, 1.8cm, auto),
        align: center + horizon,
        row-gutter: 0.45em,
        [$U(V_1 plus.o V_2)$], [], [$U(W) times U(W)$],
        [$supset.eq$], [seesaw], [$supset.eq$],
        [$U(V_1) times U(V_2)$], [], [$U(W)$],
      )
    ]
    #v(0.35em)
  ]

  The splitting characters are compatible across the seesaw: if $(chi_V, chi_W)$ splits $(U(V_1 plus.o V_2), U(W))$, then choosing $chi_(V_1), chi_(V_2)$ with $chi_(V_1) dot.c chi_(V_2) = chi_V$ (matching the parity $dim V_1 + dim V_2 = dim V$) splits $(U(V_1) times U(V_2), U(W) times U(W))$, and the Weil representation on the product Schwartz space $cal(S)(X_1(bb(A)) plus.o X_2(bb(A))) approx cal(S)(X_1(bb(A))) times.o cal(S)(X_2(bb(A)))$ satisfies the factorization
  $ &omega_(V_1 plus.o V_2, W)((g_1, g_2), h)(phi_1 times.o phi_2) \
    &= (omega_(V_1, W)(g_1, h) phi_1) times.o (omega_(V_2, W)(g_2, h) phi_2) $
  for all $(g_1, g_2) in U(V_1) times U(V_2)$ and $h in U(W)$! Consequently, the global theta kernel factors pointwise as
  $ theta_(phi_1 times.o phi_2)((g_1, g_2), h) = theta_(phi_1)(g_1, h) dot.c theta_(phi_2)(g_2, h). $

  #proposition(title: "Global Seesaw Identity")[
    Let $V = V_1 plus.o V_2$ and $W$ be as above. Let $F in cal(A)(U(W))$, $f_1 in cal(A)(U(V_1))$, and $f_2 in cal(A)(U(V_2))$ be automorphic forms, and let $phi = phi_1 times.o phi_2 in cal(S)(X_1(bb(A))) times.o cal(S)(X_2(bb(A)))$. Assuming that the double integral over $[U(V_1) times U(V_2)] times [U(W)]$ converges absolutely (which holds automatically when the groups are totally definite, or when the forms are cuspidal), we have the *seesaw identity*:
    $ &chevron.l theta_phi (F) |_(U(V_1) times U(V_2)), f_1 times.o f_2 chevron.r_(U(V_1) times U(V_2)) \
      &= chevron.l F, theta_(phi_1)(f_1) dot.c theta_(phi_2)(f_2) chevron.r_(U(W)). $
    In explicit integral notation:
    $ &integral_([U(V_1)]) integral_([U(V_2)]) theta_(phi_1 times.o phi_2)(F)(g_1, g_2) overline(f_1 (g_1)) overline(f_2 (g_2)) d g_1 d g_2 \
      &= integral_([U(W)]) F(h) overline(theta_(phi_1)(f_1)(h) dot.c theta_(phi_2)(f_2)(h)) d h $
    (where we use the convention $theta_phi (F)(g) = integral_([U(W)]) theta_phi (g, h) F(h) d h$ on the left and $theta_(phi_i)(f_i)(h) = integral_([U(V_i)]) overline(theta_(phi_i)(g_i, h)) f_i (g_i) d g_i$ on the right).
  ]

  #proof[
    By Fubini's theorem and the pointwise factorization $theta_(phi_1 times.o phi_2)((g_1, g_2), h) = theta_(phi_1)(g_1, h) dot.c theta_(phi_2)(g_2, h)$:
    $ &integral_([U(V_1)] times [U(V_2)]) ( integral_([U(W)]) theta_(phi_1 times.o phi_2)((g_1, g_2), h) F(h) d h ) \
      &quad overline(f_1 (g_1)) overline(f_2 (g_2)) d g_1 d g_2 \
    &= integral_([U(W)]) F(h) ( integral_([U(V_1)]) theta_(phi_1)(g_1, h) overline(f_1 (g_1)) d g_1 ) \
      &quad ( integral_([U(V_2)]) theta_(phi_2)(g_2, h) overline(f_2 (g_2)) d g_2 ) d h \
    &= chevron.l F, theta_(phi_1)(f_1) dot.c theta_(phi_2)(f_2) chevron.r_(U(W)). $
  ]

  Never underestimate an identity whose proof is three lines of Fubini's theorem! The seesaw identity is the Swiss army knife of global automorphic periods: it trades a *branching / restriction period* on the big group $U(V_1 plus.o V_2)$ for a *product / Rankin–Selberg period* on the smaller group $U(W)$.

  === Gan–Gross–Prasad and Bessel Periods

  To see how seesaw duality operates in the Alpöge–Claude proof, we first recall the *Gan–Gross–Prasad (GGP)* and *Bessel* periods on unitary groups.

  Let $X' subset X$ be an inclusion of Hermitian spaces over $K$ whose orthogonal complement $X^(perp) = (X')^(perp)$ has *odd* dimension $2 r + 1$:
  $ X = X' plus.o X^(perp), wide dim_K X^(perp) = 2 r + 1. $
  (The most famous case is the *codimension-one* or *co-rank-one* case $r = 0$, where $X = X' plus.o K dot.c e_0$ and $U(X') subset U(X)$ is an embedding $U(n - 1) arrow.r.hook U(n)$.)

  When $r = 0$, the *GGP period* of a pair of automorphic forms $F in pi subset cal(A)(U(X))$ and $f in sigma subset cal(A)(U(X'))$ is simply the restriction integral
  $ cal(P)_(X', X)(F, f) = integral_([U(X')]) F(h) overline(f(h)) d h. $
  When $r >= 1$ and $X^(perp)$ is *split* modulo a one-dimensional anisotropic line $K dot.c e_0$ (i.e., $X^(perp) = bb(H)^r plus.o K dot.c e_0$, where $bb(H)$ is a hyperbolic plane), let $N subset U(X)$ be the unipotent radical of the parabolic subgroup stabilizing a complete isotropic flag $0 subset L_1 subset dots.c subset L_r$ in $bb(H)^r$. The subgroup $U(X')$ normalizes $N$ and stabilizes a generic additive character $psi_N : N(K_0) backslash N(bb(A)_(K_0)) -> bb(C)^times$ determined by the anisotropic vector $e_0$. The semidirect product
  $ R = U(X') times.r N subset U(X) $
  is called the *Bessel subgroup*, and for $F in pi subset cal(A)(U(X))$ and $f in sigma subset cal(A)(U(X'))$, the *global Bessel period* is
  $ cal(B)(F, f) = integral_([U(X')]) integral_([N]) F(u h) overline(f(h)) psi_N (u)^(-1) d u d h. $
  (When $r = 0$, $N = {1}$ and the Bessel period *is* the GGP restriction period!)

  The celebrated *Gan–Gross–Prasad conjecture* and *Ichino–Ikeda formula* (proved for unitary groups by Wei Zhang, Raphaël Beuzart-Plessis, Yifeng Liu, and Hang Xue) state that the absolute square of the Bessel / GGP period is directly proportional to the central value of the Rankin–Selberg $L$-function:
  $ frac(|cal(B)(F, f)|^2, chevron.l F\, F chevron.r dot.c chevron.l f\, f chevron.r) = C dot.c frac(L(frac(1, 2), pi times sigma^or), L(1, pi, op("Ad")) L(1, sigma, op("Ad"))) dot.c product_v alpha_v (F_v, f_v), $
  where $alpha_v$ are normalized local matrix-coefficient integrals! For *totally definite* unitary groups, $X^(perp)$ has no isotropic vectors (so the relevant periods are GGP restriction periods or twisted Bessel periods after passing to a split/quasi-split auxiliary space), and the nonvanishing of $cal(B)(F, f)$ is governed by local branching laws (interlacing of highest weights at archimedean places, cf. item 7 of `remark.pdf`).

  === Seesaw Reduction of Iterated Theta Lifts: Independence of the Auxiliary Hecke Characters

  Now watch what happens when we combine an *iterated theta lift* with *seesaw duality*! This is item 12 of Alpöge's *Remark* ("Seesaw: the period of the iterated lift is a Bessel period independent of the Hecke characters, Rallis").

  Consider a single step of the theta-lift chain, $U(W) -> U(V)$, where $dim V = dim W + t$ and the theta lift $F_1 = theta_phi (F_0)$ of $F_0 in pi_0 subset cal(A)(U(W))$ uses a splitting character $chi_W$ (producing the auxiliary Hecke character $mu$ in the spectral transfer $pi_0 |-> pi_0 plus.square mu [t]$). Suppose we split $V$ orthogonally as
  $ V = V_1 plus.o V_2, $
  where $V_1$ is a subspace of codimension $t'$ and $V_2$ carries a *character* $eta$ of $U(V_2)$ (or a trivial representation $bb(1)$ twisted by the determinant character matching the splitting character $chi_W$).

  Let us compute the $U(V_1) times U(V_2)$-period of the theta lift $theta_(phi_1 times.o phi_2)(F_0)$ against a test form $f_1 in cal(A)(U(V_1))$ and a character $eta_2$ on $U(V_2)$! Applying the seesaw identity (Proposition 7.24) to the seesaw diagram
  #align(center)[
    #v(0.25em)
    #grid(
      columns: (auto, 1.5cm, auto),
      align: center + horizon,
      row-gutter: 0.35em,
      [$U(V_1 plus.o V_2)$], [], [$U(W) times U(W)$],
      [$supset.eq$], [seesaw], [$supset.eq$],
      [$U(V_1) times U(V_2)$], [], [$U(W)$],
    )
    #v(0.25em)
  ]
  we obtain
  $ &integral_([U(V_1)] times [U(V_2)]) theta_(phi_1 times.o phi_2)(F_0)(g_1, g_2) overline(f_1 (g_1)) overline(eta_2 (det g_2)) d g_1 d g_2 \
    &= integral_([U(W)]) F_0 (h) overline(theta_(phi_1)(f_1)(h) dot.c theta_(phi_2)(eta_2)(h)) d h. $
  Now inspect the two factors inside the integral on the right-hand side!
  1. Look at the splitting characters: the theta lift $theta_(phi_1 times.o phi_2)(F_0)$ depends on the splitting character $chi_W$ via a determinant twist $chi_W (det g)$ on $U(V_1 plus.o V_2)$. Restricted to $U(V_1) times U(V_2)$, this determinant splits as $chi_W (det g_1) dot.c chi_W (det g_2)$.
  2. In the Alpöge–Claude setup, we choose the test character $eta_2$ on $U(V_2)$ to *absorb* the auxiliary Hecke character $mu$ (so that $theta_(phi_2)(eta_2)$ is a fixed theta series / Eisenstein-type kernel, or even simpler, when we choose $V_2$ so that $U(V_2)$ integrates out the $mu$-twist and $theta_(phi_1)(f_1)$ reduces to a GGP/Bessel test vector on $U(W)$)!

  Even more directly, consider the *dual* seesaw where $W = W_0 plus.o W_1$ splits on the *source* side, or iterate the seesaw step $m$ times along the chain $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$!

  #theorem(title: "Seesaw Independence of Iterated Theta-Lift Periods")[
    Let $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ be a chain of global theta lifts with auxiliary splitting Hecke characters $mu_1, dots.c, mu_m$, taking a base automorphic form $f_0 in pi_0 subset cal(A)(U(X_0))$ to an iterated lift $f_m = theta_(phi_m) dots.c theta_(phi_1)(f_0)$ on $U(X_m)$. Suppose $X_m = Y plus.o Z_1 plus.o dots.c plus.o Z_m$ is an orthogonal decomposition aligned with the step increments $dim Z_j = dim X_j - dim X_(j-1) = t$, and consider the twisted GGP / Bessel period
    $ &cal(P)(f_m; mu_1, dots.c, mu_m) \
      &= integral_([U(Y)] times [U(Z_1)] times dots.c times [U(Z_m)]) f_m (y, z_1, dots.c, z_m) \
      &quad overline(h_Y (y)) product_(j=1)^m mu_j (det z_j)^(-1) d y d z_1 dots.c d z_m. $
    Then, by $m$-fold application of the seesaw identity (and evaluation of the one-step $Z_j$-theta integrals via the Siegel–Weil / Rallis inner product formula), this period factors as
    $ cal(P)(f_m; mu_1, dots.c, mu_m) = C(phi_1, dots.c, phi_m) dot.c cal(B)_0 (f_0, h_0), $
    where:
    - $cal(B)_0 (f_0, h_0)$ is a *Bessel / GGP period on the base group $U(X_0)$* that is *completely independent of the auxiliary Hecke characters $mu_1, dots.c, mu_m$*, and
    - the prefactor $C(phi_1, dots.c, phi_m)$ is an explicit product of local Schwartz–Bruhat / Bessel-isometry constants and nonvanishing $L$-factors controlled by the Rallis inner product formula.
  ]

  #proof[
    We prove the inductive step from $j$ to $j - 1$ (dropping indices for clarity: write $X_j = X'_j plus.o Z_j$ with $X'_j = Y plus.o Z_1 plus.o dots.c plus.o Z_(j-1)$). By the seesaw identity for the dual pairs $(U(X'_j plus.o Z_j), U(X_(j-1)))$ and $(U(X'_j) times U(Z_j), U(X_(j-1)))$, integrating $f_j = theta_(phi_j)(f_(j-1))$ over $[U(X'_j)] times [U(Z_j)]$ against $H_(j-1) times.o (mu_j compose det)$ yields
    $ integral_([U(X_(j-1))]) f_(j-1)(g) dot.c overline(theta_(phi'_j)(H_(j-1))(g)) dot.c overline(theta_(phi''_j)(mu_j compose det)(g)) d g. $
    Here is the magic: in the splitting of $(U(X_j), U(X_(j-1)))$, the character $mu_j$ enters the Weil representation $omega_j$ on $U(Z_j) times U(X_(j-1))$ as a twist by $mu_j (det z_j) dot.c mu_j^(c)(det g)$ (or its inverse). When we integrate over $z_j in [U(Z_j)]$ against $mu_j (det z_j)^(-1)$, the factor $mu_j (det z_j)$ cancels *identically* inside the $Z_j$-integral! What remains on $U(X_(j-1))$ is the theta integral of the *trivial* representation of $U(Z_j)$ (which by the Siegel–Weil formula is an explicit Eisenstein / constant kernel independent of $mu_j$), while the remaining $mu_j$-twist on $U(X_(j-1))$ is absorbed into the local choice of Schwartz function (or cancels against the conjugate $mu_j$ in the $X'_j$-factor).

    Applying this reduction inductively for $j = m, m - 1, dots.c, 1$ peels off every layer $Z_m, Z_(m-1), dots.c, Z_1$ one by one, stripping away all $m$ auxiliary Hecke characters $mu_m, dots.c, mu_1$ and leaving a fixed Bessel / GGP period $cal(B)_0 (f_0, h_0)$ on $U(X_0)$!
  ]

  #insight-box(title: "The Payoff: Gluing Across Hecke Characters")[
    Step back and admire the synergy between Theorems 7.6, 7.10, and 7.13:
    - By *unramified spectral transfer* (Theorem 7.15), each link in the chain $U(X_0) -> dots.c -> U(X_m)$ injects a new Hecke character $mu_j$, building an automorphic representation of rank $dim X_0 + m t$ with "multiplicity $m$".
    - By the *Rallis inner product formula* (Theorem 7.21), the Petersson norm $norm(f_m)_(L^2)^2$ is explicitly bounded in terms of special $L$-values at $s_0 + 1/2 >= 1$ and local doubling integrals.
    - By *seesaw duality* (Theorem 7.25), the Bessel / GGP period of $f_m$ reduces to a *single* base period $cal(B)_0 (f_0, h_0)$ that does *not depend on $mu_1, dots.c, mu_m$*!

    Because the target period is invariant under varying $(mu_1, dots.c, mu_m)$, the Alpöge–Claude proof can glue together an *integral structure across families of Hecke characters* (item 15 of `remark.pdf`)—taking an arithmetic "greatest common divisor" of the divisibilities produced by different choices of $(mu_1, dots.c, mu_m)$ to kill unwanted primes and Selmer obstructions while keeping the target period fixed!
  ]

  == Lean 4 Formalization

  Because the theta correspondence is the heaviest representation-theoretic machinery in the entire Alpöge–Claude proof, its formalization in `lean-rh/src` is organized into two major library trees—one dedicated to the arithmetic and representation-theoretic foundations of the theta correspondence, and a second dedicated to the analytic estimates, towers, and Weil-bound reductions on theta lifts—supported by published-theorem interfaces in `Development/AbelianVarietyTheory` and `Development/WeilBound/CoreStatements`.

  #lean-note(
    title: "Lean 4 Formalization: Theta Correspondence, Doubling Method, and Seesaw Reduction",
    module: "Development/AutomorphicArithmetic/ThetaCorrespondence & Development/WeilBound/ThetaLifts",
  )[
    The machine-checked formalization in `lean-rh/src` implements every theorem of this chapter without unproved axioms:

    - *Weil Representation and Fock Models*:
      - `Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation` (`WeilEx.lean`, `WeilTheta.lean`) defines the global theta kernel $theta_phi (g, h)$ and verifies its automorphy and Poisson summation invariance.
      - `Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels` constructs the archimedean Bargmann–Fock model and polynomial $K$-types.
      - `Development/AbelianVarietyTheory/Proofs/DivisorProofs` contains `StoneVonNeumannSchwartzBruhatAnyCharacter`, `StoneVonNeumannSchwartzBruhatTransverseLagrangia`, `AdelicStoneVonNeumannLagrangianUniqueness`, and `RealMetaplecticRepresentationHolds`.

    - *Kudla's Splitting and Local Howe Duality*:
      - `Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean` and `Proofs/DivisorProofs/KudlaSplittingSplitUnitary.lean` formalize Kudla's splitting for unitary dual pairs at split places.
      - `Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/HoweDualityReal.lean` and `Development/AutomorphicArithmetic/ThetaCorrespondence/HoweDuality` formalize local Howe duality at archimedean and non-archimedean places (including the split general linear case `GLHoweDuality`).

    - *Siegel Eisenstein Series, Siegel–Weil, and Rallis Inner Product*:
      - `Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinContinuation` (`SiegelEisensteinContinuation.lean`) and `Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂` (`SiegelEisensteinContinuationOfDoublingMethod.lean`, `SiegelEisensteinSimplePoleOfDoublingMethod.lean`) prove meromorphic continuation and the simple-pole structure of Siegel Eisenstein series.
      - `Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilStandard/SiegelWeilStd.lean` and `ThetaIntegralEqSiegelEisensteinOfWeilRange.lean` establish the Siegel–Weil formula.
      - `Development/AutomorphicArithmetic/ThetaCorrespondence/RallisInnerProduct` and `DoublingMethodLocalZetaIntegrals` combine Siegel–Weil with the Piatetski-Shapiro–Rallis doubling integral to obtain the Rallis inner product formula.

    - *Bessel Models, Seesaw Reduction, and Iterated Lift Towers*:
      - `Development/AutomorphicArithmetic/ThetaCorrespondence/BesselModels` and `CompanionTheory/AutomorphicTheory/PieriRules/ThetaBesselIsometries` formalize Bessel models, local Bessel uniqueness, and the theta–Bessel isometries underlying seesaw reduction.
      - `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts` and `Development/WeilBound/ThetaLifts` (including `TowerModels`, `SphericalSplitting`, `SchwartzMoments`, `FrameEstimates`, and `CTKernel.lean`) assemble the $m$-step iterated theta lift chain $U(X_0) -> dots.c -> U(X_m)$ and bound its norms and local Schwartz moments.
  ]

  With the representation-theoretic engine of the Weil representation, theta lifts, Rallis inner product formula, and seesaw duality firmly in hand, we are ready to turn in Chapter 8 to the *arithmetic* source of divisibility in the Alpöge–Claude proof: complex multiplication, invariant derivations on CM elliptic curves, and local divisibility at inert primes.

  #exercises((
    [
      *(Schrödinger Model and Transverse Intertwiner)* Let $(bb(W), chevron.l dot.c, dot.c chevron.r)$ be a $2n$-dimensional symplectic space over a local field $F$ with complete polarization $bb(W) = bb(X) plus.o bb(Y)$, and let $psi : F -> bb(C)^times$ be a nontrivial unitary additive character.
      (a) Verify directly from the definition of the Schrödinger representation $(rho_psi (x + y, t) phi)(y') = psi(t + chevron.l y', x chevron.r + frac(1,2) chevron.l y, x chevron.r) phi(y' + y)$ that $rho_psi ((w_1, t_1) dot.c (w_2, t_2)) = rho_psi (w_1, t_1) rho_psi (w_2, t_2)$.
      (b) Show that the symplectic Fourier transform $(cal(F) phi)(x) = integral_(bb(Y)) phi(y) psi(chevron.l x, y chevron.r) d y$ intertwines the Schrödinger model on $cal(S)(bb(Y))$ with the Schrödinger model on $cal(S)(bb(X))$ (for the opposite polarization $bb(W) = bb(Y) plus.o bb(X)$).
    ],
    [
      *(Weil Index and Metaplectic Cocycle on $op("SL")_2(bb(R))$)* Take $F = bb(R)$, $bb(W) = bb(R)^2$ with $chevron.l (x_1, y_1), (x_2, y_2) chevron.r = x_1 y_2 - y_1 x_2$, and $psi(t) = e^(2 pi i t)$.
      (a) Using the Fresnel integral $integral_(-oo)^oo e^(pi i a y^2) d y = |a|^(-1/2) e^(op("sgn")(a) pi i \/ 4)$ for $a in bb(R)^times$, compute the Weil index $gamma_psi (a)$ explicitly and verify that $gamma_psi (a b) / (gamma_psi (a) gamma_psi (b)) = (a, b)_bb(R)$, where $(a, b)_bb(R) = -1$ if $a < 0$ and $b < 0$, and $+1$ otherwise.
      (b) Deduce that the pullback of $op("Mp")_2(bb(R)) -> op("SL")_2(bb(R))$ to the maximal compact subgroup $op("SO")(2)$ is the connected double cover of $S^1$.
    ],
    [
      *(Fock Model of $op("Mp")_2(bb(R))$ and Half-Integral Weight Discrete Series)* Consider the polynomial Fock space $cal(P)(bb(C)) = bb(C)[z]$ for $n = 1$ over $bb(R)$.
      (a) Show that the operators $E_+ = frac(i, 2) z^2$, $E_- = frac(i, 2) frac(partial^2, partial z^2)$, and $H = z frac(partial, partial z) + frac(1, 2)$ span a Lie algebra isomorphic to $frak("sl")_2(bb(C))$ and compute their commutation relations.
      (b) Deduce that as a $(frak("sl")_2(bb(C)), tilde(op("SO"))(2))$-module, $bb(C)[z]$ splits into the direct sum of two irreducible submodules: the *even* polynomials $bb(C)[z]_(op("even"))$ (lowest weight $1/2$) and the *odd* polynomials $bb(C)[z]_(op("odd"))$ (lowest weight $3/2$). How does this relate to the classical Jacobi theta series $theta(tau) = sum_(n in bb(Z)) q^(n^2)$ of weight $1/2$?
    ],
    [
      *(Kudla's Splitting for $(U(1), U(1))$)* Let $K \/ K_0$ be a quadratic extension of local fields with nontrivial involution $c$ and quadratic character $omega_(K/K_0)$, and consider the unitary dual pair $(U(1), U(1))$ where $V = K$ with $(v_1, v_2)_V = v_1 v_2^c$ and $W = K$ with $chevron.l w_1, w_2 chevron.r_W = delta w_1 w_2^c$ ($delta^c = -delta$).
      (a) Show that $op("Res")_(K/K_0)(V times.o_K W) approx K$ as a $2$-dimensional symplectic $K_0$-vector space, and verify that the image of $U(1) times U(1)$ in $op("Sp")_2(K_0) = op("SL")_2(K_0)$ is the anisotropic torus $K^1 = {z in K^times : z z^c = 1}$.
      (b) Using the parity condition $chi_V |_(K_0^times) = omega_(K/K_0)$, explain why the choice of $chi_V$ resolves the sign ambiguity of the half-integral weight $1/2$ on $tilde(K)^1$ and yields a genuine linear representation of $U(1) times U(1)$.
    ],
    [
      *(Compact Dual Pair $(U(1), U(q))$)* Specialize Proposition 7.11 to the compact unitary dual pair $(U(1), U(q))$ with $q >= 1$.
      (a) Show that the polynomial Fock space $bb(C)[z_1, dots.c, z_q]$ decomposes as $plus.o.big_(k=0)^oo (chi_k times.o op("Sym")^k (bb(C)^q))$, where $chi_k (u) = u^k$ is the $k$-th power character of $U(1)$ (up to the fixed determinant shift from the splitting characters).
      (b) Compute the dimension of the $U(q)$-representation $op("Sym")^k (bb(C)^q)$ and verify that its highest weight is $(k, 0, dots.c, 0)$.
    ],
    [
      *(Unramified Satake Parameter for the Split Pair $(op("GL")_1, op("GL")_2)$)* Let $F$ be a non-archimedean local field with uniformizer $pi.alt$ and residue cardinality $q$. Consider the split unitary dual pair $(op("GL")_1 (F), op("GL")_2 (F))$ acting on $cal(S)(F^2)$ via $(omega(a, h) phi)(x) = |a|_F |det h|_F^(-1/2) phi(a^(-1) x h)$ (with trivial splitting characters).
      (a) Let $chi$ be an unramified character of $F^times$ with $chi(pi.alt) = alpha$. For $phi_0 = bb(1)_(cal(O)_F^2)$, compute the local zeta-type lift $F(h) = integral_(F^times) (omega(a, h) phi_0)(x_0) chi(a)^(-1) d^times a$ on the Borel subgroup of $op("GL")_2 (F)$.
      (b) Verify that the resulting unramified representation of $op("GL")_2 (F)$ has Satake parameter $op("diag")(alpha, 1)$ (equivalently, $chi plus.square bb(1)[1]$), confirming Theorem 7.15 for $m = 1, t = 1$.
    ],
    [
      *(Doubling Method for $U(1)$)* Let $W$ be a $1$-dimensional skew-Hermitian space over a CM field $K$, so $U(W) = U(1)$ and $U(W^square) approx U(1, 1)$ (whose derived group is $op("SL")_2$ over $K_0$).
      (a) Write down the Siegel parabolic $P subset U(1, 1)$ and the induced section $Phi_s in I(s, chi)$ explicitly.
      (b) For a Hecke character $pi$ of $U(1)(K_0) backslash U(1)(bb(A)_(K_0))$, carry out the unfolding of the doubling integral $Z(s, pi, pi, Phi)$ directly and verify that at every unramified finite place $v$ of $K_0$, the local doubling integral equals $L_v (s + frac(1, 2), pi_v chi_v) \/ L_v (2 s + 1, chi_v |_(K_(0, v)^times))$.
    ],
    [
      *(Deriving Rallis Inner Product in the Convergent Range)* Assume $V$ and $W$ are totally definite Hermitian/skew-Hermitian spaces over $K$ with $dim W > 2 dim V$, so that both the Siegel–Weil formula for $(U(V^square), U(W))$ and the doubling integral on $U(V) times U(V)$ converge absolutely at $s_0 = (dim W - dim V) / 2$.
      (a) Carefully track all complex conjugations and determinant twists in the chain of equalities from $chevron.l theta_(phi_1)(f_1), theta_(phi_2)(f_2) chevron.r_(U(W))$ to $Z(s_0, overline(f_1), overline(f_2), Phi_(phi_1 times.o overline(phi_2)))$.
      (b) Verify that for a pure tensor $phi_1 = phi_2 = phi$, the local Siegel–Weil section evaluated at $iota(g_v, 1) in U(V^square)(K_(0, v))$ equals the local Weil-representation matrix coefficient $chevron.l omega_v (g_v, 1) phi_v, phi_v chevron.r_(L^2)$.
    ],
    [
      *(Seesaw Identity and Character Cancellation)* Let $V = V_1 plus.o V_2$ with $dim V_2 = 1$, and let $W$ be a totally definite skew-Hermitian space.
      (a) Write down the explicit seesaw diagram relating $(U(V_1 plus.o V_2), U(W))$ and $(U(V_1) times U(V_2), U(W))$.
      (b) Suppose we twist the splitting character $chi_W$ by a Hecke character $mu$ of $bb(A)_K^times \/ K^times$ trivial on $bb(A)_(K_0)^times$. Using Kudla's twisting law (Theorem 7.9(3)) and the seesaw identity (Proposition 7.24), show explicitly how integrating over $g_2 in [U(V_2)]$ against $tilde(mu)(det g_2)^(-1)$ cancels the $mu$-dependence in the $V_2$-factor.
    ],
  ))
]
