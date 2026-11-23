#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch10() = [
  #chapter(
    "Galois Cohomology, Poitou–Tate Duality, and Iwasawa Towers",
    short-title: "Galois Cohomology and Iwasawa Towers",
    epigraph: "The duality theorems of Galois cohomology reveal that the obstructions to local-to-global principles are not mere accidents of arithmetic, but dual reflections of global invariants.",
    epigraph-source: "After J. Tate, ICM Stockholm (1962)",
    overview: [
      In the preceding chapters, the analytic and automorphic architecture of the Alpöge–Claude–Riemann proof—chained theta lifts on totally definite unitary groups, relative trace formulas, and Arakelov slope inequalities—reduced the optimal control of prime numbers to fine integral and cohomological properties of algebraic Hecke characters and automorphic Galois representations over CM fields. In this chapter we develop the arithmetic-cohomological machinery that governs those integral structures. We begin in Section 10.1 with continuous profinite Galois cohomology, Tate local duality, Euler–Poincaré characteristic formulas, compactly supported cohomology, and the Poitou–Tate nine-term exact sequence. In Section 10.2 we derive the exact $bb(Z)_ell$-module length identity `VFormula` relating $H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1))$ to the Tate–Shafarevich kernel $op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e))$, explaining its connection to the Kummer–Vandiver conjecture, Quillen–Lichtenbaum $K$-theory, and the weakened Vandiver bound `VVle`. Section 10.3 introduces Fontaine's $p$-adic Hodge theory ($B_"cris"$, $B_"dR"$), Bloch–Kato Selmer groups, the Greenberg–Wiles formula, and Bhatt–Scholze prismatic/crystalline integral lattices. Finally, Section 10.4 explains why the proof ascends a cyclotomic-quadratic Iwasawa tower—the number-field analogue of passing from $bb(F)_q$ to $bb(F)_(q^n)$ in Stepanov's method—and proves a generalized Behrend sphere theorem that separates Frobenius orbits from unwanted linear relations.
    ],
    label-name: "ch:galois-cohomology-iwasawa",
  )

  // ==========================================================================
  // Section 10.1
  // ==========================================================================
  == Profinite Galois Cohomology and Local/Global Dualities

  Whenever an automorphic or geometric construction produces congruences between algebraic objects modulo powers of a prime $ell$, the obstructions to lifting, separating, or gluing those objects live in continuous Galois cohomology. To make this precise in a form directly aligned with both classical class field theory and the Lean 4 formalization, we review the cohomological formalism of profinite groups, local fields, and $S$-ramified global Galois groups.

  === Continuous Cohomology of Profinite Groups

  Let $G$ be a profinite group, equipped with its Krull topology, and let $M$ be a topological $G$-module—an abelian group with a continuous $G$-action $G times M -> M$. When $M$ carries the discrete topology, continuity of the action is equivalent to the condition that the stabilizer of every element $m in M$ is an open subgroup of $G$, so that
  $ M = union.big_U M^U, $
  where $U$ runs over all open normal subgroups $U lt.tri.eq G$. For any integer $n >= 0$, the group of *continuous inhomogeneous $n$-cochains* $C^n_"cont" (G, M)$ consists of continuous maps $f : G^n -> M$ (with $C^0_"cont" (G, M) = M$), equipped with the coboundary differential $d^n : C^n_"cont" (G, M) -> C^(n+1)_"cont" (G, M)$ given by
  $
    (d^n f)(g_1, dots.c, g_(n+1)) &= g_1 dot.c f(g_2, dots.c, g_(n+1)) \
    &quad + sum_(i=1)^n (-1)^i f(g_1, dots.c, g_i g_(i+1), dots.c, g_(n+1)) \
    &quad + (-1)^(n+1) f(g_1, dots.c, g_n).
  $
  The *continuous cohomology groups*
  $ H^n (G, M) = ker(d^n) \/ op("im")(d^(n-1)) $
  are naturally $R$-modules whenever $M$ is a topological $R[G]$-module for a commutative ring $R$ with continuous scalar multiplication. In degree $0$, $H^0 (G, M) = M^G$; in degree $1$, $H^1 (G, M)$ is the group of continuous crossed homomorphisms $f : G -> M$ (satisfying $f(g h) = f(g) + g dot.c f(h)$) modulo principal crossed homomorphisms $g |-> g dot.c m - m$.

  For discrete $G$-modules, every continuous cochain $G^n -> M$ factors through $(G \/ U)^n$ for some open normal subgroup $U lt.tri.eq G$, yielding a canonical identification with the direct limit of finite-group cohomology:
  $ H^n (G, M) tilde.equiv limits(op("lim"))_(-> U) H^n (G \/ U, M^U). $
  In particular, for discrete $G$-modules, $H^n (G, M)$ is a torsion abelian group for all $n >= 1$. In arithmetic applications we also require $ell$-adic coefficients such as $M = bb(Z)_ell (n)$, which carry the profinite $ell$-adic topology rather than the discrete topology. If $M = limits(op("lim"))_(<- r) M_r$ is an inverse limit of finite discrete $G$-modules with surjective transition maps (for instance $M_r = M \/ ell^r M$) and the inverse system $\{ H^(n-1) (G, M_r) \}_r$ satisfies the Mittag-Leffler condition—which is automatic whenever each $H^(n-1) (G, M_r)$ is finite—then Tate's theorem on continuous cochains yields a canonical isomorphism
  $ H^n (G, M) tilde.equiv limits(op("lim"))_(<- r) H^n (G, M_r). $
  Every short exact sequence $0 -> A -> B -> C -> 0$ of discrete $G$-modules (or of finitely generated $bb(Z)_ell$-modules with continuous $G$-action) induces a long exact sequence in continuous cohomology. Moreover, for any closed normal subgroup $N lt.tri.eq G$, the Hochschild–Serre spectral sequence $E_2^(p, q) = H^p (G \/ N, H^q (N, M)) => H^(p+q) (G, M)$ produces in low degrees the *inflation–restriction exact sequence*:
  $
    0 &-> H^1 (G \/ N, M^N) ->^(op("Inf")) H^1 (G, M) ->^(op("Res")) H^1 (N, M)^(G \/ N) \
      &->^(op("tg")) H^2 (G \/ N, M^N) -> H^2 (G, M).
  $

  Finally, given a $G$-equivariant bilinear pairing $M times N -> P$ of topological $G$-modules, the *cup product*
  $ union : H^i (G, M) times H^j (G, N) -> H^(i+j) (G, P) $
  is induced at the cochain level by $(f union h)(g_1, dots.c, g_(i+j)) = f(g_1, dots.c, g_i) times.o g_1 dots.c g_i dot.c h(g_(i+1), dots.c, g_(i+j))$. It is graded-commutative ($a union b = (-1)^(i j) b union a$ up to the symmetry of the pairing) and functorial with respect to restriction and inflation.

  === $S$-Ramified Galois Groups and Cyclotomic Twists

  Let $F$ be a number field with ring of integers $cal(O)_F$, and fix an algebraic closure $Omega$ of $F$. Write $G_F = op("Gal")(Omega \/ F)$ for the absolute Galois group of $F$. For each finite place $v$ of $F$ (corresponding to a height-one prime ideal $frak(p)_v$ of $cal(O)_F$), choosing a valuation subring $A_v subset.eq Omega$ lying over $v$ determines a decomposition subgroup $D_v = op("Dec")(A_v) subset.eq G_F$ and an inertia subgroup $I_v = op("Ine")(A_v) lt.tri.eq D_v$. The decomposition group $D_v$ is canonically isomorphic to the absolute Galois group $G_(F_v) = op("Gal")(overline(F)_v \/ F_v)$ of the $v$-adic completion $F_v$, while the quotient $D_v \/ I_v tilde.equiv hat(bb(Z))$ is topologically generated by the arithmetic Frobenius element $op("Frob")_v$.

  Let $S$ be a finite set of finite places of $F$. Denote by $F_S subset.eq Omega$ the maximal Galois extension of $F$ inside $Omega$ that is unramified at every finite place $v in.not S$, and set
  $ G_(F, S) = op("Gal")(F_S \/ F) tilde.equiv G_F \/ overline(chevron.l I_w : w divides.not S chevron.r), $
  where the closed normal subgroup is topologically generated by all inertia groups at places of $Omega$ not lying over $S$. For each $v in S$, composing the inclusion $D_v arrow.r.hook G_F$ with the quotient map $pi_S : G_F -> G_(F, S)$ yields a continuous homomorphism $op("loc")_v : D_v -> G_(F, S)$ (formalized as `locFam`). When $S$ contains the set $op("Above")(F, ell) = \{ v : ell in frak(p)_v \}$ of all places above a rational prime $ell$, the group $G_(F, S)$ is the étale fundamental group $pi_1^"et" (op("Spec") cal(O)_(F, S))$ of the $S$-integer ring $cal(O)_(F, S)$. Because the higher étale homotopy groups of $op("Spec") cal(O)_(F, S)$ vanish away from the characteristic of the residue fields in $S$, for any $ell$-primary discrete or $bb(Z)_ell$-adic $G_(F, S)$-module $M$ one has canonical identifications
  $ H^i (G_(F, S), M) tilde.equiv H^i_"et" (op("Spec") cal(O)_(F, S), cal(F)_M). $
  In particular, when $S = op("Above")(F, ell)$, we frequently write $H^i (cal(O)_F [1\/ell], M)$ for $H^i (G_(F, S), M)$.

  The following lemma, formalized as `InfUnram` in `Formalism.GaloisCohomology.Statement`, characterizes the image of inflation from $G_(F, S)$ to $G_F$ in degree $1$.

  #lemma(title: "Unramified Characterization of Inflation (`InfUnram`)")[
    Let $S$ be a set of finite places of $F$, and let $M$ be a Hausdorff topological $R[G_(F, S)]$-module with continuous action. Let $pi_S : G_F -> G_(F, S)$ be the canonical quotient map. Then the inflation map
    $ op("Inf") : H^1 (G_(F, S), M) -> H^1 (G_F, M) $
    is injective, and a cohomology class $x in H^1 (G_F, M)$ lies in the image of $op("Inf")$ if and only if for every finite place $v in.not S$ and every valuation subring $A subset.eq Omega$ lying over $v$, the restriction of $x$ to the inertia subgroup $I_A subset.eq G_F$ vanishes:
    $ op("Res")_(I_A) (x) = 0. $
  ]

  #proof[
    Set $N = ker(pi_S) = op("Gal")(Omega \/ F_S)$. Since $N$ acts trivially on $M$, we have $M^N = M$ and $H^1 (N, M) = op("Hom")_"cont" (N, M)$. The inflation–restriction sequence gives
    $ 0 -> H^1 (G_(F, S), M) ->^(op("Inf")) H^1 (G_F, M) ->^(op("Res")) op("Hom")_"cont" (N, M)^(G_(F, S)), $
    establishing injectivity of $op("Inf")$ immediately. Moreover, $x in op("im")(op("Inf"))$ if and only if the continuous homomorphism $op("Res")_N (x) : N -> M$ is identically zero. Because $N$ is topologically generated by the inertia subgroups $I_A$ as $A$ ranges over all places of $Omega$ above finite places $v in.not S$, and because $M$ is Hausdorff so that $ker(op("Res")_N (x))$ is a closed subgroup of $N$, we have $op("Res")_N (x) = 0$ if and only if $op("Res")_(I_A) (x) = 0$ for all such $A$.
  ]

  For a fixed prime $ell$, the action of $G_F$ on the $ell$-power roots of unity $mu_(ell^oo) (Omega) = union.big_(r >= 1) mu_(ell^r) (Omega)$ defines the *$ell$-adic cyclotomic character*
  $ chi_ell : G_F -> bb(Z)_ell^times, quad sigma(zeta) = zeta^(chi_ell (sigma)) quad (zeta in mu_(ell^oo) (Omega)). $
  Because the cyclotomic extension $F(mu_(ell^oo)) \/ F$ is unramified outside the places dividing $ell$, the character $chi_ell$ factors through $G_(F, S)$ whenever $S supset.eq op("Above")(F, ell)$.

  #definition(title: "Cyclotomic Twists and Cartier–Tate Duals")[
    Let $ell$ be a prime and $S supset.eq op("Above")(F, ell)$.
    1. For any integer $n in bb(Z)$, the *$n$-th cyclotomic twist* $bb(Z)_ell (n)$ is the free rank-$1$ $bb(Z)_ell$-module $bb(Z)_ell$ equipped with the $ell$-adic topology and the $G_(F, S)$-action $g dot.c x = chi_ell (g)^n x$ (formalized as `zlTw`).
    2. For any integer $e in bb(Z)$, the discrete divisible twist $bb(Q)_ell \/ bb(Z)_ell (-e)$ is the discrete $bb(Z)_ell$-module $bb(Q)_ell \/ bb(Z)_ell$ with $G_(F, S)$-action $g dot.c x = chi_ell (g)^(-e) x$ (formalized as `qzTw`).
    3. For a finite discrete $bb(Z) \/ ell^r bb(Z)$-module $M$ with continuous $G_(F, S)$-action (or $D_v$-action), its *Cartier–Tate dual* is
       $ M^or (1) = op("Hom")_(bb(Z) \/ ell^r bb(Z)) (M, bb(Z) \/ ell^r bb(Z)) times.o mu_(ell^r) $
       with $G_(F, S)$-action $(g dot.c phi)(m) = chi_ell (g) dot.c phi(g^(-1) m)$ (formalized as `twDual`).
  ]

  Observe that at finite level $r >= 1$, the Cartier–Tate dual of $M_r = (bb(Z) \/ ell^r bb(Z)) (e+1)$ is canonically isomorphic to
  $ M_r^or (1) tilde.equiv (bb(Z) \/ ell^r bb(Z)) (-e). $
  Passing to the inverse limit on the left and the direct limit on the right, the profinite module $bb(Z)_ell (e+1) = limits(op("lim"))_(<- r) (bb(Z) \/ ell^r bb(Z))(e+1)$ and the discrete torsion module $bb(Q)_ell \/ bb(Z)_ell (-e) = limits(op("lim"))_(-> r) (bb(Z) \/ ell^r bb(Z))(-e)$ are *Pontryagin–Tate duals*:
  $ op("Hom")_"cont" (bb(Z)_ell (e+1), bb(Q)_ell \/ bb(Z)_ell (1)) tilde.equiv bb(Q)_ell \/ bb(Z)_ell (-e). $
  This exact duality between $bb(Z)_ell (e+1)$ and $bb(Q)_ell \/ bb(Z)_ell (-e)$ is the engine behind the length formula `VFormula` in Section 10.2.

  === Tate Local Duality and Local Euler–Poincaré Characteristic

  Let $v$ be a finite place of $F$, with completion $F_v$ of degree $d_v = [F_v : bb(Q)_p]$ over $bb(Q)_p$ (where $v mid p$) and absolute Galois group $G_(F_v) tilde.equiv D_v$. Local class field theory provides a canonical invariant isomorphism
  $ op("inv")_v : H^2 (G_(F_v), mu_(ell^r)) tilde.equiv bb(Z) \/ ell^r bb(Z), $
  arising from the Kummer exact sequence $1 -> mu_(ell^r) -> overline(F)_v^times ->^(ell^r) overline(F)_v^times -> 1$, Hilbert's Theorem 90 ($H^1 (G_(F_v), overline(F)_v^times) = 0$), and the Hasse invariant isomorphism $op("inv")_v : op("Br")(F_v) = H^2 (G_(F_v), overline(F)_v^times) tilde.equiv bb(Q) \/ bb(Z)$.

  For any finite discrete $bb(Z) \/ ell^r bb(Z)$-module $M$ with continuous $G_(F_v)$-action, the evaluation pairing $M^or (1) times M -> mu_(ell^r)$ induces via cup product a bilinear pairing
  $
    &union : H^i (G_(F_v), M) times H^(2-i) (G_(F_v), M^or (1)) \
    &quad -> H^2 (G_(F_v), mu_(ell^r)) ->^(op("inv")_v) bb(Z) \/ ell^r bb(Z).
  $

  #theorem(title: "Tate Local Duality and Local Euler Characteristic")[
    Let $v$ be a finite place of $F$ and $M$ a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F_v)]$-module.
    1. *(Finiteness and cohomological dimension)* The groups $H^i (G_(F_v), M)$ are finite for all $i >= 0$, and $H^i (G_(F_v), M) = 0$ for all $i >= 3$.
    2. *(Tate Local Duality)* For each $i in \{0, 1, 2\}$, the cup-product pairing
       $ H^i (G_(F_v), M) times H^(2-i) (G_(F_v), M^or (1)) -> bb(Z) \/ ell^r bb(Z) $
       is nondegenerate, inducing a canonical isomorphism $H^i (G_(F_v), M) tilde.equiv H^(2-i) (G_(F_v), M^or (1))^or$.
    3. *(Unramified Orthogonality)* Suppose $v divides.not ell$ and $M$ is unramified at $v$ (i.e., $I_v$ acts trivially on $M$). Then the unramified subspaces
       $
         H^1_"ur" (G_(F_v), M) &= ker(H^1 (G_(F_v), M) -> H^1 (I_v, M)) \
           &tilde.equiv H^1 (G_(F_v) \/ I_v, M)
       $
       and $H^1_"ur" (G_(F_v), M^or (1))$ are exact annihilators of one another under the local Tate pairing on $H^1$.
    4. *(Local Euler–Poincaré Characteristic)* Write $delta_(v mid ell) = [F_v : bb(Q)_ell]$ if $v mid ell$ and $delta_(v mid ell) = 0$ if $v divides.not ell$. Then
       $ |H^1 (G_(F_v), M)| = |H^0 (G_(F_v), M)| dot.c |H^2 (G_(F_v), M)| dot.c |M|^(delta_(v mid ell)). $
  ]

  It is instructive to verify parts (3) and (4) in the tame case ($v divides.not ell$) directly, as the argument displays the exact interplay between Frobenius, inertia, and cup products.

  #proof(title: "Tame Case of (3) and (4)")[
    Assume $v divides.not ell$ and $I_v$ acts trivially on $M$. First, $G_(F_v) \/ I_v tilde.equiv hat(bb(Z))$ has cohomological dimension $1$, so $H^2 (G_(F_v) \/ I_v, mu_(ell^r)) = 0$. Since the cup product commutes with inflation, the pairing of any two classes in $H^1_"ur" (G_(F_v), M) = op("im")(H^1 (G_(F_v) \/ I_v, M))$ and $H^1_"ur" (G_(F_v), M^or (1))$ factors through $H^2 (G_(F_v) \/ I_v, mu_(ell^r)) = 0$. Hence $H^1_"ur" (G_(F_v), M)$ and $H^1_"ur" (G_(F_v), M^or (1))$ are orthogonal.

    Next, because $hat(bb(Z)) = overline(chevron.l op("Frob")_v chevron.r)$, a $1$-cocycle on $hat(bb(Z))$ is uniquely determined by its value on $op("Frob")_v$, so $H^1_"ur" (G_(F_v), M) tilde.equiv M \/ (op("Frob")_v - 1) M$. From the exact sequence
    $ 0 -> M^(op("Frob")_v = 1) -> M ->^(op("Frob")_v - 1) M -> M \/ (op("Frob")_v - 1) M -> 0 $
    and the finiteness of $M$, we obtain $|H^1_"ur" (G_(F_v), M)| = |H^0 (G_(F_v), M)|$. Applying the same calculation to $M^or (1)$ and using local Tate duality ($i = 2$) gives
    $ |H^1_"ur" (G_(F_v), M^or (1))| = |H^0 (G_(F_v), M^or (1))| = |H^2 (G_(F_v), M)|. $
    Now consider the inflation–restriction exact sequence for $I_v lt.tri.eq G_(F_v)$:
    $ 0 -> H^1_"ur" (G_(F_v), M) -> H^1 (G_(F_v), M) -> H^1 (I_v, M)^(G_(F_v) \/ I_v) -> 0, $
    where the right-hand surjectivity holds because $H^2 (G_(F_v) \/ I_v, M) = 0$. Since $v divides.not ell$, the wild inertia subgroup $P_v subset.eq I_v$ is a pro-$p$ group ($p != ell$), so $H^1 (P_v, M) = 0$; the tame inertia quotient $I_v \/ P_v tilde.equiv product_(q != p) bb(Z)_q (1)$ has maximal pro-$ell$ quotient canonically isomorphic to $bb(Z)_ell (1)$. Therefore
    $ H^1 (I_v, M)^(G_(F_v) \/ I_v) tilde.equiv op("Hom")_(G_(F_v) \/ I_v) (bb(Z)_ell (1), M) tilde.equiv M(-1)^(op("Frob")_v = 1). $
    Because $M(-1)$ and $M^or (1)$ are finite Pontryagin duals of each other as $G_(F_v) \/ I_v$-modules, $|M(-1)^(op("Frob")_v = 1)| = |H^0 (G_(F_v), M^or (1))| = |H^2 (G_(F_v), M)|$. Multiplying by $|H^1_"ur" (G_(F_v), M)| = |H^0 (G_(F_v), M)|$ yields
    $ |H^1 (G_(F_v), M)| = |H^0 (G_(F_v), M)| dot.c |H^2 (G_(F_v), M)|. $
    Finally, since $|H^1_"ur" (G_(F_v), M)| dot.c |H^1_"ur" (G_(F_v), M^or (1))| = |H^0 (G_(F_v), M)| dot.c |H^2 (G_(F_v), M)| = |H^1 (G_(F_v), M)|$, the orthogonal subspaces $H^1_"ur" (G_(F_v), M)$ and $H^1_"ur" (G_(F_v), M^or (1))$ must be exact annihilators of one another under the nondegenerate local Tate pairing.
  ]

  In the wild case $v mid ell$, the additional factor $|M|^([F_v : bb(Q)_ell])$ comes from the rank of the local unit group $cal(O)_(F_v)^times$. By the $ell$-adic logarithm, $cal(O)_(F_v)^times$ contains an open subgroup isomorphic to $bb(Z)_ell^([F_v : bb(Q)_ell])$, so by Kummer theory
  $ |H^1 (G_(F_v), mu_(ell^r))| = |F_v^times \/ (F_v^times)^(ell^r)| = ell^(r ([F_v : bb(Q)_ell] + 1)) dot.c |mu_(ell^r) (F_v)|. $
  Since $|H^0 (G_(F_v), mu_(ell^r))| = |mu_(ell^r) (F_v)|$ and $|H^2 (G_(F_v), mu_(ell^r))| = ell^r$, the local Euler–Poincaré formula holds for $M = mu_(ell^r)$, and Tate's theorem extends it to all finite $G_(F_v)$-modules via dévissage, Shapiro's lemma, and Brauer induction.

  === Global Euler Characteristic and the Poitou–Tate Nine-Term Sequence

  Now let $S$ be a finite set of finite places of $F$ containing $op("Above")(F, ell)$, and let $M$ be a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module. For each real archimedean place $w$ of $F$, fix a complex conjugation $c_w in G_F$ associated to an embedding $Omega arrow.r.hook bb(C)$ extending $w$. Define the archimedean invariant cardinality (`archH0Card` in `ReciprocityTheory.Gal`) by
  $ A_oo (F, M) = ( product_(w " real") |M^(c_w = 1)| ) dot.c |M|^(r_2 (F)), $
  where $r_1 (F)$ and $r_2 (F)$ denote the numbers of real and complex places of $F$, so that $[F : bb(Q)] = r_1 (F) + 2 r_2 (F)$.

  #theorem(title: "Global Finiteness and Global Euler–Poincaré Characteristic")[
    Let $S supset.eq op("Above")(F, ell)$ be a finite set of finite places of $F$ and $M$ a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module.
    1. The cohomology groups $H^i (G_(F, S), M)$ are finite for all $i >= 0$. If $ell != 2$ or $F$ is totally complex (the condition `PTCase F l`), then $H^i (G_(F, S), M) = 0$ for all $i >= 3$.
    2. The global Euler–Poincaré characteristic satisfies
       $
         frac(|H^0 (G_(F, S), M)| dot.c |H^2 (G_(F, S), M)|, |H^1 (G_(F, S), M)|)
         &= frac(A_oo (F, M), |M|^([F : bb(Q)])) \
         &= product_(w mid oo) frac(|H^0 (G_(F_w), M)|, |M|^(d_w)),
       $
       where $d_w = [F_w : bb(R)] in \{1, 2\}$. Equivalently,
       $
         &|H^0 (G_(F, S), M)| dot.c |H^2 (G_(F, S), M)| dot.c |M|^([F : bb(Q)]) \
         &quad = |H^1 (G_(F, S), M)| dot.c A_oo (F, M).
       $
  ]

  Notice a striking feature of the global Euler–Poincaré characteristic: the right-hand side is *independent of $S$* (so long as $S supset.eq op("Above")(F, ell)$) and depends only on the archimedean behavior of $M$. When $F$ is totally complex ($r_1 (F) = 0$, $[F : bb(Q)] = 2 r_2 (F)$), the formula simplifies to
  $ frac(|H^0 (G_(F, S), M)| dot.c |H^2 (G_(F, S), M)|, |H^1 (G_(F, S), M)|) = |M|^(-r_2 (F)). $
  Enlarging $S$ by adding a finite place $v divides.not ell$ increases $|H^1 (G_(F, S), M)|$ and $|H^2 (G_(F, S), M)|$ by the exact same factor, leaving their ratio invariant!

  To compare global cohomology with the product of local cohomology groups over $v in S$, we introduce the *compactly supported cohomology* $H^i_c (G_(F, S), M)$ (formalized in `GroundTheory.ProfCoh`), defined as the cohomology of the shifted mapping cone of the localization morphism of continuous cochain complexes:
  $ C^bullet_c (G_(F, S), M) = op("Cone")( C^bullet (G_(F, S), M) ->^(op("loc")) product_(v in S) C^bullet (G_(F_v), M) )[-1]. $
  By construction, $H^i_c (G_(F, S), M)$ sits in a canonical long exact sequence
  $
    dots.c -> H^i_c (G_(F, S), M) -> H^i (G_(F, S), M) ->^(op("loc")_i) product_(v in S) H^i (G_(F_v), M) \
    -> H^(i+1)_c (G_(F, S), M) -> dots.c
  $
  For each $i in \{0, 1, 2\}$, the diagonal localization map $op("loc")_(2-i)$ for $M^or (1)$, combined with local Tate duality, yields a dual map
  $ op("loc")_(2-i)^* : product_(v in S) H^i (G_(F_v), M) -> H^(2-i) (G_(F, S), M^or (1))^or. $
  The global reciprocity law of class field theory ($sum_v op("inv")_v (x_v) = 0$ for global Brauer classes $x in op("Br")(F)$) produces a trace isomorphism $H^3_c (G_(F, S), mu_(ell^r)) tilde.equiv bb(Z) \/ ell^r bb(Z)$ (`gsCompactInv`), and cup product with this trace yields *Poitou–Tate global duality*:

  #theorem(title: "Poitou–Tate Duality and Nine-Term Exact Sequence (`PoitouTateNineTerm`)")[
    Let $S supset.eq op("Above")(F, ell)$ be a finite set of finite places of $F$, and assume that `PTCase F l` holds ($ell != 2$ or $F$ is totally complex). Let $M$ be a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module with Cartier–Tate dual $M^or (1)$. Then:
    1. *(Compactly Supported Global Duality)* For all integers $r, s >= 0$ with $r + s = 3$, the cup-product pairing
       $ H^r_c (G_(F, S), M) times H^s (G_(F, S), M^or (1)) -> H^3_c (G_(F, S), mu_(ell^r)) tilde.equiv bb(Z) \/ ell^r bb(Z) $
       is nondegenerate, inducing canonical isomorphisms $H^r_c (G_(F, S), M) tilde.equiv H^(3-r) (G_(F, S), M^or (1))^or$ (`poitouTate_duality_gs`).
    2. *(Nine-Term Exact Sequence)* Substituting (1) into the mapping-cone long exact sequence yields a canonical nine-term exact sequence of finite $bb(Z) \/ ell^r bb(Z)$-modules (`poitouTate_nineTerm_gs`):
       $
         0 &-> H^0 (G_(F, S), M) ->^(op("loc")_0) product_(v in S) H^0 (G_(F_v), M) \
           &-> H^2 (G_(F, S), M^or (1))^or -> H^1 (G_(F, S), M) \
           &->^(op("loc")_1) product_(v in S) H^1 (G_(F_v), M) -> H^1 (G_(F, S), M^or (1))^or \
           &-> H^2 (G_(F, S), M) ->^(op("loc")_2) product_(v in S) H^2 (G_(F_v), M) \
           &-> H^0 (G_(F, S), M^or (1))^or -> 0.
       $
    3. *(Poitou–Tate Duality for $op("Ш")$)* Define the $i$-th Tate–Shafarevich kernel by
       $ op("Ш")^i_S (F, M) = ker(op("loc")_i : H^i (G_(F, S), M) -> product_(v in S) H^i (G_(F_v), M)). $
       Then there is a canonical nondegenerate bilinear pairing (`poitouTate_sha_gs`)
       $ op("Ш")^1_S (F, M) times op("Ш")^2_S (F, M^or (1)) -> bb(Q) \/ bb(Z), $
       inducing an isomorphism $op("Ш")^2_S (F, M^or (1)) tilde.equiv op("Ш")^1_S (F, M)^or$ and in particular $|op("Ш")^1_S (F, M)| = |op("Ш")^2_S (F, M^or (1))|$.
  ]

  #proof(title: "Deduction of (3) from (2)")[
    From the nine-term exact sequence (2), the kernel of $op("loc")_2 : H^2 (G_(F, S), M) -> product_(v in S) H^2 (G_(F_v), M)$ is the image of $H^1 (G_(F, S), M^or (1))^or -> H^2 (G_(F, S), M)$, which equals the cokernel of the preceding map
    $ op("loc")_1^* : product_(v in S) H^1 (G_(F_v), M) -> H^1 (G_(F, S), M^or (1))^or. $
    Under Pontryagin duality of finite abelian groups, the cokernel of $op("loc")_1^*$ is canonically the Pontryagin dual of the kernel of its transpose
    $ op("loc")_1 : H^1 (G_(F, S), M^or (1)) -> product_(v in S) H^1 (G_(F_v), M^or (1)). $
    That kernel is by definition $op("Ш")^1_S (F, M^or (1))$. Hence $op("Ш")^2_S (F, M) tilde.equiv op("Ш")^1_S (F, M^or (1))^or$; replacing $M$ by $M^or (1)$ gives $op("Ш")^2_S (F, M^or (1)) tilde.equiv op("Ш")^1_S (F, M)^or$.
  ]

  #remark(title: "Archimedean Places and the Hypothesis `PTCase`")[
    In full generality, the Poitou–Tate sequence includes the Tate-modified cohomology $hat(H)^i (G_(F_w), M)$ at the real infinite places $w$ of $F$. When $ell != 2$, the group $G_(F_w) tilde.equiv bb(Z) \/ 2 bb(Z)$ has order $2$ coprime to $|M|$, so $hat(H)^i (G_(F_w), M) = 0$ for all $i in bb(Z)$. When $F$ is totally complex, there are no real places at all. Thus under the clean hypothesis `PTCase F l` ($ell != 2$ or $r_1 (F) = 0$), all archimedean terms vanish identically from the Poitou–Tate nine-term sequence. In the Alpöge–Claude–Riemann proof, the host fields $E$ are CM fields—hence totally complex—so `PTCase E l` holds unconditionally for *every* prime $ell$, including $ell = 2$.
  ]

  // ==========================================================================
  // Section 10.2
  // ==========================================================================
  == Tate–Shafarevich Kernels and the Exact Length Identity

  We now specialize the Poitou–Tate nine-term sequence to the cyclotomic twists $bb(Z)_ell (e+1)$ and $bb(Q)_ell \/ bb(Z)_ell (-e)$ with $S = op("Above")(F, ell)$, and derive the exact $bb(Z)_ell$-module length identity `VFormula` that links étale $H^2$ (and hence Quillen $K$-groups) to Tate–Shafarevich kernels.

  === Module Length and Passage to $ell$-Adic Limits

  Recall that for any module $M$ over a discrete valuation ring $R$ (here $R = bb(Z)_ell$), the *length* $op("len")_R (M) in bb(N) union \{oo\}$ (`Module.length ℤ_[l] M`) is the supremum of lengths $k$ of strictly increasing chains of submodules $0 = M_0 subset.neq M_1 subset.neq dots.c subset.neq M_k = M$. When $M$ is a finite $bb(Z)_ell$-module, its cardinality is
  $ |M| = ell^(op("len")_(bb(Z)_ell) (M)), $
  and length is strictly additive on short exact sequences: if $0 -> A -> B -> C -> 0$ is exact, then
  $ op("len")_(bb(Z)_ell) (B) = op("len")_(bb(Z)_ell) (A) + op("len")_(bb(Z)_ell) (C) $
  in $bb(N) union \{oo\}$. Moreover, if $M$ is finite, then its Pontryagin dual $M^or = op("Hom")_"cont" (M, bb(Q)_ell \/ bb(Z)_ell)$ is non-canonically isomorphic to $M$ as a $bb(Z)_ell$-module and hence has the exact same length: $op("len")_(bb(Z)_ell) (M^or) = op("len")_(bb(Z)_ell) (M)$.

  Let $F$ be a number field, $ell$ a prime, and $S = op("Above")(F, ell)$ the set of all finite places of $F$ dividing $ell$. For each integer $e in bb(Z)$, consider the two $G_(F, S)$-modules
  $ M = bb(Z)_ell (e+1), quad M^* = bb(Q)_ell \/ bb(Z)_ell (-e). $
  At finite level $r >= 1$, set $M_r = (bb(Z) \/ ell^r bb(Z))(e+1)$ and $M_r^* = (bb(Z) \/ ell^r bb(Z))(-e) tilde.equiv M_r^or (1)$. Because every $H^i (G_(F, S), M_r)$ and $H^i (G_(F_v), M_r)$ is finite, the inverse systems satisfy the Mittag-Leffler condition, giving canonical isomorphisms
  $
    H^i (G_(F, S), bb(Z)_ell (e+1)) &tilde.equiv limits(op("lim"))_(<- r) H^i (G_(F, S), M_r), \
    H^i (G_(F, S), bb(Q)_ell \/ bb(Z)_ell (-e)) &tilde.equiv limits(op("lim"))_(-> r) H^i (G_(F, S), M_r^*),
  $
  and analogously for the local cohomology groups at every $v in S$. Define the Tate–Shafarevich kernels
  $
    &op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e)) \
    &quad = ker( H^1 (G_(F, S), bb(Q)_ell \/ bb(Z)_ell (-e)) -> product_(v mid ell) H^1 (G_(F_v), bb(Q)_ell \/ bb(Z)_ell (-e)) ), \
    &op("Ш")^2_S (F, bb(Z)_ell (e+1)) \
    &quad = ker( H^2 (G_(F, S), bb(Z)_ell (e+1)) -> product_(v mid ell) H^2 (G_(F_v), bb(Z)_ell (e+1)) ).
  $
  In `Formalism.GaloisCohomology.Statement`, these are formalized as `Sha D e` and `Sha2Zl D e`, with lengths `shaLen D e` and `VLen D e` $= op("len")_(bb(Z)_ell) H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1))$.

  === The Exact Length Identity (`VFormula`)

  Taking the inverse limit over $r$ of the last four terms of the Poitou–Tate nine-term exact sequence for $M_r = (bb(Z) \/ ell^r bb(Z))(e+1)$ (whose dual is $M_r^or (1) = M_r^*$)—exactness being preserved by $limits(op("lim"))_(<- r)$ because all terms at finite level $r$ are finite—we obtain the exact sequence of $bb(Z)_ell$-modules:
  $
    0 &-> op("Ш")^2_S (F, bb(Z)_ell (e+1)) -> H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) \
      &->^(op("loc")_2) product_(v mid ell) H^2 (G_(F_v), bb(Z)_ell (e+1)) -> H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e))^or -> 0.
  $
  Here we used the canonical Pontryagin duality
  $
    limits(op("lim"))_(<- r) H^0 (G_(F, S), M_r^*)^or &tilde.equiv ( limits(op("lim"))_(-> r) H^0 (G_(F, S), M_r^*) )^or \
    &= H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e))^or,
  $
  where $H^0 (G_(F, S), bb(Q)_ell \/ bb(Z)_ell (-e)) = H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e))$ since $chi_ell$ factors through $G_(F, S)$.

  #theorem(title: "Exact Length Identity (`VFormula`)")[
    Let $F$ be a number field, $ell$ a rational prime, $S = \{v : v mid ell\}$, and $e in bb(Z)$. Assume `PTCase F l`, i.e., $ell != 2$ or $F$ is totally complex. Then in $bb(N) union \{oo\}$,
    $
      &op("len")_(bb(Z)_ell) H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) + op("len")_(bb(Z)_ell) H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e)) \
      &quad = op("len")_(bb(Z)_ell) op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e)) + sum_(v mid ell) op("len")_(bb(Z)_ell) H^0 (F_v, bb(Q)_ell \/ bb(Z)_ell (-e)).
    $
  ]

  #proof[
    Consider the localization map
    $ op("loc")_2 : H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) -> product_(v mid ell) H^2 (G_(F_v), bb(Z)_ell (e+1)). $
    By definition, $ker(op("loc")_2) = op("Ш")^2_S (F, bb(Z)_ell (e+1))$. Let $I = op("im")(op("loc")_2)$ and $C = op("coker")(op("loc")_2)$. We have two short exact sequences of $bb(Z)_ell$-modules:
    $ 0 -> op("Ш")^2_S (F, bb(Z)_ell (e+1)) -> H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) -> I -> 0, $
    $ 0 -> I -> product_(v mid ell) H^2 (G_(F_v), bb(Z)_ell (e+1)) -> C -> 0. $
    By additivity of $bb(Z)_ell$-module length on short exact sequences (and additivity of length over finite products),
    $ op("len") H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) = op("len") op("Ш")^2_S (F, bb(Z)_ell (e+1)) + op("len") I $
    and
    $ sum_(v mid ell) op("len") H^2 (G_(F_v), bb(Z)_ell (e+1)) = op("len") I + op("len") C. $
    Now apply the three duality inputs formalized in `Formalism.GaloisCohomology.Statement`:
    1. *Poitou–Tate cokernel (`PTCokerAt`)*: The tail of the Poitou–Tate nine-term exact sequence identifies $C tilde.equiv H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e))^or$, so
       $ op("len") C = op("len") H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e)). $
    2. *Poitou–Tate $op("Ш")$-duality (`PTShaAt`)*: Passing to the limit in the finite-level Poitou–Tate pairing $op("Ш")^2_S (F, M_r) tilde.equiv op("Ш")^1_S (F, M_r^*)^or$ gives $op("Ш")^2_S (F, bb(Z)_ell (e+1)) tilde.equiv op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e))^or$, so
       $ op("len") op("Ш")^2_S (F, bb(Z)_ell (e+1)) = op("len") op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e)). $
    3. *Local Tate duality (`TateLocalDualityH2AtPlaces`)*: For each $v mid ell$, passing to the limit in $H^2 (G_(F_v), M_r) tilde.equiv H^0 (G_(F_v), M_r^*)^or$ yields $H^2 (G_(F_v), bb(Z)_ell (e+1)) tilde.equiv H^0 (G_(F_v), bb(Q)_ell \/ bb(Z)_ell (-e))^or$, so
       $ op("len") H^2 (G_(F_v), bb(Z)_ell (e+1)) = op("len") H^0 (F_v, bb(Q)_ell \/ bb(Z)_ell (-e)). $

    Adding $op("len") C$ to the first length equation and substituting $op("len") I + op("len") C = sum_(v mid ell) op("len") H^2 (G_(F_v), bb(Z)_ell (e+1))$ gives
    $
      &op("len") H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) + op("len") C \
      &quad = op("len") op("Ш")^2_S (F, bb(Z)_ell (e+1)) + op("len") I + op("len") C \
      &quad = op("len") op("Ш")^2_S (F, bb(Z)_ell (e+1)) + sum_(v mid ell) op("len") H^2 (G_(F_v), bb(Z)_ell (e+1)).
    $
    Substituting the three duality equalities (1)–(3) yields
    $
      &op("len") H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) + op("len") H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e)) \
      &quad = op("len") op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e)) + sum_(v mid ell) op("len") H^0 (F_v, bb(Q)_ell \/ bb(Z)_ell (-e)).
    $
    Notice that this derivation requires *no finiteness assumption* on $I$ or $H^2$: because addition in $bb(N) union \{oo\}$ is associative and commutative and we never subtract $op("len") I$, the identity holds unconditionally in $bb(N) union \{oo\}$.
  ]

  To use `VFormula` quantitatively, we need to evaluate the $H^0$ terms explicitly. Fortunately, $H^0 (K, bb(Q)_ell \/ bb(Z)_ell (-e))$ is completely elementary for any global or local field $K$ of characteristic $0$:

  #proposition(title: "Explicit Computation of Cyclotomic $H^0$ Lengths")[
    Let $K$ be a number field or a finite extension of $bb(Q)_ell$, and let $e != 0$ be a nonzero integer. Let $U_K = chi_ell (G_K) subset.eq bb(Z)_ell^times$ be the image of the $ell$-adic cyclotomic character on $G_K$, and let $w_e (K)$ be the largest power of $ell$ dividing $u^e - 1$ for all $u in U_K$ (equivalently, $w_e (K) = ell^m$ where $m = min_(u in U_K) v_ell (u^e - 1)$). Then
    $
      H^0 (K, bb(Q)_ell \/ bb(Z)_ell (-e)) &tilde.equiv bb(Z) \/ w_e (K) bb(Z), \
      op("len")_(bb(Z)_ell) H^0 (K, bb(Q)_ell \/ bb(Z)_ell (-e)) &= v_ell (w_e (K)) < oo.
    $
    In particular, if $K$ is linearly disjoint from $bb(Q)(mu_(ell^oo))$ over $bb(Q)$ (for example $K = bb(Q)$ or $K = bb(Q)_ell$) and $ell$ is odd, then
    $ op("len")_(bb(Z)_ell) H^0 (K, bb(Q)_ell \/ bb(Z)_ell (-e)) = cases(1 + v_ell (e) & "if" (ell - 1) mid e, 0 & "if" (ell - 1) divides.not e.) $
  ]

  #proof[
    An element $x in bb(Q)_ell \/ bb(Z)_ell$ is fixed by $G_K$ under $chi_ell^(-e)$ if and only if $(u^(-e) - 1) x = 0$ for all $u in U_K$, equivalently $(u^e - 1) x = 0$ for all $u in U_K$ (since $u in bb(Z)_ell^times$). Because $U_K$ is an open subgroup of $bb(Z)_ell^times$ (by class field theory, $[bb(Z)_ell^times : U_K] <= [K : bb(Q)]$ or $[K : bb(Q)_ell]$) and $e != 0$, there exists $u in U_K$ with $u^e != 1$, so $m = min_(u in U_K) v_ell (u^e - 1) < oo$. The closed ideal generated by $\{ u^e - 1 : u in U_K \}$ in $bb(Z)_ell$ is therefore $ell^m bb(Z)_ell$, and the elements of $bb(Q)_ell \/ bb(Z)_ell$ annihilated by $ell^m$ form the unique cyclic subgroup $ell^(-m) bb(Z)_ell \/ bb(Z)_ell tilde.equiv bb(Z) \/ ell^m bb(Z)$ of length $m$. When $U_K = bb(Z)_ell^times$ and $ell$ is odd, $bb(Z)_ell^times tilde.equiv mu_(ell - 1) times (1 + ell bb(Z)_ell)$; if $(ell - 1) divides.not e$, a generator $zeta in mu_(ell - 1)$ has $zeta^e - 1 in bb(Z)_ell^times$ ($m = 0$), whereas if $(ell - 1) mid e$, every $u in bb(Z)_ell^times$ satisfies $u^e in 1 + ell^(1 + v_ell (e)) bb(Z)_ell$ with equality for $u = 1 + ell$ ($m = 1 + v_ell (e)$).
  ]

  #example(title: "Worked Evaluations of `VFormula`")[
    1. *Over $F = bb(Q)$ (odd prime $ell$, $e >= 1$):* There is a unique place $v = ell$ above $ell$, and $U_(bb(Q)) = U_(bb(Q)_ell) = bb(Z)_ell^times$. Thus the global and local $H^0$ lengths are equal and finite, so `VFormula` cancels them identically and gives
       $ op("len")_(bb(Z)_ell) H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1)) = op("len")_(bb(Z)_ell) op("Ш")^1_(\{ell\}) (bb(Q), bb(Q)_ell \/ bb(Z)_ell (-e)). $
    2. *Over a CM field $E$ in which $ell$ splits:* Suppose $ell$ is odd and splits completely in $E$ into $g_ell = [E : bb(Q)]$ places $v_1, dots.c, v_(g_ell)$ above $ell$, with $E$ linearly disjoint from $bb(Q)(mu_(ell^oo))$. Then $E_(v_i) tilde.equiv bb(Q)_ell$ for each $i$, so when $(ell - 1) mid e$, the local sum is $g_ell (1 + v_ell (e))$ while the global $H^0$ length is $1 + v_ell (e)$. Hence `VFormula` reads
       $
         op("len")_(bb(Z)_ell) H^2 (cal(O)_E [1\/ell], bb(Z)_ell (e+1)) &= op("len")_(bb(Z)_ell) op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e)) \
         &quad + (g_ell - 1)(1 + v_ell (e)).
       $
       In general, the discrepancy $sum_(v mid ell) op("len") H^0 (E_v, bb(Q)_ell \/ bb(Z)_ell (-e)) - op("len") H^0 (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ is always nonnegative and completely explicit in terms of the splitting behavior of $ell$ in $E$ and $v_ell (e)$.
  ]

  === Connection to Kummer–Vandiver, Quillen–Lichtenbaum, and `VVle`

  Why is the cohomology group $H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1))$ one of the deepest objects in algebraic number theory? By the *Quillen–Lichtenbaum conjecture*—proved for $F = bb(Q)$ and odd $ell$ by Soulé, Dwyer–Friedlander, and Mazur–Wiles, and in full generality for all number fields and all primes $ell$ via the Rost–Voevodsky proof of the Bloch–Kato norm residue isomorphism—the étale Chern character maps the algebraic $K$-groups of $cal(O)_F$ isomorphically onto étale cohomology in positive degrees. Specifically, for $F = bb(Q)$, odd $ell$, and every integer $e >= 1$,
  $ K_(2e) (bb(Z)) times.o_(bb(Z)) bb(Z)_ell tilde.equiv H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1)), $
  $ K_(2e+1) (bb(Z)) times.o_(bb(Z)) bb(Z)_ell tilde.equiv H^1 (bb(Z)[1\/ell], bb(Z)_ell (e+1)). $
  Over a general number field $F$, for odd $ell$ and $e >= 1$, one likewise has $K_(2e) (cal(O)_F) times.o_(bb(Z)) bb(Z)_ell tilde.equiv H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1))$ (and $K_(2e) (cal(O)_F)$ is a finite abelian group by Borel's and Quillen's finiteness theorems, so `VLen` is always finite for $e >= 1$!).

  To see the intimate link with the classical *Kummer–Vandiver conjecture*, recall that the conjecture asserts that $ell$ does not divide the class number $h^+_ell = |op("Cl")(bb(Q)(zeta_ell)^+)|$ of the maximal real subfield of the $ell$-th cyclotomic field. By Kummer theory and Soulé's descent from $bb(Q)(zeta_ell)$ to $bb(Q)$, the structure of $H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1))$ splits sharply according to the parity of $e >= 1$:
  - *Odd $e$:* The Teichmüller character power $omega^(-e)$ is *odd*, and by Herbrand–Ribet and the Mazur–Wiles Iwasawa Main Conjecture, the order of $H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1))$ is governed by the $ell$-adic valuation of the Bernoulli number $B_(e+1) \/ (e+1)$—equivalently, the special value $zeta(-e) = -B_(e+1) \/ (e+1)$. More precisely, Lichtenbaum's formula (a theorem of Wiles for totally real fields) expresses the ratio $|K_(2e)(bb(Z))| \/ |K_(2e+1)(bb(Z))|$ up to powers of $2$ in terms of $|zeta(-e)|$. Thus $H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1))$ for odd $e$ is nontrivial whenever $ell$ is an irregular prime dividing the numerator of $B_(e+1)$.
  - *Even $e$:* The character $omega^(-e)$ is *even*, so $H^2 (bb(Z)[1\/ell], bb(Z)_ell (e+1))$ is controlled by the *plus part* $op("Cl")(bb(Q)(zeta_ell)^+)[ell^oo]$ of the cyclotomic class group! Kurihara (1992) proved that $K_(2e)(bb(Z))[ell^oo] = 0$ for all even $e >= 2$ is *equivalent* to the Kummer–Vandiver conjecture for $ell$ (in fact, $K_(4k)(bb(Z))$ is conjectured to vanish for all $k >= 1$).

  #insight-box(title: "Why `VVle` Is a Significant Weakening of Vandiver")[
    In the Alpöge–Claude–Riemann proof (item 17 and footnote 6 of `remark.pdf`), one confronts global cohomology classes in $H^1 (cal(O)_E [1\/ell], bb(Q)_ell \/ bb(Z)_ell (-e))$ over the CM host field $E$ that obstruct the integral structure of chained theta lifts and *cannot* be killed by twisting by auxiliary Hecke characters. The classes that survive local trivialization at $v mid ell$ are precisely the elements of $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$.

    If one assumed the Kummer–Vandiver conjecture (and its CM-field analogue over $E$), one would have vanishing of $H^2 (cal(O)_E [1\/ell], bb(Z)_ell (e+1))$ for even $e$ and sharp control on individual $K$-groups. Yet Kummer–Vandiver is notoriously open! Crucially, the proof does *not* need Vandiver's conjecture. By `VFormula`, controlling $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ is equivalent to controlling $H^2 (cal(O)_E [1\/ell], bb(Z)_ell (e+1))$, and the proof only requires an *aggregated weighted logarithmic upper bound* (`VVle`) on the double sum
    $ sum_ell log ell sum_(e=1)^(t-1) op("len")_(bb(Z)_ell) op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e)) $
    across primes $ell$ and twists $1 <= e <= t - 1$. Because Lichtenbaum's theorem ties the orders of the étale $H^2$ groups (and $K$-groups) to special values of Dedekind zeta functions and regulators, the aggregated sum possesses substantial slack compared to pointwise vanishing: one obtains an unconditional upper bound on `VVle`—a "significant weakening of Vandiver"—that suffices to close the divisibility and slope inequality at the heart of the proof.
  ]

  // ==========================================================================
  // Section 10.3
  // ==========================================================================
  == $p$-Adic Hodge Theory, Bloch–Kato Selmer Groups, and Integral Lattices

  While Section 10.2 treated one-dimensional cyclotomic twists via Poitou–Tate duality, the automorphic representations arising from chained theta lifts carry higher-dimensional $ell$-adic Galois representations (and families of algebraic Hecke characters). Controlling their Selmer groups—in particular, specifying the correct local conditions at places $v mid ell$—requires Fontaine's $p$-adic Hodge theory and Bloch–Kato Selmer groups, together with integral $p$-adic Hodge theory (Bhatt–Scholze prismatic/crystalline lattices) to track $bb(Z)_ell$-torsion lengths rather than merely $bb(Q)_ell$-dimensions.

  In the first two subsections below we follow standard local notation and write $p$ for the residual characteristic of a local field $K \/ bb(Q)_p$, returning to $ell$ when discussing global Selmer groups.

  === Fontaine's Period Rings $B_"cris"$ and $B_"dR"$

  Let $K$ be a finite extension of $bb(Q)_p$, with algebraic closure $overline(K)$, completion $bb(C)_p = hat(overline(K))$, ring of integers $cal(O)_(bb(C)_p)$, residue field $k$, maximal unramified subfield $K_0 = W(k)[1\/p]$, and absolute Galois group $G_K = op("Gal")(overline(K) \/ K)$. To compare $p$-adic étale cohomology (which carries a $G_K$-action) with de Rham and crystalline cohomology (which carry a Hodge filtration and a Frobenius operator $phi$), Fontaine constructs topological rings that simultaneously carry $G_K$-actions, filtrations, and Frobenius endomorphisms.

  The starting point is the *tilt* of $cal(O)_(bb(C)_p)$:
  $ cal(O)_(bb(C)_p)^flat = limits(op("lim"))_(x |-> x^p) cal(O)_(bb(C)_p) \/ p cal(O)_(bb(C)_p). $
  An element of $cal(O)_(bb(C)_p)^flat$ can be represented as a multiplicative sequence $x = (x^(0), x^(1), x^(2), dots.c)$ in $cal(O)_(bb(C)_p)$ satisfying $(x^(n+1))^p = x^(n)$, with multiplication coordinatewise and addition $(x + y)^(n) = limits(op("lim"))_(m -> oo) (x^(n+m) + y^(n+m))^(p^m)$. Equipped with the valuation $v^flat (x) = v_p (x^(0))$, $cal(O)_(bb(C)_p)^flat$ is a complete, algebraically closed, perfect valuation ring of characteristic $p$ (`TiltField`, `TiltAlgClosed`). Its ring of $p$-typical Witt vectors is Fontaine's infinitesimal period ring:
  $ A_"inf" = W(cal(O)_(bb(C)_p)^flat). $
  Because $cal(O)_(bb(C)_p)^flat$ is perfect, $A_"inf"$ carries a canonical continuous Frobenius automorphism $phi$ (lifted from $x |-> x^p$ on the tilt) and a continuous $G_K$-action commuting with $phi$. There is a canonical surjective ring homomorphism
  $ theta : A_"inf" -> cal(O)_(bb(C)_p), quad sum_(n >= 0) [x_n] p^n |-> sum_(n >= 0) x_n^sharp p^n, $
  where $x |-> x^sharp = x^(0)$ is the multiplicative *untilt* map $cal(O)_(bb(C)_p)^flat -> cal(O)_(bb(C)_p)$. The kernel of $theta$ is a principal ideal $(xi)$: choosing a compatible system of $p$-power roots of unity $epsilon = (1, zeta_p, zeta_(p^2), dots.c) in cal(O)_(bb(C)_p)^flat$ with $zeta_p != 1$, one has $epsilon^sharp = 1$ and $(phi^(-1) (epsilon))^sharp = zeta_p != 1$, and one may take the generator
  $ xi = frac([epsilon] - 1, [epsilon^(1\/p)] - 1) = 1 + [epsilon^(1\/p)] + dots.c + [epsilon^((p-1)\/p)] in ker(theta). $

  From $(A_"inf", theta, epsilon)$ we construct the two fundamental period rings:
  1. *(De Rham period ring $B_"dR"$)* Let $B_"dR"^+$ be the $ker(theta)$-adic completion of $A_"inf" [1\/p]$:
     $ B_"dR"^+ = limits(op("lim"))_(<- n) A_"inf" [1\/p] \/ (ker theta)^n. $
     It is a complete discrete valuation ring with residue field $bb(C)_p$. Inside $B_"dR"^+$ lies *Fontaine's $p$-adic $2 pi i$*:
     $ t = log([epsilon]) = sum_(n=1)^oo (-1)^(n-1) frac(([epsilon] - 1)^n, n) in B_"dR"^+. $
     Because $[epsilon] - 1 in ker(theta)$, the series converges in $B_"dR"^+$; moreover, $t$ is a uniformizer of $B_"dR"^+$ (`maximalIdeal_eq_span_fontaineT`), and $G_K$ acts on $t$ by the cyclotomic character:
     $ g(t) = log([g(epsilon)]) = log([epsilon^(chi_p (g))]) = chi_p (g) dot.c t. $
     Inverting $t$ produces the *de Rham period field*
     $ B_"dR" = B_"dR"^+ [1\/t], $
     equipped with the exhaustive, separated, decreasing $G_K$-stable filtration $op("Fil")^i B_"dR" = t^i B_"dR"^+$ ($i in bb(Z)$), whose graded pieces are $op("Gr")^i B_"dR" tilde.equiv bb(C)_p (i)$.
  2. *(Crystalline period ring $B_"cris"$)* Let $A_"cris"$ be the $p$-adic completion of the divided-power envelope of $A_"inf"$ with respect to $ker(theta)$, i.e., the $p$-adic completion of $A_"inf" [xi^n \/ n! : n >= 1]$. The Frobenius $phi$ on $A_"inf"$ extends continuously to $A_"cris"$ (`ACrisPhi`). Because $([epsilon] - 1)^n \/ n = (n - 1)! dot.c ([epsilon] - 1)^n \/ n!$ has $p$-adic valuation tending to $+oo$ in $A_"cris"$, the logarithm series defining $t = log([epsilon])$ already converges in $A_"cris"$ (`ACrisLog`), and satisfies
     $ phi(t) = log([epsilon]^p) = p dot.c log([epsilon]) = p t. $
     Setting
     $ B_"cris"^+ = A_"cris" [1\/p], quad B_"cris" = A_"cris" [1\/t] = B_"cris"^+ [1\/t], $
     we obtain a $G_K$-equivariant injective embedding $B_"cris" arrow.r.hook B_"dR"$ (`ACrisBdRInj`). Thus $B_"cris"$ inherits the filtration $op("Fil")^i B_"cris" = B_"cris" inter t^i B_"dR"^+$ while retaining its Frobenius $phi$ (`FontaineBcris`).

  The foundational structural theorem of Fontaine's theory—formalized across `GroundTheory.PAdicHodge.BCrisRegular`, `BCrisNewton`, and `FundamentalSeqBCris`—is the *fundamental exact sequence of $p$-adic Hodge theory*:

  #theorem(title: "Fundamental Exact Sequence of $p$-Adic Hodge Theory")[
    We have $(B_"dR")^(G_K) = K$ and $(B_"cris")^(G_K) = K_0$. Moreover, the sequence of $G_K$-modules
    $ 0 -> bb(Q)_p -> B_"cris"^(phi = 1) -> B_"dR" \/ B_"dR"^+ -> 0 $
    is exact, and more generally $B_"cris"^(+, phi = 1) = bb(Q)_p$ and $B_"cris"^(phi = 1) inter B_"dR"^+ = bb(Q)_p$.
  ]

  The exactness on the left is immediate from $B_"cris"^(+, phi = 1) = bb(Q)_p$; the surjectivity on the right reflects the rich supply of $phi$-invariant elements in $B_"cris"$ obtained by inverting $t$ (whose $phi$-eigenvalue is $p$) and analyzing the Newton polygons of power series in $A_"cris"$ (`BCrisNewton`).

  === Crystalline and de Rham Representations

  Let $V$ be a finite-dimensional $bb(Q)_p$-vector space with a continuous linear action of $G_K$. Define the Dieudonné modules
  $ D_"dR" (V) = (V times.o_(bb(Q)_p) B_"dR")^(G_K), quad D_"cris" (V) = (V times.o_(bb(Q)_p) B_"cris")^(G_K). $
  Because $B_"dR"$ and $B_"cris"$ are *Fontaine regular* (`BCrisRegular`)—meaning in particular that the natural comparison maps $D_"dR" (V) times.o_K B_"dR" -> V times.o_(bb(Q)_p) B_"dR"$ and $D_"cris" (V) times.o_(K_0) B_"cris" -> V times.o_(bb(Q)_p) B_"cris"$ are injective—one always has
  $ dim_(K_0) D_"cris" (V) <= dim_K D_"dR" (V) <= dim_(bb(Q)_p) V. $
  We say that $V$ is *de Rham* if $dim_K D_"dR" (V) = dim_(bb(Q)_p) V$, and *crystalline* if $dim_(K_0) D_"cris" (V) = dim_(bb(Q)_p) V$. Every crystalline representation is de Rham, with $D_"dR" (V) tilde.equiv D_"cris" (V) times.o_(K_0) K$ carrying both a Frobenius-semilinear automorphism $phi$ on $D_"cris" (V)$ and a decreasing exhaustive separated filtration $op("Fil")^i D_"dR" (V) = (V times.o_(bb(Q)_p) op("Fil")^i B_"dR")^(G_K)$. The integers $i in bb(Z)$ for which $op("Gr")^i D_"dR" (V) != 0$ (counted with multiplicity $dim_K op("Gr")^i D_"dR" (V)$) are the *Hodge–Tate weights* of $V$.

  For example, the cyclotomic character $V = bb(Q)_p (n)$ is crystalline for every $n in bb(Z)$: because $t^(-n) in B_"cris"$ satisfies $g(t^(-n)) = chi_p (g)^(-n) t^(-n)$ and $phi(t^(-n)) = p^(-n) t^(-n)$, the element $e_n times.o t^(-n)$ is $G_K$-invariant, so $D_"cris" (bb(Q)_p (n)) = K_0 dot.c (e_n times.o t^(-n))$ has dimension $1$, Frobenius eigenvalue $p^(-n)$, and unique Hodge–Tate weight $-n$ (in the convention where $bb(Q)_p (1)$ has weight $-1$). More generally, if $A \/ K$ is an abelian variety with good reduction, then $V_p (A) = T_p (A) times.o_(bb(Z)_p) bb(Q)_p$ is crystalline with Hodge–Tate weights $0$ and $-1$; and if $chi$ is an algebraic Hecke character of a CM field $E$ unramified at $v mid p$, its $p$-adic Galois realization $V_(chi, v)$ is crystalline at $v$, with Hodge–Tate weights determined by the infinity type of $chi$.

  === Bloch–Kato Local Conditions and the Greenberg–Wiles Formula

  Bloch and Kato (1990) used the fundamental exact sequence of $p$-adic Hodge theory to define the *finite* (or *crystalline*) local cohomology subspace $H^1_f (G_(F_v), V) subset.eq H^1 (G_(F_v), V)$ for an $ell$-adic representation $V$ of $G_(F_v)$:
  $
    &H^1_f (G_(F_v), V) \
    &quad = cases(
      ker(H^1 (G_(F_v), V) -> H^1 (I_v, V)) = H^1_"ur" (G_(F_v), V) & "if" v divides.not ell,
      ker(H^1 (G_(F_v), V) -> H^1 (G_(F_v), V times.o_(bb(Q)_ell) B_"cris")) & "if" v mid ell.
    )
  $
  In Yoneda terms, a class in $H^1 (G_(F_v), V) tilde.equiv op("Ext")^1_(G_(F_v)) (bb(Q)_ell, V)$ lies in $H^1_f (G_(F_v), V)$ precisely when the corresponding extension $0 -> V -> cal(E) -> bb(Q)_ell -> 0$ remains unramified (for $v divides.not ell$) or crystalline (for $v mid ell$). Tensoring the fundamental exact sequence $0 -> bb(Q)_ell -> B_"cris"^(phi = 1) -> B_"dR" \/ B_"dR"^+ -> 0$ with a crystalline representation $V$ and taking $G_(F_v)$-cohomology yields the exact sequence
  $
    0 &-> V^(G_(F_v)) -> D_"cris" (V)^(phi = 1) \
      &-> D_"dR" (V) \/ op("Fil")^0 D_"dR" (V) ->^(exp_"BK") H^1_f (G_(F_v), V) -> 0
  $
  whenever $1$ is not an eigenvalue of $phi$ on $D_"cris" (V)$ (and in general $H^1_f$ is an extension of $D_"cris" (V) \/ (1 - phi) D_"cris" (V)$ by $op("im")(exp_"BK")$). In all cases for a de Rham representation $V$ at $v mid ell$, the Bloch–Kato dimension formula gives
  $
    dim_(bb(Q)_ell) H^1_f (G_(F_v), V)
    &= dim_(bb(Q)_ell) (D_"dR" (V) \/ op("Fil")^0 D_"dR" (V)) \
    &quad + dim_(bb(Q)_ell) H^0 (G_(F_v), V).
  $
  Crucially, under local Tate duality, $H^1_f (G_(F_v), V)$ and $H^1_f (G_(F_v), V^or (1))$ are exact orthogonal complements!

  For a $G_(F_v)$-stable $bb(Z)_ell$-lattice $T subset.eq V$, one propagates $H^1_f$ to the divisible module $A = V \/ T$ as the image of $H^1_f (G_(F_v), V)$ under $H^1 (G_(F_v), V) -> H^1 (G_(F_v), A)$, and to the finite torsion quotient $M = T \/ ell^r T = A[ell^r]$ as the preimage of $H^1_f (G_(F_v), A)$ under $H^1 (G_(F_v), M) -> H^1 (G_(F_v), A)$.

  Now let $F$ be a number field, $S supset.eq op("Above")(F, ell)$ a finite set of finite places, and $M$ a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module. A *Selmer structure* (or family of local conditions) $cal(L) = \{ L_v \}_(v in S)$ consists of a choice of submodule $L_v subset.eq H^1 (G_(F_v), M)$ for each $v in S$. The associated *Selmer group* is
  $ op("Sel")_cal(L) (G_(F, S), M) = ker( H^1 (G_(F, S), M) -> product_(v in S) H^1 (G_(F_v), M) \/ L_v ). $
  In `Formalism.GaloisCohomology.Statement`, given an auxiliary set of bad places $Sigma$ and chosen local conditions $L_v$ at $v mid ell$, the *Bloch–Kato local condition family* `bkCond` assigns:
  - $L_v$ for $v mid ell$ (the crystalline/Bloch–Kato condition),
  - $top = H^1 (G_(F_v), M)$ for $v in Sigma$, $v divides.not ell$ (unrestricted at ramified places),
  - $H^1_"ur" (G_(F_v), M)$ for $v in.not Sigma$, $v divides.not ell$ (unramified almost everywhere).

  By `InfUnram` (Lemma 10.1), the global Selmer group `SelAll` defined with `bkCond` inside $H^1 (G_F, M)$ coincides with $op("Sel")_cal(L) (G_(F, S), M)$ for $S = Sigma union op("Above")(F, ell)$. For each $v in S$, let $L_v^perp subset.eq H^1 (G_(F_v), M^or (1))$ denote the exact annihilator of $L_v$ under local Tate duality (`perpCond`), and write $cal(L)^perp = \{ L_v^perp \}_(v in S)$ for the dual Selmer structure.

  #theorem(title: "Greenberg–Wiles Formula (`GreenbergWiles`)")[
    Let $S supset.eq op("Above")(F, ell)$ be a finite set of finite places of $F$, assume `PTCase F l`, and let $M$ be a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module with local conditions $cal(L) = \{ L_v \}_(v in S)$. Then
    $
      &frac(|op("Sel")_cal(L) (G_(F, S), M)|, |op("Sel")_(cal(L)^perp) (G_(F, S), M^or (1))|) \
      &quad = frac(|H^0 (G_(F, S), M)|, |H^0 (G_(F, S), M^or (1))|) dot.c frac(product_(v in S) |L_v|, A_oo (F, M) dot.c product_(v in S) |H^0 (G_(F_v), M)|).
    $
    Equivalently, clearing denominators:
    $
      &|op("Sel")_cal(L) (G_(F, S), M)| dot.c |H^0 (G_(F, S), M^or (1))| \
      &quad dot.c A_oo (F, M) dot.c product_(v in S) |H^0 (G_(F_v), M)| \
      &quad = |op("Sel")_(cal(L)^perp) (G_(F, S), M^or (1))| dot.c |H^0 (G_(F, S), M)| dot.c product_(v in S) |L_v|.
    $
  ]

  #proof[
    Write $H^i_S (M) = H^i (G_(F, S), M)$ and $P^i (M) = product_(v in S) H^i (G_(F_v), M)$, and set $L = product_(v in S) L_v subset.eq P^1 (M)$ and $L^perp = product_(v in S) L_v^perp subset.eq P^1 (M^or (1))$. Consider the tail of the Poitou–Tate nine-term exact sequence starting at $H^1_S (M)$:
    $
      &H^1_S (M) ->^(op("loc")_1) P^1 (M) ->^(beta) H^1_S (M^or (1))^or \
      &quad -> H^2_S (M) -> P^2 (M) -> H^0_S (M^or (1))^or -> 0.
    $
    By definition, $op("Sel")_cal(L) (M) = ker(H^1_S (M) -> P^1 (M) \/ L)$. Moreover, since $beta$ is the Pontryagin dual of $op("loc")_1 : H^1_S (M^or (1)) -> P^1 (M^or (1))$ and $L^perp = op("Ann")(L)$, the dual of $op("Sel")_(cal(L)^perp) (M^or (1)) = ker(H^1_S (M^or (1)) -> P^1 (M^or (1)) \/ L^perp)$ is canonically isomorphic to $H^1_S (M^or (1))^or \/ beta(L)$. Quotienting $P^1 (M)$ by $L$ and $H^1_S (M^or (1))^or$ by $beta(L)$ preserves exactness, giving the seven-term exact sequence of finite abelian groups:
    $
      0 &-> op("Sel")_cal(L) (M) -> H^1_S (M) -> P^1 (M) \/ L \
        &-> H^1_S (M^or (1))^or \/ beta(L) -> H^2_S (M) \
        &-> P^2 (M) -> H^0_S (M^or (1))^or -> 0.
    $
    Taking the alternating product of cardinalities along this exact sequence gives
    $
      frac(|op("Sel")_cal(L) (M)|, |op("Sel")_(cal(L)^perp) (M^or (1))|)
      = frac(|H^1_S (M)|, |H^2_S (M)|) dot.c frac(|P^2 (M)| dot.c |L|, |P^1 (M)| dot.c |H^0_S (M^or (1))|).
    $
    Now substitute the global Euler–Poincaré characteristic formula $|H^1_S (M)| \/ |H^2_S (M)| = |H^0_S (M)| dot.c |M|^([F : bb(Q)]) \/ A_oo (F, M)$ and the product of local Euler–Poincaré characteristic formulas
    $
      frac(|P^2 (M)|, |P^1 (M)|)
      = product_(v in S) frac(|H^2 (G_(F_v), M)|, |H^1 (G_(F_v), M)|)
      = product_(v in S) frac(1, |H^0 (G_(F_v), M)| dot.c |M|^(delta_(v mid ell))).
    $
    Because $S supset.eq op("Above")(F, ell)$, we have $sum_(v in S) delta_(v mid ell) = sum_(v mid ell) [F_v : bb(Q)_ell] = [F : bb(Q)]$, so the factors $|M|^([F : bb(Q)])$ cancel identically! What remains is precisely the Greenberg–Wiles formula.
  ]

  The cancellation of $|M|^([F : bb(Q)])$ between the global and local Euler–Poincaré characteristics is one of the small miracles of arithmetic duality: it reduces the comparison of global Selmer and dual Selmer orders to purely local volumes $|L_v| \/ |H^0 (G_(F_v), M)|$ and archimedean invariants $A_oo (F, M)$.

  === Integral $p$-Adic Hodge Theory and Bhatt–Scholze Lattices

  To apply the Greenberg–Wiles formula to $M = T \/ ell^r T$ for an automorphic Galois lattice $T$ (such as the integral $ell$-adic realization of an algebraic Hecke character or an automorphic representation on a unitary group), we must know the exact cardinality $|L_v|$ of the integral crystalline condition $L_v = H^1_f (G_(F_v), T \/ ell^r T)$—not merely up to a bounded constant depending on $ell$, because in the Alpöge–Claude–Riemann proof we sum over *all* primes $ell$ and track exact $bb(Z)_ell$-module lengths!

  When $ell$ is unramified in $F_v$ and the Hodge–Tate weights of $T$ lie in a small range (specifically of spread $< ell - 1$), Fontaine–Laffaille theory provides an exact equivalence of categories between finite-length crystalline torsion representations and strongly divisible filtered $phi$-modules over $W(k)$, giving an exact integral formula for $|H^1_f (G_(F_v), T \/ ell^r T)|$. However, when $F_v \/ bb(Q)_ell$ is ramified (as occurs for $ell = 2$ or at the ramified primes of the Iwasawa tower) or when the Hodge–Tate weights exceed $ell - 1$, Fontaine–Laffaille theory breaks down.

  The modern resolution—developed by Breuil, Kisin, and in full generality by Bhatt–Morrow–Scholze (2018) and Bhatt–Scholze (2022–2023) via prismatic cohomology—replaces $A_"cris"$ by *Breuil–Kisin modules* and *prismatic $F$-crystals* (`BhattScholzeIntegral`):
  - Fix a uniformizer $pi_K$ of $K$ with Eisenstein polynomial $E(u) in W(k)[u]$, and set $frak(S) = W(k)[[u]]$ with Frobenius $phi(u) = u^p$ extending the Witt vector Frobenius on $W(k)$. Choose a compatible system $pi_K^flat = (pi_K, pi_K^(1\/p), dots.c) in cal(O)_(bb(C)_p)^flat$, which yields a $phi$-equivariant embedding $frak(S) arrow.r.hook A_"inf"$ sending $u |-> [pi_K^flat]$ and $E(u) |-> xi$ (up to a unit in $A_"inf"$).
  - By Kisin's and Bhatt–Scholze's classification theorem, every $G_K$-stable $bb(Z)_p$-lattice $T$ in a crystalline representation $V$ corresponds to a unique *Breuil–Kisin module* $frak(M)(T)$ over $frak(S)$—a finite free $frak(S)$-module equipped with a Frobenius isomorphism $phi_frak(M) : phi^* frak(M)[1\/E(u)] tilde.equiv frak(M)[1\/E(u)]$—whose base change to $A_"inf"$ recovers the *Bhatt–Scholze integral lattice*
    $ M_"inf" (T) = frak(M)(T) times.o_(frak(S)) A_"inf" subset.eq V times.o_(bb(Q)_p) B_"cris". $
  - The integral lattice $M_"inf" (T)$ satisfies
    $
      M_"inf" (T) times.o_(A_"inf") B_"cris" &tilde.equiv D_"cris" (V) times.o_(K_0) B_"cris", \
      M_"inf" (T) times.o_(A_"inf") B_"dR"^+ &tilde.equiv op("Fil")^0 (D_"dR" (V) times.o_K B_"dR"),
    $
    and its Nygaard filtration controls the integral Bloch–Kato exponential map and the torsion in $H^1_f (G_K, T \/ p^r T)$ uniformly in $p$ and in the ramification degree of $K \/ bb(Q)_p$.

  In the Alpöge–Claude–Riemann formalization, this integral $p$-adic Hodge machinery (interfaced through `BhattScholzeIntegral` and `FontaineBcris`) is used to verify that the inertia eigenvalues and Bloch–Kato local volumes of the $ell$-adic Galois representations attached to algebraic Hecke characters and unitary automorphic forms match the Tamagawa and Arakelov integral lattices without uncontrolled $p$-adic denominators.

  // ==========================================================================
  // Section 10.4
  // ==========================================================================
  == Cyclotomic Iwasawa Towers and Behrend's 3-AP-Free Sphere Construction

  We now turn to the second major theme of this chapter: why the Alpöge–Claude–Riemann proof does not work directly over $bb(Q)$ (or a fixed imaginary quadratic field), why it ascends a carefully engineered cyclotomic-quadratic Iwasawa tower, and how Behrend's 1946 sphere construction from additive combinatorics enters to separate Frobenius orbits in that tower.

  === The Function-Field Analogy: From $bb(F)_(q^n) \/ bb(F)_q$ to Iwasawa Towers

  Recall Stepanov's elementary proof of the Weil bound $|"#" C(bb(F)_q) - (q + 1)| <= 2 g sqrt(q)$ for a smooth projective curve $C \/ bb(F)_q$. A crucial feature of the function-field setting is that one can pass freely from $bb(F)_q$ to finite extensions $bb(F)_(q^n)$ of arbitrarily large degree $n$: the zeta function $Z(C \/ bb(F)_(q^n), T)$ is obtained from $Z(C \/ bb(F)_q, T)$ by raising the Frobenius eigenvalues $alpha_i$ to the $n$-th power, while the genus $g$ stays *constant* and the extension $bb(F)_(q^n) \/ bb(F)_q$ is completely unramified. In particular, one can pigeonhole over the cyclic Galois group $op("Gal")(bb(F)_(q^n) \/ bb(F)_q) tilde.equiv bb(Z) \/ n bb(Z)$ to build auxiliary functions or test distributions with large multiplicity without paying any discriminant penalty.

  Over $bb(Q)$, Minkowski's theorem forbids nontrivial unramified extensions, so one cannot mimic $bb(F)_(q^n) \/ bb(F)_q$ literally. Instead, as recorded in item 11 of `remark.pdf` ("Iwasawa tower via analogy to pigeonhole on $bb(F)_(q^n) \/ bb(F)_q$"), the closest number-field substitute is a *cyclotomic $bb(Z)_p$-extension*—specifically, a $2$-adic cyclotomic-quadratic CM tower!

  Let us describe the exact host fields constructed in `Formalism.FrobeniusOrbits.Statement`. Fix two odd primes $q$ and $d$ satisfying the congruence and reciprocity hypothesis `HostHyp q d`:
  $ q equiv 3 (mod 8), quad d equiv 7 (mod 16), quad (frac(-d, q)) = 1. $
  The smallest concrete pair, verified in `HostExample`, is $(q, d) = (11, 7)$: indeed $11 equiv 3 (mod 8)$, $7 equiv 7 (mod 16)$, and $(-7 \/ 11) = (4 \/ 11) = 1$.

  For each level $e >= 0$, let $zeta = zeta_(2^(e+2))$ be a primitive $2^(e+2)$-th root of unity, and set
  $ F_1 = bb(Q)(zeta + zeta^(-1)), quad K_d = bb(Q)(sqrt(-d)), quad E_0 = bb(Q)(sqrt(-q), sqrt(-d)). $
  The *$e$-th host CM field* (`hostE`) is the compositum
  $ E = E_e = E_0 dot.c F_1 = bb(Q)(zeta + zeta^(-1), sqrt(-q), sqrt(-d)) subset.eq bb(Q)(zeta_N), $
  with maximal totally real subfield $F = E^+ = bb(Q)(zeta + zeta^(-1), sqrt(q d))$ (`hostF`). Here $E$ is contained in a cyclotomic field $bb(Q)(zeta_N)$ of conductor $N = Q_S dot.c q dot.c d$ divisible by $2^(e+2) q d$ (formalized as the predicate `IsChiField` in `Development.AutomorphicArithmetic.CharacterBoxes.IsChiField`).

  #proposition(title: "Structure of the Cyclotomic-Quadratic CM Tower (`HostGroup`, `HostRecip`, `HostOrdinary`, `HostEta`)")[
    Let $(q, d)$ satisfy `HostHyp q d`, and let $E = E_e$ be the $e$-th host CM field ($e >= 0$) with maximal real subfield $F = E^+$. Then:
    1. *(Reciprocity)* $(-q \/ d) = -1$.
    2. *(Galois Group)* The fields $bb(Q)(sqrt(-q))$, $bb(Q)(sqrt(-d))$, and $F_1 = bb(Q)(zeta_(2^(e+2)))^+$ are linearly disjoint over $bb(Q)$, so
       $ op("Gal")(E \/ bb(Q)) tilde.equiv G_0 times H_e, $
       where $G_0 = \{plus.minus 1\} times \{plus.minus 1\} tilde.equiv op("Gal")(E_0 \/ bb(Q))$ and $H_e = (bb(Z) \/ 2^(e+2) bb(Z))^times \/ \{plus.minus 1\} tilde.equiv op("Gal")(F_1 \/ bb(Q))$. Moreover, $H_e$ is cyclic of order $2^e$, generated by the class of $5 mod 2^(e+2)$:
       $ iota : bb(Z) \/ 2^e bb(Z) tilde.equiv H_e, quad m |-> [5^m mod 2^(e+2)]. $
    3. *(Complex Conjugation and CM Type)* Complex conjugation on $E$ corresponds to $c = ((-1, -1), 1) in G_0 times H_e$. The index-$2$ subgroup $Psi_e = \{ g in G_0 times H_e : g_(1, 2) = 1 \} = op("Gal")(E \/ K_d)$ satisfies $c in.not Psi_e$, and its coset defines a lifted CM type on $E$ for which a rational prime $p$ is ordinary if and only if $p$ splits in $K_d = bb(Q)(sqrt(-d))$.
    4. *(Unramified Quadratic Extension)* The quadratic CM extension $E \/ F$ is unramified at all finite places; every prime of $F$ above $2$, $q$, or (for $e >= 2$) $d$ splits in $E \/ F$.
  ]

  #proof[
    *(1)* Since $q equiv 3 (mod 4)$ and $d equiv 3 (mod 4)$, quadratic reciprocity gives
    $
      (frac(-q, d)) &= (frac(-1, d)) (frac(q, d)) = (-1) dot.c (-(frac(d, q))) \
      &= (frac(d, q)) = -(frac(-d, q)) = -1,
    $
    using $(-1 \/ q) = -1$ and $(-d \/ q) = 1$.

    *(2)* Since $q equiv 3 (mod 4)$ and $d equiv 3 (mod 4)$, the discriminants of $bb(Q)(sqrt(-q))$ and $bb(Q)(sqrt(-d))$ are $-q$ and $-d$, respectively, while $F_1 = bb(Q)(zeta_(2^(e+2)))^+$ is ramified only at $2$. Because $2, q, d$ are distinct primes, the three fields have pairwise coprime discriminants and are therefore linearly disjoint over $bb(Q)$ by Minkowski's theorem. Thus $op("Gal")(E \/ bb(Q)) tilde.equiv op("Gal")(bb(Q)(sqrt(-q)) \/ bb(Q)) times op("Gal")(bb(Q)(sqrt(-d)) \/ bb(Q)) times op("Gal")(F_1 \/ bb(Q)) = G_0 times H_e$. Standard $2$-adic unit structure gives $(bb(Z) \/ 2^(e+2) bb(Z))^times tilde.equiv \{plus.minus 1\} times chevron.l 5 chevron.r$ where $5$ has exact order $2^e$ modulo $2^(e+2)$, so $H_e tilde.equiv bb(Z) \/ 2^e bb(Z)$ via $m |-> [5^m]$.

    *(3)* Complex conjugation fixes $F_1 subset.eq bb(R)$ and negates both $sqrt(-q)$ and $sqrt(-d)$, hence equals $((-1, -1), 1)$. The CM type lifted from $K_d$ is the set of embeddings sending $sqrt(-d)$ to $+i sqrt(d)$, which is precisely the coset $Psi_e$; a prime $p$ is ordinary for a CM type lifted from $K_d$ if and only if the decomposition group at $p$ preserves $Psi_e$ on the right, i.e., lies in $op("Gal")(E \/ K_d)$, which holds if and only if $p$ splits in $K_d$.

    *(4)* The only primes ramifying in $E \/ bb(Q)$ are $2, q, d$. At $q$, the inertia group in $G_0 times H_e$ is generated by $((-1, 1), 1) != c$; at $d$, it is generated by $((1, -1), 1) != c$; at $2$, the inertia group is contained in $\{1\} times H_e$ (since $q equiv 3 (mod 8)$ and $d equiv 7 (mod 16)$ imply $2$ is unramified in $E_0$), which also avoids $c$. Hence $c$ never lies in any inertia subgroup, so $E \/ F$ is unramified at all finite places. At $2$, $d equiv 7 (mod 8)$ implies $2$ splits in $K_d$ and $-q equiv 5 (mod 8)$ implies $2$ is inert in $bb(Q)(sqrt(-q))$, so the Frobenius at $2$ in $G_0$ is $(-1, 1) != c$; at $q$, $(-d \/ q) = 1$ implies $q$ splits in $K_d$, so $c$ does not lie in the decomposition group at $q$; at $d$, for $e >= 2$, $d equiv 7 (mod 16)$ implies $d equiv -1 (mod 8)$ so $[d] in H_e$ has nontrivial $2$-adic component (or using $(-q \/ d) = -1$ and $d equiv 7 (mod 16)$), ensuring $c$ does not generate the decomposition group over $F$ and hence primes above $2, q, d$ split in $E \/ F$.
  ]

  This tower $E_0 subset.eq E_1 subset.eq E_2 subset.eq dots.c$ gives us a totally complex CM host field (so `PTCase E_e l` holds for every prime $ell$), unramified quadratic CM extension $E_e \/ F_e$, constant ordinary-prime criterion, and an arbitrarily large cyclic Galois factor $H_e tilde.equiv bb(Z) \/ 2^e bb(Z)$ in which we can choose subsets of Galois conjugates with separated Frobenius orbits.

  === The Frobenius-Orbit Obstruction and `NoRel`

  Why can we not simply take an arbitrary subset (or interval) inside $H_e tilde.equiv bb(Z) \/ n bb(Z)$ (where $n = 2^e$)?

  When we construct families of algebraic Hecke characters or theta lifts indexed by a subset $T subset.eq bb(Z) \/ n bb(Z)$ of Galois embeddings, the Frobenius element $op("Frob")_p$ at a rational prime $p$ acts on $H_e tilde.equiv bb(Z) \/ n bb(Z)$ by translation by some step $h = h_p in bb(Z) \/ n bb(Z)$. Thus an orbit of length $L$ under $op("Frob")_p$ starting at $t in bb(Z) \/ n bb(Z)$ is an *arithmetic progression*
  $ \{ t + i dot.c h : i_0 <= i < i_0 + L \} subset.eq bb(Z) \/ n bb(Z). $
  If a translate $T + u_0$ contained three distinct elements $s_1 + u_0, s_2 + u_0, s_3 + u_0$ lying in the same short Frobenius orbit—say $s_a + u_0 equiv t + i_a h (mod n)$ with $i_1, i_2, i_3 in [i_0, i_0 + L)$—then setting $i = i_2 - i_1$ and $j = i_3 - i_1$ would give $0 < |i|, |j| < L$, $i != j$, and the linear congruence
  $ j (s_2 - s_1) equiv i (s_3 - s_1) (mod n). $
  In the character-box and theta-lift arguments, having three or more elements of a translate $T + u_0$ hit a single length-$L$ Frobenius orbit creates unwanted linear relations among the local Frobenius eigenvalues, collapsing the independence of columns in the integral structure.

  This motivates the following combinatorial non-degeneracy condition (`NoRel` in `Formalism.FrobeniusOrbits.HostThickExists`):

  #definition(title: "Generalized 3-AP-Free Sets (`NoRel`)")[
    Let $L >= 1$ be an integer. A finite set $T subset.eq bb(N)$ satisfies `NoRel T L` if for all pairwise distinct $s_1, s_2, s_3 in T$ and all integers $i, j in bb(Z)$ with $0 < |i| <= L$, $0 < |j| <= L$, and $i != j$, we have
    $ j (s_2 - s_1) != i (s_3 - s_1). $
  ]

  Observe that when $i = 1, j = 2$, the condition $2(s_2 - s_1) != s_3 - s_1$ (equivalently $s_1 + s_3 != 2 s_2$) is precisely the classical condition that $T$ contains *no nontrivial 3-term arithmetic progression* (3-AP). Thus `NoRel T L` is a bounded-slope generalization of being 3-AP-free: it forbids all three-point rational-slope collinearities $(s_2 - s_1) \/ (s_3 - s_1) = i \/ j$ with $0 < |i|, |j| <= L$.

  #proposition(title: "Orbit-Intersection Bound (`HostThickOrbit`)")[
    Let $n >= 1$ and $L >= 2$ be integers. Suppose $T subset.eq bb(N)$ satisfies $4 L s < n$ for all $s in T$ and `NoRel T L`. For any $u_0, t, h in bb(Z) \/ n bb(Z)$, let $T + u_0 = \{ (s mod n) + u_0 : s in T \} subset.eq bb(Z) \/ n bb(Z)$.
    1. If the additive order $op("ord")(h)$ in $bb(Z) \/ n bb(Z)$ satisfies $op("ord")(h) > 4 L$, then for every $i_0 in bb(Z)$,
       $ |\{ i in [i_0, i_0 + L) inter bb(Z) : t + i dot.c h in T + u_0 \}| <= 2. $
    2. If $op("ord")(h) <= 4 L$, then the entire coset $t + bb(Z) dot.c h$ intersects $T + u_0$ in at most $1$ point:
       $ |(t + bb(Z) dot.c h) inter (T + u_0)| <= 1. $
  ]

  #proof[
    *(2)* Suppose $op("ord")(h) = r <= 4 L$, and suppose $t + i_1 h = s_1 + u_0$ and $t + i_2 h = s_2 + u_0$ in $bb(Z) \/ n bb(Z)$ with $s_1, s_2 in T$. Then $s_2 - s_1 equiv (i_2 - i_1) h (mod n)$, so multiplying by $r$ gives $r (s_2 - s_1) equiv 0 (mod n)$. On the other hand, since $0 <= s_1, s_2 < n \/ (4 L)$ and $r <= 4 L$, we have
    $ |r (s_2 - s_1)| <= 4 L dot.c max(s_1, s_2) < n. $
    The only multiple of $n$ strictly smaller than $n$ in absolute value is $0$, so $r (s_2 - s_1) = 0$ and hence $s_1 = s_2$. Thus the coset meets $T + u_0$ in at most $1$ point.

    *(1)* Suppose $op("ord")(h) > 4 L$, and suppose for contradiction that there exist three distinct integers $i_1, i_2, i_3 in [i_0, i_0 + L)$ such that $t + i_a h equiv s_a + u_0 (mod n)$ for $s_1, s_2, s_3 in T$. Set $i = i_2 - i_1$ and $j = i_3 - i_1$; then $0 < |i|, |j| < L$ and $i != j$. First, $s_1, s_2, s_3$ must be pairwise distinct: if, for instance, $s_2 = s_1$, then $i h equiv 0 (mod n)$, contradicting $0 < |i| < L < 4 L < op("ord")(h)$. Next, eliminating $h$ from $s_2 - s_1 equiv i h (mod n)$ and $s_3 - s_1 equiv j h (mod n)$ gives
    $ j (s_2 - s_1) equiv i (s_3 - s_1) (mod n). $
    However, since $|i|, |j| <= L$ and $0 <= s_a < n \/ (4 L)$, the triangle inequality yields
    $
      |j (s_2 - s_1) - i (s_3 - s_1)| &<= |j| dot.c |s_2 - s_1| + |i| dot.c |s_3 - s_1| \
      &< L dot.c frac(n, 4 L) + L dot.c frac(n, 4 L) = frac(n, 2) < n.
    $
    Therefore the congruence modulo $n$ must be an exact equality in $bb(Z)$:
    $ j (s_2 - s_1) = i (s_3 - s_1), $
    contradicting `NoRel T L`!
  ]

  === Behrend's 1946 Sphere Construction

  How large can a set $T subset.eq [0, n \/ (4 L))$ satisfying `NoRel T L` be? A naive greedy construction gives only $|T| approx (n \/ L)^(1\/2)$, which is far too sparse for the pigeonhole step in the Iwasawa tower: we need $|T|$ to be *nearly linear* in $n \/ L$, losing only a subpolynomial factor $exp(-O(sqrt(log n dot.c log L)))$.

  In 1946, Felix Behrend discovered a breathtakingly simple geometric construction of dense 3-AP-free subsets of $\{1, dots.c, N\}$ of size $N exp(-c sqrt(log N))$: place integer points on a high-dimensional Euclidean sphere (which is strictly convex and therefore contains no three collinear points!) and encode them in a sufficiently large integer base so that linear combinations produce no carries. Remarkably, the *exact same* sphere-and-base-encoding mechanism generalizes seamlessly to `NoRel T L` for arbitrary slope bound $L >= 2$, as formalized in `Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`!

  Let us first record the two elementary algebraic lemmas that power the construction.

  #lemma(title: "No-Carry Uniqueness (`coeff_zero`)")[
    Let $B >= 1$ and $S >= 0$ be integers, and let $c_0, dots.c, c_(S-1) in bb(Z)$ satisfy $|c_m| < B$ for all $0 <= m < S$. If
    $ sum_(m=0)^(S-1) c_m B^m = 0, $
    then $c_m = 0$ for every $0 <= m < S$.
  ]

  #proof[
    We induct on $S$. For $S = 0$ there is nothing to prove. For $S >= 1$, reducing the sum modulo $B$ gives $c_0 equiv 0 (mod B)$; since $|c_0| < B$, we obtain $c_0 = 0$. Dividing the remaining sum by $B$ yields $sum_(m=1)^(S-1) c_m B^(m-1) = 0$, and the induction hypothesis gives $c_1 = dots.c = c_(S-1) = 0$.
  ]

  #lemma(title: "Strict Convexity of the Euclidean Sphere (`sphere_rel`)")[
    Let $S >= 0$, let $v_1, v_2, v_3 in bb(Z)^S$ lie on the same sphere of squared radius $k in bb(Z)$, i.e.,
    $ sum_(m=0)^(S-1) v_(1, m)^2 = sum_(m=0)^(S-1) v_(2, m)^2 = sum_(m=0)^(S-1) v_(3, m)^2 = k. $
    Suppose $i, j in bb(Z)$ satisfy $j != 0$, $i != j$, and $j (v_2 - v_1) = i (v_3 - v_1)$ in $bb(Z)^S$. Then $v_2 = v_1$.
  ]

  #proof[
    Expanding $v_(2, m)^2 - v_(1, m)^2 = 2 v_(1, m) (v_(2, m) - v_(1, m)) + (v_(2, m) - v_(1, m))^2$ and summing over $m$ gives
    $ A := sum_(m=0)^(S-1) (2 v_(1, m) (v_(2, m) - v_(1, m)) + (v_(2, m) - v_(1, m))^2) = k - k = 0, $
    and similarly
    $ B := sum_(m=0)^(S-1) (2 v_(1, m) (v_(3, m) - v_(1, m)) + (v_(3, m) - v_(1, m))^2) = 0. $
    Using the coordinatewise relation $j (v_(2, m) - v_(1, m)) = i (v_(3, m) - v_(1, m))$, a direct algebraic identity shows that for every $m$,
    $
      &j^2 (2 v_(1, m) (v_(2, m) - v_(1, m)) + (v_(2, m) - v_(1, m))^2) \
      &quad - i j (2 v_(1, m) (v_(3, m) - v_(1, m)) + (v_(3, m) - v_(1, m))^2) \
      &quad = i (i - j) (v_(3, m) - v_(1, m))^2.
    $
    Indeed, substituting $j (v_(2, m) - v_(1, m)) = i (v_(3, m) - v_(1, m))$ makes the linear terms $2 v_(1, m) (dots.c)$ cancel identically ($2 i j v_(1, m) (v_(3, m) - v_(1, m)) - 2 i j v_(1, m) (v_(3, m) - v_(1, m)) = 0$), leaving $i^2 (v_(3, m) - v_(1, m))^2 - i j (v_(3, m) - v_(1, m))^2 = i (i - j) (v_(3, m) - v_(1, m))^2$. Summing over $m$ gives
    $ i (i - j) sum_(m=0)^(S-1) (v_(3, m) - v_(1, m))^2 = j^2 A - i j B = 0. $
    If $i = 0$, then $j (v_2 - v_1) = 0$ with $j != 0$, so $v_2 = v_1$. If $i != 0$, then $i (i - j) != 0$, so $sum_(m=0)^(S-1) (v_(3, m) - v_(1, m))^2 = 0$. Since each term is a nonnegative integer square, $v_3 = v_1$, and therefore $j (v_2 - v_1) = i (v_3 - v_1) = 0$, again forcing $v_2 = v_1$.
  ]

  Now we assemble the full generalized Behrend theorem (`HostThickExists`, proved in `Formalism.FrobeniusOrbits.hostThickExists` with the explicit constant $C = 32$).

  #theorem(title: "Generalized Behrend Construction (`HostThickExists`)")[
    There exists an absolute constant $C > 0$ (one may take $C = 32$) such that for all integers $n >= 0$ and $L >= 2$, there exists a finite set $T subset.eq bb(N)$ satisfying:
    1. $4 L s < n$ for all $s in T$;
    2. `NoRel T L`;
    3. $|T| >= frac(n, L) exp(-C sqrt(log n dot.c log L))$.
  ]

  #proof[
    Set $C = 32$, $x = log n$, $y = log L > 1\/2$ (since $L >= 2$ and $log 2 > 0.693 > 1\/2$), and $s = sqrt(x y)$. If $(n \/ L) exp(-32 s) <= 1$, the bound is trivial: take $T = emptyset$ if $n = 0$ and $T = \{0\}$ if $n >= 1$ (any singleton trivially satisfies `NoRel`). Assume therefore that $(n \/ L) exp(-32 s) > 1$, which implies $x - y - 32 s > 0$, hence $x > 0$, $s^2 = x y$, and
    $ s^2 = x y > (32 s + y) y > 32 s y => s > 32 y > 16. $

    *(Step 1: Choice of dimension $S$ and box side $d$.)* Define
    $ S = floor(s \/ y) in bb(N), quad a = frac(x - y - 3, S), quad d = floor(frac(e^a, 4 L)) in bb(N). $
    Since $s \/ y > 32$, we have $S >= 32$, $S y <= s < (S + 1) y <= 2 S y$, and consequently $x = s^2 \/ y <= 2 s S$ and $a <= x \/ S <= 2 s$. Moreover, since $s > 32 y$ and $y > 1\/2$, we have
    $
      (7 + y) S y <= (7 + y) s &< s^2 - y^2 - 3 y = (x - y - 3) y \
      &=> a >= 7 + y,
    $
    and
    $
      3 + S (7 + y) + S + 2 a &= 3 + 8 S + S y + 2 a \
      &<= 3 + 16 S y + S y + 4 s <= 3 + 21 s <= 32 s.
    $
    In particular, $e^a >= e^(7 + y) = e^7 L >= 8 L$, so $e^a \/ (8 L) <= d <= e^a \/ (4 L)$ and $d >= 1$.

    *(Step 2: Pigeonhole on spherical shells.)* Consider the $S$-dimensional box $\{0, 1, dots.c, d - 1\}^S$ of cardinality $d^S$. For every $v in \{0, dots.c, d - 1\}^S$, its squared Euclidean norm $sum_(m=0)^(S-1) v_m^2$ is an integer in $\{0, 1, dots.c, S (d - 1)^2\}$, which has at most $S d^2$ possible values. By the pigeonhole principle (`Behrend.exists_large_sphere`), there exists $k in bb(N)$ such that the spherical shell
    $ op("sphere")(S, d, k) = \{ v in \{0, dots.c, d - 1\}^S : sum_(m=0)^(S-1) v_m^2 = k \} $
    satisfies
    $ |op("sphere")(S, d, k)| >= frac(d^S, S d^2). $

    *(Step 3: Base-$B$ encoding.)* Set the base $B = 4 L d$, and define the encoding map `Behrend.map B`:
    $ Phi_B : \{0, dots.c, d - 1\}^S -> bb(N), quad Phi_B (v) = sum_(m=0)^(S-1) v_m B^m. $
    Let $T = Phi_B (op("sphere")(S, d, k))$. We verify the three required properties:
    - *(Size bound $4 L s < n$)* For every $v in \{0, dots.c, d - 1\}^S$, since $v_m < d <= B$, base-$B$ arithmetic (`map_lt`) gives
      $ Phi_B (v) < B^S = (4 L d)^S <= e^(a S) = e^(x - y - 3) = frac(n, e^3 L). $
      Since $4 < e^3$, we get $4 L dot.c Phi_B (v) < (4 \/ e^3) n < n$.
    - *(Injectivity and `NoRel T L`)* If $Phi_B (v) = Phi_B (w)$ for $v, w in op("sphere")(S, d, k)$, then $sum (v_m - w_m) B^m = 0$ with $|v_m - w_m| < d <= B$, so Lemma 10.9 (`coeff_zero`) forces $v = w$; thus $|T| = |op("sphere")(S, d, k)|$. Similarly, suppose $s_1 = Phi_B (v_1)$, $s_2 = Phi_B (v_2)$, $s_3 = Phi_B (v_3) in T$ are pairwise distinct and $j (s_2 - s_1) = i (s_3 - s_1)$ with $0 < |i|, |j| <= L$ and $i != j$. Writing $c_m = j (v_(2, m) - v_(1, m)) - i (v_(3, m) - v_(1, m))$, we have $sum_(m=0)^(S-1) c_m B^m = 0$ and
      $
        |c_m| &<= |j| dot.c |v_(2, m) - v_(1, m)| + |i| dot.c |v_(3, m) - v_(1, m)| \
              &< L d + L d = 2 L d < 4 L d = B.
      $
      By Lemma 10.9 (`coeff_zero`), $c_m = 0$ for all $m$, so $j (v_2 - v_1) = i (v_3 - v_1)$ in $bb(Z)^S$. By Lemma 10.10 (`sphere_rel`), this forces $v_2 = v_1$ and hence $s_2 = s_1$, a contradiction! Thus $T$ satisfies `NoRel T L`.
    - *(Lower bound on $|T|$)* Using $e^(a S) = n \/ (e^3 L)$, $d >= e^a \/ (8 L)$, $d <= e^a$, $8 L <= e^(7 + y)$, and $S <= e^S$, we estimate
      $
        |T| &>= frac(d^S, S d^2) >= frac(e^(a S), (8 L)^S dot.c S dot.c e^(2 a)) \
        &= frac(n, L) dot.c frac(1, e^3 (8 L)^S S e^(2 a)) \
        &>= frac(n, L) dot.c exp(-(3 + S (7 + y) + S + 2 a)) \
        &>= frac(n, L) exp(-32 s).
      $
    This completes the proof.
  ]

  #insight-box(title: "Geometry of High-Dimensional Spheres Inside a Cyclotomic Tower")[
    It is worth pausing to admire how unexpectedly distant branches of mathematics interlock here. The Galois group $H_e tilde.equiv bb(Z) \/ 2^e bb(Z)$ of the real $2$-adic cyclotomic tower $bb(Q)(zeta_(2^(e+2)))^+$ is a purely arithmetic object; Frobenius elements act on it as translations. To prevent Frobenius orbits of length $L$ from creating linear dependencies among automorphic periods, we embed a high-dimensional Euclidean sphere of dimension $S approx sqrt(log n \/ log L)$ into $bb(Z) \/ 2^e bb(Z)$ via base-$(4 L d)$ digits! Because the Euclidean sphere is strictly convex, no three distinct points on it are collinear, and the generous base $4 L d$ prevents carries from blurring that convexity. As Levent Alpöge remarks in footnote 7 of `remark.pdf`, future simplifications of the proof may well dispense with Behrend's trick—yet in the current formalized proof it provides a completely elementary, self-contained, and rock-solid guarantee that Frobenius orbits remain separated.
  ]

  // ==========================================================================
  // Section 10.5
  // ==========================================================================
  == Lean 4 Formalization Architecture

  The cohomological, $p$-adic Hodge-theoretic, and Iwasawa-combinatorial results of this chapter span four major libraries in `lean-rh/src/`. We summarize their structure, key declarations, and dependencies below.

  #lean-note(
    title: "Lean 4 Formalization: Galois Cohomology, p-Adic Hodge Theory, and Behrend Orbits",
    module: "Formalism.GaloisCohomology · ReciprocityTheory.Gal · GroundTheory.PAdicHodge · Formalism.FrobeniusOrbits",
  )[
    - *`Formalism.GaloisCohomology.Statement`* (`lean-rh/src/Formalism/GaloisCohomology/Statement.lean`):
      - Defines the discrete divisible coefficient module `QZ l` $= bb(Q)_ell \/ bb(Z)_ell$ with discrete topology, scalar twist representations `scalRep`, and the finite set of places `Above F l` above $ell$.
      - Packages the $S$-ramified data in `structure LData F Ω l` (the finset `S` equal to `Above F l`, valuation subrings `A v` over each $v in S$, and the $S$-ramified cyclotomic character `chi : GS Ω S →* ℤ_[l]ˣ`).
      - Defines the cyclotomic twists `qzTw D e` ($bb(Q)_ell \/ bb(Z)_ell (-e)$) and `zlTw D n` ($bb(Z)_ell (n)$), the Tate–Shafarevich kernels `Sha D e` and `Sha2Zl D e`, and their `Module.length ℤ_[l]` invariants `shaLen D e`, `VLen D e`, and `sumLocalH0TwistLength D e`.
      - States the case condition `PTCase F l` (`l ≠ 2 ∨ InfinitePlace.nrRealPlaces F = 0`), the three duality hypotheses `PTCokerAt`, `PTShaAt`, `TateLocalDualityH2AtPlaces`, and the exact length identity `VFormula`.
      - Defines the global Selmer group `SelAll`, the unramified local condition `unrAt`, the Bloch–Kato local condition family `bkCond`, and the inflation characterization `InfUnram`.
    - *`ReciprocityTheory.Hypotheses.GalCoh`* and *`GroundTheory.ProfCoh`* (`GalCoh.lean`, `GalCohDefs.lean`, `PoitouTateNineTermGs.lean`):
      - Defines the Cartier–Tate dual `twDual`, local finiteness (`LocalFiniteness`), Tate local duality (`LocalTateDuality`), unramified orthogonality (`UnramifiedOrthogonality`), local and global Euler–Poincaré characteristics (`LocalEulerChar`, `GlobalEulerChar`, using `archH0Card`), `ShaDualityAt`, and the `GreenbergWiles` formula.
      - Proves compactly supported global duality (`poitouTate_duality_gs`), `Sha`-duality (`poitouTate_sha_gs`), and the full nine-term exact sequence (`poitouTate_nineTerm_gs`) for $G_(F, S)$.
    - *`GroundTheory.PAdicHodge`* and *`Development.AbelianVarietyTheory`*:
      - Constructs the tilt (`TiltField`, `TiltAlgClosed`), $A_"inf"$ (`AInfGalois`, `AInfXi`), $A_"cris"$ (`ACrisPhi`, `ACrisLog`), $B_"dR"$ (`BdRField`), and $B_"cris"$ (`BCrisRegular`, `BCrisNewton`, `FundamentalSeqBCris`), including Fontaine's uniformizer `fontaineT` and the fundamental exact sequence (`exists_mul_pow_fontaineT_eq`).
      - Interfaces the integral crystalline / prismatic lattice theory (`BhattScholzeIntegral`, `FontaineBcris`) used to control Bloch–Kato local conditions of algebraic Hecke characters and automorphic Galois representations.
    - *`Formalism.FrobeniusOrbits`* and *`Development.AutomorphicArithmetic.CharacterBoxes.IsChiField`*:
      - Constructs the CM host field tower `hostE` $= bb(Q)(zeta + zeta^(-1), sqrt(-q), sqrt(-d))$ under `HostHyp q d` (with concrete instance `HostExample` for $q = 11, d = 7$), its Galois group `GG e` $= G_0 times H_e$, its embedding into a cyclotomic field (`IsChiField`), and its splitting/ordinarity properties (`HostGroup`, `HostOrdinary`, `HostEta`).
      - Defines `NoRel`, `InTranslate`, `HostThickOrbit`, and `HostThickExists`, and proves `hostThickExists` (with $C = 32$) in `FrobeniusOrbitsProofs/ThickExists.lean` via `coeff_zero`, `map_lt`, `sphere_rel`, `noRel_image`, `card_image`, and Mathlib's `Mathlib.Combinatorics.Additive.AP.Three.Behrend` (`Behrend.sphere`, `Behrend.map`, `Behrend.exists_large_sphere`).
  ]

  // ==========================================================================
  // Exercises
  // ==========================================================================
  #exercises((
    [
      Let $G$ be a profinite group and $M = limits(op("lim"))_(<- r) M_r$ an inverse limit of finite discrete $G$-modules with surjective transition maps. Assume that $H^i (G, M_r)$ is finite for all $i >= 0$ and $r >= 1$. Use the Mittag-Leffler criterion for inverse systems of abelian groups to prove that the natural map $H^n (G, M) -> limits(op("lim"))_(<- r) H^n (G, M_r)$ is an isomorphism for every $n >= 0$.
    ],
    [
      Let $v$ be a finite place of a number field $F$ with $v divides.not ell$, and let $M$ be a finite discrete $bb(Z) \/ ell^r bb(Z)[G_(F_v)]$-module on which inertia $I_v$ acts trivially. Verify directly that $|H^0 (G_(F_v), M)| = |H^1_"ur" (G_(F_v), M)|$ and use local Tate duality to deduce that $|H^2 (G_(F_v), M)| = |H^1_"ur" (G_(F_v), M^or (1))|$. Conclude that $H^1_"ur" (G_(F_v), M)$ and $H^1_"ur" (G_(F_v), M^or (1))$ are exact annihilators of each other under the local Tate pairing.
    ],
    [
      Let $F$ be a totally real number field of degree $d = [F : bb(Q)]$, let $ell$ be an odd prime, and let $S = op("Above")(F, ell)$. Compute the global Euler–Poincaré characteristic $|H^0 (G_(F, S), M)| dot.c |H^2 (G_(F, S), M)| \/ |H^1 (G_(F, S), M)|$ for $M = (bb(Z) \/ ell bb(Z))(n)$ as a function of the parity of $n in bb(Z)$. Show that the $bb(Z)_ell$-corank of $H^1 (G_(F, S), bb(Q)_ell \/ bb(Z)_ell (n))$ is at least $d$ when $n$ is odd and at least $0$ when $n$ is even (with equality for $n = 0$ equivalent to Leopoldt's conjecture for $(F, ell)$).
    ],
    [
      Let $F = bb(Q)(sqrt(-d))$ be an imaginary quadratic field, $ell$ an odd prime that splits in $F$ as $(ell) = frak(p) overline(frak(p))$, and $e >= 1$ an integer divisible by $ell - 1$. Compute both $op("len")_(bb(Z)_ell) H^0 (F, bb(Q)_ell \/ bb(Z)_ell (-e))$ and $sum_(v mid ell) op("len")_(bb(Z)_ell) H^0 (F_v, bb(Q)_ell \/ bb(Z)_ell (-e))$. Using `VFormula`, express $op("len")_(bb(Z)_ell) H^2 (cal(O)_F [1\/ell], bb(Z)_ell (e+1)) - op("len")_(bb(Z)_ell) op("Ш")^1_S (F, bb(Q)_ell \/ bb(Z)_ell (-e))$ explicitly in terms of $v_ell (e)$.
    ],
    [
      Show that for an irregular prime $ell$ (for instance $ell = 691$, which divides the numerator of $B_(12) = -691\/2730$) and the corresponding odd integer $e = 11$, the group $H^2 (bb(Z)[1\/ell], bb(Z)_ell (12))$ is nontrivial, and hence by `VFormula` the Tate–Shafarevich group $op("Ш")^1_(\{691\}) (bb(Q), bb(Q)_(691) \/ bb(Z)_(691) (-11))$ is nontrivial. Why does this not contradict Kummer–Vandiver's conjecture?
    ],
    [
      Let $K \/ bb(Q)_p$ be a finite extension and $V = bb(Q)_p (1)$. Using Kummer theory $H^1 (G_K, bb(Q)_p (1)) tilde.equiv (limits(op("lim"))_(<- r) K^times \/ (K^times)^(p^r)) times.o_(bb(Z)_p) bb(Q)_p$, verify that the Bloch–Kato subspace $H^1_f (G_K, bb(Q)_p (1))$ coincides with the image of the unit group $cal(O)_K^times times.o_(bb(Z)_p) bb(Q)_p$, and check that its $bb(Q)_p$-dimension equals $[K : bb(Q)_p] = dim_(bb(Q)_p) (D_"dR" (bb(Q)_p (1)) \/ op("Fil")^0 D_"dR" (bb(Q)_p (1))) + dim_(bb(Q)_p) H^0 (G_K, bb(Q)_p (1))$.
    ],
    [
      Verify directly from the definition of Fontaine's element $t = log([epsilon]) in B_"dR"^+$ that $g(t) = chi_p (g) dot.c t$ for all $g in G_K$ and $phi(t) = p t$ in $A_"cris"$. Deduce that $t^(-n) in B_"cris"$ witnesses the crystallinity of $bb(Q)_p (n)$ for every $n in bb(Z)$, and compute the action of $phi$ on $D_"cris" (bb(Q)_p (n))$.
    ],
    [
      Using the Greenberg–Wiles formula, let $M$ be a finite $bb(Z) \/ ell^r bb(Z)[G_(F, S)]$-module that is self-dual up to twist ($M^or (1) tilde.equiv M$) with $cal(L)^perp = cal(L)$. Show that $|op("Sel")_cal(L) (G_(F, S), M)|$ is not constrained by Greenberg–Wiles alone, whereas if $L_v$ is replaced by a larger local condition $L'_v supset.eq L_v$ at a single prime $v in S$ while $L'_w = L_w$ for $w != v$, then
      $ frac(|op("Sel")_(cal(L)') (G_(F, S), M)|, |op("Sel")_((cal(L)')^perp) (G_(F, S), M)|) = frac(|L'_v|, |L_v|). $
    ],
    [
      Prove that the smallest pair of primes $(q, d)$ satisfying `HostHyp q d` ($q equiv 3 (mod 8)$, $d equiv 7 (mod 16)$, $(-d \/ q) = 1$) is $(q, d) = (11, 7)$. Verify using quadratic reciprocity that `HostHyp q d` always implies $(-q \/ d) = -1$ (`HostRecip`), and explain why $bb(Q)(sqrt(-q))$, $bb(Q)(sqrt(-d))$, and $bb(Q)(zeta_(2^(e+2)))^+$ are linearly disjoint over $bb(Q)$ for every $e >= 0$.
    ],
    [
      In the proof of Theorem 10.11 (`HostThickExists`), we chose $S = floor(sqrt(log n \/ log L))$ and obtained the explicit constant $C = 32$. By optimizing the choice of $S$ and $d$ as a function of $x = log n$ and $y = log L$ for large $n$ (assuming $log n \/ log L -> oo$), determine the asymptotically sharpest constant $C_0$ achievable by the Behrend sphere-and-base-$(4 L d)$ encoding method, and compare it with Behrend's classical constant $2 sqrt(2)$ for 3-AP-free sets (where $B = 2 d - 1$).
    ],
  ))
]
