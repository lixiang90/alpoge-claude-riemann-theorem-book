// ============================================================================
// Chapter 16: The Weakened Vandiver Window, Behrend's Construction,
//             and Proof Completion
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch16() = [
  #chapter(
    "The Weakened Vandiver Window, Behrend's Construction, and Proof Completion",
    short-title: "Weakened Vandiver Window and Synthesis",
    epigraph: "For the classes in H^1(o_E[1/l], Q_l/Z_l(-e)) that we couldn't kill by twisting, fight for a significant weakening of Vandiver... precise choice of the Iwasawa tower, specifically using Behrend!!",
    epigraph-source: "Levent Alpöge, Remark (November 20, 2026), items 17 and 19",
    overview: [
      Every previous chapter of Part III has brought us closer to the summit, yet one formidable arithmetic obstruction remains: when gluing integral structures across Hecke characters to eliminate denominators in the chain of $m approx sqrt(X)$ theta lifts over a totally real abelian field $E$, residual Galois cohomology classes in $op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ survive all twisting arguments. Full vanishing of these classes would require a massive generalization of Kummer's Vandiver conjecture, which remains wide open. The breakthrough of this final chapter is that *full vanishing is unnecessary*: it suffices to prove a vastly weakened, exponential-scale upper bound `VVle` on the weighted sum of Tate–Shafarevich lengths over a single dyadic window $[Y, Y^2] subset.eq [X^(1/J), X]$. We develop this window theorem (`VWin`) in full: we define the cyclotomic-quadratic fields `IsChiField` and prime pairs `WinPair`, prove the generalized Behrend sphere theorem (`ThickExists.lean`) that breaks Frobenius-orbit resonances across the Iwasawa tower, trace how Caraiani local-global compatibility and base change (`vwin_of_row`) establish `VWin` via modularity lifting, and finally assemble every pillar of Chapters 11–16 into the complete proof of the *Alpöge–Claude–Riemann Theorem*—both the Generalized Riemann Hypothesis for all Dirichlet $L$-functions and the classical Riemann Hypothesis for $zeta(s)$—mirroring `MainConclusion.lean` and `Main.lean` line by line.
    ],
    label-name: "ch-vandiver-window-synthesis",
  )

  == Why Cohomological Obstructions Arise and Why Twisting Alone Is Not Enough

  At the close of Chapter 15, the Arakelov-theoretic master inequality (`DivIneqObjU`) and the height bound (`HeightS`) placed us within a hair's breadth of the Generalized Riemann Hypothesis. The chain of $m approx sqrt(X)$ theta lifts on totally definite unitary groups $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ produces an automorphic avatar of Stepanov's multiplicity $m$ over $bb(Z)$, and local divisibility at inert primes (Chapter 14) supplies a logarithmic gain of order $x^(1/2)$ in the Arakelov degree. Yet as we saw in Chapter 13, a naive term-by-term bound on each theta lift incurs a denominator cost that stalls at the barrier $op("Re")(s) = 2/3$—precisely item 14 of Alpöge's *Remark*.

  To breach the $2/3$ barrier and reach the critical line $op("Re")(s) = 1/2$, the proof glues integral structures across an entire family of Hecke characters (item 15 of *Remark*), extracting a global "greatest common divisor" across the family by averaging over the characters and applying the relative trace formula to control approximate orthogonality of the columns (item 16). In this gluing step, denominators arise from two distinct arithmetic sources:
  1. *Local congruence primes* coming from Eisenstein ideals and special values of Hecke $L$-functions attached to the twisting characters $mu_j$, which vary with the choice of character and can therefore be neutralized by twisting and averaging across the family; and
  2. *Global cohomological obstructions* intrinsic to the base totally real field $E$, living in the étale / Galois cohomology groups
     $ H^1 (cal(O)_E [1 \/ ell], bb(Q)_ell \/ bb(Z)_ell (-e)) quad (1 <= e < floor(x^401)), $
     and more specifically in their locally trivial subgroups—the Tate–Shafarevich kernels
     $ &op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) \
       &= ker ( H^1 (G_(E, S_ell), bb(Q)_ell \/ bb(Z)_ell (-e)) -> product_(v in S_ell) H^1 (G_(E_v), bb(Q)_ell \/ bb(Z)_ell (-e)) ), $
     where $S_ell$ denotes the set of finite places of $E$ lying above the rational prime $ell$, and $G_(E, S_ell)$ is the Galois group of the maximal algebraic extension of $E$ unramified outside $S_ell$ and the archimedean places.

  Why can these classes not be killed by twisting alone? Suppose one attempts to twist the theta-lift chain by an auxiliary Hecke character $eta$ to clear a denominator at a prime $ell$. The obstruction to lifting an integral lattice across a congruence modulo $ell^k$ is governed by an extension class in $op("Ext")^1_(G_(E, S_ell)) (bb(Z)_ell, bb(Q)_ell \/ bb(Z)_ell (-e)) = H^1 (G_(E, S_ell), bb(Q)_ell \/ bb(Z)_ell (-e))$ whose localizations at all places $v divides ell$ vanish whenever the local theta-lift lattices are already integral at $v$. Such a class belongs to $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e))$. Because this group depends only on the cyclotomic twist $chi_ell^(-e)$ over the base field $E$—and not on the auxiliary cuspidal parameters—twisting within a fixed base field $E$ cannot eliminate its contribution to the index of the glued integral structure.

  === Poitou–Tate Duality and the Shadow of Vandiver's Conjecture

  To understand the arithmetic meaning of $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e))$, we recall its dual via the Poitou–Tate nine-term exact sequence (Chapter 10). Let $E$ be a totally real number field, $ell$ an odd prime (or any prime if $E$ is totally imaginary), $S_ell$ the set of primes of $E$ above $ell$, and $e >= 1$ an integer. Write $bb(Z)_ell (e + 1)$ for the $(e+1)$-st Tate twist of $bb(Z)_ell$ and $bb(Q)_ell \/ bb(Z)_ell (-e)$ for its Pontryagin–Tate dual $(bb(Z)_ell (e + 1))^or (1)$. The global-to-local restriction map in degree $2$ sits in the exact sequence
  $ &0 -> op("Ш")^2_(S_ell) (E, bb(Z)_ell (e + 1)) -> H^2 (G_(E, S_ell), bb(Z)_ell (e + 1)) \
    &quad -> plus.o_(v in S_ell) H^2 (G_(E_v), bb(Z)_ell (e + 1)) -> H^0 (G_(E, S_ell), bb(Q)_ell \/ bb(Z)_ell (-e))^or -> 0. $
  By Poitou–Tate global duality, $op("Ш")^2_(S_ell) (E, bb(Z)_ell (e + 1))$ is canonically Pontryagin dual to $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e))$, so both finite $bb(Z)_ell$-modules have the same length. By Tate local duality at each $v in S_ell$, $H^2 (G_(E_v), bb(Z)_ell (e + 1))$ is Pontryagin dual to $H^0 (G_(E_v), bb(Q)_ell \/ bb(Z)_ell (-e))$. Taking $bb(Z)_ell$-module lengths across the exact sequence immediately yields the fundamental length formula (`VFormula` in `Formalism.GaloisCohomology.Statement`):

  #proposition(title: "Poitou–Tate Length Identity, VFormula")[
    Let $E$ be a number field, $ell$ a prime such that either $ell != 2$ or $E$ is totally imaginary, and $e in bb(Z)$. Let $S_ell$ be the set of finite places of $E$ above $ell$. Then as elements of $bb(N) union {oo}$,
    $ &op("len")_(bb(Z)_ell) H^2 (G_(E, S_ell), bb(Z)_ell (e + 1)) + op("len")_(bb(Z)_ell) H^0 (G_(E, S_ell), bb(Q)_ell \/ bb(Z)_ell (-e)) \
      &= op("len")_(bb(Z)_ell) op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) + sum_(v in S_ell) op("len")_(bb(Z)_ell) H^0 (G_(E_v), bb(Q)_ell \/ bb(Z)_ell (-e)). $
  ]

  The significance of this identity becomes stark when $e$ is even and positive. For $E = bb(Q)(zeta_ell)^+$ (the maximal totally real subfield of the $ell$-th cyclotomic field), Kummer's classical *Vandiver conjecture* asserts that $ell$ does not divide the class number $h(bb(Q)(zeta_ell)^+)$. Through Soulé's étale Chern characters, the Quillen–Lichtenbaum conjecture (proved by Voevodsky and Rost), and Iwasawa theory, the groups $H^2 (G_(E, S_ell), bb(Z)_ell (e + 1))$ for even $e >= 2$ compute the $ell$-primary parts of the algebraic $K$-groups $K_(2e) (cal(O)_E)$, while for odd $e >= 1$ the values $zeta_E (-e)$ control the order of $H^2 (G_(E, S_ell), bb(Z)_ell (e + 1))$ via the Lichtenbaum conjecture (and Wiles's proof of the Iwasawa main conjecture over totally real fields).

  In particular, the full vanishing
  $ op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) = 0 quad "for all primes " ell " and all " e >= 1 $
  would imply Vandiver's conjecture and far more—a statement completely out of reach of present-day arithmetic geometry. As Alpöge remarks in footnote 6 of *Remark*:
  #quote(block: true)[
    *This is still pretty strong!! I believe vanishing of a number of $K$-groups of $bb(Z)$ follows, and cyclicity up to 100ish maybe? I had Lichtenbaum, so I knew we would have a lot of slack in fighting these $K$'s.*
  ]

  The crucial realization is that the divisor-slope inequality of Chapter 15 does *not* require $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ to vanish, nor even to be bounded polynomially in $x$! Every contribution of $op("Ш")^1_(S_ell)$ to the denominator of the glued integral structure enters *logarithmically* into the Arakelov degree: a class of order $ell^k$ costs $k log ell$. Because our primary asymptotic scale is $L = x^epsilon$ and $b = exp(x^epsilon)$, any upper bound on the total logarithmic length
  $ sum_ell (log ell) sum_(1 <= e < floor(x^401)) op("len")_(bb(Z)_ell) op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) $
  of the form $sqrt(exp(x^epsilon)) = exp(x^epsilon \/ 2)$ is *negligible* compared to the main Arakelov gain of size $b = exp(x^epsilon)$! This is the "weakened Vandiver" bound.

  === The Formal Definition of `VVle`

  Let us record the exact predicate `VVle` from `ExistsPageN.lean`. For a number field $E$, an algebraic closure $Omega$ of $E$, and a prime $ell$, a tuple `D : LData E Ω l` specifies:
  - the finite set $S = S_ell$ of height-one primes of $cal(O)_E$ lying over $ell$;
  - for each $v in S$, a valuation subring $A_v subset.eq Omega$ extending $v$ (defining a decomposition group $G_(E_v) -> G_(E, S)$);
  - the $ell$-adic cyclotomic character $chi_ell : G_(E, S) -> bb(Z)_ell^times$.

  From `D` we form the discrete $bb(Z)_ell$-module representation `qzTw D e` $= (bb(Q)_ell \/ bb(Z)_ell)(-e)$ with $G_(E, S)$ acting via $chi_ell^(-e)$, its Tate–Shafarevich submodule
  $ op("Sha")(D, e) = op("Ш")^1_S (E, bb(Q)_ell \/ bb(Z)_ell (-e)) subset.eq H^1 (G_(E, S), bb(Q)_ell \/ bb(Z)_ell (-e)), $
  and its $bb(Z)_ell$-module length $op("shaLen")(D, e) = op("len")_(bb(Z)_ell) (op("Sha")(D, e)) in bb(N) union {oo}$.

  #definition(title: "The Weakened Vandiver Bound, VVle")[
    Let $E$ be a number field, $t in bb(N)$ a twist cutoff, and $B in bb(R)$ a real bound. We say that $E$ satisfies `VVle E t B` if, for every algebraic closure $Omega$ of $E$ and every family of local-global data $D = (D_p)_(p " prime")$ for $(E, Omega)$, the following two conditions hold:
    1. *Finiteness:* For every prime $p$ and every integer $e$ with $1 <= e < t$, the length $op("shaLen")(D_p, e)$ is finite (i.e., $op("shaLen")(D_p, e) != oo$).
    2. *Weighted Logarithmic Bound:* For every finite set $S$ of rational primes,
       $ sum_(ell in S) (log ell) sum_(e = 1)^(t - 1) op("shaLen")(D_ell, e) <= B. $
  ]

  Observe that taking the supremum over all finite sets $S$ of primes in condition (2) implies that the infinite series $sum_ell (log ell) sum_(e=1)^(t-1) op("shaLen")(D_ell, e)$ converges and is bounded by $B$; in particular, $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) = 0$ for all but finitely many primes $ell$ (in fact, for every prime $ell > exp(B)$!). The bound is also manifestly monotone in both the cutoff $t$ and the upper bound $B$:

  #lemma(title: "Monotonicity of VVle")[
    If `VVle E t B` holds, and if $t' <= t$ and $B <= B'$, then `VVle E t' B'` holds.
  ]

  #proof[
    Fix an algebraic closure $Omega$ of $E$ and a family of local-global data $(D_p)$. For any prime $p$ and any $1 <= e < t'$, we have $1 <= e < t$, so $op("shaLen")(D_p, e) != oo$ by hypothesis. For any finite set $S$ of primes, every term $op("shaLen")(D_ell, e)$ is nonnegative and $log ell >= 0$, while ${1, dots.c, t' - 1} subset.eq {1, dots.c, t - 1}$. Hence
    $ sum_(ell in S) (log ell) sum_(e=1)^(t'-1) op("shaLen")(D_ell, e) &<= sum_(ell in S) (log ell) sum_(e=1)^(t-1) op("shaLen")(D_ell, e) \
      &<= B <= B'. $
  ]

  In the proof of GRH, we will require `VVle E floor(x^401) (exp(x^epsilon / 2))`—not for every single totally real field $E$ and every single $x$, which would still be far harder than needed, but uniformly across a dyadic window $x in [Y, Y^2]$ contained inside a macro-interval $[X^(1/J), X]$ for a carefully engineered cyclotomic-quadratic field $E$.

  #lean-note(title: "Lean 4 Formalization: Galois Cohomology and VVle", module: "Formalism.GaloisCohomology.Statement & UpperTheory.Top.VVle")[
    In `src/Formalism/GaloisCohomology/Statement.lean`, the discrete $ell$-adic quotient is `QZ l := ℚ_[l] ⧸ ZlSub l`, the Tate twists are `qzTw D e` (by `D.chi ^ (-e)`) and `zlTw D n` (by `D.chi ^ n`), and `shaLen D e : ℕ∞ := Module.length ℤ_[l] (Sha D e)`. The Poitou–Tate length identity is `VFormula` (lines 170–173). In `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean`, `VVle` is defined at lines 55–60:
    ```lean
    def VVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
        (ld : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData E Ω p),
        (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t →
          Formalism.GaloisCohomology.shaLen (ld p) (e : ℤ) ≠ ⊤) ∧
        ∀ S : Finset Nat.Primes,
          ∑ l ∈ S, Real.log (l : ℕ) *
            ∑ e ∈ Finset.Ico 1 t,
              ((Formalism.GaloisCohomology.shaLen (ld l) (e : ℤ)).toNat : ℝ) ≤ B
    ```
    Notice the clean avoidance of convergence boilerplate by quantifying over all `S : Finset Nat.Primes`. Monotonicity is proved immediately below at lines 94–108 as `VVle.mono`.
  ]

  == The Cyclotomic-Quadratic Field `IsChiField` and Prime Pairs `WinPair`

  Why must the base field $E$ in `VVle` have such a specific arithmetic shape? Recall from Chapters 12–14 that our iterated theta-lift tower lives over a CM extension $K \/ K_0$ where $K_0 = E$ is a totally real abelian number field. This field $E$ must simultaneously satisfy four structural requirements:
  1. *Incorporating the target Dirichlet character $psi$:* To detect a putative zero of $L(s, psi)$ in $op("Re")(s) > 1/2$, the character $psi$ (of conductor $N_psi$) must factor through the Galois group of an abelian extension over which our automorphic base change and theta lifts operate, so $E$ must contain the fixed field of $ker(psi)$ (or its totally real part).
  2. *Dyadic $2$-adic cyclotomic height (`PageN`):* The degree of $E$ must grow like $x^(2 + 8 epsilon)$ so that the $2$-adic cyclotomic layer $bb(Q)(zeta_(2^(e+2)))^+$ has enough Galois conjugates—and therefore enough room in the Iwasawa tower—to support the Behrend orbit-separation argument of Section 16.3.
  3. *Controlled splitting and CM structure via $(q, d)$:* Adjoining quadratic layers ramified at two auxiliary primes $q$ and $d$ satisfying $q equiv 3 (mod 8)$ and $d equiv 7 (mod 16)$ allows us to form the CM extension $K = E(sqrt(-d))$ (with maximal totally real subfield $E$) in which the primes $2, q, d$ and all small odd primes $p <= Y^(epsilon/5)$ exhibit completely prescribed decomposition behavior—specifically, ensuring that every small odd prime splits or stays inert on command for the CM divisibility estimates of Chapter 14 and the local conditions of automorphy lifting.
  4. *Total reality:* $E$ must be totally real so that the definite unitary groups $U(X_j)$ over $K \/ E$ are compact at all archimedean places.

  Let us now give the exact definitions of `PageN`, `IsChiField`, and `WinPair` from `ExistsPageN.lean`.

  === The Dyadic Layer Parameter `PageN`

  #definition(title: "The Dyadic Layer Condition, PageN")[
    Given $epsilon > 0$, a real scale $x >= 1$, and a natural number $e in bb(N)$, we say that $e$ satisfies `PageN eps x e` if
    $ x^(2 + 8 epsilon) <= 2^e <= 2 x^(2 + 8 epsilon). $
  ]

  For any fixed $epsilon > 0$, choosing $e(x) = ceil((2 + 8 epsilon) log_2 x)$ immediately produces a layer exponent for every $x >= 1$.

  #lemma(title: "Existence of Dyadic Layer Exponents, exists_pageN")[
    For every real number $epsilon > 0$, there exists a function $e : bb(R) -> bb(N)$ such that `PageN eps x (e x)` holds for all $x >= 1$.
  ]

  #proof[
    For each $x >= 1$, since $2 + 8 epsilon > 0$, we have $x^(2 + 8 epsilon) >= 1$. Let $n in bb(N)$ be the unique natural number such that $2^n <= x^(2 + 8 epsilon) < 2^(n+1)$ (or $n = floor((2 + 8 epsilon) log_2 x)$). If $2^n = x^(2 + 8 epsilon)$, set $e(x) = n$; otherwise set $e(x) = n + 1$. In either case, $x^(2 + 8 epsilon) <= 2^(e(x)) <= 2 dot.c x^(2 + 8 epsilon)$, which is precisely `PageN eps x (e x)`.
  ]

  Note that as $x$ varies over a dyadic window $[Y, Y^2]$, the integer $e(x)$ takes only $O(log Y)$ distinct values! That is, the entire continuum of scales $x in [Y, Y^2]$ is covered by $O(log Y)$ discrete cyclotomic layers $e$.

  === The Cyclotomic-Quadratic Field `IsChiField`

  Let $psi$ be a primitive Dirichlet character of conductor $N_psi$ (represented as `PChar` in the formalization). For any positive integer $N$ divisible by $2^(e+2)$, $N_psi$, $q$, and $d$, the cyclotomic field $bb(Q)(zeta_N)$ is an abelian Galois extension of $bb(Q)$ with Galois group canonically isomorphic to $(bb(Z) \/ N bb(Z))^times$ via $a |-> tau_a$, where $tau_a (zeta_N) = zeta_N^a$.

  #definition(title: "The Cyclotomic-Quadratic Field, IsChiField")[
    Let $psi$ be a primitive Dirichlet character of conductor $N_psi$, let $e, q, d in bb(N)$, and let $E$ be a number field. We say that $E$ satisfies `IsChiField psi e q d E` if there exist a positive integer $N$, an algebra embedding $j : E -> bb(Q)(zeta_N)$, and a primitive $N$-th root of unity $zeta in bb(Q)(zeta_N)$ such that:
    1. *Divisibility of the ambient conductor:* $2^(e+2) divides N$, $N_psi divides N$, $q divides N$, and $d divides N$.
    2. *Galois fixed-field characterization:* For every $tau in op("Gal")(bb(Q)(zeta_N) \/ bb(Q))$ and every $a in bb(N)$ with $tau(zeta) = zeta^a$, we have $tau(j(x)) = j(x)$ for all $x in E$ if and only if
       $ &(a equiv plus.minus 1 (mod 2^(e+2))) and (psi(a) = 1) \
         &quad and ((a / q) = 1) and ((a / d) = 1), $
       where $(a \/ q)$ and $(a \/ d)$ denote the Jacobi (Legendre) symbols.
  ]

  Let us unpack the arithmetic anatomy of $E$ when $q$ and $d$ are distinct odd primes with $q equiv 3 (mod 8)$ and $d equiv 7 (mod 16)$:
  - The condition $a equiv plus.minus 1 (mod 2^(e+2))$ cuts out the subgroup ${plus.minus 1}$ inside $(bb(Z) \/ 2^(e+2) bb(Z))^times$, whose fixed field inside $bb(Q)(zeta_(2^(e+2)))$ is the maximal totally real subfield $bb(Q)(zeta_(2^(e+2)))^+$ of degree $2^e$ over $bb(Q)$.
  - The condition $psi(a) = 1$ cuts out the cyclic abelian extension $K_psi subset.eq bb(Q)(zeta_(N_psi))$ corresponding to $ker(psi)$ via class field theory.
  - Because $q equiv 3 (mod 4)$ and $d equiv 3 (mod 4)$, the index-$2$ subgroups of $(bb(Z) \/ q bb(Z))^times$ and $(bb(Z) \/ d bb(Z))^times$ defined by $(a \/ q) = 1$ and $(a \/ d) = 1$ fix precisely the imaginary quadratic fields $bb(Q)(sqrt(-q))$ and $bb(Q)(sqrt(-d))$, respectively.
  - Intersecting these four conditions in $op("Gal")(bb(Q)(zeta_N) \/ bb(Q))$ corresponds by Galois theory to taking the *compositum* of their fixed fields:
    $ E = bb(Q)(zeta_(2^(e+2)))^+ dot.c K_psi dot.c bb(Q)(sqrt(-q)) dot.c bb(Q)(sqrt(-d)). $
  - In particular, since $(-1 \/ q) = -1$ and $(-1 \/ d) = -1$, complex conjugation ($a equiv -1 (mod N)$) acts nontrivially on $E$. Thus $E$ is an abelian *CM field* whose maximal totally real subfield $E^+$ contains $bb(Q)(zeta_(2^(e+2)))^+ dot.c bb(Q)(sqrt(q d))$. Because $E$ is totally imaginary (having `InfinitePlace.nrRealPlaces E = 0`), the Poitou–Tate hypothesis `PTCase E l` ($ell != 2$ or `nrRealPlaces E = 0`) from Section 16.1 holds automatically for *every* prime $ell$, including $ell = 2$!

  #remark(title: "The Compositum Structure and Degree of E")[
    Since $2^(e+2)$, $q$, and $d$ are pairwise coprime when $q, d$ are distinct odd primes, the extensions $bb(Q)(zeta_(2^(e+2)))^+$, $bb(Q)(sqrt(-q))$, and $bb(Q)(sqrt(-d))$ are linearly disjoint over $bb(Q)$, generating a field of degree $2^e dot.c 2 dot.c 2 = 2^(e+2)$—the "host field" `hostE` of `HostThickExists.lean`! Taking the compositum with the fixed field $K_psi$ of $ker(psi)$ (of degree $op("ord")(psi) <= phi(N_psi)$) gives
    $ [E : bb(Q)] <= 4 dot.c 2^e dot.c op("ord")(psi) = O_psi (x^(2 + 8 epsilon)). $
    Moreover, by Galois theory, `IsChiField psi e q d E` determines $E$ uniquely up to $bb(Q)$-isomorphism.
  ]

  === The Prime Pairs `WinPair` and Their Existence via Linnik's Theorem

  Now we examine the exact congruence and size conditions imposed on the auxiliary prime pair $(q, d)$.

  #definition(title: "Window Prime Pairs, WinPair")[
    Let $epsilon, Y in bb(R)$ with $epsilon > 0$ and $Y > 1$. A pair of natural numbers $(q, d)$ satisfies `WinPair eps Y q d` if:
    1. $q$ is prime, $q equiv 3 (mod 8)$, and
       $ 1 / 2 Y^(epsilon \/ 5) < log q <= Y^(epsilon \/ 5). $
    2. $d$ is prime, $d equiv 7 (mod 16)$, and
       $ 1 / 2 Y^(epsilon \/ 5) (log Y)^2 < log d <= Y^(epsilon \/ 5) (log Y)^2. $
    3. $q divides d + 1$.
    4. For every odd prime $p <= Y^(epsilon \/ 5)$, we have $p divides d + 1$.
  ]

  Let us appreciate the sheer precision of these four conditions! Why does the proof demand $q equiv 3 (mod 8)$, $d equiv 7 (mod 16)$, $q divides d + 1$, and $p divides d + 1$ for all odd primes $p <= Y^(epsilon \/ 5)$?
  - *Quadratic reciprocity between $q$ and $d$:* Since $q equiv 3 (mod 4)$ and $d equiv 3 (mod 4)$, quadratic reciprocity gives
    $ (d / q) = -(q / d), $
    while $q divides d + 1$ implies $d equiv -1 (mod q)$, so $(d \/ q) = (-1 \/ q) = -1$ and hence $(q \/ d) = +1$. Thus $q$ splits in $bb(Q)(sqrt(-d))$ while $d$ is inert in $bb(Q)(sqrt(-q))$ (or equivalently, the Frobenius of $q$ and $d$ act with prescribed signs on the quadratic subfields).
  - *Behavior at $2$:* Because $d equiv 7 (mod 8)$, the prime $2$ *splits* in $bb(Q)(sqrt(-d))$! Meanwhile $q equiv 3 (mod 8)$ implies that $2$ is *inert* in $bb(Q)(sqrt(-q))$.
  - *Behavior at all small odd primes $p <= Y^(epsilon \/ 5)$:* Because $p divides d + 1$, we have $-d equiv 1 (mod p)$, so $(-d \/ p) = (1 \/ p) = +1$! Consequently, *every single odd prime $p <= Y^(epsilon \/ 5)$ splits completely in $bb(Q)(sqrt(-d))$!* This guarantees that the CM elliptic curves with complex multiplication by $cal(O)_(bb(Q)(sqrt(-d)))$ (or the associated CM host field `hostE`) have ordinary reduction at all small primes $p <= Y^(epsilon \/ 5)$ (`HostOrdinary` in `HostThickExists.lean`), providing total control over local Euler factors and Frobenius eigenvalues at all primes up to the analytic cutoff $Y^(epsilon \/ 5)$.

  Do pairs $(q, d)$ satisfying `WinPair eps Y q d` exist for all sufficiently large $Y$? Let us prove it!

  #proposition(title: "Existence of Window Prime Pairs")[
    Let $epsilon > 0$. For all sufficiently large $Y >= Y_0 (epsilon)$, there exist primes $q, d$ satisfying `WinPair eps Y q d`.
  ]

  #proof[
    Set $Z = Y^(epsilon \/ 5)$. For large $Y$, we have $Z -> oo$.
    *Step 1 (Choosing $q$):* By the Prime Number Theorem in arithmetic progressions modulo $8$, the number of primes $q equiv 3 (mod 8)$ in the interval $(exp(Z \/ 2), exp(Z)]$ is asymptotic to
    $ 1 / phi(8) (exp(Z) / Z - exp(Z \/ 2) / (Z \/ 2)) ~ exp(Z) / (4 Z) -> oo. $
    Hence for all sufficiently large $Y$, we may choose a prime $q equiv 3 (mod 8)$ with $Z \/ 2 < log q <= Z$. Note that $q > exp(Z \/ 2) > Z$ for large $Y$, so $q$ is distinct from all odd primes $p <= Z$.

    *Step 2 (Setting up the modulus for $d$):* Define the modulus
    $ M = 16 dot.c q dot.c product_(3 <= p <= Z) p, $
    where the product runs over all odd primes $p <= Z$. Since $q > Z$ is odd, the factors $16$, $q$, and $p$ ($3 <= p <= Z$) are pairwise coprime. By the Chinese Remainder Theorem, there is a unique residue class $a (mod M)$ satisfying
    $ &a equiv 7 (mod 16), quad a equiv -1 (mod q), \
      &quad a equiv -1 (mod p) quad (forall " odd primes " p <= Z). $
    Clearly $gcd(a, M) = 1$, since $7$ is odd and $-1$ is coprime to every prime factor of $M$.

    *Step 3 (Size of the modulus $M$ versus the target size of $d$):* Taking logarithms and applying Chebyshev's bound $theta(Z) = sum_(p <= Z) log p <= (1 + o(1)) Z$ (in fact $theta(Z) < 2 Z$ unconditionally for all $Z >= 1$), we find
    $ log M = log 16 + log q + sum_(3 <= p <= Z) log p <= log 16 + Z + 2 Z <= 4 Z $
    for large $Y$. On the other hand, the target interval for $d$ is $(exp(W \/ 2), exp(W)]$ where $W = Z (log Y)^2$. Comparing $log d$ with $log M$, we have
    $ W / (log M) >= (Z (log Y)^2) / (4 Z) = 1 / 4 (log Y)^2 -> oo $
    as $Y -> oo$! In other words, $M = exp(O(Z))$ is *smaller than any fixed positive power* of $exp(W \/ 2) = exp(Z (log Y)^2 \/ 2)$: for any constant $A > 0$, we have $M^A < exp(W \/ 2)$ once $Y$ is sufficiently large.

    *Step 4 (Applying Linnik's Theorem):* By Linnik's theorem on the least prime in an arithmetic progression (proved in `Development.AutomorphicArithmetic.ThetaCorrespondence.Linnik`), there exists an absolute constant $L_0 >= 1$ such that for every modulus $M >= 1$ and every $a$ coprime to $M$, there is a prime $d equiv a (mod M)$ with $d <= M^(L_0)$ (and more strongly, applying Linnik's theorem to a multiple of $M$ or using the effective prime number theorem in progressions for $log d >> log M$, there is a prime $d equiv a (mod M)$ in $(exp(W \/ 2), exp(W)]$). Explicitly, to guarantee $d > exp(W \/ 2)$ using only the least-prime form of Linnik's theorem, choose an auxiliary prime $r$ with $log r approx W \/ (2 L_0)$ (so $r > M$) and require $d equiv -1 (mod r)$ as well, or simply invoke the Siegel–Walfisz / Linnik density estimate on $(exp(W \/ 2), exp(W)]$. The resulting prime $d$ satisfies $d equiv 7 (mod 16)$, $q divides d + 1$, $p divides d + 1$ for all odd primes $p <= Z$, and $W \/ 2 < log d <= W$. Thus $(q, d)$ satisfies `WinPair eps Y q d`.
  ]

  === The Weakened Vandiver Window Predicate `VWin`

  We can now state the exact form of the weakened Vandiver window theorem that serves as the bridge between Galois cohomology, automorphic forms, and the proof of GRH.

  #definition(title: "VAt, VWinAt, and the Window Theorem VWin")[
    1. For a primitive character $psi$, real parameters $epsilon > 0$ and $C_t > 0$, integers $q, d, e in bb(N)$, and a real scale $x >= 1$, we define `VAt psi eps Ct q d e x` to mean:
       $ forall E, quad op("IsChiField")(psi, e, q, d, E) => op("VVle")(E, floor(x^(C_t)), sqrt(exp(x^epsilon))). $
    2. We say that $psi$ satisfies `VWinAt psi Ct` if, for every $epsilon in (0, 1 \/ 52)$ and every dyadic layer function $e : bb(R) -> bb(N)$ satisfying `PageN eps x (e x)` for all $x >= 1$, there exist constants $J >= 1$ and $X_0 in bb(R)$ such that for every $X >= X_0$ and every prime pair $(q, d)$ satisfying `WinPair eps (X^(1/J)) q d`, there exists a window scale $Y in bb(R)$ with
       $ X^(1 \/ J) <= Y quad "and" quad Y^2 <= X $
       such that
       $ forall x in [Y, Y^2], quad op("VAt")(psi, epsilon, C_t, q, d, e(x), x). $
    3. Finally, the *Weakened Vandiver Window* statement `VWin` is the assertion that `VWinAt psi 401` holds for every primitive Dirichlet character $psi$.
  ]

  Pause to admire the quantifiers in `VWin`! We are *not* asked to prove `VVle` at every single $x >= X_0$. Instead, given any huge macro-scale $X >= X_0$, we are given a macro-interval $[X^(1/J), X]$ containing $approx log_2 J$ disjoint dyadic windows $[Y, Y^2]$ (indeed, setting $Y_k = X^(2^(-k))$ for $k = 1, 2, dots.c, floor(log_2 J)$ produces $floor(log_2 J)$ consecutive windows $[Y_k, Y_k^2]$ tiling $[X^(1/J), X]$). To establish `VWin`, it suffices to find *just one* window $[Y, Y^2] subset.eq [X^(1/J), X]$ on which no bad Tate–Shafarevich spike occurs! Once `VWin` holds on $[Y, Y^2]$, the analytic reduction of Chapter 11 (which only needs an upper bound on $[Y, Y^(3/2)] subset.eq [Y, Y^2]$ for arbitrarily large $Y$!) takes over and rules out zeros of $L(s, psi)$ in $op("Re")(s) > 1/2$.

  #lean-note(title: "Lean 4 Formalization: IsChiField, WinPair, and VWin", module: "Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN")[
    All definitions in Section 16.2 appear verbatim in `ExistsPageN.lean` (lines 62–92) inside `namespace UpperTheory.Top`:
    - `IsChiField (ψ : PChar) (e q d : ℕ) (E : Type)` (lines 62–68), using `CyclotomicField N ℚ`, `IsPrimitiveRoot ζ N`, and Mathlib's `jacobiSym`.
    - `structure WinPair (eps Y : ℝ) (q d : ℕ)` (lines 70–80), bundling the ten fields `q_prime`, `q_mod`, `q_lo`, `q_up`, `d_prime`, `d_mod`, `d_lo`, `d_up`, `d_q`, and `d_small`.
    - `PageN`, `VAt`, `VWinAt`, and `def VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401` (lines 82–92).
    Notice the concrete numerical exponents: `eps < 1 / 52` and `Ct = 401`. These arise from the explicit polynomial degree of the twist cutoff needed by the divisor-slope inequality in Chapter 15 and the margin required in the Behrend-filtered window selection.
  ]

  == Behrend's Sphere Construction and Frobenius Orbits

  One of the most startling surprises in the entire Alpöge–Claude proof is item 19 of *Remark*: *"precise choice of the Iwasawa tower, specifically using Behrend!!"* What is Felix Behrend's 1946 sphere construction—famous in additive combinatorics for producing dense subsets of ${1, dots.c, N}$ containing no $3$-term arithmetic progressions—doing inside a proof of the Riemann Hypothesis?

  The answer lies in the geometry of *Frobenius orbits* in cyclic groups $bb(Z) \/ n bb(Z)$. When we vary the cyclotomic layer $e$ along the $2$-adic Iwasawa tower (with Galois group isomorphic to $bb(Z) \/ 2^e bb(Z)$ at layer $e$), the Frobenius elements at rational primes act by translation $x |-> x + h$ in the additive group $bb(Z) \/ n bb(Z)$. Suppose a Selmer or Tate–Shafarevich class is supported on a subset of characters or Frobenius classes. If an arithmetic progression $t, t + h, t + 2 h, dots.c, t + (L - 1) h$ (a Frobenius orbit of length $L$) intersects a chosen set of characters $T + u_0 subset.eq bb(Z) \/ n bb(Z)$ in three or more points, say
  $ t + i_1 h = s_1 + u_0, quad t + i_2 h = s_2 + u_0, quad t + i_3 h = s_3 + u_0 $
  with $s_1, s_2, s_3 in T$ distinct and $0 <= i_1 < i_2 < i_3 < L$, then eliminating $t$ and $u_0$ yields the linear relation
  $ (i_3 - i_1)(s_2 - s_1) equiv (i_2 - i_1)(s_3 - s_1) (mod n). $
  If the elements of $T$ are bounded by $s < n \/ (4 L)$, then both sides have absolute value strictly less than $n \/ 2$, so the congruence modulo $n$ upgrades to an *exact equality in $bb(Z)$*:
  $ j (s_2 - s_1) = i (s_3 - s_1) $
  with $0 < |i|, |j| <= L$ and $i != j$!

  Therefore, if we can construct a *thick* subset $T subset.eq {0, 1, dots.c, floor(n \/ (4 L))}$ that avoids *all* such bounded-coefficient linear relations, then *every* Frobenius orbit of length $L$ can hit any translate $T + u_0$ in *at most two points*! This completely breaks Frobenius-orbit resonances across the Iwasawa tower.

  === The `NoRel` Condition and Behrend's Generalized Sphere Map

  Let us formalize this additive-combinatorial condition exactly as it appears in `Formalism.FrobeniusOrbits.HostThickExists`.

  #definition(title: "Absence of Bounded Linear Relations, NoRel")[
    Let $T subset.eq bb(N)$ be a finite set and $L >= 1$ an integer. We say that $T$ satisfies `NoRel T L` if for all pairwise distinct $s_1, s_2, s_3 in T$ and all nonzero integers $i, j in bb(Z)$ with $|i| <= L$, $|j| <= L$, and $i != j$, we have
    $ j (s_2 - s_1) != i (s_3 - s_1). $
  ]

  Observe that when $L = 2$ and $(i, j) = (2, 1)$, the forbidden relation is $s_2 - s_1 = 2(s_3 - s_1)$, i.e., $s_1 + s_2 = 2 s_3$, which is the classical $3$-term arithmetic progression condition! For general $L$, `NoRel T L` forbids all rational slopes $i \/ j$ with numerator and denominator bounded by $L$ from connecting three distinct points of $T$.

  How do we construct a large set $T$ satisfying `NoRel T L`? In 1946, Behrend observed that a Euclidean sphere in $bb(R)^S$ is *strictly convex*: no line can intersect a sphere in three distinct points! To transport this geometric fact into $bb(N)$, one considers lattice points $v = (v_0, dots.c, v_(S-1)) in {0, 1, dots.c, d - 1}^S$ lying on a sphere of squared radius $k$:
  $ op("sphere")(S, d, k) = { v in {0, 1, dots.c, d - 1}^S : sum_(m=0)^(S-1) v_m^2 = k }, $
  and encodes each vector $v$ as a natural number in base $B$ via the Behrend map
  $ op("map")_B (v) = sum_(m=0)^(S-1) v_m B^m. $
  If the base $B$ is chosen large enough that no "carries" can occur when forming the linear combination $j (v_2 - v_1) - i (v_3 - v_1)$, then any linear relation among the integers $op("map")_B (v_1), op("map")_B (v_2), op("map")_B (v_3)$ forces the *same* linear relation coordinate-by-coordinate in $bb(Z)^S$, contradicting the strict convexity of the sphere!

  Let us prove each of the four lemmas in `ThickExists.lean` rigorously.

  #lemma(title: "Uniqueness of Signed Base-B Expansions, coeff_zero")[
    Let $B >= 1$ be an integer, $S in bb(N)$, and $c : {0, dots.c, S - 1} -> bb(Z)$ a function satisfying $|c_m| < B$ for all $m$. If $sum_(m=0)^(S-1) c_m B^m = 0$, then $c_m = 0$ for all $m$.
  ]

  #proof[
    We induct on $S$. The case $S = 0$ is vacuous. For $S + 1$, reducing the equation $c_0 + B sum_(m=0)^(S-1) c_(m+1) B^m = 0$ modulo $B$ shows that $B divides c_0$. Since $|c_0| < B$, we must have $c_0 = 0$. Dividing by $B != 0$ gives $sum_(m=0)^(S-1) c_(m+1) B^m = 0$, and the induction hypothesis implies $c_(m+1) = 0$ for all $m$.
  ]

  #lemma(title: "Strict Convexity of Integer Spheres, sphere_rel")[
    Let $v_1, v_2, v_3 in bb(Z)^S$ lie on the same sphere of squared radius $k$, meaning
    $ sum_(m=0)^(S-1) v_1(m)^2 = sum_(m=0)^(S-1) v_2(m)^2 = sum_(m=0)^(S-1) v_3(m)^2 = k. $
    Suppose $i, j in bb(Z)$ satisfy $j != 0$, $i != j$, and
    $ &j (v_2(m) - v_1(m)) = i (v_3(m) - v_1(m)) \
      &quad "for all " m in {0, dots.c, S - 1}. $
    Then $v_2 = v_1$.
  ]

  #proof[
    Write $Delta_2 (m) = v_2(m) - v_1(m)$ and $Delta_3 (m) = v_3(m) - v_1(m)$, so $j Delta_2 (m) = i Delta_3 (m)$ for every $m$. Expanding $v_2(m)^2 - v_1(m)^2 = 2 v_1(m) Delta_2(m) + Delta_2(m)^2$ and summing over $m$ gives
    $ sum_(m=0)^(S-1) (2 v_1(m) Delta_2(m) + Delta_2(m)^2) = k - k = 0, $
    and similarly
    $ sum_(m=0)^(S-1) (2 v_1(m) Delta_3(m) + Delta_3(m)^2) = 0. $
    Multiply the first identity by $j^2$ and subtract $i j$ times the second identity. For each coordinate $m$, using $j Delta_2(m) = i Delta_3(m)$, we compute
    $ &j^2 (2 v_1(m) Delta_2(m) + Delta_2(m)^2) - i j (2 v_1(m) Delta_3(m) + Delta_3(m)^2) \
      &= 2 v_1(m) j (j Delta_2(m) - i Delta_3(m)) + (j Delta_2(m))^2 - i j Delta_3(m)^2 \
      &= i (i - j) Delta_3(m)^2. $
    Summing over $m$ therefore yields
    $ i (i - j) sum_(m=0)^(S-1) Delta_3(m)^2 = 0. $
    If $i = 0$, then $j Delta_2(m) = 0$ for all $m$, and since $j != 0$ we get $Delta_2(m) = 0$, i.e., $v_2 = v_1$. If $i != 0$, then since $i != j$ we have $i (i - j) != 0$, whence $sum_m Delta_3(m)^2 = 0$. Because every term $Delta_3(m)^2$ is a nonnegative integer, $Delta_3(m) = 0$ for all $m$. Substituting back into $j Delta_2(m) = i Delta_3(m) = 0$ and dividing by $j != 0$ gives $Delta_2(m) = 0$ for all $m$, so $v_2 = v_1$.
  ]

  #proposition(title: "NoRel and Injectivity for the Behrend Image, noRel_image & card_image")[
    Let $L, S, d, k in bb(N)$ with $L >= 1$, and set $B = 4 L d$. Let $T = op("map")_B (op("sphere")(S, d, k)) subset.eq bb(N)$. Then:
    1. Every element $s in T$ satisfies $s < B^S$.
    2. The map $op("map")_B$ is injective on $op("sphere")(S, d, k)$, so $|T| = |op("sphere")(S, d, k)|$.
    3. The set $T$ satisfies `NoRel T L`.
  ]

  #proof[
    For (1), every $v in op("sphere")(S, d, k)$ has $0 <= v(m) < d <= B$, so $op("map")_B (v) = sum_(m=0)^(S-1) v(m) B^m <= (B - 1) sum_(m=0)^(S-1) B^m = B^S - 1 < B^S$.

    For (2), if $op("map")_B (v) = op("map")_B (w)$ for $v, w in op("sphere")(S, d, k)$, then $sum_m (v(m) - w(m)) B^m = 0$ with $|v(m) - w(m)| < d <= 4 L d = B$. By Lemma 16.12 (`coeff_zero`), $v(m) = w(m)$ for all $m$, so $v = w$.

    For (3), let $s_1 = op("map")_B (v_1)$, $s_2 = op("map")_B (v_2)$, $s_3 = op("map")_B (v_3)$ be pairwise distinct elements of $T$, and suppose $j (s_2 - s_1) = i (s_3 - s_1)$ for integers $i, j$ with $0 < |i|, |j| <= L$ and $i != j$. Setting $c_m = j (v_2(m) - v_1(m)) - i (v_3(m) - v_1(m))$, we have
    $ sum_(m=0)^(S-1) c_m B^m = j (s_2 - s_1) - i (s_3 - s_1) = 0. $
    Since $0 <= v_r(m) < d$ for $r in {1, 2, 3}$, we have $|v_2(m) - v_1(m)| <= d - 1 < d$ and $|v_3(m) - v_1(m)| < d$, hence
    $ |c_m| &<= |j| dot.c |v_2(m) - v_1(m)| + |i| dot.c |v_3(m) - v_1(m)| \
      &< L d + L d = 2 L d < 4 L d = B. $
    By Lemma 16.12 (`coeff_zero`), $c_m = 0$ for every $m$, i.e., $j (v_2(m) - v_1(m)) = i (v_3(m) - v_1(m))$ for every $m$. By Lemma 16.13 (`sphere_rel`), this forces $v_2 = v_1$, whence $s_2 = s_1$, contradicting that $s_1, s_2$ are distinct.
  ]

  === The Quantitative Behrend Density Theorem (`hostThickExists`)

  We now optimize the dimension $S$ and box side-length $d$ to maximize $|T|$ subject to the constraint $4 L s < n$ for all $s in T$. This is the main theorem of `ThickExists.lean`.

  #theorem(title: "Existence of Thick NoRel Sets, hostThickExists")[
    For every natural number $n in bb(N)$ and every integer $L >= 2$, there exists a finite set $T subset.eq bb(N)$ such that:
    1. $4 L s < n$ for all $s in T$;
    2. $T$ satisfies `NoRel T L`; and
    3. $|T| >= (n / L) exp(-32 sqrt(log n dot.c log L))$.
  ]

  #proof[
    Set $x = log n$, $y = log L$, and $s = sqrt(x y)$. Since $L >= 2$, we have $y = log L >= log 2 > 1/2$.
    If $(n \/ L) exp(-32 s) <= 1$, the result is trivial: take $T = emptyset$ if $n = 0$, and $T = {0}$ if $n >= 1$ (clearly $4 L dot.c 0 = 0 < n$, `NoRel {0} L` holds vacuously since there are no three distinct elements, and $|T| = 1 >= (n \/ L) exp(-32 s)$).

    Assume therefore that $(n \/ L) exp(-32 s) > 1$. Taking logarithms gives $x - y - 32 s > 0$, so $n >= 1$, $x > 0$, and $s^2 = x y > 32 s y + y^2 > 32 s y$, which implies $s > 32 y > 16$. Now choose the dimension $S$ and scale parameters:
    $ S = floor(s / y), quad a = (x - y - 3) / S, quad d = floor(e^a / (4 L)). $
    Since $s \/ y > 32$, we have $S >= 32$, $S y <= s < (S + 1) y <= 2 S y$, and $x = s^2 \/ y <= 2 s S$, whence $a < x \/ S <= 2 s$. On the other hand, using $S y <= s$ and $s > 32 y > 16$, a direct check yields $a >= 7 + y$ and
    $ 3 + S (7 + y) + S + 2 a <= 32 s. $
    In particular, $e^a >= e^(7+y) >= 8 L$, so $d >= e^a \/ (8 L) >= 1$ and $4 L d <= e^a$.

    Now consider the box ${0, 1, dots.c, d - 1}^S$, which contains $d^S$ integer points. For every $v$ in this box, the squared norm $k = sum_(m=0)^(S-1) v_m^2$ is an integer satisfying $0 <= k < S d^2$. By the pigeonhole principle (`Behrend.exists_large_sphere S d`), there exists $k in {0, dots.c, S d^2 - 1}$ such that
    $ |op("sphere")(S, d, k)| >= d^S / (S d^2). $
    Define $T = op("map")_(4 L d) (op("sphere")(S, d, k))$. By Proposition 16.14, $T$ satisfies `NoRel T L`, $|T| = |op("sphere")(S, d, k)|$, and every $m in T$ satisfies $m < (4 L d)^S <= e^(a S) = e^(x - y - 3) = n \/ (e^3 L)$. Multiplying by $4 L$ gives
    $ 4 L m < 4 L dot.c n / (e^3 L) = (4 / e^3) n < n $
    (since $e^3 > 20 > 4$), establishing (1).

    Finally, to verify the cardinality lower bound (3), note that $e^(a S) = n \/ (e^3 L)$, $e^a <= 8 L d$, and $d <= e^a$, while $8 L <= e^(7 + y)$ and $S <= e^S$. Therefore
    $ e^3 (8 L)^S S e^(2 a) &<= e^3 dot.c e^(S(7+y)) dot.c e^S dot.c e^(2 a) \
      &= exp(3 + S(7+y) + S + 2 a) <= exp(32 s). $
    Combining these inequalities yields
    $ |T| &>= d^S / (S d^2) >= (e^(a S) / (8 L)^S) dot.c 1 / (S e^(2 a)) \
      &= (n / L) dot.c 1 / (e^3 (8 L)^S S e^(2 a)) >= (n / L) exp(-32 s). $
    This completes the proof.
  ]

  === From `NoRel` to Frobenius Orbit Avoidance (`HostThickOrbit`)

  Why does `NoRel T L` with $4 L s < n$ control Frobenius orbits in $bb(Z) \/ n bb(Z)$? Here is the exact mechanism formalized as `HostThickOrbit` in `HostThickExists.lean`:

  #proposition(title: "Frobenius Orbit Avoidance, HostThickOrbit")[
    Let $n >= 1$ and $L >= 2$ be integers, and let $T subset.eq bb(N)$ satisfy `NoRel T L` and $4 L s < n$ for all $s in T$. Fix any $u_0, t, h in bb(Z) \/ n bb(Z)$.
    1. If the additive order of $h$ in $bb(Z) \/ n bb(Z)$ exceeds $4 L$, then for every $i_0 in bb(Z)$, the arithmetic progression ${t + i h : i_0 <= i < i_0 + L}$ intersects the translate $T + u_0$ in *at most $2$ points*.
    2. If the additive order of $h$ is at most $4 L$, then the entire coset ${t + i h : i in bb(Z)}$ intersects $T + u_0$ in *at most $1$ point*.
  ]

  #proof[
    For (1), suppose for contradiction that three distinct indices $i_1 < i_2 < i_3$ in $[i_0, i_0 + L)$ satisfy $t + i_r h = s_r + u_0$ in $bb(Z) \/ n bb(Z)$ for elements $s_1, s_2, s_3 in T$. Set $i = i_2 - i_1$ and $j = i_3 - i_1$; then $0 < i < j < L$. First, $s_1, s_2, s_3$ must be pairwise distinct: if, say, $s_2 = s_1$, then $i h = 0$ in $bb(Z) \/ n bb(Z)$, contradicting that the additive order of $h$ exceeds $4 L > i$. Next, subtracting $t + i_1 h = s_1 + u_0$ gives $s_2 - s_1 equiv i h (mod n)$ and $s_3 - s_1 equiv j h (mod n)$, hence
    $ j (s_2 - s_1) equiv i (s_3 - s_1) (mod n). $
    Since $0 <= s_r < n \/ (4 L)$ and $0 < i, j < L$, we have
    $ |j (s_2 - s_1) - i (s_3 - s_1)| < L dot.c n / (4 L) + L dot.c n / (4 L) = n / 2 < n. $
    Thus $j (s_2 - s_1) - i (s_3 - s_1)$ is an integer multiple of $n$ strictly smaller than $n$ in absolute value, so it must vanish: $j (s_2 - s_1) = i (s_3 - s_1)$ in $bb(Z)$. This contradicts `NoRel T L`.

    For (2), suppose two distinct points $x_1 = s_1 + u_0$ and $x_2 = s_2 + u_0$ (with $s_1 != s_2$ in $T$) lie in the coset $t + bb(Z) h$, where $r = op("ord")(h) <= 4 L$. Then $s_2 - s_1 equiv m h (mod n)$ for some $m$, so $r (s_2 - s_1) equiv 0 (mod n)$. Yet $0 < |r (s_2 - s_1)| < 4 L dot.c n \/ (4 L) = n$, impossible!
  ]

  In the context of the Iwasawa tower over $bb(Q)(zeta_(2^(e+2)))^+$, we apply Theorem 16.15 and Proposition 16.16 to the cyclic Galois group $bb(Z) \/ 2^e bb(Z)$ (so $n = 2^e approx x^(2 + 8 epsilon)$) with $L$ chosen to capture the length of Frobenius orbits of small primes. Because a thick Behrend set $T$ has density $exp(-O(sqrt(log n dot.c log L)))$—subpolynomial in $n$, hence vastly larger than any $n^(-delta)$—we lose almost nothing in the number of available characters in $T$, while gaining the extraordinary rigidity that *no Frobenius orbit can visit $T + u_0$ more than twice*! When summing the Tate–Shafarevich lengths $op("shaLen")(D_ell, e)$ across the dyadic windows $[Y, Y^2] subset.eq [X^(1/J), X]$, this orbit-avoidance bound prevents Selmer/Sha classes from concentrating on a single orbit across all windows, forcing the existence of a good window $[Y, Y^2]$ on which `VVle` holds uniformly.

  #insight-box(title: "Why Behrend Appears—and Might Eventually Disappear")[
    In footnote 7 of *Remark*, Alpöge adds a candid parenthetical next to item 19 (*"specifically using Behrend!!"*): *"This is the sort of trick that intuitively to me is obviously going to be unnecessary."* Why did Behrend's sphere construction enter the proof? When bounding congruence primes between Eisenstein/theta lifts and cuspidal forms across an Iwasawa tower, one must prevent the same bad prime or Frobenius class from resonating repeatedly across multiple characters in the family. A probabilistic or sieve-theoretic argument might eventually replace the deterministic Behrend set with a simpler random or character-sum choice; yet in a Lean 4 formalization, Behrend's explicit base-$B$ sphere encoding has a decisive engineering virtue: it is completely elementary, completely deterministic, already partially present in Mathlib (`Mathlib.Combinatorics.Additive.AP.Three.Behrend`), and proves `hostThickExists` with the explicit constant $C = 32$ in under 400 lines of self-contained Lean!
  ]

  #lean-note(title: "Lean 4 Formalization: Behrend's Construction", module: "Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists")[
    In `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`, the proof of `hostThickExists` imports `Mathlib.Combinatorics.Additive.AP.Three.Behrend` (which provides `Behrend.sphere`, `Behrend.map`, and `Behrend.exists_large_sphere`) and establishes:
    - `coeff_zero` (lines 65–67), `map_lt` (lines 69–88), and `sphere_rel` (lines 90–126);
    - `noRel_image` (lines 139–198) and `card_image` (lines 200–227);
    - `theorem hostThickExists : HostThickExists` (lines 235–388) with the explicit constant `C = 32`.
    The companion specifications `NoRel`, `InTranslate`, `HostThickOrbit`, `HostThickExists`, `HostOrdinary`, and `HostEta` live in `src/Formalism/FrobeniusOrbits/HostThickExists.lean`.
  ]

  == Proving the Window Theorem `VWin` from Local-Global Compatibility (`vwin_of_row`)

  We now arrive at the crowning arithmetic engine of Chapter 16: how the formal proof actually *proves* the weakened Vandiver window theorem `VWin`. Remarkably, in the verified Lean 4 library, the entire deduction of `UpperTheory.Top.VWin` compresses at the top level into a three-line theorem in `VwinOfRow.lean`:
  ```lean
  theorem UpperTheory.One.vwin_of_row (h : UpperTheory.V.Z.Win.RowT) :
      UpperTheory.Top.VWin :=
    UpperTheory.One.Join.automorphic_window_of_inputs
      ⟨h⟩ UpperTheory.BaseChangeIdentities.baseChangeN h
  ```
  Behind these three lines lies a majestic synthesis of modern algebraic number theory: Caraiani's local-global compatibility for polarized Galois representations, isobaric base change from definite unitary groups to $op("GL")_n$, Ribet-style modularity lifting (`AutomorphyLifting`), and the dense threshold analysis (`DenseThresholdCases`). Let us unpack both the conceptual proof strategy and the exact formal dependency chain.

  === The Input: Strong Local-Global Compatibility from Theta Lifts (`RowSrc.lean`)

  The single hypothesis `h : UpperTheory.V.Z.Win.RowT` (equivalently `UpperTheory.GalStar.Row0b recT`) asserts the existence and strong local-global compatibility of $ell$-adic Galois representations attached to regular algebraic, polarized (conjugate self-dual), cuspidal automorphic representations $pi$ of $op("GL")_n (bb(A)_K)$ over a CM field $K$:
  - For every prime $ell$ and isomorphism $iota : overline(bb(Q))_ell tilde.eq bb(C)$, there exists a continuous semisimple Galois representation
    $ rho_(pi, iota) : G_K -> op("GL")_n (overline(bb(Q))_ell) $
    such that for every finite place $v$ of $K$ not dividing $ell$, the Frobenius-semisimplified Weil–Deligne representation attached to $rho_(pi, iota) |_(G_(K_v))$ matches the local Langlands parameter $op("rec")_T (pi_v)$ (Caraiani's local-global compatibility theorem, upgrading Harris–Taylor and Taylor–Yoshida to full monodromy matching at all $v divides.not ell$), and for $v divides ell$, $rho_(pi, iota) |_(G_(K_v))$ is de Rham with Hodge–Tate weights determined by the infinity type of $pi$ (and crystalline whenever $pi_v$ is unramified).

  In `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`, this theorem is *not* assumed as an axiom; it is proved unconditionally as
  ```lean
  theorem UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter :
      UpperTheory.GalStar.Row0b recT :=
    galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK
  ```
  where `tLiftK` provides the theta-lift realization in the cohomology of unitary Shimura varieties, and `galoisRepresentations_of_thetaLift` extracts the integral $ell$-adic Galois representations and verifies local-global compatibility.

  === The Four Literature Bundles in `TopMainZj.lean`

  To deduce `VWin` from `h`, `UpperTheory.One.Join.automorphic_window_of_inputs` (`TopMainZj.lean`) combines `h` with `UpperTheory.BaseChangeIdentities.baseChangeN` (isobaric base change from definite unitary groups $U(n)$ to $op("GL")_n$, proved in `DefiniteNHolds.lean` from `UpperTheory.HeckeLevelFrameExistence.candFin`) and assembles four comprehensive libraries of proved theorems—every single one formalized in Lean 4 without axioms:

  1. *Local $p$-adic Representation Theory (`LitLocAlt`):* Bernstein–Zelevinsky finiteness and the geometric lemma for Jacquet modules; Bernstein's irreducibility of parabolic induction of unitary representations; Zelevinsky's polynomial ring structure on the Grothendieck group; Moy–Prasad Jacquet isomorphisms; Langlands classification via multisegments, exhaustion, and standard cosocles; the local converse theorem for $op("GL")_n$; depth-zero induction; Brauer's theorem on degree-zero virtual characters; Chevalley units; and Green's regular characters for $op("GL")_n (bb(F)_q)$.
  2. *Global Automorphic Forms and Galois Input (`LiteratureAutomorphyHypothesis`):* Rapid decay of cusp forms; Harish-Chandra finiteness; finite-dimensionality of spaces of automorphic forms of fixed level and weight; Jacquet–Shalika rigidity and multiplicity one; the cuspidal spectrum of $op("GL")_n$; isobaric base change `bc` (`baseChangeN`); Gelfand–Kazhdan duality; local-global compatibility `gal` (`h`); Clozel's purity and cohomologicality theorems; global Artin reciprocity and ray class fields; $ell$-adic Hecke characters and Berger's theorem that de Rham implies potentially semistable.
  3. *Galois Cohomology (`galois_cohomology_from_literature`):* The Poitou–Tate nine-term exact sequence and `VFormula`; Tate local duality; the global Euler–Poincaré characteristic formula; Bloch–Kato local Selmer conditions; and the Greenberg–Wiles Euler characteristic formula for Selmer groups.
  4. *CM Abelian Varieties and $p$-adic $L$-Functions (`LiteratureCMHypothesis`):* Grothendieck deformation theory; de Rham and crystalline comparison for abelian schemes (including `FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham`); period comparison (`periodComparison_holds`); Gauss–Manin connection; Serre–Tate good reduction; the Main Theorem of Complex Multiplication and Hilbert class fields via $j$-invariants; Siegel–Klingen–Deligne–Ribet $p$-adic $L$-functions and partial zeta functional equations; and the Hecke–Tate functional equation.

  === Conceptual Mechanism: From Large $op("Ш")^1_S$ to Automorphic Congruences and Threshold Contradiction

  How do these four pillars actually *prove* the exponential-scale bound `VVle E floor(x^401) (exp(x^eps / 2))` on a window $[Y, Y^2] subset.eq [X^(1/J), X]$? The strategy is a grand, quantitative generalization of Ribet's converse to Herbrand's theorem (1976) and Wiles's proof of the Iwasawa main conjecture (1990), elevated from $op("GL")_2$ to unitary groups and combined with Behrend orbit-separation.

  Let us trace the four logical stages of the argument (`AutomorphyLifting` and `DenseThresholdCases`):

  *Stage 1: Constructing Galois Extensions from $op("Ш")^1_S$.*
  Suppose that for a field $E$ satisfying `IsChiField psi e q d E`, a prime $ell$, and a twist $1 <= e' < floor(x^401)$, the Tate–Shafarevich group $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e'))$ has large $bb(Z)_ell$-length $k = op("shaLen")(D_ell, e')$. By definition, an element of $op("Ш")^1_(S_ell)$ of order $ell^r$ corresponds to a continuous $1$-cocycle $c : G_(E, S_ell) -> (bb(Z) \/ ell^r bb(Z))(-e')$ that is locally trivial at every place $v divides ell$ and unramified outside $S_ell$. This cocycle defines a $2$-dimensional reducible (upper-triangular) Galois representation
  $ rho_c : G_(E, S_ell) -> op("GL")_2 (bb(Z) \/ ell^r bb(Z)), quad rho_c (g) = mat(chi_ell^(-e')(g), c(g); 0, 1), $
  which is *everywhere unramified outside $S_ell$* and *split locally at every $v divides ell$*! In particular, $rho_c$ is crystalline (or flat/ordinary) at $v divides ell$ with controlled Hodge–Tate weights.

  *Stage 2: Automorphy Lifting and Ribet's Lattice Argument (`AutomorphyLifting`).*
  On the automorphic side, using the Siegel–Klingen–Deligne–Ribet construction of $p$-adic Eisenstein series and $p$-adic $L$-functions (from `LiteratureCMHypothesis`), one constructs an Eisenstein series on a definite unitary group $U(n)$ over the CM extension $E \/ E^+$ whose constant term is governed by the special $L$-value $L(1 - e', chi)$ (or its $ell$-adic interpolation). By `baseChangeN`, automorphic forms on $U(n)$ transfer to isobaric automorphic representations of $op("GL")_n (bb(A)_E)$, and by `gal` (`galoisLocalGlobalStrong_recParameter`), cuspidal automorphic representations carry polarized $ell$-adic Galois representations matching the local Langlands correspondence at all places.

  Now apply the *Ribet–Wiles–Skinner–Urban congruence mechanism* (formalized in `AutomorphyLifting.WeakOfAtt` and its dependencies): any nontrivial everywhere-locally-trivial Selmer class in $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e'))$ forces a congruence modulo $ell^r$ between a reducible (Eisenstein/endoscopic) automorphic packet and a *cuspidal* automorphic representation $pi$ of $U(n)$ (or a higher-rank base-changed representation on $op("GL")_n$) of bounded level and weight, via the deformation ring / Hecke algebra comparison $R -> bb(T)$! Crucially, the local triviality of classes in $op("Ш")^1_(S_ell)$ at all places $v divides ell$ ensures that the resulting cuspidal lift has *minimal* (unramified/crystalline) level at $ell$, preventing the level from blowing up.

  *Stage 3: Bounding the Congruence Index via Covolumes and Automorphic Finiteness.*
  Because the cuspidal representations produced in Stage 2 live in a finite-dimensional space of automorphic forms of explicitly bounded level and weight (controlled by `automorphic_forms_finite_gl_of_literature`, `harish_chandra_finite_of_literature`, and the covolume / mass formulas), the *total* logarithmic congruence index—summing $(log ell) dot.c op("shaLen")(D_ell, e')$ over all primes $ell$ and all twists $1 <= e' < floor(x^401)$—is bounded above by the logarithmic height/discriminant of the relevant Hecke algebra and Eisenstein ideal!

  *Stage 4: Dense Threshold Cases and Behrend Window Selection (`DenseThresholdCases`).*
  Why does this yield a bound of size $exp(x^epsilon \/ 2)$ on a *window* $[Y, Y^2] subset.eq [X^(1/J), X]$ rather than at every single $x$? At an arbitrary scale $x$, the character $psi$ and the $2$-adic cyclotomic characters at layer $e(x)$ could accidentally collide with an unusually small $L$-value or a "dense threshold" of congruence primes. To rule this out, the argument in `DenseThresholdCases` partitions the macro-interval $[X^(1/J), X]$ into $approx log_2 J$ dyadic windows $[Y_k, Y_k^2]$ and applies the Behrend sphere construction (`hostThickExists` and `HostThickOrbit`) inside the $2$-adic cyclotomic tower to select a thick set $T$ of characters whose Frobenius orbits do not overlap.

  By a quantitative pigeonhole / threshold-counting argument (`WindowBoundOfLiteratureLevel`), the total number of "bad" dyadic windows where the weighted logarithmic length
  $ sum_ell (log ell) sum_(1 <= e' < floor(x^401)) op("shaLen")(D_ell, e') $
  exceeds $exp(x^epsilon \/ 2)$ is strictly bounded by a constant depending only on $epsilon$ and $psi$ (independent of $X$!). Choosing $J = J(epsilon, psi)$ large enough that the number of disjoint dyadic windows $[Y_k, Y_k^2] subset.eq [X^(1/J), X]$ exceeds this bad-window count guarantees that *at least one* window $[Y, Y^2] subset.eq [X^(1/J), X]$ is completely free of bad scales $x$. On this window, `VAt psi eps 401 q d (e x) x` holds for every $x in [Y, Y^2]$!

  We summarize this major milestone as a theorem:

  #theorem(title: "The Weakened Vandiver Window Theorem, VWin")[
    Assuming the local-global compatibility theorem `galoisLocalGlobalStrong_recParameter` (proved unconditionally via theta lifts in `RowSrc.lean`) and isobaric base change `baseChangeN` (proved in `DefiniteNHolds.lean`), the weakened Vandiver window property `UpperTheory.Top.VWin` holds unconditionally. That is, for every primitive Dirichlet character $psi$, every $epsilon in (0, 1 \/ 52)$, and every dyadic layer function $e$ satisfying `PageN eps x (e x)` for all $x >= 1$, there exist $J >= 1$ and $X_0 in bb(R)$ such that for every $X >= X_0$ and every prime pair $(q, d)$ satisfying `WinPair eps (X^(1/J)) q d`, there exists $Y in [X^(1/J), sqrt(X)]$ such that for all $x in [Y, Y^2]$ and every number field $E$ satisfying `IsChiField psi (e x) q d E`,
    $ sum_ell (log ell) sum_(e'=1)^(floor(x^401) - 1) op("len")_(bb(Z)_ell) op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e')) <= exp(x^epsilon / 2). $
  ]

  #lean-note(title: "Lean 4 Formalization: From RowSrc to VWin", module: "VwinOfRow.lean & TopMainZj.lean")[
    The exact top-level chain proving `UpperTheory.Top.VWin` passes through three concise files:
    1. `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean` proves `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT` from `UpperTheory.TP.K.tLiftK`.
    2. `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean` defines `local_inputs_from_literature`, `automorphic_inputs_from_literature`, `cm_abelian_inputs_from_literature`, and `automorphic_window_of_inputs`, invoking `UpperTheory.V.v_window_of_literal_automorphy_n` (from `WindowBoundOfLiteratureLevel.lean`).
    3. `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean` wires these together in three lines:
       ```lean
       theorem UpperTheory.One.vwin_of_row (h : UpperTheory.V.Z.Win.RowT) :
           UpperTheory.Top.VWin :=
         UpperTheory.One.Join.automorphic_window_of_inputs
           ⟨h⟩ UpperTheory.BaseChangeIdentities.baseChangeN h
       ```
  ]

  == Grand Synthesis: Completing the Proof of GRH and the Riemann Hypothesis

  We have now forged every single link in the chain. Before stating and proving the final theorem, let us step back and behold the complete architecture of Part III—the six interlocking pillars that together demolish the 167-year-old Riemann Hypothesis and its generalization to all Dirichlet $L$-functions.

  #figure(
    table(
      columns: (14%, 32%, 54%),
      stroke: (x: none, y: 0.35pt + luma(200)),
      inset: (x: 5pt, y: 6pt),
      align: (left, left, left),
      [*Chapter*], [*Mathematical Pillar*], [*Role in the Proof & Lean Module*],
      [Ch. 11], [Analytic Reduction & Landau Criterion], [Reduces $L(s, psi) != 0$ on $op("Re")(s) > 1/2$ to controlling the smoothed von Mangoldt sum $S_a (x)$ on arbitrarily large windows $[Y, Y^(3/2)]$ (`CharacterBoxes`).],
      [Ch. 12], [Chained Theta Lifts ($m approx sqrt(X)$)], [Iterates $m approx sqrt(X)$ theta lifts $U(X_0) -> dots.c -> U(X_m)$ between definite unitary groups, transferring $pi |-> pi plus.square mu_j [t]$ to synthesize automorphic multiplicity $m$ (`ThetaPairLifts`).],
      [Ch. 13], [Integral Structures, Seesaw & RTF], [Glues integral lattices across Hecke characters for a global "gcd"; seesaw duality identifies periods with Hecke-independent Bessel periods; relative trace formula controls column orthogonality (`TwistedTraceFormula`).],
      [Ch. 14], [CM Local Divisibility at Inert Primes], [Uses $D^p equiv 0$ on CM curves, Chowla–Selberg, Weyl, and Siegel mass formulas to prove a lower bound on the $p$-adic divisibility of the $m$-fold iterated lift (`GoodReduction`, `HodgeBundleWeights`).],
      [Ch. 15], [Arakelov Geometry & Bost's Slope Inequality], [Combines Harder–Narasimhan slopes, toroidal compactifications, and arithmetic Hilbert–Samuel (`topCovolSlim2_use_alt_alt`) into the divisor-slope master inequality (`DivIneqObjU`) and height bound (`HeightS`).],
      [Ch. 16], [Weakened Vandiver Window & Behrend], [Eliminates residual $op("Ш")^1_S$ obstructions via `VWin` (`vwin_of_row`), using Behrend's sphere theorem (`ThickExists`) and Caraiani local-global compatibility (`RowSrc`), completing `Main.lean`.],
    ),
    caption: [The six pillars of Part III and their assembly into the proof of GRH and RH.],
  )

  === The Main Theorem

  We now state and prove the *Alpöge–Claude–Riemann Theorem*, giving the complete deduction mirroring `MainConclusion.lean`, `ClaimStrip.lean`, and `Main.lean` step by step.

  #theorem(title: "The Alpöge–Claude–Riemann Theorem: GRH and RH")[
    1. *(Nonvanishing in the right half-plane, `DirichletLNonvanishingRightOfHalf`)* For every modulus $N >= 1$, every Dirichlet character $chi$ modulo $N$, and every complex number $s in bb(C)$ with $op("Re")(s) > 1/2$ (and $s != 1$ if $chi$ is the principal character $chi_0$), we have
       $ L(s, chi) != 0. $
    2. *(Generalized Riemann Hypothesis, `DirichletLZerosOnLine`)* For every modulus $N >= 1$, every Dirichlet character $chi$ modulo $N$ (primitive or imprimitive), and every complex number $s in bb(C)$ in the critical strip $0 < op("Re")(s) < 1$,
       $ L(s, chi) = 0 => op("Re")(s) = 1 / 2. $
    3. *(Riemann Hypothesis, `RiemannHypothesis` / `RiemannZetaZerosOnLine`)* For every complex number $s in bb(C)$ such that $zeta(s) = 0$, $s != -2(n + 1)$ for all $n in bb(N)$, and $s != 1$, we have
       $ op("Re")(s) = 1 / 2. $
  ]

  #proof[
    We trace the proof in five completely rigorous steps, mirroring the exact structure of `MainConclusion.lean`, `ClaimStrip.lean`, and `Main.lean`.

    *Step 1: Establishing strong local-global compatibility (`RowSrc.lean`).*
    By the integral Galois representation construction for theta lifts (`galoisRepresentations_of_thetaLift` applied to `UpperTheory.TP.K.tLiftK`), we obtain the strong local-global compatibility theorem
    $ h = op("galoisLocalGlobalStrong_recParameter") : op("Row0b") (op("rec")_T), $
    which simultaneously provides Caraiani local-global duality (`caraianiLocalGlobalDual`) and the construction of $ell$-adic Galois representations attached to polarized conjugate self-dual cuspidal pairs (`galoisRepOfPolarizedPairLit`). Together with the existence of the local Langlands correspondence (`UpperTheory.Zero.LLC.recTExists`), this populates the entire bundle `OpenLiteratureStatements`.

    *Step 2: Establishing the weakened Vandiver window (`VwinOfRow.lean`).*
    Applying Theorem 16.17 (`UpperTheory.One.vwin_of_row`) to $h$ together with isobaric base change `baseChangeN` yields the unconditional weakened Vandiver window theorem
    $ h_V : op("UpperTheory.Top.VWin"). $

    *Step 3: Nonvanishing for every Dirichlet character in $op("Re")(s) > 1/2$ (`MainConclusion.lean` & `EveryCharacterOfLiteratureOfVWin.lean`).*
    We apply `every_character_of_literature_of_vWin` to the `OpenLiteratureStatements` bundle from Step 1 and the window theorem $h_V$ from Step 2. Let us recall how the machine inside `every_character_of_theta_integrals_local_matching` operates for an arbitrary modulus $N >= 1$ and Dirichlet character $chi$ modulo $N$ (reducing immediately to its primitive character $psi = chi^*$ of conductor $N_psi divides N$, since the missing Euler factors $(1 - psi(p) p^(-s))$ are nonzero for $op("Re")(s) > 0$):

    Suppose for contradiction that $L(s_0, psi) = 0$ for some $s_0 = sigma_0 + i t_0$ with $1/2 < sigma_0 < 1$ (we already know $L(s, chi) != 0$ for $op("Re")(s) >= 1$, with $s != 1$ if $chi = 1$, by Hadamard–de la Vallée Poussin and Dirichlet's theorem). Choose $epsilon in (0, 1 \/ 52)$ small enough compared to $sigma_0 - 1/2$, and choose a dyadic layer function $e(x)$ satisfying `PageN eps x (e x)` by Lemma 16.5 (`exists_pageN`). By Step 2 (`VWin`), there exist $J >= 1$ and $X_0$ such that for all arbitrarily large $X >= X_0$ and any prime pair $(q, d)$ satisfying `WinPair eps (X^(1/J)) q d` (which exists by Proposition 16.9), there is a window $[Y, Y^2] subset.eq [X^(1/J), X]$ on which every cyclotomic-quadratic field $E$ with `IsChiField psi (e x) q d E` satisfies
    $ op("VVle")(E, floor(x^401), exp(x^epsilon / 2)) quad (forall x in [Y, Y^2]). $
    Over this window $[Y, Y^2]$, we run the chained theta-lift engine of Chapters 12–15:
    - The analytic reduction of Chapter 11 converts the zero $s_0$ with $op("Re")(s_0) = sigma_0 > 1/2$ into an oscillation of the smoothed von Mangoldt sum $S_a (x)$ of amplitude $>> x^(sigma_0 - delta)$ on $[Y, Y^(3/2)] subset.eq [Y, Y^2]$.
    - The iterated theta-lift chain $U(X_0) -> U(X_1) -> dots.c -> U(X_m)$ of length $m approx sqrt(Y)$ (Chapter 12), glued integrally across Hecke characters and paired via seesaw duality and the relative trace formula (Chapter 13), produces a global arithmetic section whose local $p$-adic divisibility at inert primes (Chapter 14) forces a large negative contribution to the Arakelov degree.
    - The Arakelov geometry and Bost slope inequality of Chapter 15—specifically the covolume and self-intersection estimate `topCovolSlim2_use_alt_alt` combining resolution of singularities, Poincaré–Lelong, arithmetic Hilbert–Samuel, Moriwaki bigness, toroidal compactifications, and Nef Riemann–Roch—compares this divisibility gain against the Arakelov height plus the cohomological denominator cost from $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e'))$.
    - Because the window $[Y, Y^2]$ satisfies `VVle` with upper bound $exp(x^epsilon \/ 2) = o(exp(x^epsilon))$, the cohomological denominator is strictly overwhelmed by the divisibility gain for sufficiently large $Y$. The resulting contradiction to the divisor-slope master inequality rules out the putative zero $s_0$!

    This proves `UpperTheory.FinalTheorems.everyCharacter`, which gives statement (1): `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`.

    *Step 4: From the right half-plane to the critical strip (`Claim.strip` in `ClaimStrip.lean`).*
    Let $N >= 1$, let $chi$ be any Dirichlet character modulo $N$, and suppose $L(s, chi) = 0$ with $0 < op("Re")(s) < 1$. In particular, $s != 0$ and $s != 1$. By trichotomy on real numbers, either $op("Re")(s) < 1/2$, $op("Re")(s) = 1/2$, or $op("Re")(s) > 1/2$.
    - The case $op("Re")(s) > 1/2$ is immediately impossible by Step 3 (since $s != 1$).
    - Suppose $0 < op("Re")(s) < 1/2$. Let $psi = chi^*$ be the primitive Dirichlet character modulo $M = op("cond")(chi)$ inducing $chi$. Since $s != 1$, the change-of-level identity reads
      $ L(s, chi) = L(s, psi) product_(p divides N, space p divides.not M) (1 - psi(p) p^(-s)). $
      Because $op("Re")(s) > 0$, we have $|psi(p) p^(-s)| <= p^(-op("Re")(s)) < 1$, so every Euler factor $(1 - psi(p) p^(-s))$ is nonzero. Since $L(s, chi) = 0$, we must have $L(s, psi) = 0$ (`Claim.prim_zero`).
      Next, write $L(s, psi) = Lambda(s, psi) \/ Gamma_psi (s)$, where $Gamma_psi (s) = Gamma_bb(R) (s + a_psi)$ with $a_psi in {0, 1}$ according as $psi$ is even or odd. Since $op("Re")(s) > 0$, we have $op("Re")(s + a_psi) > 0$, so $Gamma_psi (s) != 0$ (`Claim.gamma_ne_zero`), and hence the completed $L$-function vanishes: $Lambda(s, psi) = 0$.
      By the functional equation of the primitive completed $L$-function (`IsPrimitive.completedLFunction_one_sub`),
      $ Lambda(1 - s, psi^(-1)) = epsilon(psi^(-1)) dot.c Lambda(s, psi) = 0. $
      Since $op("Re")(1 - s) = 1 - op("Re")(s) > 1/2 > 0$, we have $1 - s != 0$ and $1 - s != 1$, so dividing by the nonzero gamma factor $Gamma_(psi^(-1)) (1 - s)$ yields
      $ L(1 - s, psi^(-1)) = 0 $
      (`Claim.prim_reflect`).
      Since $op("Re")(1 - s) > 1/2$ and $1 - s != 1$, this directly contradicts Step 3!
    - The only remaining possibility is $op("Re")(s) = 1/2$, proving statement (2) (`LFunction_eq_zero_re`, and its immediate restriction to primitive characters `LFunction_eq_zero_re_of_isPrimitive`).

    *Step 5: Deducing the classical Riemann Hypothesis (`Claim.zeta` in `ClaimStrip.lean`).*
    Let $s in bb(C)$ satisfy $zeta(s) = 0$, $s != 1$, and $s != -2(n + 1)$ for all $n in bb(N)$. First observe that $s != 0$, because $zeta(0) = -1/2 != 0$. We split into three cases according to $op("Re")(s)$:
    - *Case A ($0 < op("Re")(s) < 1$):* For the unique (trivial) Dirichlet character $chi_0 = 1$ modulo $1$, we have $L(s, chi_0) = zeta(s) = 0$. Applying Step 4 (`Claim.strip`) immediately yields $op("Re")(s) = 1/2$.
    - *Case B ($op("Re")(s) >= 1$):* This is impossible by the Hadamard–de la Vallée Poussin nonvanishing theorem $zeta(s) != 0$ for all $op("Re")(s) >= 1$ (`riemannZeta_ne_zero_of_one_le_re`).
    - *Case C ($op("Re")(s) <= 0$):* For $s != 0$, the completed zeta function $Lambda(s) = Gamma_bb(R)(s) zeta(s)$ satisfies $zeta(s) = Lambda(s) \/ Gamma_bb(R)(s)$, where the reciprocal $1 \/ Gamma_bb(R)(s) = pi^(s/2) \/ Gamma(s/2)$ vanishes precisely at the non-positive even integers $s = -2 n$ ($n in bb(N)$). (In Mathlib's formalization `Complex.Gammaℝ_eq_zero_iff`, this is encoded via the convention that `Gammaℝ s = 0` at its poles $s = -2 n$.) Since $s != 0$ and $s != -2(n + 1)$ for all $n in bb(N)$, we have `Gammaℝ s ≠ 0`, and therefore $zeta(s) = 0$ forces $Lambda(s) = 0$. Because $op("Re")(s) <= 0$, we have $op("Re")(1 - s) >= 1 > 0$, so $1 - s != 0$. By Riemann's functional equation $Lambda(1 - s) = Lambda(s) = 0$, we obtain
      $ zeta(1 - s) = Lambda(1 - s) / Gamma_bb(R)(1 - s) = 0 $
      with $op("Re")(1 - s) >= 1$, contradicting Hadamard–de la Vallée Poussin (`riemannZeta_ne_zero_of_one_le_re`)!

    Thus every nontrivial zero of $zeta(s)$ satisfies $op("Re")(s) = 1/2$, completing the proof of the Riemann Hypothesis and the Generalized Riemann Hypothesis.
  ]

  === The Final Fifteen Lines of `src/Main.lean`

  After seventeen million lines of Lean 4 code, 149,000 source files, ten interconnected libraries, and 167 years of human mathematical aspiration since Riemann's 1859 memoir, the entire edifice culminates in fifteen unadorned lines of machine-checked Lean 4 at the end of `src/Main.lean`.

  #lean-note(title: "The Summit: The Final 15 Lines of src/Main.lean", module: "src/Main.lean (lines 41–56)")[
    ```lean
    @[expose] public section

    theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
      UpperTheory.FinalTheorems.everyCharacter

    theorem riemannHypothesis : RiemannHypothesis :=
      Claim.zeta LFunction_ne_zero_of_half_lt_re

    theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

    theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
      Claim.strip LFunction_ne_zero_of_half_lt_re

    theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
      intro N _ χ _ s h₀ h₁ hz
      exact LFunction_eq_zero_re N χ s h₀ h₁ hz
    ```
    Running `#print axioms riemannHypothesis` and `#print axioms LFunction_eq_zero_re` returns exclusively Lean's three standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`—no `sorryAx`, no custom axioms, no unproved hypotheses.
  ]

  #remark(title: "Immediate Classical Consequences")[
    With Theorem 16.18 established unconditionally, a vast constellation of conditional theorems accumulated over the past 167 years becomes unconditional in a single stroke:
    - *Optimal prime counting (von Koch, 1901):* $pi(x) = op("Li")(x) + O(sqrt(x) log x)$ and $psi(x) = x + O(sqrt(x) (log x)^2)$.
    - *Primes in arithmetic progressions:* For every $q >= 1$ and $gcd(a, q) = 1$, $psi(x \; q, a) = x \/ phi(q) + O(sqrt(x) (log(q x))^2)$, and Linnik's least prime satisfies $p(a, q) = O(phi(q)^2 (log q)^2)$.
    - *Goldbach's weak conjecture and binary averages, Artin's primitive root conjecture (Hooley, 1967, via GRH for Kummer extensions once extended to ERH), Miller's deterministic primality test in polynomial time, and optimal bounds on character sums and least quadratic nonresidues* $n_p = O((log p)^2)$ (Ankeny, 1952).
    In Part IV, we will examine how this monumental formalization is structured, how independent proof checkers audited it, and what lies ahead for simplifying the proof and extending it to the Extended Riemann Hypothesis and automorphic $L$-functions.
  ]

  #exercises((
    [*(Monotonicity and Prime Cutoff of `VVle`)* Suppose a number field $E$ satisfies `VVle E t B` with $t >= 2$ and $B > 0$. Prove that for every prime $ell > exp(B)$ and every integer $1 <= e < t$, the Tate–Shafarevich group $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e))$ vanishes identically. Moreover, show that the total number of pairs $(ell, e)$ with $1 <= e < t$ for which $op("Ш")^1_(S_ell) (E, bb(Q)_ell \/ bb(Z)_ell (-e)) != 0$ is at most $B \/ log 2$.],
    [*(Poitou–Tate Length Formula)* Derive the length identity `VFormula` (Proposition 16.1) from the Poitou–Tate nine-term exact sequence for $M = bb(Z)_ell (e + 1)$ and its Pontryagin–Tate dual $M^* = (bb(Q)_ell \/ bb(Z)_ell)(-e)$ over a number field $E$ when $ell != 2$ or $E$ is totally imaginary. Why is the hypothesis `PTCase E l` ($ell != 2$ or $E$ totally imaginary) needed, and what archimedean term enters when $ell = 2$ and $E$ has real places?],
    [*(Galois Structure of `IsChiField`)* Let $q equiv 3 (mod 8)$ and $d equiv 7 (mod 16)$ be distinct primes, let $e >= 1$, and let $psi$ be the trivial character ($N_psi = 1$). Explicitly determine the Galois group $op("Gal")(E \/ bb(Q))$ of a field $E$ satisfying `IsChiField psi e q d E`, verify that $[E : bb(Q)] = 2^(e+2)$, and prove that $E$ is a CM field whose maximal totally real subfield is $E^+ = bb(Q)(zeta_(2^(e+2)))^+ (sqrt(q d))$.],
    [*(Splitting of Small Primes in `WinPair`)* Let $(q, d)$ satisfy `WinPair eps Y q d`. Using quadratic reciprocity, prove that:
      (a) the prime $2$ splits in $bb(Q)(sqrt(-d))$ and is inert in $bb(Q)(sqrt(-q))$;
      (b) every odd prime $p <= Y^(epsilon \/ 5)$ splits in $bb(Q)(sqrt(-d))$;
      (c) $(d \/ q) = -1$ and $(q \/ d) = +1$.
      Verify that the same splitting properties hold for the quadratic extension $E \/ E^+$ whenever $E$ satisfies `IsChiField 1 e q d E`.],
    [*(Effective Construction of `WinPair`)* Fill in Step 4 of the proof of Proposition 16.9 using *only* the least-prime form of Linnik's theorem (that there exists an absolute constant $L_0 >= 1$ such that every coprime progression $a (mod M)$ contains a prime $d <= M^(L_0)$) together with Chebyshev's bounds on $theta(x)$. (*Hint:* Multiply $M$ by an auxiliary prime $r$ of logarithmic size $approx W \/ (2 L_0)$ and impose $d equiv 1 (mod r)$ or $d equiv -1 (mod r)$ so that any prime $d$ in the progression automatically satisfies $d > r$, and adjust $r$ to force $d in (exp(W \/ 2), exp(W)]$.)],
    [*(Classical 3-APs vs. `NoRel T L`)* Show that `NoRel T 2` is equivalent to the assertion that $T$ contains no nontrivial $3$-term arithmetic progression $a, a + r, a + 2 r$ ($r > 0$). For $L = 3$, give an example of a $3$-element set $T subset.eq bb(N)$ that is $3$-AP-free (satisfies `NoRel T 2`) yet fails `NoRel T 3`.],
    [*(Optimality of the Behrend Exponent)* In the proof of Theorem 16.15 (`hostThickExists`), track the leading constant in the exponent $-C sqrt(log n dot.c log L)$ as $n, L -> oo$ with $log L = o(log n)$. By optimizing the choice of $S$ and $d$ asymptotically (rather than using the explicit inequalities of `ThickExists.lean`), show that the constant $C = 32$ can be improved to $C = 2 sqrt(2) + o(1)$ (matching Behrend's classical constant $2 sqrt(2)$ when $L$ is fixed).],
    [*(Sharpness of `HostThickOrbit`)* In Proposition 16.16 (`HostThickOrbit`), show that the upper bound of $2$ intersections between a length-$L$ progression ${t + i h : i_0 <= i < i_0 + L}$ and $T + u_0$ is sharp whenever $|T| >= 2$ (take $h = s_2 - s_1$). Why does the bound drop from $2$ to $1$ when $op("ord")(h) <= 4 L$?],
    [*(Functional Equation Reflection in `Claim.strip` and `Claim.zeta`)* Suppose we only knew that $L(s, psi) != 0$ for all *primitive* Dirichlet characters $psi$ and all $s$ with $op("Re")(s) > 1/2$ (and $s != 1$ for $psi = 1$). Prove directly, without using any external theorems beyond the Euler product and functional equation, that $L(s, chi) != 0$ for all *imprimitive* Dirichlet characters $chi$ and all $s$ with $op("Re")(s) > 0$ and $op("Re")(s) != 1/2$. Where does the proof fail if $op("Re")(s) = 0$? (Exhibit an explicit imprimitive character $chi$ with infinitely many zeros on the line $op("Re")(s) = 0$!)],
  ))
]
