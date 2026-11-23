// ============================================================================
// Chapter 14: Integral Structures, Local Divisibility, and the Relative Trace Formula
// ============================================================================
#import "template.typ": chapter, theorem, proposition, lemma, corollary, conjecture, definition, remark, example, proof, lean-note, insight-box, exercises, gtm-navy, gtm-accent, gtm-tint, gtm-rule

#let ch14() = [
  #chapter(
    "Integral Structures, Local Divisibility, and the Relative Trace Formula",
    short-title: "Integral Structures and Local Divisibility",
    epigraph: "The arithmetic of automorphic forms lives in the tension between two metrics: the archimedean norm, which measures oscillation in the complex plane, and the p-adic valuation, which records hidden congruence.",
    epigraph-source: "After Bost, Siegel, and Weil",
    overview: [
      In the preceding chapters, we constructed the $m$-fold iterated theta lift $op("U")(X_0) -> op("U")(X_1) -> dots.c -> op("U")(X_m)$ between totally definite unitary groups, producing automorphic forms with formal multiplicity $m approx sqrt(X)$ whose Bessel periods encode the Weil explicit-formula test functionals. To convert this algebraic multiplicity into an Arakelov-geometric contradiction via Bost's slope inequality, we must control both the *archimedean sizes* and the *$p$-adic integrality* of the lifted forms with extraordinary precision. This chapter develops the five interlocking analytic and arithmetic engines that govern the local-to-global inequality: (1) the norms, levels, and cancellation of order-$m$ terms via the Chowla–Selberg formula, Weyl branching (`GradedWeylDivisibility`), and the Siegel–Weil mass formula (`SiegelWeilStd`, `DoubleCosetMeasures`); (2) lower bounds on $p$-adic divisibility of the $m$-fold iterated lift at inert primes, producing the arithmetic gain $2 F_0$ in `DivIneqObjU`; (3) gluing a global $cal(O)_K$-lattice $R$ across a family of Hecke characters to achieve an effective "greatest common divisor" averaging; (4) the relative trace formula and projected Poincaré series norm estimates establishing approximate orthogonality of the columns of $R$; and (5) covolume estimates (`TopCovolSlim2Use`, `CovolumeBoundOfX`), theta series indices (`LatticeIndexTer`), and congruences between theta lifts and eigenforms (`WeightCongruences`, `BoundAtTwoThreeFamilyFon`).
    ],
    label-name: "ch-local-divisibility-integral",
  )

  == Norms, Levels, and Cancellation of Order-$m$ Terms

  When one iterates the theta correspondence $m$ times along a chain of totally definite unitary groups
  $ op("U")(X_0) -> op("U")(X_1) -> dots.c -> op("U")(X_m), quad pi |-> pi plus.square mu_j [t], $
  where $m$ grows like $sqrt(X)$ with the length $X$ of the von Mangoldt sum, an immediate analytic danger arises. Each step of the theta lift introduces archimedean Gamma factors, combinatorial factorial weights from the polynomial Fock model, and volume factors from the local-global Tamagawa measures. If these archimedean and combinatorial factors accumulated unchecked with a positive coefficient of order $m$ in the logarithm of the height, they would completely swamp the $p$-adic divisibility gain coming from inert primes and render the final slope inequality vacuous.

  The first fundamental miracle of the Alpöge–Claude architecture is that the *order-$m$ archimedean and factorial terms cancel exactly* against the corresponding CM periods and Weyl branching norms, leaving only controlled lower-order errors. Three classical pillars—recast into a unified quantitative framework—orchestrate this cancellation: the Chowla–Selberg period formula, graded Weyl branching in the polynomial Fock space, and the Siegel–Weil mass formula expressed through double coset measures.

  === The Chowla–Selberg Period Normalization

  Let $K$ be a CM number field with totally real subfield $K_0$ of degree $d_0 = [K_0 : bb(Q)]$, and let $Phi$ be a CM type of $K$. For an abelian variety $A$ of dimension $g$ with complex multiplication by $cal(O)_K$ and CM type $Phi$, the de Rham cohomology $H^1_"dR" (A / overline(bb(Q)))$ carries a canonical decomposition into one-dimensional eigenspaces indexed by the embeddings $tau : K arrow.r.hook bb(C)$. At each $tau in Phi$, comparing an $cal(O)_K$-integral invariant differential $omega_tau in H^0 (A, Omega^1_A)$ with a Betti homology cycle $gamma_tau in H_1 (A(bb(C)), bb(Z))$ yields the CM period
  $ Omega_tau = integral_(gamma_tau) omega_tau in bb(C)^times, $
  well-defined up to multiplication by algebraic units (and globally up to $cal(O)_K^times$ once a Néron model over $cal(O)_K$ is fixed).

  In the iterated theta lift, the archimedean Weil representation acts on the holomorphic Fock space of polynomials on the tangent space at the CM point. Taking $a$-th covariant derivatives along the invariant derivation $D_tau$ multiplies a normalized theta function by $Omega_tau^a$ in the transcendental comparison between the algebraic (Betti/de Rham) lattice and the analytic (Petersson/$L^2$) metric. To keep track of the logarithmic height across $m$ steps, one needs the exact archimedean size of $log |Omega_tau|$.

  #theorem(title: "Chowla–Selberg Formula for CM Periods")[
    Let $K$ be an imaginary quadratic field of discriminant $-D_K < 0$ and Kronecker character $chi_K = (-D_K / dot.c)$, and let $E$ be an elliptic curve with complex multiplication by $cal(O)_K$ defined over the Hilbert class field $H_K$, with fundamental period $Omega_E$. Then, up to a nonzero algebraic number whose height is $O(log D_K)$,
    $ |Omega_E| approx (2 pi)^(-1/2) product_(a = 1)^(D_K - 1) Gamma(a / D_K)^(w_K chi_K (a) / (4 h_K)), $
    where $w_K = |cal(O)_K^times|$ and $h_K$ is the class number of $K$. Equivalently, by Lerch's identity relating the logarithmic derivative of $L(s, chi_K)$ at $s = 0$ to Gamma values,
    $ log |Omega_E| = -1/2 log(2 pi) - 1/4 log D_K - 1/2 (L'(0, chi_K)) / (L(0, chi_K)) + O(1). $
    More generally, for a CM field $K / K_0$ with CM type $Phi$ and a Colmez-normalized CM abelian variety $A$, the Faltings height $h_F (A)$ and the averaged logarithmic periods $log |Omega_tau|$ satisfy Colmez's formula
    $ h_F (A) &= - sum_(tau in Phi) log |Omega_tau| + 1/2 log |op("disc")(K_0)| + O(d_0) \
      &= -1/2 (L'(0, chi_(K / K_0))) / (L(0, chi_(K / K_0))) - 1/4 log(N_(K_0 / bb(Q))(frak(d)_(K / K_0))) + O(d_0). $
  ]

  #proof[
    We sketch the classical derivation for imaginary quadratic $K$ via the Kronecker limit formula, as the general CM case follows by Yoshida's and Colmez's averaging over CM types. Consider the Dedekind zeta function $zeta_K (s) = zeta(s) L(s, chi_K)$. Near $s = 1$, comparing the Laurent expansion of $zeta_K (s)$ with the sum over ideal classes $[frak(a)] in op("Cl")(K)$ of the real-analytic Eisenstein series $E(tau_frak(a), s)$ gives
    $ &lim_(s -> 1) (zeta_K (s) - (2 pi h_K) / (w_K sqrt(D_K)) dot.c 1 / (s - 1)) \
      &= (2 pi h_K) / (w_K sqrt(D_K)) (2 gamma - log(2 pi) - 1/h_K sum_([frak(a)]) log(sqrt(op("Im")(tau_frak(a))) |eta(tau_frak(a))|^2)). $
    On the other hand, expanding $zeta(s) L(s, chi_K)$ at $s = 1$ using $zeta(s) = (s - 1)^(-1) + gamma + O(s - 1)$ and the functional equation $L'(1, chi_K) / L(1, chi_K) = -L'(0, chi_K) / L(0, chi_K) + log(2 pi / D_K) + gamma$ expresses the average of $log(|eta(tau_frak(a))|^2 op("Im")(tau_frak(a))^(1/2))$ directly in terms of $L'(0, chi_K) / L(0, chi_K)$. Since the discriminant modular form $Delta(tau) = (2 pi)^12 eta(tau)^24$ relates the algebraic discriminant of $E$ to $(2 pi / Omega_E)^12$, taking logarithms and invoking the Dirichlet class number formula $L(0, chi_K) = 2 h_K / w_K$ yields the stated expression for $log |Omega_E|$.
  ]

  In the Lean formalization, this period normalization enters `DivIneqObjU` through the scalar parameter `logOm` ($log Omega$). Notice how the term $-a_T (t) log Omega$ appears inside the main archimedean sum $sum_(t in T T) m (op("ph")(a_T (t)) - a_T (t) log Omega)$: every factor of $m$ multiplying $a_T (t) log Omega$ must be matched precisely against the algebraic period scaling of the $m$-fold lift so that no spurious $O(m dot.c a_T log Omega)$ discrepancy survives.

  === Graded Weyl Divisibility and the Polynomial Fock Model

  At the archimedean places, the theta lift from $op("U")(X_(j-1))$ to $op("U")(X_j)$ is realized on the holomorphic Fock space $cal(F)_(r, n) = bb(C)[x_(a, s) : 1 <= a <= r, space 1 <= s <= n]$, where the rows index the target group $op("GL")_r$ (or $op("U")(r)$) and the columns index the source group $op("GL")_n$ (or $op("U")(n)$). Under the Howe duality decomposition
  $ bb(C)[x_(a, s)] tilde.equiv plus.o.big_nu V_nu^((r)) times.o V_nu^((n)), $
  summed over partitions (dominant weights) $nu = (nu_1 >= nu_2 >= dots.c >= nu_n >= 0)$ of length at most $min(r, n)$, an automorphic form of weight $nu$ lifts to a polynomial lying in the isotypic component $V_nu^((r)) times.o V_nu^((n))$.

  Over $bb(C)$, Howe duality is purely representation-theoretic. Over $bb(Z)$ or a discrete valuation ring $cal(O)_(K, y)$, however, the integral structure of the polynomial ring $cal(O)[x_(a, s)]$ does *not* split directly into a sum of integral Weyl modules: there are nontrivial $p$-adic denominators separating the Weyl module (generated by divided powers acting on the highest-weight vector) from the dual Weyl module (the kernel of column-raising operators). Controlling these denominators—and the exact factorial norms of highest-weight vectors in the Fock inner product—is the subject of `Formalism.GradedWeylDivisibility`.

  #definition(title: "Weyl Modules, Dual Weyl Modules, and the Rational Fock Form")[
    Let $R$ be a commutative ring and $r, n >= 1$ integers with $n <= r$. Let $A_R = R[x_(a, s) : a in op("Fin") r, space s in op("Fin") n]$ be the polynomial ring in $r n$ variables, equipped with the column-weight grading $op("colW")(a, s) = e_s in bb(N)^n$ and row-weight grading $op("rowW")(a, s) = e_a in bb(N)^r$.
    1. For $l < j$ in $op("Fin") n$, the *column-addition homomorphism* $op("colAddGen")_(l, j) : A_R -> A_R [t]$ sends $x_(a, j) |-> x_(a, j) + t x_(a, l)$ and fixes $x_(a, s)$ for $s != j$. Given a dominant weight $nu : op("Fin") n -> bb(N)$ (antitone, i.e., $nu_0 >= nu_1 >= dots.c >= nu_(n-1)$), the *dual Weyl module* is
       $ op("dualWeyl")_R (r, n, nu) = A_R^((nu)) inter inter.big_(l < j) ker(op("colAddGen")_(l, j) - op("incl")), $
       where $A_R^((nu))$ is the $op("colW")$-homogeneous component of multidegree $nu$.
    2. For $a, b in op("Fin") r$ and $k in bb(N)$, the *divided-power row operator* $op("rowDiv")_(a, b, k) : A_R -> A_R$ is the coefficient of $t^k$ in the algebra homomorphism $x_(b, s) |-> x_(b, s) + t x_(a, s)$ (fixing rows $!= b$).
    3. Let $Delta_s = det(x_(p, q))_(0 <= p, q < s)$ denote the $s times s$ leading principal minor (`lpMinor`). The *highest-weight vector* of weight $nu$ is
       $ op("hw")_R (nu) = product_(s = 0)^(n - 1) Delta_(s + 1)^(nu_s - nu_(s + 1)), $
       with the convention $nu_n = 0$. The *Weyl module* $op("weyl")_R (r, n, nu)$ is the $R$-submodule of $A_R$ spanned by all iterated applications of $op("rowDiv")_(a, b, k)$ to $op("hw")_R (nu)$.
    4. Over $bb(Q)$, the *rational Fock inner product* on $A_bb(Q)$ is defined on monomials $x^m = product_(a, s) x_(a, s)^(m(a, s))$ by
       $ chevron.l f, g chevron.r_"Fock" = sum_m f_m g_m product_(a, s) m(a, s)!. $
  ]

  The rational Fock inner product is the exact algebraic shadow of the Bargmann–Fock Gaussian integral $pi^(-r n) integral_(bb(C)^(r n)) f(z) overline(g(z)) exp(-norm(z)^2) dif z$. Its two decisive properties—positive definiteness and adjointness of divided-power operators—guarantee that the rational Weyl and dual Weyl modules coincide, while pinning down the exact factorial scaling of every matrix coefficient.

  #proposition(title: "Fock Adjointness and Rational Weyl–Dual Weyl Identification")[
    Let $n <= r$ and let $nu : op("Fin") n -> bb(N)$ be antitone.
    1. The form $chevron.l dot.c, dot.c chevron.r_"Fock"$ is symmetric, bilinear, and strictly positive definite on $A_bb(Q)$.
    2. For all $a, b in op("Fin") r$, $k in bb(N)$, and $f, g in A_bb(Q)$, the divided-power operators satisfy the transpose-adjointness identity
       $ chevron.l op("rowDiv")_(a, b, k)(f), g chevron.r_"Fock" = chevron.l f, op("rowDiv")_(b, a, k)(g) chevron.r_"Fock". $
    3. Over $bb(Q)$, the Weyl module and dual Weyl module coincide:
       $ op("weyl")_bb(Q) (r, n, nu) = op("dualWeyl")_bb(Q) (r, n, nu). $
    4. For any $f in op("weyl")_bb(Z) (r, n, nu)$, the Fock norm squared $chevron.l f, f chevron.r_"Fock"$ is governed by the hook-length product of the Young diagram of $nu$, and in particular the highest-weight vector satisfies
       $ chevron.l op("hw")(nu), op("hw")(nu) chevron.r_"Fock" = product_(s = 1)^n (nu_s + n - s)! / (n - s)! dot.c (op("hook factors of ") nu). $
  ]

  #proof[
    Part (1) is immediate from the definition: $chevron.l f, f chevron.r_"Fock" = sum_m f_m^2 product_(a, s) m(a, s)! > 0$ for $f != 0$.

    For Part (2), note that $op("rowDiv")_(a, b, k) = 1 / k! (sum_(s=0)^(n-1) x_(a, s) partial / (partial x_(b, s)))^k$ when $a != b$, and for $a = b$ it acts diagonally on each monomial $x^m$ by the binomial coefficient $binom(sum_s m(a, s), k)$ (which is self-adjoint since monomials are orthogonal). For $a != b$, it suffices to check the adjointness of $E_(a, b) = sum_s x_(a, s) partial / (partial x_(b, s))$ with $E_(b, a) = sum_s x_(b, s) partial / (partial x_(a, s))$ on monomials $x^m, x^(m')$. For a single coordinate $s$, $x_(a, s) partial / (partial x_(b, s))$ maps $x_(a, s)^p x_(b, s)^q$ to $q x_(a, s)^(p+1) x_(b, s)^(q-1)$, whose Fock pairing with $x_(a, s)^(p+1) x_(b, s)^(q-1)$ is
    $ q (p + 1)! (q - 1)! = (p + 1) p! q!, $
    which equals the Fock pairing of $x_(a, s)^p x_(b, s)^q$ with $(p + 1) x_(a, s)^p x_(b, s)^q = E_(b, a) (x_(a, s)^(p+1) x_(b, s)^(q-1))$. Summing over $s$ and iterating $k$ times (dividing by $k!$) yields $chevron.l op("rowDiv")_(a, b, k)(f), g chevron.r_"Fock" = chevron.l f, op("rowDiv")_(b, a, k)(g) chevron.r_"Fock"$.

    For Part (3), first observe that column operations commute with row operations, so $op("hw")_bb(Q) (nu) in op("dualWeyl")_bb(Q) (r, n, nu)$ and $op("dualWeyl")_bb(Q) (r, n, nu)$ is closed under all $op("rowDiv")_(a, b, k)$ (`RowDivClosed`). Hence $M = op("weyl")_bb(Q) (r, n, nu) subset.eq op("dualWeyl")_bb(Q) (r, n, nu)$. Let $M^perp$ be the orthogonal complement of $M$ inside $op("dualWeyl")_bb(Q) (r, n, nu)$ with respect to $chevron.l dot.c, dot.c chevron.r_"Fock"$. By Part (2), $M^perp$ is also closed under all $op("rowDiv")_(a, b, k)$. If $M^perp != 0$, then since $M^perp$ is finite-dimensional and graded by row weights (`RowDivClosedGraded`), it must contain a nonzero vector $f$ annihilated by all raising operators $op("rowDiv")_(a, b, k)$ with $a < b$ and $k >= 1$. By the uniqueness of the highest-weight line in $op("dualWeyl")_bb(Q) (r, n, nu)$ (`HWLine`), $f = c dot.c op("hw")_bb(Q) (nu)$ for some $c != 0$, contradicting $op("hw")_bb(Q) (nu) in M$ and $M inter M^perp = {0}$. Thus $M^perp = 0$ and $op("weyl")_bb(Q) = op("dualWeyl")_bb(Q)$.

    Part (4) follows from the classical Capelli identity / hook-length formula for Schur polynomials in the Bargmann–Fock metric: the norm squared of a bideterminant of shape $nu$ is proportional to $product_((i, j) in nu) h(i, j)$ times the factorial column shifts, where $h(i, j)$ is the hook length of box $(i, j)$ in the Young diagram of $nu$.
  ]

  The significance of Part (4) for the cancellation of order-$m$ terms is immediate. Define the Stirling-normalized log-factorial function
  $ op("ph")(u) = u log u - u quad (u > 0), quad op("ph")(0) = 0. $
  When an automorphic form on $op("U")(X_j)$ of highest weight $nu = (nu_1, dots.c, nu_(n_r))$ is lifted through $m$ stages, the archimedean Fock norm contributes $sum_i log(nu_i!) approx sum_i op("ph")(nu_i)$, while the hook-length denominators contribute $-log H_j (rho)$ (the log-hook product of the partition $nu(j, rho)$ at the archimedean place $rho$). Under Weyl branching along the chain $op("U")(X_0) -> dots.c -> op("U")(X_m)$, the interlacing of weights forces the difference
  $ &sum_i op("ph")(nu(j, rho, i)) - log H_j (rho) \
    &quad <= cases(op("ph")(a_T (rho)) + e_E (j, rho) & "if " rho in T T, e_E (j, rho) & "if " rho in.not T T), $
  where the error $e_E (j, rho) = O((w(j, rho) + S + N^2 + m (t_t + 1) eta) L_a)$ is strictly lower order than the main term $a_T (rho) log a_T (rho)$!

  === Siegel–Weil Formula and Double Coset Measures

  While Chowla–Selberg and Weyl branching control the archimedean periods and combinatorial norms, the *level* and *global $L^2$-norm* of the theta lift are controlled by the Rallis inner product formula and the Siegel–Weil formula. For a dual reductive pair $(op("U")(V), op("U")(W))$ with $V$ totally definite of dimension $n_V$ and $W$ skew-Hermitian, the Siegel–Weil formula identifies the theta integral of a Schwartz–Bruhat function $Phi in cal(S)(V(bb(A)_K)^m)$ over the compact adelic quotient $[op("U")(V)] = op("U")(V)(K_0) backslash op("U")(V)(bb(A)_(K_0))$ with a special value (or residue) of a Siegel Eisenstein series:
  $ integral_([op("U")(V)]) Theta(g, h ";" Phi) dif h = kappa_(V, W) dot.c E(g, s_0 ";" Phi). $

  Because $op("U")(V)$ is totally definite, the adelic quotient $op("U")(V)(K_0) backslash op("U")(V)(bb(A)_(K_0, f)) / K_f$ for an open compact subgroup $K_f subset op("U")(V)(bb(A)_(K_0, f))$ is a *finite set* of double cosets representing the genus of a Hermitian $cal(O)_K$-lattice $Lambda subset V$. The Haar integral over $[op("U")(V)]$ collapses to a finite weighted sum:
  $ integral_([op("U")(V)]) F(h) dif h = sum_(i = 1)^h (op("vol")(K_f)) / (|op("Aut")(Lambda_i)|) F(h_i), $
  and for $F equiv 1$ this is the *Siegel mass formula*:
  $ op("Mass")(op("gen")(Lambda)) = sum_(i = 1)^h 1 / (|op("Aut")(Lambda_i)|) = 2 dot.c product_v alpha_v (Lambda)^(-1), $
  where $alpha_v (Lambda)$ are the local representation densities (local Tamagawa factors).

  In `Formalism.DoubleCosetMeasures`, this conversion of adelic integrals into finite double-coset sums and its interaction with unipotent orbits and lattice cokernels is formalized in complete generality.

  #proposition(title: "Two-Sided Double Coset Integration and Relative Index Scaling")[
    Let $G_1, G_2$ be locally compact Hausdorff topological groups with right-invariant Haar measure $mu_1$ on $G_1$ and left-invariant Haar measure $mu_2$ on $G_2$, and let $K_1 subset G_1$, $K_2 subset G_2$ be open compact subgroups. Let $E$ be a Banach space and $f : G_1 times G_2 -> E$ a compactly supported function that is $K_1$-left-invariant in the first variable and $K_2$-right-invariant in the second:
    $ f(a x, y b) = f(x, y) quad (forall a in K_1, space b in K_2, space x in G_1, space y in G_2). $
    Then the induced function on $(K_1 backslash G_1) times (G_2 / K_2)$ has finite support, and
    $ integral_(G_1 times G_2) f(x, y) dif(mu_1 times mu_2) = sum_([x] in K_1 backslash G_1) sum_([y] in G_2 / K_2) mu_1 (K_1) mu_2 (K_2) f(x, y). $
    Furthermore, when $G_1, G_2$ are local unipotent/parabolic subgroups over a non-archimedean local field $F$ with ring of integers $cal(O)_F$, the measure of the integral unipotent double coset associated to a matrix $Z in M_n (F)$ scales inversely with the cardinality of the cokernel $op("coker")(Z) = cal(O)_F^n / (cal(O)_F^n inter Z cal(O)_F^n)$, matching the local representation density in the Siegel–Weil formula.
  ]

  #proof[
    Since $K_1$ and $K_2$ are open, the quotient spaces $K_1 backslash G_1$ and $G_2 / K_2$ are discrete, and the projection $pi : G_1 times G_2 -> (K_1 backslash G_1) times (G_2 / K_2)$ is a continuous open map. Because $f$ is $(K_1, K_2)$-bi-invariant, its support is a union of cosets $K_1 x times y K_2$. Compactness of $op("supp")(f)$ implies that $pi(op("supp")(f))$ is compact in a discrete space, hence finite. Decomposing the integral as a finite sum over the cosets in $pi(op("supp")(f))$, each coset $K_1 x times y K_2$ has product measure $mu_1 (K_1 x) mu_2 (y K_2) = mu_1 (K_1) mu_2 (K_2)$ by right-invariance of $mu_1$ and left-invariance of $mu_2$. The local scaling for unipotent orbits follows from the change-of-variables formula on $F^n$ and the elementary divisor theorem for $Z$ over the discrete valuation ring $cal(O)_F$.
  ]

  #theorem(title: "Cancellation of Order-m Terms in the Iterated Theta Lift")[
    Let $pi_0$ be a level-$N_0$ automorphic representation on $op("U")(X_0)$, and let $pi_m = theta_(X_(m-1), X_m) dots.c theta_(X_0, X_1) (pi_0)$ be its $m$-fold iterated theta lift along the chain $op("U")(X_0) -> dots.c -> op("U")(X_m)$ with Hecke characters $mu_1, dots.c, mu_m$. Suppose that at each step:
    1. the archimedean Fock polynomials are normalized by the CM period powers $Omega_tau^(a_T (tau))$ via the Chowla–Selberg formula;
    2. the local Schwartz functions are chosen to be standard spherical/level-adapted functions whose inner products are evaluated by the Siegel–Weil formula (`SiegelWeilStd`).
    Then in the global Arakelov height $h_u$ of the lifted family, the $O(m)$-multiples of the intermediate level logarithms and intermediate Weyl-dimension factors cancel identically between the numerator (Fock norm + Chowla–Selberg period) and the denominator (hook-length product + Siegel mass covolume), yielding
    $ &h_u = - sum_(t in T T) a_T (t) log T \
      &quad + sum_(j = 1)^m sum_rho (sum_i op("ph")(nu(j, rho, i)) - log H_j (rho) \
      &quad quad - (sum_i nu(j, rho, i)) log Omega) + O(m f N^2 (L_a + m^3 L)). $
  ]

  #proof[
    At each stage $j in {1, dots.c, m}$, the $L^2$-norm squared of the $j$-th theta lift is given by the Rallis inner product formula (proved via the doubling method and `SiegelWeilStd`) as a product of the central $L$-value $L(1/2, pi_(j-1) times mu_j)$ and local zeta integrals $Z_v (Phi_v, f_v)$. Taking logarithms separates the global period into three pieces: the archimedean Fock norm $sum_i op("ph")(nu(j, rho, i)) - log H_j (rho)$ (from Proposition 14.3), the CM period contribution $-(sum_i nu(j, rho, i)) log Omega$ (from Theorem 14.1), and the finite-place volume/level ratio (from Proposition 14.4). Because the local doubling zeta integral at every unramified place equals the reciprocal of the local Siegel–Weil mass density, the finite-place Tamagawa factors telescope across $j = 1, dots.c, m$, leaving only the ramified-place contribution $-sum_(t in T T) a_T (t) log T$ and the polynomial error $O(m f N^2 (L_a + m^3 L))$.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Weyl Branching, Siegel–Weil, and Double Coset Measures",
    module: "Formalism.GradedWeylDivisibility, PositivityTheory.SiegelWeilFormula, Formalism.DoubleCosetMeasures",
  )[
    - `Formalism.GradedWeylDivisibility.StatementA` and `StatementB` define `dualWeyl`, `weyl`, `hw`, `lpMinor`, `rowDiv`, and the rational Fock form `fockQ`, proving `FockQPos`, `FockQRowDivAdj`, `HWLine`, and `WeylEqNablaQ` (`weyl ℚ r n hn ν = dualWeyl ℚ r n ν`).
    - `PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd` (in `SiegelWeilStd.lean`) establishes the standard Siegel–Weil identity `SiegelWeilStd` from the constant-term splitting `ctSplit_of`.
    - `Formalism.DoubleCosetMeasures.Statement` defines `IntTwoSided`, `IsLowUni`, `IsUpUni`, `coker`, and `RelIndexMulMeasure` to bridge Haar integrals on adelic groups to finite double-coset sums.
  ]

  == Lower Bounds on $p$-Adic Divisibility of the $m$-Fold Iterated Lift

  Having tamed the archimedean growth and forced the order-$m$ nuisance terms to cancel, we now harvest the arithmetic engine of the entire proof: the *lower bound on $p$-adic divisibility* of the $m$-fold iterated theta lift at inert primes (`remark.pdf` item 10).

  Recall from Chapter 8 the phenomenon on a single CM elliptic curve $E / cal(O)_K$: for a rational prime $p$ that is *inert* in $K$, the reduction $E mod p$ is supersingular, so the Hasse invariant vanishes and the invariant derivation $D$ satisfies
  $ D^p equiv 0 mod p. $
  Iterating this congruence on the theta function $theta$ of $E$ shows that the normalized algebraic Taylor coefficient $D^a theta(0) / Omega^a$ is divisible by a massive power of $p$:
  $ v_p ((D^a theta(0)) / Omega^a) &>= floor(a / p) + floor(a / p^3) + floor(a / p^5) + dots.c - O(log a) \
    &= a / (p - 1/p) - O(log a) = (p a) / (p^2 - 1) - O(log a). $
  Notice the crucial difference between inert primes and split primes: at a split prime $p = frak(p) overline(frak(p))$, $E mod frak(p)$ is ordinary, the formal group is multiplicative ($hat(bb(G))_m$), and $D^p equiv D mod p$ gives *no* extra divisibility beyond the ordinary factorial $a!$. At an inert prime $p$, the formal group has height $2$, $D^p equiv 0 mod p$, and every $p$-th differentiation gains an extra factor of $p$ on top of what the archimedean factorial predicts!

  === Extending Inert-Prime Divisibility to the $m$-Fold Iterated Lift

  How does this single-curve phenomenon propagate through an $m$-fold chain of theta lifts $op("U")(X_0) -> op("U")(X_1) -> dots.c -> op("U")(X_m)$? At each step $j in J$ (with $|J| = m$), the theta kernel is built from a Hermitian lattice $M_j subset K^D$ and a family of local lattices $T_l (j, t) subset K^D$ indexed by the Hecke-character tuple $t in "Tup"$, linked by invertible transition matrices $theta_j (t) in op("GL")_D (K)$ and rational Hermitian forms $H_T (j, t) in M_D (K)$.

  Let $T_w subset.eq S_y$ be the finite set of height-one primes $y in op("Spec")_(h=1)(cal(O)_K)$ that are inert (or lie above inert rational primes) in the active divisibility window. For each $y in op("Spec")_(h=1)(cal(O)_K)$, let:
  - $overline(y) = op("conjPl")(y)$ denote the complex-conjugate prime under the CM involution of $K$;
  - $l_w (y) = (log N(y)) / [K : bb(Q)]$ denote the normalized logarithmic weight of the place $y$;
  - $op("ramw")(y) in bb(N)_(>= 1)$ denote the ramification/inert-degree multiplicity weight at $y$;
  - $op("idx")_y (A, B) in bb(Z)$ denote the signed relative index of two full $cal(O)_(K, y)$-lattices $A, B subset K_y^D$ (formally defined in Section 14.5 via DVR module length, so that $op("idx")_y (A, B) = v_y (det(g))$ when $B = g A$);
  - $j_w (H, y, L) in bb(Z)$ denote the local $y$-adic valuation of the Gram determinant of a Hermitian matrix $H$ on a lattice $L$ at the place $y$.

  In the $m$-fold lift, the supersingular vanishing $D^p equiv 0$ at an inert prime $y in T_w$ acts independently at each of the $m$ links of the chain, because the $j$-th theta kernel pulls back the invariant differential operators on the $j$-th CM factor $E_j$ to the $j$-th block of the lifted automorphic form. However, the local lattices $M_j$ and $theta_j (mu(y)) T_l (j, mu(y))$ do not coincide on the nose: their relative index measures precisely how much *extra $y$-adic divisibility* the lifted lattice $theta_j (mu(y)) T_l (j, mu(y))$ possesses inside the ambient integral lattice $M_j$.

  #definition(title: "Local Divisibility Gain and Defect Decomposition at Inert Primes")[
    For each $y in T_w$ and $j in J$, let $F_0 (y, j) >= 0$ be the *principal inert-prime divisibility gain* per dimension $D$ at the $j$-th link and place $y$ (coming from the supersingular height-$2$ congruence $D^p equiv 0$ on the CM factor). Let $v_(U, 0) (y) >= 0$ denote the local unramified/unit defect, $r_0 (y, j)$ the ramified-tail defect, $d_K (j)$ the discriminant-conductor parameter, $delta_q > 0$ the truncation parameter, and $epsilon_0 (y, j)$ the tiny higher-order truncation error. We say that the $m$-fold lift satisfies the *local index bounds at $T_w$* if for all $y in T_w$ and $j in J$:
    1. *Index bound at $y$:*
       $ &op("idx")_y (M_j, theta_j (mu(y)) T_l (j, mu(y))) \
         &quad <= op("ramw")(y) ( (e_0 (y, j) + v_(U, 0) (y)) D \
         &quad quad + (r_0 (y, j) + d_K (j) v_(U, 0) (y)) / delta_q + epsilon_0 (y, j) ), $
       and symmetrically at the conjugate prime $overline(y) = op("conjPl")(y)$:
       $ &op("idx")_(overline(y)) (M_j, theta_j (mu(y)) T_l (j, mu(y))) \
         &quad <= op("ramw")(overline(y)) ( (e_0 (overline(y), j) + v_(U, 0) (overline(y))) D \
         &quad quad + (r_0 (overline(y), j) + d_K (j) v_(U, 0) (overline(y))) / delta_q + epsilon_0 (overline(y), j) ). $
    2. *Conjugate-pair gain identity:* writing $g_q (y) >= 4 v_(U, 0) (y)$ for the local Gram-defect budget,
       $ e_0 (y, j) + e_0 (overline(y), j) - 2 F_0 (y, j) + 2 g_q (y) <= op("errl")(y, j). $
    3. *Hermitian Gram valuation bound:*
       $ j_w (H_T (j, mu(y)), y, T_l (j, mu(y))) <= J_y (j) D + eta_y (j). $
  ]

  Observe the sign convention carefully! In `Formalism.DivisorInequality`, the index $op("idx")_y (M_j, theta_j (mu(y)) T_l (j, mu(y)))$ is *negative* when $theta_j (mu(y)) T_l (j, mu(y))$ is deeply divisible inside $M_j$ (or equivalently, $e_0 (y, j) < 0$ carries the negative contribution $-F_0 (y, j)$ when $F_0 (y, j) > 0$, since $e_0 (y, j) + e_0 (overline(y), j) <= 2 F_0 (y, j) + op("errl")(y, j) - 2 g_q (y)$ with $F_0$ oriented as a positive gain subtracted on the left-hand side of the final inequality). Let us trace the exact algebra that turns these local inequalities into the global arithmetic gain $2 F_0$.

  #lemma(title: "Summing the Paired Local Index Bounds Over Inert Primes")[
    Assume the local index bounds of Definition 14.6 hold for all $y in T_w$ and $j in J$, together with the symmetry $op("ramw")(overline(y)) = op("ramw")(y)$, $v_(U, 0) (overline(y)) = v_(U, 0) (y)$, and the global error budgets:
    - $d_K (j) / delta_q <= 3 D$ for all $j in J$;
    - $sum_(j in J) (epsilon_0 (y, j) + epsilon_0 (overline(y), j)) <= 2 / (op("plc")(y))^2$ for all $y in T_w$;
    - $sum_(y in T_w) l_w (y) op("ramw")(y) op("errl")(y, j) <= E_A (j)$ and $sum_(y in T_w) l_w (y) op("ramw")(y) r_0 (y, j) <= R_b (j)$;
    - $sum_(y in T_w) l_w (y) J_y (j) <= E_J (j)$ and $sum_(y in T_w) l_w (y) eta_y (j) / D <= E_2 (j)$.
    Then, summing over $j in J$ and $y in T_w$ and dividing by $D$, the total finite-place index and Hermitian Gram contribution satisfies
    $ &1 / D sum_(y in T_w) l_w (y) sum_(j in J) (op("idx")_y (M_j, theta_j (mu(y)) T_l (j, mu(y))) \
      &quad + op("idx")_(overline(y)) (M_j, theta_j (mu(y)) T_l (j, mu(y))) \
      &quad + j_w (H_T (j, mu(y)), y, T_l (j, mu(y)))) $
    $ &<= 2 F_0 + sum_(j in J) (E_A (j) + (2 R_b (j)) / (delta_q D) + E_J (j) + E_2 (j)) \
      &quad + sum_(y in T_w) (2 l_w (y) op("ramw")(y)) / (D dot.c op("plc")(y)^2), $
    where the *total arithmetic divisibility gain* is
    $ 2 F_0 = 2 sum_(j in J) sum_(y in T_w) l_w (y) op("ramw")(y) F_0 (y, j). $
  ]

  #proof[
    Fix $y in T_w$ and $j in J$. Adding the local index bounds at $y$ and $overline(y)$ and using $op("ramw")(overline(y)) = op("ramw")(y)$ and $v_(U, 0) (overline(y)) = v_(U, 0) (y)$ gives
    $ &op("idx")_y + op("idx")_(overline(y)) <= op("ramw")(y) [ (e_0 (y, j) + e_0 (overline(y), j) + 2 v_(U, 0) (y)) D \
      &quad + (r_0 (y, j) + r_0 (overline(y), j) + 2 d_K (j) v_(U, 0) (y)) / delta_q + epsilon_0 (y, j) + epsilon_0 (overline(y), j) ]. $
    By the hypothesis $d_K (j) / delta_q <= 3 D$, the coefficient of $v_(U, 0) (y) D$ inside the bracket is bounded by
    $ 2 v_(U, 0) (y) D + 2 (d_K (j) / delta_q) v_(U, 0) (y) &<= 2 v_(U, 0) (y) D + 6 v_(U, 0) (y) D \
      &= 8 v_(U, 0) (y) D <= 2 g_q (y) D, $
    where the last inequality uses $4 v_(U, 0) (y) <= g_q (y)$. Substituting the conjugate-pair gain inequality $e_0 (y, j) + e_0 (overline(y), j) + 2 g_q (y) <= 2 F_0 (y, j) + op("errl")(y, j)$, we obtain
    $ op("idx")_y + op("idx")_(overline(y)) &<= op("ramw")(y) [ (2 F_0 (y, j) + op("errl")(y, j)) D \
      &quad + (r_0 (y, j) + r_0 (overline(y), j)) / delta_q + epsilon_0 (y, j) + epsilon_0 (overline(y), j) ]. $
    Now add the Hermitian Gram bound $j_w (H_T (j, mu(y)), y, T_l (j, mu(y))) <= J_y (j) D + eta_y (j)$, divide by $D$, multiply by $l_w (y)$, and sum over $j in J$ and $y in T_w$. The first term yields precisely $2 sum_j sum_(y in T_w) l_w (y) op("ramw")(y) F_0 (y, j) = 2 F_0$. The remaining terms are bounded individually by $E_A (j)$, $2 R_b (j) / (delta_q D)$ (using $l_w (overline(y)) = l_w (y)$ on the conjugate sum), $E_J (j)$, $E_2 (j)$, and the $op("plc")(y)^(-2)$ tail.
  ]

  When this finite-place divisibility bound is combined with the Arakelov slope comparison for the glued lattice $R$ (Section 14.3) and the archimedean height $h_u$ (Section 14.1), the sign flips upon passing to the dual lattice `dualLat R`, placing $-2 F_0$ on the *left-hand side* of the master divisor inequality `DivIneqObjU`:

  #theorem(title: "Master Divisor Inequality with Inert-Prime Gain (DivIneqObjU)")[
    Under the local index bounds of Definition 14.6, the Gram-determinant bound $L_G$ of Section 14.4, the covolume and slope transfer bounds of Section 14.5, and the parameter regime $b = exp(x^epsilon)$, $a = x b$, $B_0 = f m b x^epsilon$, the cusp-normalized slope $mu_C$, archimedean height $h_u$, and total inert-prime divisibility gain $F_0 = sum_(j in J) sum_(y in T_w) l_w (y) op("ramw")(y) F_0 (y, j)$ satisfy
    $ &mu_C + h_u - 2 F_0 \
      &<= sum_(t in T T) (m (op("ph")(a_T (t)) - a_T (t) log Omega) - a_T (t) log T) \
      &quad + (50 C_0 + 10) (|T T| dot.c a L_a + c_e m (x^epsilon B_0 + (log x)^2 N_c)). $
  ]

  #insight-box(title: "Why the Factor of 2 in 2 F_0 Breaks the 2/3 Barrier")[
    In `remark.pdf` item 14, Alpöge notes that a naive computation of the "cost" of each theta lift would halt at a zero-free / density threshold of $2/3$ rather than reaching $1/2$. Why does the factor $2 F_0$ in `DivIneqObjU` overcome this barrier? First, because $K$ is a CM field and the gluing map satisfies $mu(overline(y)) = mu(y)$, every inert prime $y in T_w$ contributes *both* $op("idx")_y$ and $op("idx")_(overline(y))$ (the conjugate-pair symmetry), doubling the single-place divisibility gain $F_0 (y, j)$ to $2 F_0 (y, j)$. Second, $F_0$ is summed over all $m = |J|$ links of the theta chain, so $2 F_0$ scales *linearly with $m$*, matching the $m dot.c op("ph")(a_T (t))$ scaling of the main term while the error $O(m (x^epsilon B_0 + (log x)^2 N_c))$ stays strictly sub-leading as $m approx sqrt(X)$ grows.
  ]

  #lean-note(
    title: "Lean 4 Formalization: DivIneqObjU and BoundsMu",
    module: "Formalism.DivisorInequality.DivIneqTopAnchorU, Formalism.DivisorInequality.StatementObj",
  )[
    The master inequality of Theorem 14.8 is formalized verbatim as `Formalism.DivisorInequality.DivIneqObjU` in `DivIneqTopAnchorU.lean`, built on top of the abstract lattice-slope inequality `BoundsMu` in `StatementObj.lean`. In `DivIneqObjU`, the total divisibility gain is defined by
    `Fo = ∑ j, ∑ y ∈ Tw, lw y * ((ramw y : ℝ) * F0 y j)`
    and appears in the conclusion as
    `muC + hu - 2 * Fo ≤ ∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT) + ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10) * ce * (m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc)))`.
  ]

  == Gluing an Integral Structure Across Hecke Characters ("GCD" Averaging)

  A subtle arithmetic obstruction threatens the application of Theorem 14.8 if one works with a *single* tuple of Hecke characters $mu_0 = (mu_(0, 1), dots.c, mu_(0, m))$. For any fixed choice of Hecke characters $mu_0$, the associated $m$-fold theta lift produces a full $cal(O)_K$-lattice $iota(mu_0) "abelian"_2 (mu_0) subset K^D$, whose archimedean metric is encoded by a matrix $X_Q (mu_0)$ and whose local Gram determinant at a height-one prime $y$ is $G_m (mu_0, y)$.

  Unfortunately, a single character tuple $mu_0$ inevitably suffers from *spurious prime factors*:
  - primes $y$ dividing the conductor of $mu_0$, where the local Bessel/theta integral degenerates;
  - primes $y$ dividing the special $L$-values $L(1/2, pi_(j-1) times mu_(0, j))$ (so-called *congruence primes* or accidental $p$-adic zeros of the central $L$-value), which inflate the denominator of the period ratio and artificially degrade the local index $op("idx")_y$;
  - primes $y$ where the local lattice $iota(mu_0) "abelian"_2 (mu_0)$ fails to be unimodular with respect to the quotient Hermitian form $H_m$.

  If we were forced to use a single global tuple $mu_0$ at *every* finite place $y$, these spurious primes would accumulate in the error term $L_G = sum_(y in S_y) l_w (y) g_y (y)$ and destroy the inequality!

  The conceptual breakthrough of `remark.pdf` item 15 is to stop asking for a single character tuple $mu_0$ that behaves well at *all* primes simultaneously. Instead, we consider a *family* of character tuples $t in "Tup"$, and at each height-one prime $y in op("Spec")_(h=1)(cal(O)_K)$ we *choose the best tuple* $mu(y) in "Tup"$ for that prime—and then *glue* the resulting local lattices $cal(O)_(K, y)$-place by $cal(O)_(K, y)$-place into a single global $cal(O)_K$-lattice $R subset K^D$!

  === Local-to-Global Gluing Over a Dedekind Domain

  Let $K$ be a number field with ring of integers $cal(O)_K$, and let $V = K^D$. For each height-one prime $y in op("Spec")_(h=1)(cal(O)_K)$, let $cal(O)_(K, y)$ be the localization of $cal(O)_K$ at $y$ (a discrete valuation ring with fraction field $K$). Given any full $cal(O)_K$-lattice $L subset V$, its localization is $L_y = cal(O)_(K, y) dot.c L = op("localization")_2 (y, L) subset V$.

  #theorem(title: "Local-Global Gluing of Integral Structures Across Hecke Characters")[
    Let `"Tup"` be an index set of Hecke-character tuples with a basepoint $mu_0 in "Tup"$, and let $mu : op("Spec")_(h=1)(cal(O)_K) -> "Tup"$ be a selection map such that:
    1. $mu(overline(y)) = mu(y)$ for every $y in op("Spec")_(h=1)(cal(O)_K)$ (conjugation symmetry);
    2. the set ${y in op("Spec")_(h=1)(cal(O)_K) : mu(y) != mu_0}$ is finite.
    For each $t in "Tup"$, let $"abelian"_2 (t) subset K^D$ be a full $cal(O)_K$-lattice and $iota(t) in op("GL")_D (K)$ an invertible matrix, and set $L_t = iota(t) "abelian"_2 (t)$. Then there exists a *unique* full $cal(O)_K$-lattice $R subset K^D$ such that for every height-one prime $y in op("Spec")_(h=1)(cal(O)_K)$,
    $ op("localization")_2 (y, R) = op("localization")_2 (y, iota(mu(y)) "abelian"_2 (mu(y))). $
    Moreover, if $R$ is equipped with the archimedean Hermitian frame $X_E$ and the basepoint $mu_0$ satisfies the determinant-ratio factorization
    $ &op("detRatio")(X_Q (t), X_E, iota(t), v_0) \
      &= (kappa(v_0) rho_r (t))^D product_(j in J) op("detRatio")(X_T (j, t), X_W (j), theta_j (t), v_0), $
    with $rho_D (t) in K$ satisfying $v_0 (rho_D (t)) = rho_r (t)^D$ and $v_w (y, rho_D (mu(y))) = 0$ for all $y$, then the Harder–Narasimhan / Bost slope `muDef` of the dual lattice `dualLat R` satisfies
    $ &op("muDef")("dualFrame"(X_E), "dualLat"(R)) \
      &<= op("meanLog")(kappa) + sum_(j in J) (op("lcv")(X_W (j), M_j)) / D \
      &quad + 1 / D sum_y l_w (y) (v_w (y, G_m (mu(y), y)) \
      &quad quad + sum_(j in J) (op("idx")_y (j) + op("idx")_(overline(y)) (j) + j_w (j))), $
    where $op("lcv")(X_W (j), M_j) / D = -op("muDef")(X_W (j), M_j)$ is the normalized log-covolume of the $j$-th factor lattice.
  ]

  #proof[
    For existence and uniqueness of $R$, define
    $ R = inter.big_(y in op("Spec")_(h=1)(cal(O)_K)) op("localization")_2 (y, L_(mu(y))) subset K^D. $
    Because $S = {y : mu(y) != mu_0}$ is finite and $L_(mu_0)$ is a full $cal(O)_K$-lattice, there exists a nonzero element $a in cal(O)_K$ (supported only at primes in $S$) such that $a L_(mu_0)_y subset.eq (L_(mu(y)))_y subset.eq a^(-1) L_(mu_0)_y$ for all $y in S$, while $(L_(mu(y)))_y = (L_(mu_0))_y$ for all $y in.not S$. Intersecting over all $y$ gives $a L_(mu_0) subset.eq R subset.eq a^(-1) L_(mu_0)$, proving that $R$ is finitely generated over the Noetherian ring $cal(O)_K$ and spans $K^D$, i.e., $R$ is a full $cal(O)_K$-lattice.

    To check that $op("localization")_2 (y_0, R) = (L_(mu(y_0)))_(y_0)$ for every fixed prime $y_0$, the inclusion $subset.eq$ is immediate from the definition of $R$. Conversely, given any $x in (L_(mu(y_0)))_(y_0)$, there are only finitely many primes $y != y_0$ for which $x in.not (L_(mu(y)))_y$. By the Chinese Remainder Theorem (weak approximation in $cal(O)_K$), we can choose $u in cal(O)_K without y_0$ such that $u x in (L_(mu(y)))_y$ for all $y != y_0$. Since $u in cal(O)_(K, y_0)^times$, we also have $u x in (L_(mu(y_0)))_(y_0)$, whence $u x in R$ and therefore $x = u^(-1) (u x) in cal(O)_(K, y_0) R = op("localization")_2 (y_0, R)$. Uniqueness follows from the fact that any $cal(O)_K$-lattice equals the intersection of its localizations at all height-one primes.

    For the slope inequality, recall that the Arakelov degree of a metrized $cal(O)_K$-lattice $(R, X_E)$ is given by the product formula as the sum of the archimedean log-determinant ratio and the finite-place relative indices against a reference lattice. At each finite place $y$, the local index of $R$ against the basepoint lattice is computed *purely locally* from $op("localization")_2 (y, R) = (L_(mu(y)))_y$, and the product formula for the nonzero scalar $rho_D (mu(y))$ (which has $v_w (y, rho_D (mu(y))) = 0$ at every finite place $y$) transfers the determinant-ratio identity at $v_0$ directly into the sum of local Gram valuations $v_w (y, G_m (mu(y), y))$, relative indices $op("idx")_y + op("idx")_(overline(y))$, and Hermitian Gram valuations $j_w$. Dividing by $D$ and applying the duality identity $op("lcv")(X_W (j), M_j) / D = -op("muDef")(X_W (j), M_j)$ yields the stated inequality (`BoundsMu`).
  ]

  #insight-box(title: "Why Local Gluing Is Literally 'GCD' Averaging")[
    Suppose we have a family of nonzero ideals $frak(a)_t subset cal(O)_K$ indexed by Hecke characters $t in "Tup"$, representing the "bad denominator" of the theta lift for character $t$. For any single $t$, $frak(a)_t$ may be divisible by unwanted primes $y$. However, if at each prime $y$ we choose $mu(y) in "Tup"$ to *minimize* the valuation $v_y (frak(a)_t)$, then the glued ideal $frak(a)_R$ whose localization at $y$ is $(frak(a)_(mu(y)))_y$ has
    $ v_y (frak(a)_R) = min_(t in "Tup") v_y (frak(a)_t) quad (forall y). $
    In ideal arithmetic, the ideal whose $y$-adic valuation at every prime $y$ is the minimum of $v_y (frak(a)_t)$ is precisely the *greatest common divisor*
    $ frak(a)_R = gcd_(t in "Tup") frak(a)_t = sum_(t in "Tup") frak(a)_t! $
    In higher rank $D > 1$, gluing the local lattices $op("localization")_2 (y, R) = op("localization")_2 (y, iota(mu(y)) "abelian"_2 (mu(y)))$ is the exact higher-dimensional analogue of taking the GCD across the family of Hecke characters. It strips away every spurious prime factor that does not divide *all* lifts in the family simultaneously—without ever needing to find a single global Hecke character that avoids every bad prime at once!
  ]

  Notice a vital requirement in Theorem 14.9: at each place $y$, the archimedean metric $X_Q (t)$ and the local lattice $"abelian"_2 (t)$ must be compared via the *same* archimedean reference frame $X_E$ and the *same* global quotient metric $H_m$ at the basepoint $mu_0$. This means that the gluing only pays off if we can uniformly bound the local Gram determinant valuation $v_w (y, G_m (mu(y), y)) <= D g_y (y)$ across the family—which requires knowing that the columns of the integral structure $R$ do not suffer destructive cancellation. That is precisely the problem solved by the relative trace formula in the next section.

  == The Relative Trace Formula, Poincaré Series, and Approximate Orthogonality

  To apply Bost's slope inequality to the glued $cal(O)_K$-lattice $R subset K^D$, we need an upper bound on the Arakelov covolume of $R$, or equivalently, a *lower bound* on the determinant of the archimedean Gram matrix
  $ G(R) = (chevron.l v_alpha, v_beta chevron.r_(X_E))_(1 <= alpha, beta <= D) $
  of an integral basis (or generating set of columns) $v_1, dots.c, v_D$ of $R$. By Hadamard's inequality,
  $ det G(R) <= product_(alpha = 1)^D norm(v_alpha)^2, $
  with equality if and only if the columns $v_1, dots.c, v_D$ are pairwise orthogonal. In the opposite direction, if the columns had large mutual inner products (near linear dependence), $det G(R)$ could be exponentially smaller than $product_alpha norm(v_alpha)^2$, blowing up $L_G = sum_(y in S_y) l_w (y) g_y (y)$ and destroying `DivIneqObjU`.

  In `remark.pdf` item 16, Alpöge and Claude resolve this by establishing *approximate orthogonality* of the columns of the glued integral structure $R$. The mechanism is a striking fusion of Jacquet's relative trace formula (RTF), the automorphy of the character family $mu$ via the sixfold cover of $op("GL")_5$, and a Cauchy–Schwarz reduction to the $L^2$-norm of a suitably projected Poincaré series.

  === Relative Trace Formula and Cauchy–Schwarz Reduction to Projected Poincaré Series

  Let $G$ be our ambient reductive group (arising from the unitary dual pair or the metaplectic sixfold cover $tilde(op("GL"))_5$ on which the cubic/sextic Gauss-sum theta function lives, as sketched in `remark.pdf` items 3 and 16), and let $H_1, H_2 subset G$ be the period subgroups defining our Bessel/GGP periods. For a compactly supported test function $phi in C_c^oo (G(bb(A)))$, the automorphic kernel is
  $ K_phi (x, y) = sum_(gamma in G(K_0)) phi(x^(-1) gamma y), $
  and the *relative trace formula* evaluates the doubly integrated period
  $ I(phi) = integral_([H_1]) integral_([H_2]) K_phi (h_1, h_2) chi_1 (h_1) overline(chi_2 (h_2)) dif h_1 dif h_2 $
  in two ways:
  1. *Spectrally*, as a sum over automorphic representations $pi$ of $G$ of the product of period functionals $cal(P)_(H_1, chi_1) (f) overline(cal(P)_(H_2, chi_2) (f))$, which encodes the Gram matrix entries $chevron.l v_alpha, v_beta chevron.r$ of our column vectors indexed by Hecke characters!
  2. *Geometrically*, as a sum over double cosets $gamma in H_1 (K_0) backslash G(K_0) / H_2 (K_0)$ of relative orbital integrals
     $ O(gamma, phi) = integral_(H_1 (bb(A)) times H_2 (bb(A)) / op("Stab")(gamma)) phi(h_1^(-1) gamma h_2) chi_1 (h_1) overline(chi_2 (h_2)) dif(h_1, h_2). $

  The identity double coset ($gamma = 1$, or more generally the diagonal orbits) produces the *main diagonal term* $norm(v_alpha)^2$ of the Gram matrix, while the non-trivial double cosets produce the *off-diagonal terms* $chevron.l v_alpha, v_beta chevron.r$ ($alpha != beta$). To bound the off-diagonal spectral sum without needing to estimate every individual orbital integral with full square-root cancellation by hand, one introduces the *projected Poincaré series*
  $ P_(phi, alpha) (g) = sum_(gamma in H_1 (K_0) backslash G(K_0)) integral_(H_1 (bb(A))) phi_alpha (h_1^(-1) gamma g) chi_1 (h_1) dif h_1, $
  and projects it onto the relevant isotypic / weight space $cal(V)_"proj"$ via the orthogonal projector $Pi_"proj"$.

  #proposition(title: "Cauchy–Schwarz Reduction to the Norm of a Projected Poincaré Series")[
    Let $cal(H) = L^2 ([G], omega)$ be the automorphic Hilbert space, let $Pi_"proj" : cal(H) -> cal(V)_"proj"$ be the orthogonal projection onto the subspace spanned by the lifted forms of fixed weight and level, and for each column index $alpha in {1, dots.c, D}$, let $P_alpha = Pi_"proj" (P_(phi, alpha)) in cal(V)_"proj"$ be the projected Poincaré series representing the period functional $v_alpha$ via Riesz representation:
    $ chevron.l f, P_alpha chevron.r_cal(H) = cal(P)_(H_1, chi_1, alpha) (f) quad (forall f in cal(V)_"proj"). $
    Then the Gram matrix $G_(alpha, beta) = chevron.l P_alpha, P_beta chevron.r_cal(H)$ satisfies:
    1. *Exact spectral-geometric identity:* $G_(alpha, beta) = integral_([H_1]) P_(phi, alpha) (h) overline(chi_(1, beta) (h)) dif h$, whose diagonal term is the identity orbital integral $M_alpha > 0$.
    2. *Cauchy–Schwarz off-diagonal bound:* for any off-diagonal perturbation $E_(alpha, beta) = G_(alpha, beta) - delta_(alpha, beta) M_alpha$, if $Pi_"off"$ projects onto the orthogonal complement of the main diagonal mode, then
       $ |E_(alpha, beta)| <= norm(Pi_"off" P_alpha)_cal(H) dot.c norm(Pi_"off" P_beta)_cal(H). $
    3. *Approximate orthogonality and determinant lower bound:* if there exists $delta in (0, 1/2)$ such that
       $ sum_(beta != alpha) (|G_(alpha, beta)|) / (sqrt(M_alpha M_beta)) <= delta quad (forall alpha in {1, dots.c, D}), $
       then the normalized Gram matrix $tilde(G)_(alpha, beta) = G_(alpha, beta) / sqrt(M_alpha M_beta)$ is strictly diagonally dominant, all its eigenvalues lie in $[1 - delta, 1 + delta]$, and
       $ det G >= (1 - delta)^D product_(alpha = 1)^D M_alpha. $
  ]

  #proof[
    Part (1) is the standard unfolding of the Poincaré series $P_(phi, alpha)$: since $Pi_"proj"$ is self-adjoint and $P_beta in cal(V)_"proj"$, we have $chevron.l P_alpha, P_beta chevron.r_cal(H) = chevron.l P_(phi, alpha), P_beta chevron.r_cal(H)$, which unfolds over $H_1 (K_0) backslash G(K_0)$ to the period integral of $P_beta$.

    For Part (2), write $P_alpha = P_alpha^("main") + Pi_"off" P_alpha$, where the main diagonal terms are pairwise orthogonal ($chevron.l P_alpha^("main"), P_beta^("main") chevron.r = delta_(alpha, beta) M_alpha$) and orthogonal to $op("im")(Pi_"off")$. Then for $alpha != beta$,
    $ E_(alpha, beta) = chevron.l P_alpha, P_beta chevron.r = chevron.l Pi_"off" P_alpha, Pi_"off" P_beta chevron.r, $
    and the Cauchy–Schwarz inequality in $cal(H)$ gives $|E_(alpha, beta)| <= norm(Pi_"off" P_alpha)_cal(H) norm(Pi_"off" P_beta)_cal(H)$.

    For Part (3), the normalized Gram matrix $tilde(G) = D_M^(-1/2) G D_M^(-1/2)$ (with $D_M = op("diag")(M_1, dots.c, M_D)$) is Hermitian positive semidefinite with diagonal entries $tilde(G)_(alpha, alpha) = 1$ and off-diagonal row sums bounded by $sum_(beta != alpha) |tilde(G)_(alpha, beta)| <= delta$. By the Gershgorin circle theorem, every eigenvalue $lambda_i$ of $tilde(G)$ satisfies $|lambda_i - 1| <= delta$, hence $lambda_i >= 1 - delta > 0$. Taking the product of eigenvalues gives
    $ det G &= (det D_M) (det tilde(G)) = (product_(alpha = 1)^D M_alpha) (product_(i = 1)^D lambda_i) \
      &>= (1 - delta)^D product_(alpha = 1)^D M_alpha. $
  ]

  Notice the power of Part (3): once approximate orthogonality holds with $delta <= 1/2$, we have
  $ log det G >= sum_(alpha = 1)^D log M_alpha - D log 2, $
  so the *entire* destructive-cancellation loss across a $D$-dimensional lattice is at most $O(D)$—purely linear in $D$, with *zero* logarithmic blowup in the level or conductor!

  === The Four Engines of Approximate Orthogonality in Lean

  In the formal proof, establishing the hypothesis of Proposition 14.10—and bounding the resulting local Gram valuation $v_w (y, G_m (mu(y), y)) <= D g_y (y)$—is decomposed into four specialized modules, each addressing a distinct facet of the Gram matrix:

  1. *Character Column Kernels (`Formalism.CharacterColumnKernels`)*: When the column vectors are indexed by characters $chi$ of an abelian group (or blocks of Hecke characters), the Gram matrix factors through idempotent normal forms. In `CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean`, the lemma `collectAlt` aggregates the valuations of the $(t + 1)$ spectral blocks $L(0), L(1), dots.c, L(t)$: the principal block $L(0)$ captures the row lengths and column exponents, $L(1)$ captures the Eisenstein/zeta-value contribution $v_(h_E) + sum_w v_zeta (w)$, and the higher blocks $L(c)$ ($c >= 2$) are controlled by the Tate–Shafarevich / Selmer-type terms $op("Sha")(c - 1)$ plus uniform degree-dependent error budgets.

  2. *Fock Gram Window (`Formalism.SharpRestriction.GrowthBounds.FockGramWindow`)*: At the archimedean places, one must relate the Bargmann–Fock Gram matrix of the lifted polynomials to the integral lattice metric. The theorem `theorem_A_closed_form_holds` (`IntegralityFromMetricForLargeConstants`) combines three ingredients: the existence of a minimal-norm nonzero lattice vector (`exists_minimalNormVector`), a lower bound on the diagonal rank (`diagonal_rank_bound`), and the window-level restriction bound (`restWinE_proved`, which operates in the regime $k^2 Y^2 <= p$). Together, they guarantee that the Fock Gram matrix stays inside a well-conditioned window where no column collapses.

  3. *Mean Squares on $op("GL")_3$ and Genus Asymptotics (`Formalism.GL3MeanSquares`)*: To bound the norm $norm(Pi_"off" P_alpha)_cal(H)^2$ of the off-diagonal projected Poincaré series, one evaluates mean squares of automorphic $L$-functions and Jacobi character sums (`GenusMeanAsymptotics.JacobiCharacterSums`), unimodular class representatives (`UnimodularClassRepresentatives`), and the joint dimension-mass bound (`HookFormulaTorsion.DimensionMassJointBound`, `MassLowerBoundClosed`). These bounds confirm that the spectral mass of the off-diagonal terms is polynomially suppressed relative to the main diagonal mass $M_alpha$.

  4. *Unramified Local Orthogonality (`GlobalTheory.unramifiedOrthogonality_holds`)*: At all unramified finite places $y in.not S_y$, the local Hecke operators are self-adjoint and the spherical vectors corresponding to distinct unramified Satake parameters are *strictly orthogonal*. Formalized as `ReciprocityTheory.Gal.UnramifiedOrthogonality`, this ensures that off-diagonal terms vanish identically outside the finite ramified set $S_y$, matching the hypothesis in `DivIneqObjU` that the local sum vanishes for all $y in.not S_y$.

  #theorem(title: "Approximate Orthogonality and the Global Gram Valuation Bound")[
    Assume the unramified orthogonality theorem (`UnramifiedOrthogonalityHolds`), the Fock Gram window bound (`FockGramWindow`), and the $op("GL")_3$ / Poincaré-series mean-square bound (`GL3MeanSquares`). Then for the glued $cal(O)_K$-lattice $R$ of Theorem 14.9, there exists a local Gram-defect profile $g_y : S_y -> bb(R)$ and a global bound $L_G > 0$ such that:
    1. For every prime $y in S_y$,
       $ v_w (y, G_m (mu(y), y)) <= D dot.c g_y (y). $
    2. Summing over $S_y$ weighted by $l_w (y) = (log N(y)) / [K : bb(Q)]$,
       $ sum_(y in S_y) l_w (y) g_y (y) <= L_G <= lambda_0 + log D_G + C_b f N^2 log g, $
       where $log D_G <= C_b f N log(f N)$ bounds the discriminant/Fock-window distortion, $lambda_0$ is the archimedean approximation tolerance, and $C_b f N^2 log g$ absorbs the ramified-place off-diagonal defect.
  ]

  #proof[
    For each $y in S_y$, let $e_b (t, y)$ be a local $cal(O)_(K, y)$-basis of $"abelian"_2 (t)$ at $y$, so that the Gram determinant $G_m (t, y) in K$ satisfies $v_0 (G_m (t, y)) = det op("gram")(X_Q (t), v_0, e_b (t, y))$. By the product formula over all places of $K$, the $y$-adic valuation $v_w (y, G_m (mu(y), y))$ is bounded above by the archimedean log-Gram determinant minus the valuations at all other finite places. At unramified places $y' in.not S_y$, `UnramifiedOrthogonalityHolds` forces the local Gram matrix to be unimodular (valuation $0$). At the archimedean place $v_0$, Proposition 14.10(3) (with the off-diagonal Poincaré norm bounded by `GL3MeanSquares` and the Fock metric compared to the integral basis by `FockGramWindow`) yields
    $ &log det op("gram")(X_Q (mu(y)), v_0, e_b (mu(y), y)) \
      &quad >= sum_(alpha = 1)^D log M_alpha - D log(1 / (1 - delta)), $
    while the character-column block decomposition (`CharacterColumnKernels`) bounds the ramified-place defect per dimension by $g_y (y)$ with total weighted sum $sum_(y in S_y) l_w (y) g_y (y) <= lambda_0 + log D_G + C_b f N^2 log g$.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Approximate Orthogonality Modules",
    module: "Formalism.CharacterColumnKernels, Formalism.SharpRestriction.GrowthBounds.FockGramWindow, Formalism.GL3MeanSquares, GlobalTheory.unramifiedOrthogonality_holds",
  )[
    - `Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne` proves `collectAlt`, aggregating the valuations across character-column blocks.
    - `Formalism.SharpRestriction.GrowthBounds.FockGramWindow` proves `theorem_A_closed_form_holds : IntegralityFromMetricForLargeConstants D` from `exists_minimalNormVector`, `diagonal_rank_bound`, and `restWinE_proved`.
    - `Formalism.GL3MeanSquares` provides the genus mean asymptotics (`JacobiCharacterSums`, `UnimodularClassRepresentatives`) and torsion/mass bounds (`DimensionMassJointBound`, `MassLowerBoundClosed`).
    - `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds` exports `unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality`.
  ]

  == Covolumes, Theta Series' Index, and Congruences Between Lifts and Forms

  To close the loop from the local-global divisor inequality `DivIneqObjU` to the final Arakelov contradiction in Chapter 15, three final quantitative ingredients (`remark.pdf` item 18) must be supplied:
  1. upper bounds on the *covolumes* of the ambient arithmetic lattices and Hodge bundles (`TopCovolSlim2Use`, `CovolumeBoundOfX`);
  2. exact algebraic control of the *index of the theta series lattice* inside the space of integral automorphic forms (`LatticeIndexTer`); and
  3. *congruences between theta lifts and Hecke eigenforms*, including explicit uniform control at the small primes $2$ and $3$ (`WeightCongruences`, `BoundAtTwoThreeFamilyFon`).

  === Covolumes via Arakelov Geometry and Toroidal Compactifications

  In Bost's slope inequality, the upper bound on the slope of the dual lattice `dualLat R` must be compared against the *covolume* (normalized Arakelov degree) of the ambient space of automorphic forms, which is realized geometrically as a space of global sections $H^0 (overline(cal(A))_g, omega^(times.o k))$ of a power of the Hodge bundle $omega$ on a toroidal compactification $overline(cal(A))_g$ of a Siegel or unitary Shimura variety.

  Computing the covolume of $H^0 (overline(cal(A))_g, omega^(times.o k))$ equipped with the Petersson ($L^2$) metric—and proving that its leading asymptotic is bounded by `CovolumeBoundOfX`—requires uniting deep results from Arakelov geometry and moduli theory:
  - *Toroidal compactifications and integral models* (`SiegelToroidalIntegral`, `ToroidalForFanKS`): extending the Hodge bundle $omega$ to a nef line bundle on a smooth projective toroidal compactification over $cal(O)_K$, with controlled boundary divisors.
  - *Fubini–Study and Chow form height comparison* (`ChowFormHeightComparison`, `FubiniStudyChowHeightFormula`, `ChowFormHyperplaneSection`): relating the $L^2$-covolume of small sections to the Arakelov height of the Chow form of the projective embedding defined by $omega^(times.o k)$, using the injectivity of small sections (`SmallSectionsInjective`).
  - *Arithmetic Hilbert–Samuel and Moriwaki bigness* (`MoriwakiBigStatement`, `HSUse`, `NefRR`): converting the self-intersection number $hat(c)_1 (overline(omega))^(d + 1)$ into an explicit asymptotic upper bound on the normalized log-covolume `lcv (XW j) (M j) / D`.
  - *Deformation theory and $p$-adic Hodge / Fargues–Fontaine inputs* (`GrothendieckDeformation`, `FarguesExact`, `ZarhinStatement`): controlling the $p$-adic integral models of abelian schemes and ensuring that the semi-abelian Lie algebra at the boundary is seminegative (`SemiAbelianLieSeminegative`).

  #theorem(title: "Covolume Bound for the Ambient Hodge-Bundle Lattice (CovolumeBoundOfX)")[
    Let $overline(cal(A))$ be a smooth projective toroidal compactification of the unitary Shimura variety associated to $op("U")(X_j)$, equipped with the Petersson-metrized Hodge line bundle $overline(omega)$. Under the standard arithmetic-geometric hypotheses (resolution of singularities and principalisation in characteristic zero, Poincaré–Lelong inversion, arithmetic Hilbert–Samuel / Moriwaki bigness, Grothendieck deformation, and toroidal compactification with seminegative boundary Lie algebra), the normalized log-covolume of the integral lattice $M_j$ of automorphic forms satisfies the uniform upper bound `CovolumeBoundOfX`:
    $ (op("lcv")(X_W (j), M_j)) / D = -op("muDef")(X_W (j), M_j) <= -mu_G (j) + P_9 (j), $
    where $mu_G (j)$ is the good-stratum slope lower bound controlled by the Fubini–Study Chow height of $overline(omega)$ and $P_9 (j)$ is an explicit error term satisfying $P_d (j) + 12 delta_d (j) Q_d (j) + P_9 (j) <= b$.
  ]

  In `TopCovolSlim2Use.lean`, this entire chain of Arakelov-geometric deductions is assembled into a single theorem `topCovolSlim2_use_alt_alt`, which takes the published geometric theorems as explicit hypotheses and outputs `_root_.GlobalTheory.CovTop.CovolumeBoundOfX`.

  === The Theta Series' Index Over Discrete Valuation Rings

  To connect the covolume of the ambient space $M_j$ of integral automorphic forms to the covolume of the sublattice spanned by theta lifts $theta_j (mu(y)) T_l (j, mu(y))$, we need a clean, functorial theory of the *relative index* of two full lattices over a discrete valuation ring. This is developed in `Formalism.LatticeIndexTer` (`StatementIdx.lean`, `IdxAdd`, `IdxDet`).

  #definition(title: "Relative Lattice Index Over a DVR")[
    Let $cal(O)$ be a discrete valuation ring with fraction field $K$ and additive valuation $v : cal(O) without {0} -> bb(N)$. Let $X$ be a finite-dimensional $K$-vector space. A *full $cal(O)$-lattice* $A subset X$ (`IsLat`) is a finitely generated $cal(O)$-submodule such that $K dot.c A = X$. For any two full $cal(O)$-lattices $A, B subset X$, define the *quotient length*
    $ op("qlen")(A, B) = op("length")_cal(O) (A / (A inter B)) in bb(N) union {oo}, $
    and the *signed relative index*
    $ op("idx")(A, B) = op("qlen")(A, B) - op("qlen")(B, A) in bb(Z). $
  ]

  When $B subset.eq A$, we have $A inter B = B$, so $op("qlen")(B, A) = 0$ and $op("idx")(A, B) = op("length")_cal(O) (A / B) >= 0$ is the ordinary module-length index $[A : B]_cal(O)$. The signed extension to arbitrary pairs $(A, B)$ satisfies two fundamental properties—exact additivity and the determinantal formula—which make local-to-global index computations completely algebraic.

  #theorem(title: "Additivity and Determinantal Formula for the Relative Lattice Index")[
    Let $cal(O)$ be a discrete valuation ring with fraction field $K$ and additive valuation $v$, and let $X, Y$ be finite-dimensional $K$-vector spaces.
    1. *Finiteness (`LatFinite`):* For any two full $cal(O)$-lattices $A, B subset X$, $op("qlen")(A, B) < oo$.
    2. *Additivity (`IdxAdd`):* For any three full $cal(O)$-lattices $A, B, C subset X$,
       $ op("idx")(A, C) = op("idx")(A, B) + op("idx")(B, C). $
    3. *Determinantal formula (`IdxDet`):* Let $b_X$ be a $K$-basis of $X$, $b_Y$ a $K$-basis of $Y$, and $f : X tilde.equiv_K Y$ a $K$-linear isomorphism. Let $A = cal(O) dot.c b_X$ and $B = cal(O) dot.c b_Y$. If $a, b in cal(O) without {0}$ satisfy $a = det([f]_(b_X, b_Y)) dot.c b$ in $K$, then
       $ op("idx")(B, f(A)) = v(a) - v(b). $
  ]

  #proof[
    Since $cal(O)$ is a DVR (hence a PID) and $A, B$ are finitely generated torsion-free $cal(O)$-modules spanning $X$, both $A$ and $B$ are free of rank $n = dim_K X$ (`LatBasis`). Choose a nonzero uniformizer power $pi^k in cal(O)$ such that $pi^k A subset.eq B$. Then $A / (A inter B)$ is a quotient of $A / pi^k A tilde.equiv (cal(O) / pi^k cal(O))^n$, which has finite length $n k$, proving (1).

    For (2), choose $C_0 = A inter B inter C$, which is also a full $cal(O)$-lattice contained in $A$, $B$, and $C$. From the short exact sequence $0 -> (A inter B) / C_0 -> A / C_0 -> A / (A inter B) -> 0$ and additivity of module length, we have
    $ op("qlen")(A, B) = op("length")(A / C_0) - op("length")((A inter B) / C_0). $
    Subtracting the symmetric identity for $op("qlen")(B, A)$ cancels $op("length")((A inter B) / C_0)$ identically, yielding
    $ op("idx")(A, B) = op("length")(A / C_0) - op("length")(B / C_0). $
    Therefore
    $ &op("idx")(A, B) + op("idx")(B, C) \
      &= (op("length")(A / C_0) - op("length")(B / C_0)) \
      &quad + (op("length")(B / C_0) - op("length")(C / C_0)) \
      &= op("length")(A / C_0) - op("length")(C / C_0) = op("idx")(A, C). $

    For (3), let $M = [f]_(b_X, b_Y) in op("GL")_n (K)$. Multiplying by a nonzero scalar $b in cal(O)$ clears denominators so that $b M in M_n (cal(O))$. By the Smith normal form over the DVR $cal(O)$, there exist $U, V in op("GL")_n (cal(O))$ and integers $e_1, dots.c, e_n >= 0$ such that $U (b M) V = op("diag")(pi^(e_1), dots.c, pi^(e_n))$. Since $U$ and $V$ preserve the lattices $B$ and $A$ respectively, we have
    $ op("idx")(B, b f(A)) &= op("length")_cal(O) (cal(O)^n / op("diag")(pi^(e_1), dots.c, pi^(e_n)) cal(O)^n) \
      &= sum_(i = 1)^n e_i = v(det(b M)) = n v(b) + v(det M). $
    On the other hand, $op("idx")(b f(A), f(A)) = -op("idx")(f(A), b f(A)) = -n v(b)$. By additivity (Part 2),
    $ op("idx")(B, f(A)) &= op("idx")(B, b f(A)) + op("idx")(b f(A), f(A)) \
      &= v(det M) = v(a) - v(b), $
    where $v(det M) = v(a) - v(b)$ follows from $a = det(M) b$.
  ]

  Applying Theorem 14.14 to the theta series lattice $theta_j (mu(y)) T_l (j, mu(y))$ inside the integral automorphic lattice $M_j$ allows us to express the local index $op("idx")_y (M_j, theta_j (mu(y)) T_l (j, mu(y)))$ directly as the $y$-adic valuation of the transition determinant—which is precisely how the inert-prime divisibility of the theta derivatives translates into the lattice-index bounds of Section 14.2!

  === Congruences Between Theta Lifts and Eigenforms, and the Small Primes $2$ and $3$

  The final piece of `remark.pdf` item 18 bridges *theta lifts* (which have explicit, computable $p$-adic divisibility from CM curves) to *cuspidal Hecke eigenforms* (whose $L$-functions and Bessel periods appear in the Weil explicit formula). In general, a theta lift of weight $k$ need not be a single cuspidal eigenform; it is a linear combination of eigenforms, and its weight may differ from the target weight by a shift governed by the roots of unity $mu_K$ of the CM field $K$.

  To transfer divisibility and nonvanishing between theta lifts and eigenforms without losing control of the Galois / Hecke action, one establishes *weight congruences* (`Development.AutomorphicArithmetic.WeightCongruences`):

  #proposition(title: "CM-Type Weight Congruences and Lift-to-Eigenform Transfer")[
    Let $K$ be a CM field with torsion subgroup $mu_K = (cal(O)_K^times)_"tors"$ of order $w_K$, and let $Phi$ be a CM type of $K$.
    1. *Phase-to-norm congruence (`ProdCmTypeEqNormAndWeightCongruenceOne`):* For any unit $u in cal(O)_K^times$ whose CM-type phase product satisfies $product_(tau in Phi) tau(u) / overline(tau(u)) = 1$ (up to a root of unity $zeta in mu_K$), there exists a weight shift $0 <= s < w_K$ (`ExistsShiftWeightCongruenceLtTorsionOrder`) such that the shifted Hecke character $mu dot.c |dot.c|^s$ has trivial central restriction on units and satisfies the exact weight congruence needed for $p$-adic interpolation.
    2. *Congruence between lifts and eigenforms:* If $f$ is an $m$-fold iterated theta lift whose Fourier–Jacobi / Bessel coefficients are divisible by $frak(p)^r$ at an inert prime $frak(p)$, and $g$ is a cuspidal Hecke eigenform congruent to $f$ modulo $frak(p)^r$ (detected via the idempotent interpolation of Hecke operators, `DvdNormSubOneOfIdempotentInterpolationRelNormOne`), then the normalized Bessel period of $g$ inherits the same $frak(p)^r$-divisibility up to the congruence modulus of the Hecke algebra.
  ]

  #proof[
    For Part (1), since $K$ is CM, for every unit $u in cal(O)_K^times$ the ratio $u / overline(u)$ has absolute value $1$ at every archimedean place, hence by Kronecker's theorem $u / overline(u) in mu_K$ is a root of unity (`ExistsUnitEqRootOfUnityMulConjPhaseOne`). Taking the product over $tau in Phi$ yields an element of $mu_K$ of order dividing $w_K$. Choosing the unique residue $0 <= s < w_K$ annihilating this root of unity aligns the infinity-type of the Hecke character with the integral weight lattice.

    For Part (2), let $bb(T)$ be the integral Hecke algebra acting on the space of integral automorphic forms $M_j$ over $cal(O)_(K, frak(p))$. By finite-dimensionality, $bb(T) times.o K_frak(p)$ splits as a product of fields indexed by eigenforms $g_i$, with orthogonal idempotents $e_i in bb(T) times.o K_frak(p)$. The denominator of $e_i$ in $bb(T)$ is precisely the *congruence ideal* $eta_(g_i)$ measuring congruences between $g_i$ and other eigenforms. Applying the scaled idempotent $c_i e_i in bb(T)$ (with $c_i in eta_(g_i)$) to the congruence $f equiv 0 mod frak(p)^r$ preserves integrality and transfers the $frak(p)$-adic divisibility directly to the $g_i$-isotypic component, up to the $frak(p)$-adic valuation of the congruence modulus $c_i$.
  ]

  One last subtlety remains: the prime $2$ (where the Weil representation has metaplectic sign ambiguities and quadratic-form parity issues) and the prime $3$ (where $mu_K$ for $K = bb(Q)(sqrt(-3))$ has order $6$, creating extra torsion in the Hilbert/Eisenstein congruence ideals). In `BoundAtTwoThreeFamilyFon.lean`, these two exceptional primes are handled uniformly across the entire family of parameters `FamP eps` via `BoundAtTwoThreeFamilyFonAlt`:

  #theorem(title: "Uniform Control at the Small Primes 2 and 3 (BoundAtTwoThreeFamilyFon)")[
    Let `Fm : FamP eps` be an admissible family of automorphic data parameterized by $x > x_1$ and $i in op("Ix")(x)$, satisfying the canonical height normalization (`Canon`), polynomial parameter bounds (`ParametersPolynomiallyBounded`), sufficiently large length ($L >= 8$) and split-prime bound ($>= 60$), the killing condition (`KillAt`), and odd finiteness of the Tate–Shafarevich obstruction (`ShaFinOdd`). Then there exist absolute constants $C, x_0 > 0$ such that for all $x >= x_0$ and all $i in op("Ix")(x)$, the local contributions at the primes $2$ and $3$ satisfy the uniform bound `BoundAtTwoThree (Fm.L x i) X.ρ C`, preventing the small primes from degrading either the divisibility gain $2 F_0$ or the Gram-determinant bound $L_G$.
  ]

  #lean-note(
    title: "Lean 4 Formalization: Covolumes, Indices, and Congruences",
    module: "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt, Formalism.LatticeIndexTer, Development.AutomorphicArithmetic.WeightCongruences, GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt",
  )[
    - `TopCovolSlim2Use.lean` proves `topCovolSlim2_use_alt_alt -> CovolumeBoundOfX`, assembling the toroidal compactification, Chow form height, and Moriwaki bigness bounds.
    - `Formalism.LatticeIndexTer` (`StatementIdx.lean`) defines `IsLat`, `qlen`, `idx`, and proves `LatFinite`, `LatBasis`, `IdxAdd`, and `IdxDet`.
    - `Development.AutomorphicArithmetic.WeightCongruences` proves `ProdCmTypeEqNormAndWeightCongruenceOne`, `ExistsShiftWeightCongruenceLtTorsionOrder`, and `DvdNormSubOneOfIdempotentInterpolationRelNormOne`.
    - `BoundAtTwoThreeFamilyFon.lean` formalizes `SetupAlt`, `ExtraAlt`, `FactsFAlt`, and `BoundAtTwoThreeFamilyFonAlt` controlling the primes $2$ and $3$ uniformly across the family.
  ]

  #remark(title: "Looking Ahead to the Endgame")[
    With Theorem 14.8 (`DivIneqObjU`) in hand—supported by the order-$m$ cancellation of Section 14.1, the inert-prime divisibility gain $2 F_0$ of Section 14.2, the glued GCD lattice $R$ of Section 14.3, the approximate orthogonality bound $L_G$ of Section 14.4, and the covolume, index, and congruence estimates of Section 14.5—every analytic and local-arithmetic ingredient of the proof is now in place. What remains in Chapter 15 is the global arithmetic synthesis: selecting the Iwasawa tower via Behrend's theorem on progression-free sets, neutralizing the remaining Galois cohomology classes in $H^1 (cal(O)_E [1/ell], bb(Q)_ell / bb(Z)_ell (-e))$ via a quantitative weakening of Vandiver's conjecture, and executing the final Bost slope contradiction to establish the Generalized Riemann Hypothesis.
  ]

  #exercises((
    [
      *Chowla–Selberg for $K = bb(Q)(i)$ and $bb(Q)(sqrt(-3))$.* Using Theorem 14.1 and Euler's reflection formula $Gamma(z) Gamma(1 - z) = pi / sin(pi z)$, compute the explicit period $|Omega_E|$ (up to algebraic constants) for the elliptic curves $y^2 = x^3 - x$ (CM by $bb(Z)[i]$, $D_K = 4$, $w_K = 4$, $h_K = 1$) and $y^2 = x^3 - 1$ (CM by $bb(Z)[omega]$, $D_K = 3$, $w_K = 6$, $h_K = 1$). Verify that $Omega_E = Gamma(1/4)^2 / (2 sqrt(2 pi))$ for $D_K = 4$ and $Omega_E = Gamma(1/3)^3 / (2^(4/3) pi)$ for $D_K = 3$.
    ],
    [
      *Fock Inner Product and Divided Powers.* Let $r = n = 2$ and consider the weight $nu = (2, 1)$ in $A_bb(Q) = bb(Q)[x_(0, 0), x_(0, 1), x_(1, 0), x_(1, 1)]$. Write down the highest-weight vector $op("hw")_bb(Q) (nu) = x_(0, 0) (x_(0, 0) x_(1, 1) - x_(0, 1) x_(1, 0))$ explicitly, compute its Fock norm squared $chevron.l op("hw")(nu), op("hw")(nu) chevron.r_"Fock"$, and verify by direct calculation that $chevron.l op("rowDiv")_(1, 0, 1)(f), g chevron.r_"Fock" = chevron.l f, op("rowDiv")_(0, 1, 1)(g) chevron.r_"Fock"$ for $f = op("hw")(nu)$ and $g = op("rowDiv")_(1, 0, 1)(op("hw")(nu))$.
    ],
    [
      *Failure of Integral Weyl–Dual Weyl Equality.* Proposition 14.3(3) shows that $op("weyl")_bb(Q) (r, n, nu) = op("dualWeyl")_bb(Q) (r, n, nu)$ over $bb(Q)$. Show by an explicit example with $r = n = 2$ and $nu = (p, 0)$ (where $p$ is a prime) that over $bb(F)_p$ (or over $bb(Z)$ localized at $p$), the Weyl module $op("weyl")_bb(Z) (2, 2, (p, 0))$ is a *proper* sublattice of $op("dualWeyl")_bb(Z) (2, 2, (p, 0))$, and compute the $p$-adic index $[op("dualWeyl")_bb(Z) : op("weyl")_bb(Z)]$.
    ],
    [
      *Two-Sided Double Coset Formula on $op("SL")_2 (bb(Q)_p)$.* Apply Proposition 14.4 to $G_1 = G_2 = op("SL")_2 (bb(Q)_p)$ with $K_1 = K_2 = op("SL")_2 (bb(Z)_p)$ and $f$ the indicator function of the double coset $K_1 op("diag")(p, p^(-1)) K_2$. Compute the number of right $K_1$-cosets in $K_1 op("diag")(p, p^(-1)) K_1$ and verify the relation to the local Hecke eigenvalue of the $p$-th Hecke operator $T(p^2)$.
    ],
    [
      *Inert-Prime Divisibility Constant.* Using the expansion $v_p (D^a theta(0) / Omega^a) >= sum_(k >= 0) floor(a / p^(2 k + 1)) - O(log a)$ for a prime $p$ inert in an imaginary quadratic field $K$, show that as $a -> oo$,
      $ liminf_(a -> oo) 1 / a v_p ((D^a theta(0)) / Omega^a) >= p / (p^2 - 1). $
      Compare this with the ordinary factorial valuation $v_p (a!) / a -> 1 / (p - 1)$ and explain why the difference $1 / (p - 1) - p / (p^2 - 1) = 1 / (p^2 - 1)$ is crucial when comparing against $op("ph")(a) = a log a - a$.
    ],
    [
      *Local-Global Lattice Gluing as GCD.* Let $cal(O)_K = bb(Z)$ and $D = 2$. Consider the two lattices $L_1 = bb(Z) dot.c (2, 0) + bb(Z) dot.c (0, 3)$ and $L_2 = bb(Z) dot.c (5, 0) + bb(Z) dot.c (0, 7)$ in $bb(Q)^2$. Define $mu(p) = 1$ for $p in {5, 7}$ and $mu(p) = 2$ for all other primes $p$ (so $mu_0 = 2$). Construct the glued lattice $R subset bb(Q)^2$ satisfying $R_p = (L_(mu(p)))_p$ for all primes $p$, showing that $R = bb(Z)^2$—illustrating how gluing strips away *all* spurious prime factors ${2, 3, 5, 7}$.
    ],
    [
      *Gershgorin Lower Bound and Hadamard Comparison.* Let $G in M_D (bb(C))$ be a Hermitian positive definite matrix with diagonal entries $M_1, dots.c, M_D > 0$, and suppose $|G_(alpha, beta)| <= (delta / (D - 1)) sqrt(M_alpha M_beta)$ for all $alpha != beta$, where $0 < delta < 1$. Prove that
      $ (1 - delta)^D product_(alpha = 1)^D M_alpha <= det G <= product_(alpha = 1)^D M_alpha, $
      and show that the lower bound is asymptotically sharp (up to the constant in the exponent) by evaluating $det((1 - epsilon) I_D + epsilon J_D)$ where $J_D$ is the all-ones matrix and $epsilon = -delta / (D - 1)$.
    ],
    [
      *Additivity and Smith Normal Form for `idx`.* Let $cal(O) = bb(Z)_p$ and $X = bb(Q)_p^3$. Let $A = bb(Z)_p^3$, $B = g A$, and $C = h A$, where
      $ g = mat(p^2, 1/p, 0; 0, p, 0; 0, 0, 1/p^2), quad h = mat(1/p, 0, 0; 0, p^3, 1; 0, 0, p). $
      Compute $op("qlen")(A, B)$, $op("qlen")(B, A)$, $op("idx")(A, B)$, $op("idx")(B, C)$, and $op("idx")(A, C)$ directly from Definition 14.13, and verify both `IdxAdd` and `IdxDet` from Theorem 14.14.
    ],
    [
      *Congruence Ideals and Weight Shifts.* Let $K = bb(Q)(sqrt(-3))$, so $mu_K = chevron.l zeta_6 chevron.r$ has order $w_K = 6$. For an algebraic Hecke character $mu$ of $K$ of infinity type $(k_1, k_2)$ (i.e., $mu((alpha)) = alpha^(k_1) overline(alpha)^(k_2)$ on principal ideals prime to the conductor), determine the exact congruence condition on $k_1 - k_2$ required for $mu$ to be well-defined on $cal(O)_K^times$ when the conductor is $(1)$. How does shifting $mu$ by a finite-order character of conductor dividing $(2)$ or $(3)$ relax this congruence condition, and why does this necessitate the separate treatment in `BoundAtTwoThreeFamilyFon`?
    ],
  ))
]
