#import "style.typ": *
#chapter[Designing a positive family]

== An identity on a cyclic quotient <c10s01>

Fix a primitive target character $psi$ and let $o$ be its order. Take the primitive characters inducing the powers $psi^j$, $0<=j<o$. They are distinct as characters on integers coprime to the original modulus. The desired statistic is
$ F_(psi)(x)=G_(z)(x)+1/(3o+1) sum_(j=1)^(o-1) G_((psi^j)^*)(x). $
The star indicates the primitive inducing character. For $o=1$ this prescription gives $G_z$ with an empty second sum. The formula remains meaningful if some powers have smaller conductors.

Here is the elementary design behind the coefficient. On the cyclic group of order $o$ assign mass $4/(3o+1)$ to the identity and $3/(3o+1)$ to each other element. These masses sum to one. For a nontrivial character $lambda$ of the group, orthogonality gives
$ sum_g P(g)lambda(g)
   = (3 sum_g lambda(g)+lambda(1))/(3o+1) = 1/(3o+1). $
For the trivial character the transform is one. These are the exact coefficients of the target distribution. The arithmetic counting measure approximates each of its coset masses with absolute error at most $x^(-1+epsilon)$. Summing against a character of modulus one makes the Fourier error at most $o x^(-1+epsilon)$. In the larger group two auxiliary signs are still present. Their nontrivial Fourier components need estimates of their own.

#example[Order three][The three masses are $4/10,3/10,3/10$. If $omega^3=1$ and $omega!=1$, their Fourier coefficient is $(4+3omega+3omega^2)/10=1/10$. The statistic sees both primitive powers even when they are complex conjugates. A zero of either one contributes to its Mellin pole.]

== Fourier inversion with a prescribed positive coefficient <c10s02>

Suppose one wants a single real sum capable of detecting zeros of all the powers of a character of order $o$. An equal average on the cyclic quotient gives zero for every nontrivial Fourier coefficient. A point mass at its identity gives coefficient one to every character, but would require all selected places to lie in the same coset. A small increase in the density of one coset gives a distribution with both a positive signal and a positive mass in every coset.

Let $C$ be cyclic of order $o$ and let $u_C$ denote its uniform probability distribution. For $0<a<1$ consider $(1-a)u_C+a delta_0$, where $delta_0$ is the point mass at the identity. Under the unnormalized Fourier sum on probability masses the trivial coefficient is one and all nontrivial coefficients are $a$. Indeed the Fourier transform of a point mass at zero is identically one, and that of $u_C$ vanishes off the trivial character. Taking $a=1/(3o+1)$ gives the ratio four to three between the distinguished coset and each of its neighbors. This recovers the chosen masses from their intended coefficients.

Fourier inversion also proves uniqueness for this choice of coefficients. If two masses have the same Fourier coefficients, apply the inverse transform to their difference. Orthogonality yields zero in each coordinate. The real and positive character coefficients are therefore an exact requirement on the distribution of the top places. A finite sample is allowed some error, and that error must be quantified in the *primal* coset masses. If $N_T>0$ places contribute counts $n_c$ with
$ abs(frac(n_c,N_T)-P(c))<=h quad (c in C), $
the error in any single Fourier coefficient has absolute value at most $o h$. This uses only the unit modulus of a finite character. For the trivial Fourier coefficient the error is exactly zero since both mass vectors have total mass one. There is often cancellation in other coefficients, but the uniform estimate $o h$ requires none.

If a coefficient error multiplies a ramp of size at most $C_1 x(log x)^2$, the resulting error is at most $C_1 o x^(epsilon)(log x)^2$ for $h=x^(-1+epsilon)$. Because the target family is fixed, $o$ remains fixed as $x$ grows. For any $eta>0$, $(log x)^2<=x^eta$ eventually. In particular this approximation costs much less than a square-root power of $x$. The high accuracy in the top shares earns its keep here, whereas the lower bound on the *number* of top places will be used later for a different division.

== Two different finite sets <c10s03>

The finite abelian group of the construction comes from a cyclotomic field. In coordinates it is $E_0 times H$ with $E_0=(ℤ slash 2ℤ)^2$ and $H$ finite abelian. The chosen CM type consists of elements whose first sign coordinate is zero. It has $2|H|$ elements. Write $H$ additively and fix the subgroup $A_0$ on which the retained characters are trivial. Two choices of subsets serve different purposes.

The set $T$ indexes the distinguished top places. Its projected counts implement the masses just calculated. The set $T_2 subset.eq A_0$ indexes archimedean weights that will be large. Its additive structure controls overlaps between concentration conditions imposed by distinct iterates. Translates $u+T_2$ allow the location of the large weights to vary without changing their number. Later one sums over every $u in A_0$.

For a character $xi$ of the large group and $s in A_0$,
$ sum_(u in A_0) xi(0,-u-s)=cases(|A_0| & "if " xi|_(A_0)=1, 0 & "otherwise"). $
Indeed, translation permutes $A_0$ and the sum of a nontrivial character on a finite group vanishes. Orthogonality first discards all characters nontrivial on $A_0$. Among the survivors are, besides the $o$ desired powers, the powers twisted by one or both of two quadratic characters. There are at most $4o$ relevant characters, with at most $3o$ in these extra cosets. The bound is independent of the growing degree of the field. This distinction allows the final normalization to absorb a constant depending on $psi$.

== An entire host average with twelve elements in its abelian factor <c10s04>

We work out the quotient projection explicitly. Let $H=ℤ slash 12ℤ$ and $A_0={0,3,6,9}$. The quotient consists of three cosets, labeled by reduction modulo three. Write $lambda_(j)(h)=exp(2 pi i j h/12)$ with $0<=j<12$. The normalized average of $lambda_j$ on $A_0$ is
$ frac(1,4) sum_(b=0)^3 exp(2 pi i j b/4)
  =cases(1 & "if " 4 divides j,0 & "otherwise"). $
One can see the projection directly on an arbitrary function $f$ on $H$. Replace $f(h)$ by the average of $f(h+u)$ over $u in A_0$. All four values on the same coset become equal. Averaging twice leaves the result unchanged. In the character basis the eigenvalues of this operation are exactly the zeros and ones in the displayed formula. In particular $lambda_4$ and $lambda_8$, the two nontrivial characters of the quotient, survive even though many characters of $H$ disappear.

Choose ten distinct top positions:
$ T={0,3,6,9,1,4,7,2,5,8}. $
The counts in the three cosets are respectively $4,3,3$. At $j=4$ the normalized Fourier coefficient from $T$ is $(4+3omega+3omega^2)/10=1/10$, with $omega=exp(2 pi i/3)$. At $j=8$ it is the conjugate, also $1/10$. At $j=0$ it is one. The raw Fourier coefficient of $T$ at a character nontrivial on $A_0$ need not vanish. It is the separate translation average that annihilates it. To see the distinction without evaluating another geometric series, replace one member of $T$ by a different position in the same coset. The three coset counts and the three surviving coefficients stay fixed; a character that takes different values at the two positions can change its raw coefficient.

The thick set plays another role. For any nonempty $D subset.eq A_0$ and any character of $H$, the sum
$ sum_(u in A_0) sum_(s in D) lambda_(j)(-u-s) $
vanishes for $j$ not divisible by four. For the other three characters every summand is one, giving $4 abs(D)$. Restoring the normalization by $abs(A_0)$ leaves $abs(D)$. In the arithmetic calculation $D$ is $T_2$, chosen for additive separation. Averaging makes its detailed shape disappear from the leading character projection. The shape has already controlled the prime-by-prime errors, which is why one cannot replace it by an arbitrary set at the start of the construction.

Adjoin the two binary sign coordinates to $H$. Each of the three surviving characters can be multiplied by any of four sign characters. The quotient now supports twelve possible characters. Three have trivial auxiliary signs and nine have at least one nontrivial sign. This simple count explains the general upper bound of $4o$, independently of the size of the annihilated subgroup. A representation of the host at much higher degree need not create a larger set of analytic terms after projection. The example computes only this finite Fourier calculation; choosing the physical field, sizes and separated set takes further arguments in the next chapter.

== The conductor can change along a single cyclic family <c10s05>

Here is an example in which every family member can be listed. On the units modulo fifteen let $psi=chi_3 chi_5$, where $chi_3$ is the nontrivial quadratic character modulo three and $chi_5$ is the quartic character modulo five with $chi_(5)(2)=i$. The Chinese remainder theorem makes the two factors independent. The conductor of their product is fifteen. If the product factored modulo five, changing only the residue modulo three could not change its value, contrary to nontriviality of $chi_3$. The same argument excludes conductor three. The order is four. The powers have the following primitive sources.

#align(center)[#table(columns:(auto,auto,auto),inset:(x:8pt,y:3pt),align:left,stroke:none,
  table.hline(stroke:0.6pt), [*Power*], [*Primitive source*], [*Conductor*],table.hline(stroke:0.35pt),
  [$0$], [trivial], [$1$],
  [$1$], [$chi_3 chi_5$], [$15$],
  [$2$], [$chi_5^2$], [$5$],
  [$3$], [$chi_3 overline(chi_5)$], [$15$],table.hline(stroke:0.6pt))]

On the common unit group all four powers are distinct. On arbitrary integers one must retain their own conductor conventions. The square viewed at modulus fifteen is zero at three. Its primitive source at modulus five has value $-1$ at three. Indeed $3 equiv 2^3$ modulo five, so $(chi_5^2)(3)=-1$. The imprimitive series for the square is therefore the primitive series times $1+3^(-s)$. This cannot introduce a zero of positive real part, but it changes the uncentered ramp at all powers of three and the logarithmic derivative at one. An equality of centered prime sums using the two conventions would be incorrect even though the open-strip zero sets agree.

The distribution on the four cosets is $(4,3,3,3)/13$. For the trivial character the coefficient is one. For each of the other three characters it is $1/13$. In particular the character of conductor five in the table keeps its positive coefficient. The possibility of computing with all characters at a common large modulus on units is a convenience for finite group theory. The subsequent analytic comparison must specify the primitive source that supplies the prime weights at ramified primes. The release packages a primitive character together with its conductor for precisely this purpose.

For a general cyclic family, why do different powers fail to merge after primitive induction? If two primitive sources were equal, changing that primitive character to the common original level would yield the same character on its unit group for both powers. Since a generator has order $o$, exponents in $0,dots,o-1$ giving equal powers are equal. Conversely taking inverses commutes with primitive induction: any modulus carrying a character also carries its inverse, whence their conductors are equal, and the values on units agree after inversion. The retained family is therefore closed under inverse, contains the trivial primitive character, and contains the target itself. These are the closure properties needed to pass from its real statistic to a statement for the original complex character.

== Two auxiliary primes <c10s06>

Put $z=Y^(epsilon/5)$ for a base parameter $Y$. The construction takes primes $q,d$ with
$ q equiv 3 (mod 8), quad z/2<log q<=z, $
$ d equiv 7 (mod 16), quad z(log Y)^2/2<log d<=z(log Y)^2. $
In addition, $d equiv -1$ modulo $q$ and every odd prime $p<=z$. The primes avoid the fixed character modulus. The restrictions on $d$ have an arithmetic purpose. For example $p$ can be forced to have a prescribed quadratic behavior through the relation $d equiv -1$ modulo $p$. The residues at two separately control the signs there.

Write $chi_q$ and $chi_d$ for the quadratic characters given by the Jacobi symbols with denominators $q$ and $d$. Every unwanted character is induced by $psi^j chi_q^i chi_d^h$ with $(i,h)!=(0,0)$, $i,h in {0,1}$. The pair-selection theorem chooses $q,d$ so that the centered twisted sums of these characters are small and their logarithmic derivatives at one are controlled throughout a prescribed base range. This is a statement about auxiliary characters with conductors going to infinity. The bounds impose no analogous estimate on the original $psi$.

The proof of pair selection filters candidate primes twice. It first retains a positive proportion of the candidate $q$ with the desired bounds. For each retained $q$, it retains a positive proportion of the candidate $d$ in the requisite progressions, checking both twists involving $d$. The goodness conditions apply to the finitely many base characters at once. Moment and exceptional-set estimates and lower bounds for the candidate sets make each retained set nonempty. One can then choose a single pair for the whole requested range. The asymmetry between the two logarithmic sizes allows the congruence conditions involving $q$ to be imposed at the second stage.

== Quadratic reciprocity explains the two sign coordinates <c10s07>

In the pair conditions $q equiv 3$ modulo eight and $d equiv 7$ modulo sixteen. For an odd prime $p<=z$ different from $d$ the construction imposes $d equiv -1$ modulo $p$. The quadratic reciprocity law gives a concrete use of this condition. Since $d equiv 3$ modulo four,
$ (frac(p,d))=(frac(d,p))(-1)^((p-1)/2). $
Here parentheses with a prime denominator denote a Legendre symbol. Substituting $d equiv -1$ gives $(d/p)=(-1)^((p-1)/2)$ in ordinary Legendre-symbol notation. The signs cancel, so $(p/d)=1$. The condition $q divides d+1$ gives the same conclusion at $p=q$. In the opposite direction $(d/q)=(-1/q)=-1$ because $q equiv 3$ modulo four. The supplementary law at two gives $(2/q)=-1$ and $(2/d)=1$. These explicit values are useful when checking which candidate belongs to a prescribed Frobenius or inertia case.

For illustration take $q=3$ and $d=23$. They obey these congruences with each other. This small pair is used only to display the local symbols. The asymptotic assertion also imposes growing logarithmic size conditions. Write $chi_(q)(p)=(p/q)$ and $chi_(d)(p)=(p/d)$. Some values are

#align(center)[#table(columns: (auto,auto,auto,auto,auto,auto),align:center,inset:(x:6pt,y:3pt),stroke:none,
  table.hline(stroke:0.65pt), [$p$],[$2$],[$3$],[$5$],[$7$],[$23$],table.hline(stroke:0.35pt),
  [$chi_(q)(p)$],[$-1$],[$0$],[$-1$],[$1$],[$-1$],
  [$chi_(d)(p)$],[$1$],[$1$],[$-1$],[$-1$],[$0$],table.hline(stroke:0.65pt))]

At an unramified prime all entries are signs. The zero at its own conductor is different: for example $chi_(d)(23)=0$, so the quadratic local factor is deleted instead of taking either of the signs. In the host group the corresponding operation is averaging over an inertia coset. The characters which are nontrivial on inertia cancel in that average. This is the point at which the zero convention from elementary Dirichlet characters meets the geometric language of Chapter 13.

At a base character $xi$, the three extra twists have sign exponents $(1,0),(0,1),(1,1)$. If a prime $q$ is odd and coprime to the conductor of a primitive $xi$, the product of $xi$ with the quadratic character of conductor $q$ is primitive at the product conductor. On the two factors of the unit group it restricts to the original primitive characters. If a smaller conductor carried their product, restriction while keeping the other factor fixed would give a smaller conductor for at least one of them. This simple conductor argument explains why recovering the primitive representative is a reliable way to count candidates. The release also supplies the appropriate change-of-level results for characters originally presented at redundant moduli.

== A mean square controlling every point of an interval <c10s08>

The pointwise estimate needed from an auxiliary twist holds throughout a continuum of values $y$. A mean square over primes $q$ at one $y$ does not by itself prove that a single $q$ works at every $y$. The reduction from a continuum to a controlled set of bad primes is sufficiently elementary to derive here. The deeper input about the distribution of primes will appear only in the mean-square estimate.

For $Z>=1$ and complex coefficients $abs(kappa_m)<=1$, consider the finite sum
$ S_(q)(y)=sum_(1<=m<=Z) Lambda(m) kappa_m chi_(q)(m) min(1,frac(y,m)). $
This uses the capped kernel that occurs in the pair-selection argument. Each summand is continuous and affine on either side of $y=m$. Define the right derivative
$ D_(q)(v)=sum_(v<m<=Z) frac(Lambda(m) kappa_m chi_(q)(m),m). $
Adding the elementary integrals of the finitely many summands gives $S_(q)(y)-S_(q)(Y)=integral_Y^y D_(q)(v)dif v$ for $y>=Y$. The choice of derivative at finitely many endpoints has no effect on the integral. Let $P$ be a nonempty finite candidate set and let $2<=Y<=w_q<=W<=2Y$ for every $q in P$. The sampling point $w_q$ is allowed to be different for every candidate. Cauchy–Schwarz gives
$ abs(S_(q)(w_q))^2 <= 2abs(S_(q)(Y))^2+
        2Y integral_Y^W abs(D_(q)(v))^2 dif v. $
To obtain a derivative bound from a mean square for $S$, observe that $v D_(q)(v)$ is $S_(q)(v)$ with the coefficient sequence replaced by $kappa_m bold(1)_(m>v)$. On that support the capped kernel equals $v/m$. For a fixed $v$, this truncation is common to all $q$. It is therefore an allowed test sequence for the uniform mean-square hypothesis. Thus, if throughout the block it gives
$ sum_(q in P) abs(S_(q)(v))^2<=C v(log v) abs(P) $
for every such sequence, it also gives $sum_(q in P) abs(D_(q)(v))^2<=C (log v)frac(abs(P),v)$. Since $integral_Y^(2Y)1/v dif v=log 2<1$, summing the Cauchy–Schwarz inequality now yields
$ sum_(q in P) abs(S_(q)(w_q))^2<=4 C Y log(2Y) abs(P). $
The right side knows nothing about the individual choices of $w_q$. This uniformity is the decisive extra information obtained by controlling the derivative.

Let a candidate be bad if at some point of the block its modulus exceeds $y^(1/2+tau)/2$, with $tau>0$. For each bad candidate choose just one witnessing point. Its square contributes at least $Y^(1+2tau)/4$. The proportion of bad candidates on this block is at most
$ 16 C log(2Y) Y^(-2tau). $
For large $Y$ this is at most a constant depending on $C,tau$ times $Y^(-tau)$. For several dyadic blocks starting at $2^j Y$ the sum of the corresponding bounds is a geometric series in $2^(-tau)$. It tends to zero with the first endpoint, independently of the number of blocks. Hence a prescribed small bad proportion suffices on a whole range. The formal construction feeds this estimate a mean square produced by quadratic-character sums, and separately counts possible zero-box exceptions. A dyadic argument from one point alone, without the derivative estimate or another maximal inequality, would not justify selecting one prime for the full interval.

== Which objects depend on the window <c10s09>

The powers of $psi$, the reciprocal $1/(3o+1)$, and $F_psi$ have been chosen once. The primes, the growing cyclotomic layer, $H$, the top places, and their theta-lift data can all depend on the large scale. Orthogonality converts their output back to the *same* $F_psi$. If the analytic family could change when a new interval was chosen, a putative zero of the original character could disappear from the transform. The fixed coefficient calculation prevents this.

#example[Reading the statistic at two primes][Take the nontrivial character $psi$ modulo four from Chapter 4. Here $o=2$. The coset masses are $4/7$ and $3/7$, and their difference is $1/7$. Thus $F_(psi)(x)=G_(z)(x)+frac(1,7) G_(psi)(x)$. Before subtracting the centers, the coefficient of $Lambda(p^k) r_(p^k)(x)$ in this expression is $1+psi(p)^k/7$ at each odd prime $p$. At five it is $8/7$ for every $k$. At three it is $6/7$ for odd $k$ and $8/7$ for even $k$. At two the character vanishes and only the untwisted coefficient one survives.]

The same fraction has an analytic meaning. Imagine a zero $rho$ in the open strip of this character's $L$-function, of multiplicity $m$, where $zeta(rho)!=0$. Because the character is real, its real ramp already contains the entire pole. Proposition 8.1 gives the residue of the family transform as
$ -frac(m,7 rho(rho-1)). $
Every choice of auxiliary primes must recover that coefficient. The field used to produce one upper bound can have much higher degree than the field used for the next, yet both bounds test the same proposed zero.

== Two selections and their order <c10s10>

At the first stage a finite set $P_1$ of candidate primes $q$ is nonempty and a subset of size at least $(1-eta)abs(P_1)$ works for all the required base choices at that stage. For *each* retained $q$ the second candidate set $P_(2)(q)$ of primes $d$ is nonempty, and at least the same fraction survives the additional tests involving $d$. Taking $eta=1/2$ leaves a positive integer number of choices in each stage. Choose the first prime and then the second. An estimate averaged jointly over all pairs would require an extra argument to reach the same conditional conclusion when $P_(2)(q)$ varies with $q$.

One reason for the asymmetric order lies in the size of the congruence modulus. The choices of $d$ must include the congruence modulo the particular $q$ already retained as well as the congruences at small primes. Their product enters the progression within which potential $d$ are counted. The construction supplies lower bounds for the number of primes in the two sets and upper bounds for the bad part. Positivity of the final difference is what yields an eligible pair. The source theorem takes upper ranges $X<=Y^K$ and permits the larger logarithmic scale to vary between $z(log Y)^2$ and $K^(2z)(log Y)^2$. This flexibility is carried forward to the selection at an outer cohomological scale.

The analytic output has three distinct uses. It bounds the centered ramp of every unwanted twist by $y^(1/2+epsilon/2)$ on the selected base range, it bounds its logarithmic derivative at one by $4 log y$, and it excludes zeros of the specified real twists from a rectangle near the line one. The first estimate removes the extra characters after averaging. The second controls their linear centers under perturbation. The zero-free rectangle is used in the thin-weight, large-argument comparison. It is imposed on the auxiliary twists of the stated real base characters. Imposing the same square-root control on the original target at this stage would assume the estimate that the remaining construction has to produce.

#source-note[The fixed coefficients and primitive powers are defined in #src("Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions")[the level and share definitions]. The blockwise derivative estimate and bad-proportion argument are #src("Development.AutomorphicArithmetic.MeanSquareBounds.BadShare")[bad_share]. See also #src("Development.AutomorphicArithmetic.MeanSquareBounds.MeanSqAbs")[the character mean square], #src("Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim")[primitive twists], #src("Development.AutomorphicArithmetic.MeanSquareBounds.PairShare")[two successive positive proportions], and #src("Development.AutomorphicArithmetic.CharacterBoxes.PairGood")[the final good-pair conditions].]

#source-note[The positive weights are packaged in #src("Development.AutomorphicArithmetic.PrimitiveCosets.LevelFamily")[the level family]. The two-stage selection is implemented by #src("Development.AutomorphicArithmetic.MeanSquareBounds.PairExists")[the prime-pair existence theorem] and its #src("Development.AutomorphicArithmetic.MeanSquareBounds.pairEx")[character estimates].]
