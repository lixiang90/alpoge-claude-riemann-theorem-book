#import "style.typ": *
#chapter[The contradiction and the critical line]

== One family on arbitrarily late windows <c18s01>

Let $psi$ be primitive and keep its cyclic family fixed. Chapter 17 bounds $F_(psi)(x)$ at a physical point carrying the required host. To use the analytic criterion of Chapter 9, every point of an entire late interval must carry such a host. The arithmetic assertion to be proved is that for every fixed $psi$ and all sufficiently small $epsilon>0$,
$ forall Y_0, exists Y>=Y_0, forall x in [Y,Y^(3/2)],
          quad F_(psi)(x)<=x^(1/2+9epsilon). $
The function in this statement stays fixed across the choices of $Y$ and $x$. The auxiliary field and the dimensions of the word spaces can vary with $x$. We verify the required order of choices by following the prime pair and the field through the rescaling.

== Choosing an interval after all the thresholds <c18s02>

Fix the target $psi$ and an admissible $epsilon$. The prime-pair and cohomological thresholds may depend on these data. The prescribed lower endpoint of the physical interval can now be increased while keeping both thresholds fixed.

Let $u=2+8epsilon$ and let $c=c(psi)>=1$ be the fixed integer in the order $n=|H|=c dot 2^e$ of the auxiliary group. The full field degree is $[E:ℚ]=4n$, and the complex places in the chosen CM type number $f=2n$. Put $kappa=c^(1/u)$. Let $y$ be the requested starting position. The window theorem supplies a fixed $J>=1$. Denote by $Y_1$ the threshold for the auxiliary primes and by $X_0$ the cohomological threshold. Enlarge the lower bounds to include the fixed estimates at large scale. Choose
$ M=max(1,y,Y_1,kappa^3,kappa^400), quad X>=max(X_0,M^J), quad Y=X^(1/J). $
Then $Y>=M$. The auxiliary primes are chosen at this $Y$. Their estimates hold as far as $X$. The cohomological theorem, applied to this pair, gives $W>=Y$ with $W^2<=X$ and estimates on the whole raw interval $[W,W^2]$. In particular both ends of this interval are already inside the range where the pair can be used.

What scale does the theta construction see? For $Z=kappa W$, take $Z<=x<=Z^(3/2)$ and put $x'=x/kappa$. By $kappa^3<=W$,
$ W<=x'<=x<=(kappa W)^(3/2)<=W^2<=X. $
The two uses of the interval are now visible. The prime estimates apply at $x$. The cyclotomic layer is the one at $x'$. If its index is $e$, then
$ (x')^u<=2^e<=2(x')^u quad ==> quad x^u<=c 2^e<=2x^u. $
This computation puts the actual $n$ in the rank window at $x$, while the field still has the layer chosen at $x'$. The prime-pair datum has a second lower-bound requirement. Because $x<=X$ and $J>0$, one has $x^(1/J)<=X^(1/J)=Y$. Conversely $Y<=W<=x$. Hence the pair may be reused with $x^(1/J)<=Y<=x$, and its character bounds on the closed interval $[Y,X]$ restrict to $[Y,x]$. The zero boxes depend on $Y$ and the auxiliary primes, so reducing the upper endpoint of the character interval preserves them as well. #src("Development.AutomorphicArithmetic.CharacterBoxes.TwistForm")[All six fields of the common window datum.] #src("Development.AutomorphicArithmetic.CharacterBoxes.PairGood")[Monotonicity in its upper endpoint.]

The exponent of the twist cutoff has one unit of room. Since $x'>=W>=kappa^400$,
$ floor(x^400)<=floor((x')^401), quad
  sqrt(exp((x')^epsilon))<=sqrt(exp(x^epsilon)). $
The first inequality follows by multiplying $kappa^400<=x'$ by $(x')^400$ and taking floors. The bound from Chapter 16 therefore applies through the physical cutoff. The actual rank parameter $t$ still has to satisfy $t<=floor(x^400)$. Appendix A.3 derives this from the defining rank identity, including the rounded term of size $x^377$. It follows that the positive twists $1<=j<t$ for this very host are among the twists for the raw field estimate. The cohomology theorem supplies both finiteness and the bound for every finite prime subtotal. Restriction to fewer twists and enlargement of the budget preserve both clauses. #src("Development.AutomorphicArithmetic.CharacterBoxes.WinPairs")[Choice of the scales and witnesses.] #src("Development.AutomorphicArithmetic.ShortNorms.supplyOfAdmOf")[Specialization to the host field and its actual rank.]

#figure(image("scale-transfer.svg", width: 93%),caption: [Interval containment in the coordinate $frac(log x,log kappa)$ when $kappa>1$ and $W=kappa^4$. Dividing physical points by $kappa$ translates the middle segment one unit to the left. The additional requirement $W>=kappa^400$ is used for the twist cutoff.])

The choice $W=kappa^4$ in the picture displays the geometry of the endpoints. When $kappa=1$, the two variables agree and the endpoints need no rescaling. The proof nevertheless uses the same physical interval $[W,W^(3/2)]$. It is enough for the analytic contradiction, and it gives a single width for every fixed family.

== One field must satisfy both estimates <c18s03>

It is helpful to follow one witness through the proof. A prime pair and a layer define a particular field and its Galois action. The field gives a group mapping to the fixed cyclic quotient attached to $psi$. After the ranks have been chosen, one must supply within this same object the top places, the separated weights, and the integral data. One cannot first find a field with favorable class groups and independently take the best Fourier weights found on some other field. Here the top places are constructed on the prescribed input field. Forgetting the new top data recovers the original object.

This is an equality of mathematical witnesses, not just a comparison of their sizes. To see why it has content, suppose two possible lattices have numerical invariants $(P,Q)$ equal to $(0,2)$ and $(2,0)$. Each coordinate achieves a lower bound of zero, and both minima are realized. There is no lattice in this family on which the sum of the coordinates is zero. An estimate for the sum which substituted the individual minima would be false. In the proof the same issue arises when the analytic quality of a host and the cohomological quality of its field enter the same inequality for a prime sum.

The following choices occur at different points of the argument. They can be read in order without identifying any of the three averaging sets.

#table(columns:(1fr,2.5fr),inset:(x:4pt,y:3pt),stroke:none,
table.hline(stroke:0.65pt),[*Stage*],[*Data and dependence*],table.hline(stroke:0.35pt),
[Before the window],[Fix $psi$, the finite Fourier coefficients, $epsilon$, the multiplier $c$, and the exponent $J$.],
[For one window],[Choose the outer scale and a good pair of primes. The proof of the existence theorem uses this pair throughout the interval.],
[At one physical point],[Choose the layer at $x/kappa$ and the associated field. Choose ranks, places, lattices and weights on that field.],
[At one translate],[Average over words in the lift construction. The estimates on both losses apply at this particular translate.],
[Across translates],[Average the resulting inequality over the subgroup that preserves the prescribed cosets. Orthogonality singles out the fixed characters.],
table.hline(stroke:0.65pt))

The field and the finite averaging sets may change when $x$ changes. Their output is always an inequality for the same explicit real function $F_(psi)$, with the same coefficients. In the opposite direction the pole calculation concerns that fixed function before the arithmetic choices are made. This is exactly where a family chosen anew at each scale would prevent the two halves of the proof from meeting. #src("Development.AutomorphicArithmetic.CharacterBoxes.HostOfField")[Extension of a given host and joint conclusion.] #src("Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion")[Use of the common Galois input.]

== Excluding a zero <c18s04>

#proof[Suppose a member of the family has a zero $rho$ with $1/2<beta=Re rho<1$. Choose $theta$ strictly between $1/2$ and $beta$, and then choose $epsilon$ small enough for all the construction theorems, with $epsilon<1/52$ and $9epsilon<theta-1/2$. On the arbitrarily late windows the upper bound from Chapter 17 implies $F_(psi)(x)<=x^theta$. By Theorem 9.1 with $delta=1/2$ this excludes the supposed zero. Since $psi$ is one of its own retained characters, every primitive Dirichlet character is covered. Absolute Euler-product convergence handles $Re s>1$, and classical nonvanishing at $Re s=1$ handles the boundary away from a principal pole.]

== Testing the sign and the order of the contradiction <c18s05>

Write $I_Y=[Y,Y^(3/2)]$. The exact negation of the window inequality $forall Y_0, exists Y>=Y_0, forall x in I_Y, F_(psi)(x)<=x^theta$ is
$ exists Y_0, quad forall Y>=Y_0, quad exists x in I_Y, quad F_(psi)(x)>x^theta. $
The witness in each late interval must have positive excess. An arbitrarily large negative value still satisfies the upper bound.

For a numerical test of all the strict inequalities, take $beta=1/2+1/4000$. Let $theta=1/2+1/8000$. If the construction is valid for $0<epsilon<epsilon_(0)$, put $epsilon=min(10^(-6),epsilon_(0)/2,1/104)$. Then $epsilon>0$, $epsilon<1/52$, and $9epsilon<=9 dot 10^(-6)<1/8000$. At $x>=1$ raising $x$ to $1/2+9epsilon$ gives at most $x^theta$. The difference $beta-theta$ is available to the pole argument and the difference $theta-1/2-9epsilon$ to the arithmetic estimate. No uniform lower bound for either difference as $beta$ tends to one half is required.

Replacing “every point” by “some point” would change the criterion even for a smooth function. Put $B(x)=x^(theta)(1+sin^(2)(pi log_2 x))$ for $x>1$. At each $x=2^k$ the inequality $B(x)<=x^theta$ holds with equality. Yet for every $Y>=4$ the interval $[log_2 Y,(3/2)log_2 Y]$ has length at least one. It contains a half-integer $k+1/2$, so that $x=2^(k+1/2)$ lies in the corresponding physical interval and has $B(x)=2x^theta$. Thus one good point past every threshold can coexist with a strict violation on every late window.

== Primitive, imprimitive, and untwisted conclusions <c18s06>

For an arbitrary character $chi$ modulo $N$, take its primitive inducing character $chi^*$. At $Re s>0$ every extra factor $1-chi^(*)(p)p^(-s)$ for $p divides N$ and $p nmid op("cond")(chi^*)$ is nonzero. Thus right-half-plane nonvanishing holds for $chi$ wherever the continued function has no principal pole. If $chi^*$ has a zero in the open critical strip strictly to the left of the middle line, its functional equation supplies a right-half-plane zero of the conjugate primitive character. The same finite factors transfer the resulting open-strip statement to $chi$. This proves Theorem 7.2, including its primitive specialization.

For $zeta$, the character of conductor one, a nontrivial zero in the open strip must now have real part $1/2$. For completeness, at $Re s<0$ use
$ zeta(s)=2^s pi^(s-1)sin(pi s/2)Gamma(1-s)zeta(1-s). $
The gamma factor is finite and nonzero, and the last factor has absolutely convergent nonzero Euler product. The only possible zeros there come from the sine, at $-2,-4,dots$. At $Re s=0$ and $s!=0$ the reflected zeta value lies on the classically zero-free line at a point other than one, and the other factors are nonzero. At zero one has $zeta(0)=-1/2$. The point one is its simple pole. This proves Theorem 7.1 in the form that excludes exactly the negative even integers and the pole.

== What carried the square root <c18s07>

The factor $x^rho$ from an isolated Mellin pole fixes what size of error can detect that zero. The finite Fourier average ensures that zeros of different characters cannot cancel at a common pole. The integral calculation buys a factor of $m$ through divisibility at $m$ steps, while the overlap and rank costs grow with $m$. Balancing these effects leaves $x^(1/2+9epsilon)$ after all normalizations. The cohomological selection provides enough places on the logarithmic axis where this comparison works simultaneously. A positive margin between $1/2$ and any proposed right-hand zero determines how small $epsilon$ must be before the arithmetic construction is applied.

== Returning to the count in Riemann's paper <c18s08>

We can now answer quantitatively the prime-counting question with which the book began. The classical argument below uses an integrated explicit formula and the zero-counting bound developed after Chapter 6. It is a consequence of the zero statement. Its proof also explains why removing a smoothing from a prime count costs logarithms.

Write $Psi(x)=sum_(n<=x)Lambda(n)$ and
$ I(x)=integral_1^x Psi(u) dif u=sum_(n<=x)(x-n)Lambda(n). $
Interchange of sum and integral is immediate because only finitely many indices contribute. The linear weight makes the formula continuous even when $x$ is a prime power. Mellin inversion gives a factor $1/(s(s+1))$. In the integrated explicit formula the pole at one contributes $x^2/2$, and the nontrivial zeros, counted with multiplicity, contribute
$ I(x)=x^2/2-sum_rho frac(x^(rho+1),rho(rho+1)) + C_1 x + O(1) quad (x>=2). $
Here $C_1=-log(2pi)$. The constant contribution and the convergent terms from the negative even zeros are bounded in this range. The sum over the nontrivial zeros is absolutely convergent. A convenient published form uses the same kernel and absorbs the bounded terms in an explicit error. #link("https://sites.unimi.it/molteni/research/papers-pdf/36-molteni-Primes_in_explicit_short_intervals_on_RH.pdf")[Dudek, Grenié and Molteni, §1.]

Put $rho=1/2+i gamma$. From $N(T)=O(T log(2T))$ and conjugation one obtains for $T>=2$
$ sum_(abs(gamma)<=T) frac(1,abs(rho))=O(log^(2)(2T)), quad
  sum_(abs(gamma)>T) frac(1,abs(rho(rho+1)))=O(frac(log(2T),T)). $
For the first estimate group ordinates into blocks $2^j<abs(gamma)<=2^(j+1)$. There are at most a constant times $2^(j)(j+1)$ in one block, and each summand is at most $2^(-j)$. Summing up to $log_2 T$ gives the square of a logarithm. The finitely many ordinates of absolute value at most one have bounded contribution. For the second estimate use blocks starting at $T,2T,4T,dots$. The $j$th contribution is at most a constant times $(log(2T)+j)/(2^j T)$. A convergent geometric series and its derivative give the stated tail estimate.

For $x$ large let $h=sqrt(x)$, so $x/2<=x-h<x+h<=2x$. By monotonicity,
$ frac(I(x)-I(x-h),h)<=Psi(x)<=frac(I(x+h)-I(x),h). $
The main terms of these quotients are $x-h/2$ and $x+h/2$. For zeros of height at most $T$, apply the fundamental theorem of calculus to each term. On the entire interval the derivative of $u^(rho+1)/(rho(rho+1))$ has absolute value $frac(sqrt(u),abs(rho))$. Hence the low zeros cost $O(sqrt(x)log^(2)(2T))$ in either quotient. For the high zeros, bound the two endpoint values without differentiating and use the second sum. Their total cost is
$ O(frac(x^(3/2),h) frac(log(2T),T)). $
Now set $T=x/h=sqrt(x)$. The high zeros cost $O(sqrt(x)log x)$, the main-term displacement costs $O(sqrt(x))$, and the linear term in $I$ costs $O(1)$. Both quotients therefore give
$ Psi(x)=x+O(sqrt(x)log^2 x). $
There is a reason to split the series before differentiation. Differentiating every term would leave a sum of absolute values comparable to the divergent series of reciprocal zero heights. Grouping by height separates the bounded interval over which differentiation is profitable from the tail where two powers in the denominator are needed.

Write $vartheta(x)=sum_(p<=x)log p$. Chapter 1 gives $vartheta(u)=O(u)$ and
$ Psi(x)-vartheta(x)=sum_(k=2)^floor(log_2 x) vartheta(x^(1/k)). $
The square terms cost $O(sqrt(x))$, and the higher terms cost $O(x^(1/3)log x)=O(sqrt(x))$ as $x$ tends to infinity. Thus $vartheta$ satisfies the same estimate as $Psi$. Partial summation now gives
$ pi(x)=frac(vartheta(x),log x)+integral_2^x frac(vartheta(t),t log^2 t) dif t. $
Substitution of $vartheta(t)=t+O(sqrt(t)log^2 t)$ gives an endpoint error $O(sqrt(x)log x)$ and an integral error $O(integral_2^x t^(-1/2) dif t)=O(sqrt(x))$. The main terms differentiate to $frac(1,log x)$. Choosing $op("Li")(x)=integral_2^x frac(dif t,log t)$, their fixed difference at two can be absorbed into the error. We obtain the classical von Koch estimate
$ pi(x)=op("Li")(x)+O(sqrt(x)log x). $
The original conjecture was about the real parts of complex zeros. This consequence is about ordinary prime counts at every sufficiently large real $x$. Its uniformity follows here from the explicit formula after the zeros have been located. The good intervals used to locate them were required only at arbitrarily late positions. #link("https://zenodo.org/records/2347595")[Von Koch's 1901 paper.]

== What the Dirichlet conclusion measures <c18s09>

Suppose $q>=1$ and $a$ is coprime to $q$. Let $Psi(x";"q,a)$ count the terms $Lambda(n)$ with $n<=x$ and $n equiv a mod q$. Expanding the indicator of $a$ in the character table of $(ℤ slash q ℤ)^times$ gives the exact finite identity
$ Psi(x";"q,a)=frac(1,varphi(q)) sum_(chi mod q) overline(chi(a)) Psi(x,chi), quad
 Psi(x,chi)=sum_(n<=x)chi(n)Lambda(n). $
Every character is extended by zero on nonunits. A nonunit integer can contribute to neither side because $a$ is a unit. For a unit $n$, the inner character sum equals the size of the group if $n equiv a$ and vanishes otherwise. Thus there is no error term in this change of coordinates.

The principal term removes certain prime powers from $Psi(x)$. Indeed, with $chi_0$ principal, one has
$ Psi(x)-Psi(x,chi_0)=sum_(p divides q) floor(frac(log x,log p)) log p <= omega(q)log x, $
where $omega(q)$ counts the distinct prime divisors. The main term $frac(x,varphi(q))$ in a reduced residue class comes from this one character. Nonprincipal character transforms have no pole at one. Their open-strip zeros lie on the middle line by the Dirichlet conclusion, and for a fixed modulus the explicit formula can be applied to each of the finitely many primitive inducing characters. Recovering an imprimitive sum removes only the powers of primes dividing the modulus. The constants in such a fixed-modulus argument may depend on $q$. Bounds for a varying modulus require tracking that dependence in the zero count and in the conductor terms.

Here is an extra point in passing from the integrated formula to a sharp character sum. For a complex character the partial sums have no monotonicity. Nevertheless, if $x<=u<=x+h$ with $1<=h<=x$, the difference between the sharp sums at $u$ and $x$ has absolute value at most $(h+1)log(2x)$. Indeed at most $h+1$ new integer arguments appear and each coefficient has modulus at most $log(2x)$. Averaging in $u$ yields
$ abs(Psi(x,chi)-frac(I_(chi)(x+h)-I_(chi)(x),h))<=(h+1)log(2x), $
where $I_(chi)(x)=sum_(n<=x)(x-n)chi(n)Lambda(n)$. The error with $h=sqrt(x)$ is admissible even though there is no order relation between the complex numbers.

For a fixed primitive character the classical integrated explicit formula has the same nontrivial-zero sum as before, with its own zeros. There is a quadratic term only for the principal character. The residues at zero and minus one can include logarithms if a trivial zero coincides with a denominator zero. Even the coarse bound $O_(q)(x log(2x))$ for the aggregate of these elementary terms suffices here, since division by $h$ gives $O_(q)(sqrt(x)log(2x))$. The count of zeros through height $T$ is $O_(q)(T log(2T))$ for fixed conductor. The same low- and high-zero estimates then give an error $O_(q)(sqrt(x)log^(2)(2x))$ for the sharp sum. Finite Euler-factor omissions add at most $omega(q)log x$. Substitution in the exact character identity gives
$ Psi(x";"q,a)=frac(x,varphi(q))+O_(q)(sqrt(x)log^(2)(2x)). $
This argument keeps $q$ fixed from the outset. Explicit dependence on conductor and height is a further quantitative problem. #link("https://arxiv.org/abs/2003.01925")[Ernvall-Hytönen and Palojärvi on explicit progression estimates.]

One can also read off the contribution of a pair of complex characters without an estimate. Take $q=5$, choose $2$ as generator, and let $chi(2)=i$. The values of $chi$ at the successive powers $1,2,4,3$ are $1,i,-1,-i$. In the difference between the counts at $2$ and $3$ the trivial and quadratic characters disappear because these two units have the same quadratic sign. Fourier inversion, or the character table itself, gives
$ Psi(x";"5,2)-Psi(x";"5,3)=Im Psi(x,chi). $
For instance the coefficient of a prime power congruent to two is one on each side, and for a power congruent to three it is minus one. Counts of actual primes follow from removing higher powers and then logarithmic weights, just as in the preceding section. The elementary character table introduced near the start of the book can therefore single out a concrete discrepancy in the distribution of primes for which the final zero theorem gives a square-root-scale estimate.

#source-note[The compatible supply is #src("Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi")[supplyChi]. The choice of constants appears in #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape")[the global shape theorem]. The final assembly is #src("Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion")[MainConclusion], followed by #src("Formalism.GammaFactorNonvanishing.CritLine")[reflection] and #src("Main")[the public theorem statements].]
