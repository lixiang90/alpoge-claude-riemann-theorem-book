#import "style.typ": *
#chapter[A prime sum with a Mellin transform]

== The ramp and its center <c08s01>

For a nonprincipal character $chi$ of positive modulus put
$ S_(chi)(x)= sum_(n<=x) Lambda(n)chi(n)(x/n-1). $
The notation includes all positive prime powers. At an integer endpoint the newly included term is zero, so $S_chi$ is continuous and piecewise linear. Suppose first that $Re s>1$. A change of variable and two elementary integrals give
$ integral_n^infinity (x/n-1)x^(-s-1) dif x
       = n^(-s)(1/(s-1)-1/s) = n^(-s)/(s(s-1)). $
Absolute convergence permits termwise integration. The logarithmic derivative of the Euler product now yields
$ integral_1^infinity S_(chi)(x)x^(-s-1) dif x
       = - (L'(s,chi))/(L(s,chi)s(s-1)). $
Thus the price of the smoothing is exactly the denominator $s(s-1)$. Its two simple factors will also determine the sign of the contribution from a real zero.

For $chi$ nonprincipal, $L(1,chi)$ is finite and nonzero. The pole contributed at one by the displayed expression has residue $-frac(L'(1,chi),L(1,chi))$. Adding a multiple of $x$ cancels it. Write
$ g_(chi)(x) = S_(chi)(x) + x frac(L'(1,chi),L(1,chi)),
    quad G_(chi)(x)=Re g_(chi)(x). $
The principal case requires two terms. Write $S_1$ for the untwisted ramp sum, with the primitive character of conductor one. If $h=s-1$, the Laurent expansions are
$ -frac(zeta'(1+h),zeta(1+h))=1/h-gamma+O(h),
    quad 1/((1+h)h)=1/h-1+O(h). $
Their product starts with $h^(-2)-(1+gamma)h^(-1)$. Since $x log x$ and $x$ transform into $(s-1)^(-2)$ and $(s-1)^(-1)$, respectively, the centered untwisted sum is
$ G_(z)(x) = S_(1)(x)-x log x+(1+gamma)x. $
This fixes the sign of the Euler constant and the linear term. A sign error here would leave a singularity at one even in the absence of any zero.

== A computation with prime powers <c08s02>

At $x=5$ the positive contributions to $S_(1)(5)$ come from $2,3,4$. The term at $5$ has just turned on. Hence
$ S_(1)(5) = (3/2+1/4)log 2 + (2/3)log 3. $
The contribution at $4$ has weight $log 2$. Replacing the sum over prime powers by a sum over primes changes the logarithmic derivative and destroys the transform identity. The identity also explains why smoothing is valuable. Each of the discontinuities in the sharp count has become just a change of slope.

#figure(image("ramps.svg", width: 94%), caption: [The untwisted sum up to $x=11$. The dashed lines show three of its individual contributions.])

== The sharp count hidden in the ramp <c08s03>

Write $a_n=Lambda(n)chi(n)$, and at first allow any coefficients satisfying $abs(a_n)<=log n$ for $n>=2$, with $a_1=0$. Define two step functions, including the endpoint in each sum,
$ A(x)=sum_(n<=x) frac(a_n,n), quad B(x)=sum_(n<=x) a_n. $
The ramp satisfies two exact identities:
$ S(x)=x A(x)-B(x)=integral_1^x A(t) dif t. $
The first identity follows by expanding each summand. For the second, fix a finite endpoint $x$. The term $a_n/n$ is present in $A(t)$ for exactly the subinterval $[n,x]$, of length $x-n$ if $n<=x$. Integration hence gives $a_(n)(x/n-1)$. This is a finite calculation; the endpoint convention at an integer has no effect on its integral.

For $m<x<m+1$ the derivative $S'(x)$ equals $A(m)$. At a positive integer $m$ the jump in the derivative is $a_m/m$. Thus a continuous, piecewise affine graph records *all* the original coefficients. One can recover $a_m$ as $m$ times the change of slope at $m$. Only the terms at prime powers produce corners for the arithmetic coefficients. When $chi$ is complex the graph is a curve in the complex plane, and the slope formula still holds as a complex identity.

Partial summation expresses $A$ by means of the more familiar sharp count $B$. For each $n<=x$, write
$ frac(1,n)=frac(1,x)+integral_n^x frac(dif t,t^2). $
Multiply by $a_n$ and sum. This gives
$ A(x)=frac(B(x),x)+integral_1^x frac(B(t),t^2) dif t, quad
  S(x)=x integral_1^x frac(B(t),t^2) dif t. $
The two terms containing $B(x)$ cancel exactly in the second formula. For the trivial character, $B$ is the Chebyshev prime-power count. Inserting the model $B(t)=t$ gives $x log x$. For a nonprincipal character there is no constant-density term in the sharp count, but the integral of its fluctuations can still yield a linear term in $S(x)$. The value of the logarithmic derivative at one identifies the correct linear term. Merely removing $x log x$ from the untwisted ramp, or removing nothing from a twisted ramp, would leave just such an unwanted contribution.

#example[A negative ramp from ordinary primes][Take the nontrivial real character modulo four and $x=6$. Powers of two make zero contribution. The prime three contributes $-log 3$ and the prime five contributes $(log 5)/5$, so the total is negative. On $5<x<7$ the slope is $-(log 3)/3+(log 5)/5$. At seven it changes by $-(log 7)/7$. These signs come from the character, while the ramp multiplier $max(x/n-1,0)$ is nonnegative throughout. Thus a bound above for a sum of such ramps cannot be turned into a bound for the sum of the magnitudes of its terms.]

The two ways to write the smoothing explain the scale of the final problem. Smoothing integrates a step function and suppresses the discontinuity at a prime. Its Mellin multiplier must therefore decay more rapidly along a vertical line than the multiplier of an unsmoothed count. At the same time each individual coefficient can still be recovered from a local change of slope. The multiplication by $x$ in the integral of $B(t)t^(-2)$ is also why the linear normalization has to be exact.

== Absolute convergence and the contour for one ramp <c08s04>

Set $sigma=Re s>1$. For a single $n>=1$ the real integral of the absolute value of its kernel is exactly
$ integral_n^infinity (frac(x,n)-1)x^(-sigma-1) dif x
  =frac(n^(-sigma),sigma(sigma-1)). $
Both terms converge at infinity. Since $a_n$ may be complex, this *real* integral, with $sigma$ in both denominators, provides the domination needed to exchange sum and integral. Its sum weighted by $abs(a_n)$ is bounded by a fixed multiple of $sum_(n>=2)(log n)n^(-sigma)$. To verify convergence, take $0<eta<sigma-1$ and use $log n<=n^eta/eta$. This proves absolute summability. It also gives domination locally uniformly as $s$ varies in any closed smaller half-plane $Re s>=1+delta$ with $delta>0$.

With interchanges justified, the calculation for complex $s$ yields
$ integral_1^infinity S(x)x^(-s-1)dif x
     =frac(1,s(s-1)) sum_(n>=1) frac(a_n,n^s). $
For the arithmetic sequence one obtains the logarithmic derivative by differentiating the local geometric logarithms on compact subsets of this half-plane. More explicitly,
$ -frac(L'(s,chi),L(s,chi))
  =sum_p sum_(k>=1) chi(p)^k (log p) p^(-k s). $
The derivative multiplies $p^(-k s)/k$ by $-k log p$, which removes the divisor $k$. This explains why $Lambda(p^k)$ has value $log p$ independent of $k$. Inserting $log(p^k)$ instead would weight the higher powers too heavily.

The inverse transform for a *single* ramp clarifies why two neighboring poles of the kernel occur. Fix $c>1$ and $u>0$. Consider the absolutely convergent vertical integral
$ K(u)=frac(1,2 pi i) integral_(c-i infinity)^(c+i infinity)
            frac(u^s,s(s-1)) dif s. $
For $u>1$ move the line left. In a rectangle between $c$ and a fixed $-M$, the horizontal edges have length $M+c$ and integrand of size $O_(M,c,u)(T^(-2))$ at ordinate $T$. Their contribution tends to zero as $T$ tends to infinity. The residues at one and zero are $u$ and $-1$. The remaining vertical integral tends to zero as $M$ tends to infinity. Indeed $u^(-M)$ tends to zero, and the integral of $abs(s(s-1))^(-1)$ on this line is $O(1/M)$. Hence $K(u)=u-1$. For $u<1$ move to $Re s=M>c$ instead. There are no crossed poles and $u^M$ tends to zero, giving $K(u)=0$. At $u=1$ either rectangle works, since the vertical integral is still $O(1/M)$ and the two residues sum to zero. Thus
$ K(u)=max(u-1,0) $
including at the corner. Reading the same result in the opposite direction gives the kernel formula for $x/n$. A step function in Perron's formula generally requires a half-value convention at the jump. The ramp is continuous there, and this elementary contour calculation exhibits the convention directly.

One may substitute $u=x/n$ and sum the inverse formula on $Re s=c$. The absolute integral is bounded by a constant times $x^c sum_n abs(a_n)n^(-c)$, so this substitution is legitimate for each fixed $x$. It recovers
$ S(x)=frac(1,2 pi i) integral_(c-i infinity)^(c+i infinity)
        -frac(L'(s,chi),L(s,chi)) frac(x^s,s(s-1)) dif s. $
Moving this *whole* contour far left would require control of the logarithmic derivative uniformly along a sequence of horizontal and vertical contours and a prescription for summing infinitely many zeros. The argument in this book uses the local singularities of the transform. It deliberately avoids relying on the absolute convergence of an infinite residue expansion obtained by shifting this last contour.

== A single formula regular at one <c08s05>

The two center calculations can be organized as a divided difference. For a nonprincipal character put $U(s)=L(s,chi)$ and $kappa=0$. For the trivial character of conductor one put $U(s)=(s-1)zeta(s)$, continuing it at one, and $kappa=1$. In both cases $U$ is holomorphic and nonzero at one. Put $D(s)=frac(U'(s),U(s))$ near one. For the zeta case, $U(1)=1$ and $D(1)=gamma$, as seen from $zeta(1+h)=h^(-1)+gamma+O(h)$. In either case the transform of the centered ramp can be written away from zeros, zero and one as
$ Phi(s)=frac(-D(s)+s D(1)+kappa(s-1),s(s-1)). $
For a nonprincipal character this is the sum of its uncentered transform and $frac(D(1),s-1)$. For the zeta case first use $zeta'/zeta=D-1/(s-1)$. Subtract the transform of $x log x$ and add that of $(1+gamma)x$. The apparent double-pole terms combine to $-1/(s(s-1))$, leaving exactly the numerator displayed above.

Let $s=1+h$. Taylor's theorem gives $D(1+h)=D(1)+h D'(1)+O(h^2)$. The numerator of $Phi$ becomes $h(D(1)-D'(1)+kappa)+O(h^2)$. More strongly, holomorphy of $D$ shows that the numerator divided by $h$ extends holomorphically. Therefore
$ Phi(1)=D(1)-D'(1)+kappa. $
No bound for primes has been assumed in identifying this value. The only inputs were continuation and nonvanishing at one for the relevant $U$. The finite value is not needed numerically, but its existence asserts that the main term has been completely removed. A small error in the coefficient subtracted from the ramp cannot be absorbed by any later choice of $epsilon$: changing the coefficient of $x$ by $h_0$ inserts $h_0/(s-1)$ in the transform.

At a zero $rho$ with $0<Re rho<1$, both $s$ and $s-1$ are units in the local ring of analytic germs at $rho$. If the order of $U$ there is $m$, write $U(s)=(s-rho)^m V(s)$ and $V(rho)!=0$. Taking a logarithmic derivative in a punctured disk gives $D(s)=m/(s-rho)+frac(V'(s),V(s))$. Write $Q(s)=-1/(s(s-1))$. The product of the pole with $Q$ can itself be decomposed,
$ frac(m Q(s),s-rho)=frac(m Q(rho),s-rho)
        +m frac(Q(s)-Q(rho),s-rho). $
The second term extends holomorphically because it is a divided difference. We have now produced the *whole local decomposition* used later, a principal part and a function holomorphic in a neighborhood. Knowledge only of the order of magnitude $O(frac(1,abs(s-rho)))$ would not determine the leading derivatives or the sign of the real residue.

#example[Sign and height][At a hypothetical real zero $beta=3/4$ the coefficient $Q(beta)$ is $16/3$. At a nonreal point $rho$ the denominator has a phase. Distinct positive multiplicities at the same $rho$ multiply the same complex number $Q(rho)$, so they point in the same direction in the complex plane. At different zeros the complex numbers can have quite different phases. The next chapter arranges to isolate one of them before comparing magnitudes.]

== Passing from a complex character to a real observable <c08s06>

Real parts commute with addition and integration against a real measure, but the weight $x^(-s-1)$ is complex for nonreal $s$. Thus one cannot move the symbol $Re$ outside the Mellin integral while keeping $s$ unchanged. To make the issue explicit, let $H$ be a complex function whose transform $M(s)$ is absolutely convergent for $Re s>c$. Direct conjugation under the integral shows that the transform of $overline(H)$ is
$ M^(sharp)(s)=overline(M(overline(s))). $
Consequently the transform of $Re H$ is $(M(s)+M^(sharp)(s))/2$. Both terms are holomorphic where the original transform is holomorphic. For example, if $M$ has a power series at $overline(rho)$, conjugating the coefficients gives a power series for $M^sharp$ at $rho$. Applying $Re$ to the numerical value $M(s)$ would instead produce a function that is generally not holomorphic.

For the arithmetic ramps, the identity $overline(g_(chi)(x))=g_(overline(chi))(x)$ holds for real $x$. For the prime terms it follows coefficient by coefficient. For the linear term differentiate $L(s,overline(chi))=overline(L(overline(s),chi))$ at the real argument one. This last statement follows either from the local power series or by taking a real increment in the complex derivative. Thus the contribution of $Re g_chi$ at $rho$ is one half the sum of the orders at $rho$ for $chi$ and its conjugate, multiplied by $Q(rho)$. For real $rho$ the two orders agree. For nonreal $rho$ it is enough that one of them is positive.

Now take a finite index set $I$, characters $chi_i$ admitted by the center convention and positive real coefficients $a_i$. At a possible pole define
$ M_rho=frac(1,2) sum_(i in I) a_i
       (op("ord")_(rho) L( dot,chi_i)+op("ord")_(rho) L(dot,overline(chi_i))). $
The orders in this formula refer to points of the open strip, so they are nonnegative integers; regular nonzero values have order zero. Hence $M_rho>=0$. It is strictly positive if any selected function vanishes there. One may repeat a character or give conjugate members different positive coefficients. Neither operation hides a zero. When $rho$ is real, $M_rho Q(rho)$ is a strictly positive real number. If coefficients of both signs had been admitted, the list consisting of the same character twice with coefficients $1$ and $-1$ would have zero transform. Positivity of the coefficients controls the residues even though it does not control the sign of the real ramp pointwise.

The zero set in a bounded region with compact closure inside $Re s>0$ is finite. To see this for one character, local holomorphy and nonidentity give isolated zeros. At a pole multiply by the appropriate local factor to obtain a nonzero holomorphic value. If a compact region contained infinitely many distinct zeros, a convergent subsequence would contradict one of these local statements. A finite union across the selected characters and their conjugates still has this property. We can therefore isolate a pole near an arbitrary proposed height without limiting the height in advance. This local finiteness is the compactness input in Chapter 9.

== Local singularities of the real family <c08s07>

#claim[Proposition 8.1][Take finitely many characters of positive modulus, each nonprincipal or of modulus one. Form $F(x)=sum_i a_i G_(chi_i)(x)$ with $a_i>0$, using the untwisted center for modulus one. Its Mellin transform is meromorphic on $Re s>0$ and holomorphic at one. Every zero of a member in $0<Re s<1$ gives a simple pole. Each such pole on the real axis has positive residue.]

#proof[By #link(<c08s05>)[§8.5], a zero of multiplicity $m$ of one complex member contributes $m Q(rho)$ to the residue, where $Q(rho)=-1/(rho(rho-1))$. Real projection adds the multiplicity of the conjugate character and divides the result by two, as in #link(<c08s06>)[§8.6]. Thus the residue for $F$ is $Q(rho)$ times a positive real number whenever a selected member vanishes. Coincident zeros increase this coefficient and the pole remains simple. At a real zero $0<rho<1$, $Q(rho)>0$. Holomorphy at one follows from the centering identity for each summand.]

For a real character with a double zero at $rho$, its summand with coefficient $a>0$ has residue $2a Q(rho)$. If a second real character has a simple zero there and weight $b>0$, the combined residue is $(2a+b)Q(rho)$. This is how the order of a zero is recorded in a simple pole. The individual centered sums may still take either sign as $x$ varies.

== Controlling the ramp away from a good interval <c08s08>

For all $x>=1$ and every character,
$ abs(S_(chi)(x))<=x sum_(2<=n<=x) frac(log n,n)
                 <=x (log x)(1+log x). $
The second step uses $sum_(n<=x)1/n<=1+log x$. Adding either center changes the right side by at most a fixed multiple of $x(1+log x)$. Thus the fixed family's real sum satisfies a polynomial times $x$ upper bound in absolute value. Substituting $x=exp u$, we obtain $abs(F(exp u))<=C exp(2u)$ for $u>=0$ after increasing $C$. This rough estimate has a different job from the much sharper arithmetic inequality of later chapters. It controls the tails of a localized integral outside the chosen window, and it holds on the entire positive half-axis in $u$.

A related estimate allows a small change of the weight before summing over a very large collection of places. Fix $a>0$ and let $H(w)=w S_(chi)(a/w)$, $w>0$. The equality
$ H(w)=sum_(n<=a/w) a_n max(a/n-w,0) $
shows where all its corners lie. On a compact interval $0<w_1<=w<=w_2$ only the terms $n<=a/w_1$ can enter. The positive-part map is $1$-Lipschitz. It follows directly, including across all the corners at once, that
$ abs(H(w_1)-H(w_2))<=abs(w_1-w_2) sum_(n<=a/w_1) Lambda(n). $
For a nonprincipal center the term $w(a/w)D(1)=a D(1)$ is constant. For the principal center the new nonconstant term is $a log w$, with derivative $a/w$. Hence the same kind of estimate is available for the centered functions. The elementary upper bound for the sharp Chebyshev count now saves a logarithm compared with the rough estimate above. Chapter 17 applies this continuity estimate at one scale and a different, large-argument bound where the weight is too small for perturbation about that scale.

Together the local pole decomposition, the conjugation identity and the global growth bound supply three different properties of the same function. The moment calculation uses all three. Growth alone permits large fluctuations of either sign. A pole alone does not specify where the positive values must occur. The fixed positive residue at real poles and the common phase at a coincident complex pole are what turn this analytic data into a test for a one-sided arithmetic estimate.

#source-note[The coefficient convention and family weights are in #src("Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily")[CharFamily]. For the analytic ingredients see #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp")[the ramp transform], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne")[the twisted center], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne")[the untwisted center], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal")[the local order calculation], and #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiConj")[the conjugation identity].]


