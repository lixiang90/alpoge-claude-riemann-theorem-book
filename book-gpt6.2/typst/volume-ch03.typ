#import "style.typ": *
#chapter[Transforms, residues, and symmetry]

== Measuring growth with a transform <c03s01>

A power $x^beta$ becomes $e^(beta u)$ in the coordinate $u=log x$. A factor $x^(i t)$ becomes an ordinary oscillation $e^(i t u)$. These two facts make the Mellin transform the natural combination of a growth test and a Fourier transform. We use the following convention on $x>=1$,
$ M f(s)=integral_1^infinity f(x)x^(-s-1)dif x
        =integral_0^infinity f(e^u)e^(-s u)dif u. $
If $|f(x)|<=C x^beta$, the integral converges absolutely for $Re s>beta$ and is holomorphic there by dominated convergence on compact subsets. A pure power gives $M(x^beta)(s)=frac(1,s-beta)$. Differentiating with respect to $beta$ gives $M(x^beta log x)(s)=frac(1,(s-beta)^2)$. Poles thus distinguish both the exponent and a logarithmic correction.

Consider $f(x)=x^b cos(t log x)$ for real $b$ and $t!=0$. Splitting the cosine into two exponentials yields
$ M f(s)=frac(1,2) (frac(1,s-b-i t)+frac(1,s-b+i t)). $
This function has two distinct singularities of equal real part. Integrating the original oscillations over a carefully chosen interval could make them nearly cancel. The singularities of the transform still see them separately. A later chapter makes this observation effective even for one-sided data on short parts of the logarithmic axis.

== How large a half-plane does an integral control? <c03s02>

Let $f$ be locally integrable on $[1,infinity)$ and suppose $|f(x)|<=C x^(b)(1+log x)^A$ for $x>=1$, where $A$ is a nonnegative integer. For $u=log x$ and $Re s>=b+delta$, the absolute value of the transformed integrand is bounded by $C(1+u)^A e^(-delta u)$. Each additional derivative in $s$ inserts a factor $-u$. Thus for every integer $k>=0$,
$ (-1)^k (M f)^((k))(s)=integral_0^infinity f(e^u) u^k e^(-s u) dif u. $
Weil-type explicit formulas often treat derivatives as information about zeros. Here a derivative taken at a large real part has a direct real-variable meaning, an average with a positive weight tilted toward a particular distance from the origin.

For a quantitative dominating integral, integrate by parts on $[0,B]$ and let $B$ tend to infinity. The boundary term at $B$ tends to zero because each fixed power grows slower than an exponential. The result, with $k>=0$, is
$ integral_0^infinity u^k e^(-delta u) dif u=frac(k!,delta^(k+1)). $
For $A=0$ this implies $frac(abs((M f)^((k))(s)),k!)<=frac(C,(Re s-b)^(k+1))$. The factorial is the normalization of a Taylor coefficient. Upon dividing by it, the bound measures distance from the line of absolute convergence as a geometric factor to the $k$th power. Cauchy's inequality for a function analytic in a disk will supply an independent estimate of the same kind. The proof in Chapter 9 compares those two estimates.

A converse to the holomorphy statement requires hypotheses. For example, define $f(e^u)=e^(b u)sin(e^(a u))$ with $a>0$. Its absolute size has growth exponent $b$. Substituting $v=e^(a u)$ gives
$ M f(s)=frac(1,a) integral_1^infinity v^(frac(b-s,a)-1)sin(v) dif v. $
Integration by parts at infinity gives conditional convergence on $Re s>b-a$, because the boundary coefficient tends to zero there and the new integral is absolutely convergent on compact subsets. The original integral is absolutely convergent for $Re s>b$. Oscillation has enlarged the region in which one can represent the transform. For arbitrary signed functions the analytic continuation of an integral therefore need not determine an upper bound for its absolute size. A pole can, nevertheless, obstruct a proposed bound through specific information about the oscillations.

== Multiplicative convolution and a pair of poles <c03s03>

For functions $f,g$ on $[1,infinity)$ define their multiplicative convolution by
$ (f star g)(x)=integral_1^x f(frac(x,y))g(y) frac(dif y,y). $
The measure $frac(dif y,y)$ is forced by invariance under dilation. In the coordinate $u=log x$ this becomes the ordinary one-sided convolution of $f(e^u)$ and $g(e^u)$. Under absolute convergence the transform of the convolution is the product of the transforms. To prove this, replace $x$ by $y z$ in the double integral. The region $1<=y<=x$ becomes $1<=y$ and $1<=z$. The factors become $f(z)z^(-s)$ and $g(y)y^(-s)$, each with its own logarithmic measure. Fubini's theorem now factors the integral. Polynomial bounds of the kind used in the preceding section give a common right half-plane in which absolute convergence holds.

Take $f(x)=x^a$ and $g(x)=x^b$. If $a!=b$, the convolution is $frac(x^a-x^b,a-b)$. At $a=b$ its value is $x^a log x$. The product transform is
$ frac(1,(s-a)(s-b)). $
For distinct exponents this has two simple poles. As $b$ tends to $a$ the two modes coalesce into a logarithmic factor, as the divided difference of powers shows pointwise. The corresponding transform has a double pole. With $a=1,b=0$ the convolution is $x-1$ on $x>=1$. Extending by zero to $x<1$ gives the ramp, and immediately recovers its denominator $s(s-1)$. This derivation never inverts a conditionally convergent vertical integral.

For an individual integer $n$ consider the operator that is zero below $n$ and sends $f(x)$ to $f(frac(x,n))$ above $n$. A substitution in the transform shows that its multiplier is $n^(-s)$. Hence any finite sum of dilations of the ramp has transform
$ frac(1,s(s-1)) sum_(n<=N) a_n n^(-s). $
If $sum |a_n| n^(-sigma)$ converges for $sigma>1$, this formula extends to an infinite sequence on that half-plane because the integral of each absolute-value summand is bounded by $frac(abs(a_n)n^(-sigma),sigma(sigma-1))$. The functions themselves are locally finite sums since only $n<=x$ occur at any fixed point. This observation proves the transform identity without prescribing a value of a discontinuous function at its jumps.

#example[Two atoms survive a sign change][Take $a_2=1$, $a_3=-1$. The function of $x$ is zero below two, equals $frac(x,2)-1$ on $[2,3]$, and equals $frac(x,6)$ above three. Its transform is $frac(2^(-s)-3^(-s),s(s-1))$. At $s=0$ the numerator vanishes. This cancels one of the two apparent poles even though both individual ramps had that pole. The remaining residue at $s=1$ is $frac(1,6)$, exactly the coefficient of linear growth at infinity. Cancellation of a main term has a local analytic signature.]

More generally, take real coefficients supported in a finite set of positive integers. On the right of their largest index the smoothed sum is exactly
$ x sum_n frac(a_n,n)-sum_n a_n. $
Thus one can predict its two pole coefficients before doing any complex analysis. Infinite prime sums introduce a qualitatively different possibility. Their generating series can have singularities of its own after continuation. The extra centering terms in the book remove the specified singularity at one and preserve those at individual zeros of $L$-functions.

== A contour calculation one can do by hand <c03s04>

For $c>1$, consider the vertical integral of $frac(x^s,s(s-1))$ divided by $2pi i$. For $x>1$ move the contour left. The residues at $s=0$ and $s=1$ are $-1$ and $x$ respectively. For $0<x<1$ move it right and enclose no pole. For instance one can first use a finite rectangle, let its horizontal sides tend to infinity at fixed vertical sides, and finally move the new vertical side to infinity. The denominator gives integrability on the vertical lines and the power of $x$ gives decay in the direction of the move. The result is $(x-1)_+$. At $x=1$ the value follows by continuity. Rescaling $x$ to $frac(x,n)$ gives a weight that begins at $n$. Its denominator, including the factor $s-1$, explains a later centering term.

For comparison, summation by parts gives, initially for $Re s>1$,
$ -frac(zeta'(s),zeta(s))=s integral_1^infinity Psi(x)x^(-s-1)dif x. $
If $Psi(x)=x+E(x)$, the transform of $x$ contributes $frac(s,s-1)$. An absolute bound $E(x)=O(x^theta)$ would make the remaining integral holomorphic on $Re s>theta$. A zero of $zeta$ there would give a pole of its logarithmic derivative. This proves the easy direction of the usual prime-error criterion and motivates a version that can use less information about $E$.

== Mellin inversion with a convergent regulator <c03s05>

On the vertical line $Re s=c>b$ put $h(u)=e^(-c u)f(e^u)$ for $u>=0$ and $h(u)=0$ for $u<0$. Under the growth hypotheses above it is integrable on the whole real line. Then $M f(c+i t)=integral h(u)e^(-i t u) dif u$. We use *angular* frequency $t$ in this formula. It differs by a factor $2pi$ from the convention used to state Poisson summation below. Confusing the two conventions changes the normalizing constant in an inversion integral.

Take $A>0$. Multiply the transform by $e^(-frac(t^2,4A))$ and integrate against $frac(e^(i t v),2pi)$. Fubini's theorem applies because $h$ is integrable and the frequency cutoff is integrable. Evaluation of the Gaussian integral gives
$ frac(1,2pi)integral_(-infinity)^infinity M f(c+i t)e^(i t v-frac(t^2,4A)) dif t
 = sqrt(frac(A,pi)) integral_(-infinity)^infinity h(u)e^(-A(u-v)^2) dif u. $
The right side is convolution with a Gaussian approximate identity centered at $v$. At a continuity point where $h$ is locally bounded, split the integral into $|u-v|<delta$ and its complement. In the first part continuity controls the difference $h(u)-h(v)$. Off this neighborhood the supremum of the Gaussian tends to zero after factoring out the integrable size of $h$. Thus it tends to $h(v)$. If $h$ has finite, possibly different, one-sided limits, the same argument on the two sides gives their arithmetic mean. This explains why symmetric inversion assigns a half weight at a jump.

If the transform itself is absolutely integrable in $t$, dominated convergence also removes the regulator on the left. Multiplying by $e^(c v)$ gives the ordinary inverse Mellin integral at $x=e^v$. For the step $f(x)=1$ on $x>=1$, the transform $frac(1,s)$ decays only as $frac(1,abs(t))$, so this absolute argument fails even though the regulated inverse remains well defined. For the ramp the transform $frac(1,s(s-1))$ decays as $frac(1,abs(t)^2)$ on every line $c>1$. There the ordinary integral works and varies continuously with $x$ on compact positive intervals. These simple integrability tests explain one gain from inserting a single integration before studying zeros.

== How much transform data determine the coefficients? <c03s06>

Suppose a Dirichlet series $D(s)=sum_n a_n n^(-s)$ converges absolutely for $Re s>c$. If it vanishes identically there, every coefficient vanishes. To see this, let $m$ be the smallest index with $a_m!=0$. Then for real $sigma>c$,
$ m^sigma D(sigma)=a_m+sum_(n>m) a_(n)(frac(m,n))^sigma. $
The tail tends to zero as $sigma$ tends to infinity by dominated convergence, after dominating at any fixed $sigma_0>c$. The resulting limit would be $a_m$, a contradiction. Successive subtraction of the leading term gives the general coefficient-recovery principle. It explains why identities of absolutely convergent Dirichlet series imply exact formulas for arithmetic functions, as will happen for norms of Gaussian integers in Chapter 4.

For values on a set with an interior accumulation point, the identity theorem for holomorphic functions gives uniqueness throughout the connected component. Finitely many sampled values give no such conclusion. For example choose distinct real $s_1,dots,s_k>1$ and set $P(X)=product_(j=1)^(k)(X-2^(-s_j))$. Then $P(2^(-s))$ is a nonzero Dirichlet polynomial supported on the powers $1,2,4,dots,2^k$ of two and vanishes at all the prescribed $s_j$. Changing the list of coefficients by any multiple of that polynomial preserves each sampled value. The exactness of the transform identities used in the proof comes from known equations on a full domain and their analytic continuation.

For the continuous Mellin transform, uniqueness is most transparent on a vertical line. In logarithmic coordinates the transform there is the Fourier transform of an integrable function. The Gaussian regularization in #link(<c03s05>)[§3.5] reconstructs it at continuity points. If a continuous ramp sum has identically zero transform on the line, the sum vanishes everywhere, and its successive changes of slope then recover zero prime coefficients. A bound for transform derivatives at some points gives much less information than a complete line of values. The later argument exploits just the inequality needed to rule out a pole from the given information about the prime weights.

== An explicit formula with a chosen test function <c03s07>

Let $F(s)=sum_n a_n n^(-s)$ converge absolutely on the line $Re s=c$. Fix $X>0$ and a smooth real function $phi$ of compact support on the logarithmic axis. Define its two-sided transform using a *positive* exponential,
$ B(s)=integral_(-infinity)^infinity phi(u)e^(s u) dif u. $
It is entire. On a bounded vertical strip $alpha<=Re s<=c$ it decreases faster than every inverse power of $|Im s|$. To prove this, differentiate the compactly supported smooth function $u mapsto phi(u)e^(sigma u)$ in the real variable and integrate by parts repeatedly against $e^(i t u)$. Each derivative has uniformly bounded integral on that strip and the endpoints vanish. The rapid decay allows ordinary Fourier inversion in the preceding sense. It also permits multiplication by any fixed polynomial in the height.

Inverting each weight and using absolute convergence on the initial line gives
$ sum_n a_n phi(log(frac(n,X)))
 =frac(1,2pi i) integral_(c-i infinity)^(c+i infinity) F(s) X^s B(s) dif s. $
The support restricts the left side to a finite multiplicative interval. For instance support in $[-h,h]$ restricts $n$ to $[X e^(-h),X e^h]$. The factor $X^s$ records the center of the interval. The analytic factor $B(s)$ records its shape. On moving the line to $Re s=alpha$, a simple pole of $F$ at $rho$ contributes $op("Res")_(rho)(F) X^rho B(rho)$. This conclusion uses the residue theorem in successive rectangles. It applies directly if there are finitely many poles in the strip, the boundary avoids them, and $F$ is polynomially bounded on the new vertical line and on a sequence of horizontal sides tending to infinity. Rapid decay of $B$ makes the horizontal integrals vanish under those bounds. With infinitely many poles additional convergence estimates for their contributions are necessary.

One can compute an example without an infinite series. Take $F(s)=frac(1,s-a)$ and real $a$. Its right-half-plane Laplace representation on the logarithmic coordinate is the transform of $e^(a u)$ for $u>=0$. The smoothed expression is an integral over that half-line. Once the translated test support lies strictly inside $u>0$, the contribution at $a$ is exactly $X^a B(a)$. This verifies both the sign convention for $B$ and the location of the scale factor. For nonreal $a$ the same identity holds algebraically, and the factor $X^(i Im a)$ is a phase.

Even a smooth nonnegative test can have $B(rho)=0$ at a prescribed nonreal argument, since its Fourier components can cancel. If the support is sufficiently short around zero, one can prevent cancellation for a *fixed* $rho$. Indeed, if $|Im rho|h<frac(pi,2)$, the real part of $e^(rho u)$ is strictly positive on $[-h,h]$. Any nonzero nonnegative $phi$ supported there then has $Re B(rho)>0$. As the imaginary part increases the allowed support narrows. A single test optimized for a known low zero does not automatically detect every high one. The differentiated Mellin kernels of the proof respond to the position of the proposed pole while taking advantage of the specific intervals on which arithmetic bounds hold.

== A Gaussian in both variables <c03s08>

Fix the Fourier convention $hat(f)(xi)=integral_(-infinity)^infinity f(u)e^(-2pi i u xi) dif u$. The factor $2pi$ ensures that the dual frequencies of the integers are the integers. Write $I(xi)$ for the transform of $e^(-pi u^2)$. The Gaussian integral, proved by squaring it and using polar coordinates in the plane, is one. Differentiation in $xi$ followed by integration by parts in $u$ gives
$ I'(xi)=-2pi xi I(xi), quad I(0)=1. $
The endpoint terms at infinity vanish exponentially. Solving the differential equation gives $I(xi)=e^(-pi xi^2)$. Dilation now yields the transform of $e^(-pi t u^2)$, namely $t^(-frac(1,2))e^(-frac(pi xi^2,t))$ for $t>0$. In this argument one positivity property belongs to the real Gaussian. Fourier transformation introduces phases, yet the entire result is again real and positive.

To pass to a lattice, periodize the Gaussian. For each fixed $t>0$ the series $P_(t)(x)=sum_(n in ℤ) e^(-pi t(x+n)^2)$ converges uniformly on $[0,1]$ along with each derivative. Every term outside $|n|<=2$ can be bounded by a fixed polynomial in $|n|$ times a Gaussian there. Its $k$th Fourier coefficient is obtained by integrating term by term on that interval and substituting $y=x+n$. The factor $e^(2pi i k n)=1$ for integer $k,n$ allows the intervals to be joined into the real line. The coefficient is $t^(-frac(1,2))e^(-frac(pi k^2,t))$. The Fourier series with these coefficients is also absolutely uniformly convergent. The uniqueness of Fourier coefficients, or the elementary convergence theorem for a smooth periodic function, identifies it with $P_t$. Evaluating at zero proves the Gaussian theta identity.

It pays to note the strength of exponential decay. For $t>=1$ one has
$ 0<vartheta(t)-1=2sum_(n>=1)e^(-pi n^2 t)
 <=frac(2e^(-pi t),1-e^(-pi t)). $
For $t$ near zero use the theta identity to find $vartheta(t)=t^(-frac(1,2))+O(t^(-frac(1,2))e^(-frac(pi,t)))$. These two endpoint expansions supply separate pieces of the continuation of zeta. Splitting the integral at one sends the small-$t$ tail to the large-$t$ tail. The two explicitly subtracted powers yield the rational functions $frac(1,s-1)$ and $-frac(1,s)$. The integral left over is entire because it admits derivatives of every order bounded uniformly on each compact subset by integrable functions. An estimate for large $t$ by a fixed inverse power alone would give only a finite strip of continuation.

In the completed function the residues at one and zero are $1$ and $-1$. The sign difference agrees with reflection around the middle line. Taking the limit at zero, the asymptotic $Gamma(frac(s,2))∼frac(2,s)$ forces $zeta(0)=-frac(1,2)$. At a negative even integer $s=-2m$ the reflected completed value at $1+2m$ is finite and nonzero by the Euler product. Since the gamma factor on the left has a simple pole there and the other elementary factor is nonzero, zeta has exactly a simple zero. Thus the trivial zeros and their multiplicities can be read off from the continuation once the poles of gamma are understood.

== Why the gamma factor has no hidden zero <c03s09>

For $Re z>0$ define the gamma integral $Gamma(z)=integral_0^infinity u^(z-1)e^(-u) dif u$. Integration by parts gives $Gamma(z+1)=z Gamma(z)$ and $Gamma(1)=1$. This continues gamma meromorphically one unit at a time. The recurrence alone, even together with its integer values, does not immediately exclude complex zeros outside the integers. An instructive proof of nonvanishing starts with a compact integral. For integer $n>=1$, repeated integration by parts gives
$ integral_0^1 t^(z-1)(1-t)^n dif t=frac(n!,z(z+1) dots (z+n)). $
Set $u=n t$ and multiply by $n^z$. The integrand becomes $u^(z-1)(1-frac(u,n))^n$ on $[0,n]$, bounded in absolute value by $u^(Re z-1)e^(-u)$. Dominated convergence gives
$ Gamma(z)=lim_(n->infinity) frac(n^z n!,z(z+1) dots (z+n)). $

The reciprocals of the finite expressions can be written as
$ z exp(z(H_n-log n)) product_(m=1)^n (1+frac(z,m))e^(-frac(z,m)), $
where $H_n=sum_(m=1)^n frac(1,m)$. The prefactor converges to $z e^(gamma z)$. On a bounded set of $z$ the logarithms of the tail factors are $O(frac(abs(z)^2,m^2))$, by the Taylor series of $log(1+w)-w$ for $|w|<frac(1,2)$. The product therefore converges uniformly on compact sets to an entire function and the tail is nonzero there. The only zeros come from the leading $z$ and the individual factors $1+frac(z,m)$. In particular the limiting reciprocal is nonzero on $Re z>0$, proving that its reciprocal is the gamma integral there. We obtain both the absence of zeros of gamma and the simple poles at $0,-1,-2,dots$.

This computation also fixes one constant in Chapter 1. Taking the derivative of the logarithm of the product at $z=1$ gives
$ -frac(Gamma'(1),Gamma(1))=1+gamma+sum_(m>=1)(frac(1,m+1)-frac(1,m))=gamma. $
On the other hand differentiating the gamma integral at one gives $Gamma'(1)=integral_0^infinity e^(-u)log u dif u$. Thus the logarithmic moment of the unit exponential distribution is $-gamma$. The harmonic average appearing in prime counting and the local expansion of gamma contain exactly the same Euler constant.

== The Gaussian and the functional equation <c03s10>

Let $vartheta(t)=sum_(n in ℤ) e^(-pi n^2 t)$ for $t>0$. The periodization in #link(<c03s08>)[§3.8] gave $vartheta(t)=t^(-frac(1,2))vartheta(frac(1,t))$. It allows the same integral to describe the two ends of the positive axis.

For $Re s>1$ termwise integration gives
$ frac(1,2) integral_0^infinity (vartheta(t)-1)t^(frac(s,2)) frac(dif t,t)
    =pi^(-frac(s,2))Gamma(frac(s,2))zeta(s). $
Split at one, apply the theta transformation below one, and substitute $t mapsto frac(1,t)$. The right side is now expressed as
$ frac(1,s-1)-frac(1,s) + frac(1,2) integral_1^infinity
    (vartheta(t)-1)(t^(frac(s,2))+t^(frac(1-s,2)))frac(dif t,t). $
The integral is entire in $s$ because $vartheta(t)-1$ decays exponentially at infinity. Each term of the full expression is unchanged by $s mapsto 1-s$ after combining the two rational terms. Multiplication by $frac(s(s-1),2)$ gives the entire function $xi$ from the first chapter. Since the gamma function has poles at the nonpositive integers and has no zeros, the formula also explains why negative even integers are distinguished in the zeta theorem.

== Localizing on the logarithmic axis <c03s11>

For $a>0$ the density
$ P_(k,a)(u)=frac(a^(k+1),k!) u^k e^(-a u), quad u>=0, $
has total mass one by the integral already evaluated. Its first and second moments, obtained by using $k+1$ and $k+2$ in the same integral, are $frac(k+1,a)$ and $frac((k+1)(k+2),a^2)$. Its variance is $frac(k+1,a^2)$. Its most likely value for $k>0$ is $frac(k,a)$, by differentiating $k log u-a u$. Thus increasing $k$ with $a$ fixed moves the center outward linearly and widens the kernel only by order $sqrt(k)$. On the multiplicative axis the center moves exponentially far out in $x$. This is how arbitrarily late windows can be selected by the order of a derivative at a fixed argument.

For $q=k+1$, let $T$ have this density. Chebyshev's inequality bounds the probability of a relative displacement of at least $h>0$ by
$ bb("P")(abs(T-q/a)>=h q/a)<=frac(1,h^2 q). $
For example, when $q=100$ and $h=1/2$, this guarantees that the interval from half the mean to three halves of the mean contains at least $96%$ of the mass. Increasing $q$ to $400$ improves the guarantee to $99%$. In the prime-sum argument two rates are raised to the $k$th power. A power of $q$ in the denominator may then be too small a saving. The stronger exponential tail estimate, with constants uniform in the location of the window, is proved in #link(<c09s04>)[§9.4].

Moving the differentiation center vertically to $sigma+i tau$ multiplies the real weight by $e^(-i tau u)$. Oscillations can therefore affect the derivative at that height even though its absolute integral has the same weight. The next section calculates what becomes of these phases when the original arithmetic sum is replaced by its real part.

== Taking a real part before transforming <c03s12>

An individual Dirichlet character may be complex. The arithmetic inequality is an ordering of real numbers and consequently uses real parts of the character sums. Suppose a complex-valued function $g$ on $[1,infinity)$ has Mellin transform $H(s)$ on a right half-plane. On that half-plane conjugating *both* the integrand and the parameter gives
$ M(overline(g))(s)=overline(H(overline(s))). $
Thus the transform of $Re g$ is $frac(1,2)(H(s)+overline(H(overline(s))))$. It is generally different from the ordinary real part of $H(s)$ at a nonreal point. The latter is not a holomorphic function of $s$ unless it is constant. The reflected conjugate of a holomorphic series is holomorphic because it simply conjugates its Taylor coefficients and reflects its center.

Take $g(x)=(1+i)x^(b+i t)$ with $b,t$ real and $t>0$. Then $Re g(x)=x^(b)(cos(t log x)-sin(t log x))$. Its transform is
$ frac(1+i,2(s-b-i t))+frac(1-i,2(s-b+i t)). $
There are two poles with conjugate residues, although the original $g$ has a transform with just one pole. At a real parameter the transformed real part does equal $Re H(s)$ by linearity of the integral. At a nonreal parameter the two poles are separately visible. If one later adds the real transforms for different characters, their common pole coefficients must be compared *after* making this reflection. The coefficient calculation in Chapter 8 does exactly that.

There is also an elementary reality property of the Taylor coefficients at a real center. A real-valued function $g$ of the real variable has a transform satisfying $H(overline(s))=overline(H(s))$ wherever both sides are continued from the defining integral. Coefficients of its Taylor series at a real point are real, and the residue at a real simple pole is real. Nothing in this symmetry fixes the sign of that residue. Computing it from the logarithmic derivative and the two ramp denominators is therefore indispensable to a one-sided argument.

== Taylor coefficients seen from two different centers <c03s13>

Let a meromorphic function $H$ have a single simple pole at $rho$ in a closed disk $|s-z|<=R$, and suppose it is meromorphic on an open neighborhood of the disk. Writing $c$ for the residue gives $H(s)=frac(c,s-rho)+J(s)$ with $J$ holomorphic on the disk and its boundary. If $|z-rho|<R$, Cauchy's estimate on the boundary gives
$ frac((-1)^k,k!) H^((k))(z)=frac(c,(z-rho)^(k+1))+O(R^(-k)). $
The implied constant can be the maximum of $|J|$ on the circle. It is independent of $k$. Subtracting only a principal part is enough to make this estimate. No global expansion over all poles is needed. A smaller circle for a second center with no pole at all gives an upper bound for its normalized derivative by a geometric sequence controlled by that circle.

One can see exactly why a bound at selected orders may miss a pole. Take the sum of two reciprocals with residues one at $b+i t$ and $b-i t$, where $t>0$. At the real center $sigma=b+t$ the two differences have arguments $-pi/4$ and $pi/4$. The normalized coefficient is
$ 2(sqrt(2)t)^(-k-1)cos((k+1)pi/4). $
It vanishes for $k=1,5,9,dots$ although both poles are present. A test that controlled only these orders would see complete cancellation. In #link(<c09s02>)[§9.2] the center is shifted vertically, making one pole strictly nearer so that a single term dominates at every sufficiently large order.

At a real pole a vertical shift may increase its distance from the center. Then the sign of its residue matters. For $b>theta>0$, the transforms of $e^(b u)$ and $-e^(b u)$ have residues $1$ and $-1$ at the same pole. The first function eventually exceeds any fixed positive multiple of $e^(theta u)$ and the second satisfies an upper bound of zero. Chapter 8 computes which sign occurs for the centered prime sums.


