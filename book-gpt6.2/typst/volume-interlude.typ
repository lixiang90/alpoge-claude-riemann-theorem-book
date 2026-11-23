#import "style.typ": *

#front[Classical arguments revisited]

The first two chapters followed the historical questions. With the transform and character tools of Chapters 3 and 4 now available, we can return to the analytic proofs. The endpoint computation fixes the interpretation of the explicit formula. The Tauberian argument explains how a zero-free boundary implies the prime number theorem. The argument principle explains the count a computation must certify. Stirling's formula gives its smooth main terms, while the final estimate relates the width of a zero-free region to the size of the error in prime counting. Readers continuing directly to the new proof can return to these sections individually.

#heading(level: 2, numbering: none)[A symmetrical count at a jump] <classic1>
At noninteger $x$ the statement that $n<x$ and the statement that $n<=x$ have identical truth values for an integer $n$. At an integer where a counting measure has an atom, inversion by a symmetric Fourier cutoff assigns half the jump. An elementary example explains the convention. For $c>0$ put
$ K_(T)(1)=frac(1,2pi) integral_(-T)^T frac(dif t,c+i t). $
The odd imaginary part integrates to zero. The even real part gives $K_(T)(1)=frac(1,pi) arctan(frac(T,c))$, which tends to $frac(1,2)$. Thus the inverse integral of $frac(1,s)$, at the unit argument, takes the average of the values on the two sides. In a sum over integers the resulting count at a prime power $p^k$ is the left count plus $frac(1,2k)$ for the measure $dif J$, or plus $frac(log p,2)$ for $dif Psi$. This convention matters in a pointwise explicit formula. It does not affect estimates on intervals after continuous smoothing.

An alternative is to integrate the sharp indicator once before inversion. For $x>=1$ and a fixed positive integer $n$,
$ integral_1^x frac(1,n) bold(1)_(t>=n) dif t=max(frac(x,n)-1,0). $
The new weight vanishes exactly where the jump would have occurred. Its graph records how far one has gone beyond the threshold, divided by the threshold. A prime power just below $x$ then contributes very little to the smoothed count. A small prime contributes repeatedly to changes of slope. The smoothing thus changes the way errors can accumulate while preserving their relation to the Euler product.

For a finite signed measure one can invert this integration in the sense of distributions. If
$ B(x)=sum_(n<=x) a_(n)(frac(x,n)-1), $
its right derivative away from new atoms is $sum_(n<=x) frac(a_n,n)$. The derivative jumps by $frac(a_n,n)$ at $n$, so multiplying that jump by $n$ recovers the coefficient. Hence using ramps retains the discrete arithmetic sequence as long as the entire function $B$ is known. An upper estimate on $B$ is much less data, and yields no pointwise upper bound for all derivative jumps of an arbitrary signed sequence. A later analytic argument will use a more rigid property specific to the coefficients coming from $L$-functions.

One can now read the historical question in two coordinates. On the positive real axis one sees arithmetic masses whose size and placement depend on factorization. On the complex side one sees singularities whose positions encode possible oscillations. Unique factorization, logarithms, differentiation, and smoothing give the exact correspondence in the domain of absolute convergence. The harder steps are continuing that correspondence past its original domain and turning its singularities into quantitative information at arbitrarily large scales.

#heading(level: 2, numbering: none)[From a zero-free boundary to a theorem about primes] <classic2>
There is a substantial step between nonvanishing on $Re s=1$ and the assertion that $frac(vartheta(x),x)$ tends to one. The Dirichlet series is known to converge absolutely only on the open side of that line. An Euler product on the open half-plane can approach the boundary without its coefficient sums having a prescribed pointwise asymptotic. A Tauberian argument uses an extra property of the coefficients. In the prime number theorem they are positive, so $vartheta$ is increasing. We give the deduction to see how much information the nineteenth-century method extracts from the boundary.

For $Re s>1$ define $D(s)=sum_p (log p)p^(-s)$. The prime powers of exponent at least two contribute
$ H(s)=sum_p sum_(k>=2) (log p)p^(-k s). $
On each half-plane $Re s>=frac(1,2)+delta$ with $delta>0$, this second series converges locally uniformly. Indeed, its absolute value is bounded by a fixed multiple of $sum_(n>=2)(log n)n^(-1-2delta)$, obtained by summing a geometric series at each prime. Therefore $H$ is holomorphic for $Re s>frac(1,2)$. On the original domain of convergence,
$ D(s)=-frac(zeta'(s),zeta(s))-H(s). $
At $s=1$ the negative logarithmic derivative has residue one. At other points of $Re s=1$ it is regular by nonvanishing. Hence $D(s)-frac(1,s-1)$ extends holomorphically across every finite segment of that boundary. The size of its neighborhood of continuation can depend on the segment.

Partial summation with the logarithmic coordinate $x=e^u$ gives the identity
$ frac(D(1+z),1+z)-frac(1,z)
 =integral_0^infinity (e^(-u) vartheta(e^u)-1)e^(-z u) dif u $
for $Re z>0$. The integrand before multiplication by $e^(-z u)$ is bounded, by Chebyshev's bound from Chapter 1. On the left the apparent singularity at zero is removable. We now show that these two properties force convergence of the integral at zero as an ordinary improper integral. Absolute convergence at zero would be a much stronger statement.

#claim[Newman's boundary lemma][Let $f$ be a bounded, locally integrable function on $[0,infinity)$. Suppose its Laplace transform $g(z)$, initially defined for $Re z>0$, extends holomorphically to a neighborhood of each point of $Re z=0$. Then $integral_0^T f(u) dif u$ tends to $g(0)$ as $T$ tends to infinity.]

#proof[Write $g_(T)(z)=integral_0^T f(u)e^(-z u) dif u$, an entire function, and assume $|f|<=M$. For fixed $R>0$ introduce
$ K_(T)(z)=frac(e^(T z),z)(1+frac(z^2,R^2)). $
Its pole at zero has residue one. Along the circle $|z|=R$ the factor $|frac(1+frac(z^2,R^2),z)|$ is $frac(2abs(Re z),R^2)$. On the right semicircle $|g(z)-g_(T)(z)|<=frac(M e^(-T Re z),Re z)$. Thus the contour integral of $(g-g_T)K_T$ over that semicircle, divided by $2 pi i$, has modulus at most $frac(M,R)$.

For $g_T$ complete the circle on the left. If $Re z<0$, direct integration gives $|g_(T)(z)|<=frac(M e^(-T Re z),abs(Re z))$. The integral of $g_T K_T$ over the left semicircle satisfies the same bound $frac(M,R)$. For $g$ use a different return arc. Along the compact imaginary segment from $-i R$ to $i R$ there is a strip of positive width on which the continuation exists locally and agrees on overlaps, by uniqueness of continuation from the right. Take an arc just to the left of that segment, meeting the circle at its two imaginary endpoints and avoiding zero. The continued function $g$ is bounded there. On the interior of this fixed arc $e^(T z)$ tends to zero and is uniformly bounded by one. Dominated convergence makes its integral of $g K_T$ tend to zero. Both closed contours encircle the origin once.

The residue theorem and the two semicircle bounds now yield $limsup_(T->infinity) |g(0)-g_(T)(0)|<=frac(2M,R)$. Each $R$ can be chosen independently, so this limsup is zero. The factors vanishing at $i R$ and $-i R$ are essential to the estimates near the endpoints.]

Apply the lemma to $f(u)=e^(-u)vartheta(e^u)-1$. Returning to the multiplicative coordinate shows that the integral of $frac(vartheta(x)-x,x^2)$ from one to infinity converges. A convergent signed integral alone does not imply that its integrand is small everywhere. An excess in the *increasing function* $vartheta$, however, cannot vanish instantaneously. Fix $lambda>1$. On $[A,lambda A]$ monotonicity gives
$ integral_A^(lambda A) frac(vartheta(x)-x,x^2) dif x
 >=frac(vartheta(A),A)(1-frac(1,lambda))-log lambda. $
The integral tends to zero as $A$ grows, by the Cauchy criterion for an improper integral. Applying monotonicity on $[frac(A,lambda),A]$ in the opposite direction gives an upper bound for that integral by $frac((lambda-1)vartheta(A),A)-log lambda$. These imply
$ frac(log lambda,lambda-1)<=liminf_(A->infinity) frac(vartheta(A),A), $
$ limsup_(A->infinity) frac(vartheta(A),A)<=frac(log lambda,1-frac(1,lambda)). $
Both outer expressions tend to one as $lambda$ decreases to one. This proves the prime number theorem. The boundary argument has two distinct uses of size. Uniform boundedness of the normalized count permits the analytic continuation argument, and monotonicity converts an integrated limit into a pointwise one. The smoothed character sums in Part II are signed. There the information that replaces monotonicity is the residue of a pole at a real zero. #link("https://www.tandfonline.com/doi/abs/10.1080/00029890.1997.11990704")[Zagier's account of Newman's proof.]

#heading(level: 2, numbering: none)[How an explicit formula displays individual zeros] <classic3>
There is another way to test a proposed exponent. For $x>1$ write $Psi_(0)(x)$ for the average of the left and right limits of $Psi$ at $x$. In the classical von Mangoldt explicit formula one has
$ Psi_(0)(x)=x-sum_rho frac(x^rho,rho)-log(2pi)-frac(1,2) log(1-x^(-2)). $
The sum is over nontrivial zeros, counted with multiplicity and ordered by symmetric height, interpreting it as the limit of the symmetrically truncated sums. This is a theorem about a specifically ordered limit. The displayed formula can be used without converting the sum into an absolutely convergent series. At an integer prime power the half weight on the left from the endpoint calculation is part of the statement. #link("https://doi.org/10.1515/crll.1895.114.255")[Von Mangoldt's paper.]

The terms and their signs can be recovered by considering the integrand
$ -frac(zeta'(s),zeta(s)) frac(x^s,s). $
At the pole of zeta at one the negative logarithmic derivative has residue one, giving $x$. At a nontrivial zero of order $m$ its residue is $-m$, giving $-m frac(x^rho,rho)$. The value at the origin contributes $-frac(zeta'(0),zeta(0))=-log(2pi)$. At $s=-2j$, $j>=1$, the trivial zero contributes $frac(x^(-2j),2j)$. Their convergent sum is the logarithmic term on the right of the formula. To obtain the full theorem one must also bound the horizontal and vertical integrals along a sequence of expanding contours. The residues give the individual terms in the cited explicit formula.

It is useful to compare the sizes at height $T$ and at scale $x$. If a pair $rho=beta+i gamma$, $overline(rho)$ is present, its contribution to $Psi_0$ has amplitude $frac(2x^beta,abs(rho))$. A very large $|gamma|$ makes that amplitude small at first even if $beta$ is large. Comparing it with $sqrt(x)$ suggests looking beyond values where $x^(beta-frac(1,2))$ exceeds $|rho|$. Moreover the oscillation reaches large positive or negative values at phases separated by a fixed amount in $log x$. As a result no one finite table of prime errors can detect a hypothetical zero of arbitrarily large height and real part arbitrarily close to $frac(1,2)$.

Here is a different calculation which explains the logarithms in a standard bound. Suppose the terms associated to zeros up to height $T$ have $Re rho=frac(1,2)$. The individual upper estimate is $frac(sqrt(x),abs(rho))$. The Riemann–von Mangoldt counting estimate gives $N(u)=O(u log(2u))$ for $u>=2$. Partial summation then gives
$ sum_(0<Im rho<=T) frac(1,|rho|)=O((log(2T))^2). $
One logarithm arises from the number of zeros per unit height and one from integrating the reciprocal height. This explains the bound for a *truncated* group of zeros of size $O(sqrt(x)(log(2T))^2)$. To pass to a bound for the actual prime count one needs a truncation error with its dependence on $x$, $T$, and the distance to a prime-power jump. Von Koch's theorem supplies the classical conclusion on assuming all zeros lie on the line. Treating the informal sum over all heights by termwise absolute values would diverge.

One can see the benefit of smoothing in the denominators. Integrating $frac(u^rho,rho)$ in $u$ introduces another factor of order $|rho|$ in the denominator. For large $T$,
$ sum_(T<Im rho<=2T) frac(1,|rho|^2)=O(frac(log(2T),T)). $
The dyadic sum of this bound converges. In the later ramp transform the corresponding factor is $frac(1,rho(rho-1))$. This improves height convergence and also changes the sign at a real zero with $0<rho<1$. The geometric construction naturally estimates the ramp itself. Both features make it an effective statistic to study.

#heading(level: 2, numbering: none)[Translating one zero term into Riemann's counting language] <classic4>
In Riemann's paper the independent variable of his symmetric entire function can be read as $t$ in $s=frac(1,2)+i t$. A nonreal value $t=u+i v$ corresponds to $s=frac(1,2)-v+i u$. Thus his assertion about the reality of the zeros in the $t$ variable is exactly the assertion that the real part in the $s$ variable is $frac(1,2)$. This change of variables also explains a historical difference in appearance between formulas for a prime count and formulas for a logarithmically weighted prime count. A weight $log n$ is produced by differentiation on the analytic side, so undoing it integrates the contribution from an individual zero.

Fix $x_0>1$. For any $x>x_0$ the jump identity proved above gives the finite Stieltjes integral
$ J(x)-J(x_0)=integral_(x_0)^x frac(1,log t) dif Psi(t), $
where the left endpoint is excluded and the right endpoint included. The identity holds on each atom $p^k$ because its contribution is $frac(log p,log(p^k))=frac(1,k)$. To see what happens to one smooth mode of an explicit formula, replace a term in $Psi(t)$ by $-frac(t^rho,rho)$, with $rho!=0$. Its contribution to this operation is
$ -integral_(x_0)^x frac(t^(rho-1),log t) dif t
   =-integral_(log x_0)^(log x) frac(e^(rho v),v) dif v. $
This is the difference of the corresponding exponential integrals at the two endpoints. Using a definite integral avoids a choice of complex logarithm in writing an individual term. The main term $t$ in the weighted prime count similarly gives the logarithmic integral of the unweighted main term.

For a fixed $rho$ with real part $beta>0$, integration by parts gives
$ integral_(x_0)^x frac(t^(rho-1),log t) dif t
 =frac(x^rho,rho log x)+O_(rho,x_0)(frac(x^beta,(log x)^2)). $
The boundary at $x_0$ is constant. The remaining integral involves $frac(t^(rho-1),(log t)^2)$. Split it at $sqrt(x)$, using a fixed lower bound for $log t$ on the first part and $(log t)>=frac(log x,2)$ on the second, to get the displayed error for large $x$. Taking a conjugate pair again gives oscillation in $log x$ with amplitude of order $frac(x^beta,log x)$. This term-by-term calculation explains why the two formulations detect the same real part while their errors have different logarithmic weights. It does not interchange an infinite zero sum with an integral.

There is a second correction before one returns from $J$ to $pi$. The leading proper prime-power term is $frac(pi(sqrt(x)),2)$. By the prime number theorem discussed in Chapter 2 it is asymptotic to $frac(sqrt(x),log x)$. The sum of the remaining terms for $k>=3$ is at most $O(x^(frac(1,3))log x)$ by a trivial bound on their number and size. Hence even if one knew the weighted count with extraordinary precision, dropping the square term at the end would introduce an error comparable in scale to the contribution of a low zero on the critical line. Carrying out the inverse Möbius formula, or keeping all the prime powers from the beginning, is an arithmetic necessity at that scale.

#heading(level: 2, numbering: none)[What is required to count all the zeros in a box?] <classic5>
Suppose $f$ is holomorphic in a neighborhood of a rectangle and has no zero on the boundary. The change in a continuous argument of $f$ round the boundary, divided by $2pi$, counts the interior zeros with their orders. For an entire function this follows by integrating $frac(f',f)$. A zero of order two contributes two circuits even when a real restriction of the function does not change sign there. For a meromorphic function a pole contributes with its order subtracted. Applying this to the completed entire $xi$ avoids tracking the pole of $zeta$ and its trivial zeros while one counts in the critical strip.

Functional symmetry provides a second count. At $s=frac(1,2)+i t$, the two identities for $xi$ give
$ overline(xi(frac(1,2)+i t))=xi(frac(1,2)-i t)=xi(frac(1,2)+i t). $
Thus values are real on this line. Rigorous intervals with opposite strict signs at two heights certify an odd number of zeros between them, counted with multiplicity. If intervals for the heights are disjoint, each sign change gives a separate zero. To certify that all zeros in a box lie on the line, the resulting lower bound can be compared to a rigorous upper count for the entire box. This remains valid when two ordinates are close, provided one has sufficiently fine intervals and can certify the total count. Extra procedures can be needed to handle multiple zeros or values where no sign can be resolved.

#example[Two counts for a polynomial][Put $u=s-frac(1,2)$ and $P(s)=(u^2+1)(u^2+4)(u^2-a^2)$ with $0<a<frac(1,2)$. The polynomial has real coefficients and satisfies $P(1-s)=P(s)$. A rectangle containing the whole strip up to imaginary parts $3$ and $-3$ contains six zeros. On the middle line the zero ordinates are $-2,-1,1,2$, all simple, and the last factor equals $-t^2-a^2$. There are four sign changes. The difference between the counts detects two off-line zeros even if one has never plotted the function on the real interval where they lie. Replacing the last factor by $u^2$ puts the additional zeros on the line with multiplicity two at zero. It gives the same sign-change deficit. The deficit alone leaves both possibilities open.]

A finite-height result quantifies over every zero up to a threshold. A lower-density result instead compares counts as the height tends to infinity. To see the logical difference, imagine exceptional ordinates $2,4,16,256,dots$ obtained by repeated squaring, amongst a collection whose size up to height $T$ grows proportionally to $T log T$. Their proportion tends to zero even though the exceptions continue to arbitrary heights. Alternatively, a count confined to one fixed height range is compatible with *every* later ordinate having some other property. The one-sided interval argument in Part II takes a single putative off-line zero and chooses a threshold depending on it. This order of quantifiers suffices to rule out every such zero individually.

#heading(level: 2, numbering: none)[The count supplied by the gamma factor] <classic6>
For positive $T$ away from a zero ordinate, a more precise count of zeta zeros can be written using a continuous argument of the gamma function. Set
$ theta(T)=Im log Gamma(frac(1,4)+frac(i T,2))-frac(T,2)log pi. $
On the vertical ray the logarithm is continued from its real value at $T=0$. The completed factor $pi^(-frac(s,2))Gamma(frac(s,2))$ restricted to $s=frac(1,2)+i T$ has argument $theta(T)$. Multiplying $zeta(frac(1,2)+i T)$ by $e^(i theta(T))$ therefore gives a real value. Equivalently this real function is the completed function divided by its real nonvanishing factors along the line. Using it to detect sign changes avoids evaluating exponentially small values of the full completion high in the strip.

Stirling's formula for $log Gamma(z)$ on a closed sector away from the negative real axis gives $(z-frac(1,2))log z-z+frac(log(2pi),2)+O(frac(1,abs(z)))$. For $z=frac(1,4)+frac(i T,2)$, one has $log|z|=log(frac(T,2))+O(T^(-2))$ and $arg z=frac(pi,2)+O(T^(-1))$. The imaginary part of $(z-frac(1,2))log z$ is $(frac(T,2)) log|z|-frac(arg z,4)$. Substitution gives
$ theta(T)=frac(T,2)log(frac(T,2pi))-frac(T,2)-frac(pi,8)+O(T^(-1)). $
The gamma factor thus changes its argument at a rate depending on height. It accounts for the nonuniform spacing of zeros in the usual counting asymptotic.

In the classical argument-principle formula one has $N(T)=1+frac(theta(T),pi)+S(T)$, where $S(T)$ is $frac(1,pi)$ times the variation giving the argument of $zeta(frac(1,2)+i T)$ along the path from $2$ to $2+i T$ to $frac(1,2)+i T$, starting with zero argument at the positive real point. A height away from all zero ordinates keeps zeros off the horizontal leg. This choice gives an *unwrapped* argument. Reducing the final value modulo $2pi$ would discard precisely the integer information used by the count. Together with the classical bound $S(T)=O(log T)$, this gives the familiar leading two terms
$ N(T)=frac(T,2pi)log(frac(T,2pi))-frac(T,2pi)+O(log T). $
We use the classical counting formula and its bound here as inputs. The gamma calculation explains their leading smooth part. Counting all zeros in a given finite box requires a certified remainder or a direct counting argument to obtain an exact integer count.

The derivative of this smooth main term is $frac(log(frac(T,2pi)),2pi)$. Its reciprocal $frac(2pi,log(frac(T,2pi)))$ gives a characteristic average spacing on a height scale on which the error is controlled. It predicts no particular gap between consecutive zeros. For example, intervals containing several zeros close together can have the same average density as intervals with evenly spaced zeros. A grid that resolves one mean spacing may still miss a pair of real-line sign changes. This illustrates why counting methods supplement rigorous point evaluations in finite-height work.

#heading(level: 2, numbering: none)[The width of a zero-free region and its arithmetic cost] <classic7>
Nonvanishing at every point of the line $Re s=1$ supplies a zero-free neighborhood of each compact segment. Removing the pole at one first makes this an elementary compactness statement about zeros of a nonvanishing holomorphic function. As the segment gets longer its neighborhood may become narrower. To give a rate in the prime number theorem one needs a lower bound on that width together with estimates for truncated inversion. De la Vallée Poussin obtained a quantitative region traditionally expressed in the shape
$ Re s >=1-frac(c,log(2+|Im s|)) $
for a sufficiently small positive constant $c$, away from the pole. This gives a width which decreases with height, and so leaves open much of the critical strip. #link("https://www.persee.fr/doc/marb_0770-8459_1899_num_59_1_2449")[De la Vallée Poussin's memoir.]

One can trace the functional form of the resulting error by a simple balance. Consider a truncated explicit formula at height $T$ and first consider the zeros appearing explicitly. A zero in this range satisfying the region contributes at most a factor
$ x^(Re rho)<=x exp(-frac(c log x,log(2+T))). $
We have already bounded the sum of reciprocal heights by a squared logarithm. Increasing $T$ makes the use of the zero-free region weaker, whereas raising the cutoff improves the error in truncating the inverse integral. A typical truncation term at suitable half-integer $x$ has size $frac(x,T)$ times a fixed power of $log(x T)$ in the range needed here. For general $x$ one may use monotonicity of $Psi$ and neighboring half-integers so that a point lying very close to a jump introduces no uncontrolled denominator. Precise contour estimates are needed to establish the truncation theorem. We now balance the two costs in its conclusion.

Ignoring log powers, put $L=log x$ and $u=log T$. The two relative error scales are $exp(-frac(c L,u))$ and $exp(-u)$. Setting $u=sqrt(c L)$ gives the same order for the two. For any smaller positive constant $c'$ than the resulting square-root exponent, powers of $log x$ are absorbed, yielding the characteristic error scale $x exp(-c' sqrt(log x))$. It is smaller than $frac(x,(log x)^A)$ for every fixed $A$, but for every $theta<1$ it is ultimately larger than $x^theta$. Indeed their logarithmic ratio is $(1-theta)log x-c' sqrt(log x)$, which tends to plus infinity. A very strong improvement over a power of a logarithm can coexist with a large gap to a square-root error.

Contrast that height dependence with a hypothesis excluding every zero in the entire half-plane $Re s>frac(1,2)$. In the truncated zero sum the factor $x^(Re rho)$ is then at most $sqrt(x)$ independently of $T$, by symmetry and the location of all the zeros. Raising $T$ incurs the much slower cost from the number of zeros and their reciprocal heights. This is the substantial gain behind von Koch's conditional estimate. The proof in Part II exploits the converse implication. A bound slightly above square-root size on a sequence of whole intervals excludes a proposed individual zero. Uniform control on every $x$ and every height simultaneously is a stronger assumption than that inverse argument requires.