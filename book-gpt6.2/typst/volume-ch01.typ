#import "style.typ": *
#set par(leading: 0.585em, spacing: 0.64em)
#chapter[Why the primes led to a function of a complex variable]

== Two ways of counting <c01s01>

There are four primes up to ten and twenty-five up to one hundred. Extending a table soon makes two features visible. The primes thin out, yet the count grows in a fairly regular way. Write $pi(x)$ for the number of primes at most $x$. A smooth curve that stays close to this staircase should have slope roughly equal to the local density of primes. Gauss's estimate for that density was $frac(1,log x)$. It leads to the integral of $frac(1,log t)$ as a model for the count.

#align(center)[#table(columns: 3, align: (right,right,right), inset: (x: 11pt,y: 4pt), stroke: none,
  table.hline(stroke: 0.7pt), [$x$], [$pi(x)$], [$frac(x,log x)$],
  table.hline(stroke: 0.4pt), [100], [25], [21.71], [1,000], [168], [144.76],
  [10,000], [1,229], [1,085.74], [100,000], [9,592], [8,685.89], table.hline(stroke: 0.7pt))]

At these sizes the last column systematically underestimates the second. Integration by parts explains part of the discrepancy. The integral from $2$ to $x$ of $frac(dif t,log t)$ starts with $frac(x,log x)$, and its next term is of order $frac(x,(log x)^2)$. Determining the leading term, determining a bound for the error against the integral, and determining how that error changes sign are three progressively finer questions.

Euler found another way to bring all primes into one expression. For a real number $s>1$ multiply the geometric series $1+p^(-s)+p^(-2s)+dots$ for primes $p<=P$. Unique factorization shows that every integer having no prime factor above $P$ occurs exactly once. Let $P$ tend to infinity. Positivity gives the identity for real $s$, and absolute convergence gives it for complex $s$ with $Re s>1$,
$ sum_(n>=1) n^(-s)=product_p (1-p^(-s))^(-1). $
This common function is $zeta(s)$. The left side allows analysis by sorting terms according to size. The right side remembers the primes individually. Euler's product provides the passage between the two.

In 1837 Dirichlet introduced characters to distinguish residue classes and proved that every reduced arithmetic progression contains infinitely many primes. In his 1852 memoir Chebyshev bounded the prime count above and below by positive constant multiples of $frac(x,log x)$ for large $x$. Two questions remained for Riemann's generation. Could one determine the leading constant, and could one describe the fluctuations left after subtracting a smooth main term?

== What Riemann counted in 1859 <c01s02>

Riemann's paper to the Berlin Academy asked how many primes lie below a given magnitude. He treated $s$ as a complex variable and related prime counting to the zeros of the continued zeta function. A small modification of the counting function explains why this was possible. Define
$ J(x)=sum_(p^k<=x) frac(1,k). $
Then $J(x)=pi(x)+frac(pi(sqrt(x)),2)+frac(pi(x^(frac(1,3))),3)+dots$, a finite sum for fixed $x$. At $x=10$, the terms are $4+frac(2,2)+frac(1,3)=frac(16,3)$. Taking the logarithm of the Euler product gives
$ log zeta(s)=sum_p sum_(k>=1) frac((p^k)^(-s),k)
             =integral_(1^-)^infinity x^(-s) dif J(x). $
The last integral is simply a sum over the jumps of a step function. Its value first defines a branch of $log zeta$ in $Re s>1$. Inverting the triangular relation recovers $pi(x)=sum_(k>=1)frac(mu(k)J(x^(frac(1,k))),k)$, where $mu$ is the Möbius function. This weighted count retains the prime counts exactly.

Riemann's further step was analytic continuation. A complex function initially defined by a convergent series in one region may agree there with a function having a larger domain. The geometric series is the elementary example. On $|z|<1$ it sums to $(1-z)^(-1)$, and this fraction makes sense at every complex point except one. The continuation of $zeta$ has a pole at one, trivial zeros at the negative even integers, and other zeros in the critical strip. Later chapters obtain the relevant continuation and symmetry from a Gaussian theta series.

== Why the middle line <c01s03>

The completed function
$ xi(s)=frac(1,2) s(s-1) pi^(-frac(s,2)) Gamma(frac(s,2)) zeta(s) $
is entire and satisfies $xi(s)=xi(1-s)$ and $xi(overline(s))=overline(xi(s))$. Its zeros are the nontrivial zeros. If $beta+i gamma$ is a zero, then reflection in the real axis and reflection in the vertical line $Re s=frac(1,2)$ preserve the zero set. A point on the middle line is fixed by the second reflection. Points off the line could occur in quartets. Symmetry alone allows them.

#claim[Riemann's hypothesis (1859)][Every nontrivial zero of $zeta(s)$ has real part $frac(1,2)$. Equivalently, the entire function $Xi(z)=xi(frac(1,2)+i z)$ of a complex variable $z$ has all of its zeros on the real axis.]

To see why real parts measure an error, take a conjugate pair of terms of the form $frac(x^rho,rho)$. Their sum is
$ frac(2x^beta,abs(rho)) cos(gamma log x - arg rho). $
Their oscillation is periodic in $log x$. Their amplitude grows like $x^beta$. The pole at one accounts for the macroscopic trend in prime counts. A zero with real part $0.8$ would have a different long-range effect from a zero with real part $0.5$, even if their first oscillations looked similar. Riemann's proposed location for *all* the zeros is thus a quantitative assertion about the possible size of prime-counting fluctuations.

The sum over all zeros requires a prescription for convergence, and discontinuous counting functions require an endpoint convention. Our proof will use a continuous prime sum with an elementary transform. Its zero terms can be studied one singularity at a time. This avoids making the first encounter with the problem depend on a delicate infinite explicit formula.

== What information is lost by counting prime powers? <c01s04>

Four counting functions will recur. Besides $pi$ and $J$, put
$ vartheta(x)=sum_(p<=x) log p, quad Psi(x)=sum_(p^a<=x) log p. $
In this chapter $vartheta$ counts primes with logarithmic weights. The Gaussian theta function in Chapter 3 has a different argument and meaning. Each summand in $Psi$ has one copy of $log p$, whether its argument is $p$ or $p^6$. For an integer $n$ the jumps in $J$ and $Psi$ obey
$ Delta Psi(n)=(log n) Delta J(n). $
Indeed, at $n=p^a$ the two jumps are $log p$ and $frac(1,a)$. At any other integer they both vanish. This identity has a differential interpretation. Multiplying $n^(-s)$ by $log n$ is the effect of differentiating with respect to $s$ and changing sign. Thus the transformation from the measure $dif J$ to the measure $dif Psi$ passes from $log zeta$ to its negative derivative. At a zero a logarithm needs a choice of branch. Its derivative has a well-defined pole with a residue. This small change of weight gives a decisive advantage later.

The exact inverse transformation uses the Möbius function. Define $mu(1)=1$. For squarefree $k$ having $r$ prime factors set $mu(k)=(-1)^r$, and put $mu(k)=0$ otherwise. The identity
$ sum_(d divides k) mu(d)=cases(1 & k=1,0 & k>1) $
follows by multiplying $1-1$ for each distinct prime of $k$. We can now verify the inverse for $J$ directly. At a fixed $x$ all sums below are finite since $x^(frac(1,k))<2$ for large $k$. In
$ sum_(k>=1) frac(mu(k),k) J(x^(frac(1,k))), $
the coefficient of $pi(x^(frac(1,m)))$ is the sum over factorizations $m=k a$ of $frac(mu(k),k a)$. It equals $frac(1,m) sum_(k divides m) mu(k)$. The only survivor is $m=1$. No assumption on the distribution of primes entered the argument. The inverse rests entirely on the possible exponents in a prime power.

#example[Six exponents at sixty-four][The prime counts at the successive roots of $64$ are $18,4,2,1,1,1$. Hence $J(64)=frac(1277,60)$. At exponents $2,3,5,6$ the values of $J$ to subtract or add are $frac(29,6),frac(5,2),1,1$. The inverse gives
$ frac(1277,60)-frac(29,12)-frac(5,6)-frac(1,5)+frac(1,6)=18. $
The fourth-root term is present in $J(64)$ and absent in its inverse sum because $mu(4)=0$. It has already been removed through the lower exponents. The sixth-root term reappears with positive sign because six has two different prime divisors.]

The jumps also prove an identity involving all integers. Define $Lambda(n)=Delta Psi(n)$ and set $Lambda(1)=0$. Then
$ log n=sum_(d divides n) Lambda(d). $
For example, for $n=72=2^3 3^2$ the contributing divisors are $2,4,8,3,9$. There are three copies of $log 2$ and two of $log 3$. Generally the divisors $p,p^2,dots,p^a$ of $n$ account for the full power $p^a$ in its factorization. Summing the identity over $n<=x$ and interchanging two finite sums yields
$ log floor(x)! =sum_(d<=x) Lambda(d) floor(frac(x,d)). $
Here the left side is the logarithm of the factorial of $floor(x)$. A common proof technique is to replace $floor(frac(x,d))$ by $frac(x,d)$ and control the discarded fractional parts. One then obtains a smoothed estimate from an exact identity, while keeping the prime powers at their correct weights.

== A bound of the right order from a binomial coefficient <c01s05>

The central binomial coefficient is simultaneously a count of subsets and a product of prime powers. Let $B_n=binom(2n,n)$. Since the $2n+1$ binomial coefficients in the same row sum to $4^n$, and the central one is largest,
$ frac(4^n,2n+1)<=B_n<=4^n. $
The logarithm already has order $n$. To interpret it prime by prime, count the multiples of $p^j$ in a factorial. This gives the exact expansion
$ log B_n=sum_(p^j<=2n) (floor(frac(2n,p^j))-2 floor(frac(n,p^j))) log p. $
For every nonnegative number $u$, $floor(2u)-2floor(u)$ is either zero or one. Every prime between $n$ and $2n$ occurs, and no power contributes more than one copy of its logarithm. Thus
$ vartheta(2n)-vartheta(n)<=log B_n<=Psi(2n). $
The two bounds give different information. A change of scale turns the left inequality into an upper bound for $vartheta$. The elementary lower bound for the binomial coefficient turns the right inequality into a lower bound for $Psi$.

#claim[Elementary Chebyshev bounds][There are positive constants $a,b$ such that $a x<=vartheta(x)<=Psi(x)<=b x$ for every sufficiently large $x$. In particular $pi(x)$ is bounded above and below by positive constant multiples of $frac(x,log x)$.]

#proof[At powers of two, add $vartheta(2^(j+1))-vartheta(2^j)<=2^(j+1) log 2$ for $0<=j<r$. The result is $vartheta(2^r)<=2^(r+1)log 2$. For arbitrary $x>=2$, compare it with the first power of two at least $x$. This gives $vartheta(x)<=4x log 2$. On the other hand take $n=floor(frac(x,2))$. Then
$ Psi(x)>=(x-2)log 2-log(x+1). $
For the higher powers there is the exact relation
$ Psi(x)-vartheta(x)=sum_(2<=j<=floor(frac(log x,log 2))) vartheta(x^(frac(1,j))). $
Every term on the right is at most $4sqrt(x) log 2$ and there are at most $frac(log x,log 2)$ terms. Their total is $O(sqrt(x)log x)=o(x)$. This gives both the lower bound for $vartheta$ and the upper bound for $Psi$. Finally $vartheta(x)<=pi(x)log x$. To bound $pi(x)$ above, separate the primes up to $sqrt(x)$ from the larger ones. The number in the first group is at most $sqrt(x)$, and each prime in the second contributes at least $frac(log x,2)$ to $vartheta(x)$. The claimed comparison follows.]

This proof exhibits precisely where the constants are lost. The lower bound for $Psi$ allows every prime power up to $2n$ a contribution, including powers for which the binomial exponent is zero. The upper bound for $vartheta$ covers the interval by successively smaller intervals and uses only a crude count of the total subsets at each step. To determine an exact asymptotic by such a method one would need finer average information about the floor differences. Chebyshev's memoir gives more refined constants. The estimates just proved suffice for the elementary inequalities in later chapters.

For $n=5$, $B_5=252=2^2 3^2 7$. The contribution at five itself is zero. Among the powers of two up to ten, the differences at $2,4,8$ are $1,0,1$. For $3,9$ they are $1,1$. The only prime in $(5,10]$ is seven, so the left-hand difference of Chebyshev functions is $log 7$. This example shows why replacing the full factorial by a count of primes in one interval leaves out substantial mass.

== Partial summation keeps track of the weights <c01s06>

Suppose $(a_n)$ is a sequence and $A(x)=sum_(n<=x) a_n$, with $A(x)=0$ for $x<1$. If $g$ has a continuous derivative, integrate $A(t)g'(t)$ from one to $x$. The contribution of each $a_n$ is $a_(n)(g(x)-g(n))$. Rearranging gives
$ sum_(n<=x) a_n g(n)=A(x)g(x)-integral_1^x A(t)g'(t) dif t. $
This argument includes a possible term at $n=1$ and a possible jump at $x$. It works for complex $a_n$. It gives no inequality until one estimates the two terms on the right. The ability to postpone absolute values is especially helpful for characters, whose cancellations would be lost by taking magnitudes term by term.

Apply the formula on $[2,x]$ to the jumps of $vartheta$ with $g(t)=frac(1,log t)$. Starting just below two includes its atom. We obtain
$ pi(x)=frac(vartheta(x),log x)+integral_2^x frac(vartheta(t),t(log t)^2) dif t. $
The reverse identity, obtained by weighting the jumps of $pi$ by $log t$, is
$ vartheta(x)=pi(x)log x-integral_2^x frac(pi(t),t) dif t. $
Suppose first that $vartheta(x)=x+o(x)$. Then the first term in the expression for $pi$ is $frac(x,log x)+o(frac(x,log x))$. The part of the integral below $sqrt(x)$ is $O(sqrt(x))$ by the preceding upper bound for $vartheta$. Above $sqrt(x)$ it is $O(frac(x,(log x)^2))$. This proves one direction of the asymptotic equivalence. Conversely $pi(x)∼frac(x,log x)$ gives $pi(x)log x∼x$, and the integral in the reverse identity is $o(x)$ by the same splitting argument. Together with the prime-power estimate, this proves the equivalence of the prime number theorem in its three familiar forms.

An error term can also be transported, provided one identifies the correct main term. Write $vartheta(x)=x+E(x)$ for $x>=2$. Direct differentiation of $frac(x,log x)$ shows
$ frac(x,log x)+integral_2^x frac(dif t,(log t)^2)
    =frac(2,log 2)+integral_2^x frac(dif t,log t). $
It follows that
$ pi(x)-integral_2^x frac(dif t,log t)
 =frac(2,log 2)+frac(E(x),log x)+integral_2^x frac(E(t),t(log t)^2) dif t. $
For example, $E(t)=O(sqrt(t)(log t)^2)$ makes the endpoint term $O(sqrt(x)log x)$ and the integral $O(sqrt(x))$. Thus an estimate of square-root size with two logs for $vartheta$ gives a square-root estimate with one log for $pi$ relative to the logarithmic integral. The comparison with $frac(x,log x)$ would give a much larger systematic discrepancy. This is the distinction visible in the numerical table that opened the chapter.

Taking $g(t)=frac(1,t)$ instead gives the harmonic average of the prime weights in terms of $Psi$,
$ sum_(n<=x) frac(Lambda(n),n)=frac(Psi(x),x)+integral_1^x frac(Psi(t),t^2) dif t. $
The elementary upper bound already gives $O(1+log x)$ for this average. In the proof in Part II a ramp multiplies this harmonic weight by $x$ and subtracts a second term. This calculation bounds the ramp sum by $O(x log x)$. The factorial identity below determines its actual leading term.

== Euler's product close to its boundary <c01s07>

Let $s=sigma+i tau$. For $sigma>=1+delta$ with $delta>0$, the finite products of $(1-p^(-s))^(-1)$ are uniformly bounded in modulus by $zeta(1+delta)$. If all primes up to $P$ have been included, the omitted positive integers having a prime factor above $P$ are all larger than $P$. The absolute error between the corresponding product and the full Dirichlet series is at most $sum_(n>P) n^(-1-delta)$, which tends to zero. This verifies uniform convergence on these closed half-planes. An absolutely convergent series of logarithms provides a direct proof of nonvanishing there. For $|z|<1$, $-log(1-z)=sum_(k>=1) frac(z^k,k)$ when the branch is zero at the origin. Summing with $z=p^(-s)$ gives an absolutely convergent analytic series, whose exponential is the Euler product. The exponential of a finite complex number is nonzero.

Although every individual factor is well behaved as real $s$ decreases to one, the product diverges. One can see separately which powers cause this. For real $s>1$,
$ log zeta(s)=sum_p p^(-s)+sum_p sum_(k>=2) frac(p^(-k s),k). $
The second term stays bounded for $s>=1$. Ignoring $frac(1,k)$ and summing the geometric tail bounds it above by $sum_p frac(1,p(p-1))<=sum_(n>=2) frac(1,n(n-1))=1$. The size of the first term is therefore determined up to a bounded error by the size of $log zeta(s)$. This calculation proves that prime reciprocals diverge once we know that $zeta(s)$ is unbounded near one. If their sum converged, the first term would be bounded by that sum and the second by one.

To quantify this singularity, apply partial summation to $a_n=1$. Since $A(x)=floor(x)$, for $Re s>1$ one gets
$ zeta(s)=s integral_1^infinity floor(x) x^(-s-1) dif x
 =frac(s,s-1)-s integral_1^infinity {x} x^(-s-1) dif x. $
The braces denote fractional part. It is bounded by one, so the integral on the far right is holomorphic for $Re s>0$. To justify complex differentiation on a compact subset of that half-plane, one can dominate the $j$th derivative by a constant times $(1+log x)^j x^(-1-delta)$ for some $delta>0$. We have continued $zeta$ through its original abscissa of convergence and shown that it has a simple pole of residue one. A first continuation already needs cancellation, supplied here by subtracting the continuous count $x$ from $floor(x)$.

It follows for real $h>0$ tending to zero that
$ sum_p p^(-1-h)=log(frac(1,h))+O(1). $
The parameter $h$ smooths the size of the primes, since $p^(-h)=exp(-h log p)$. It would require an additional argument to replace the smooth cutoff by a sharp condition $p<=exp(frac(1,h))$ with the same quality of error. In Part II the smoothing function is chosen to have an explicitly computable transform. One can then reason directly about the smoothed quantity throughout the proof.

#example[The finite part at the pole][The constant term of $zeta(s)$ at one is Euler's constant $gamma$. Indeed the preceding integral gives $1-integral_1^infinity {x} x^(-2) dif x$. On each interval $[n,n+1]$, integrate $frac(x-n,x^2)$ explicitly. Summing to an integer $N$ gives
$ integral_1^N {x} x^(-2) dif x=log N-sum_(n=1)^(N-1) frac(1,n+1). $
Taking limits gives the claimed value because $gamma=lim_(N->infinity)(sum_(n=1)^N frac(1,n)-log N)$. The same constant returns in Chapter 8 after multiplying the logarithmic derivative by the transform of the ramp.]

== A harmonic prime count with its constant <c01s08>

The factorial identity and Chebyshev's upper bound together determine a useful average with leading constant one, even before the prime number theorem. Replacing each $floor(frac(x,d))$ in that identity by $frac(x,d)$ makes a nonnegative error of at most $Psi(x)$ in total. Thus
$ sum_(d<=x) frac(Lambda(d),d)=frac(log(floor(x)!),x)+O(1)=log x+O(1). $
For the last equality one can compare the sum of $log n$ with the integral of $log t$, since the difference up to an integer $N$ is at most $log N$. Evaluating the integral gives $log(N!)=N log N-N+O(log(2N))$, and changing $N$ to a real $x$ with $N=floor(x)$ costs $O(log(2x))$. A bounded error after division by $x$ is all we need. The constant one in front of $log x$ here comes from the integer factorial. Write $S_(1)(x)=sum_(n<=x)Lambda(n)(x/n-1)$ for the untwisted ramp introduced above. Then $S_(1)(x)=x sum_(n<=x)frac(Lambda(n),n)-Psi(x)=x log x+O(x)$. This identifies the coefficient of $x log x$ before using a zero-free region. The Laurent expansion in Chapter 8 determines the remaining centering term.

The prime powers of exponent at least two contribute a bounded amount to this particular average. Extending their sum to infinity and summing a geometric series gives the finite majorant $sum_(n>=2)frac(log n,n(n-1))$. Hence, on writing $A(x)=sum_(p<=x)frac(log p,p)$, we have $A(x)=log x+R(x)$ with $R$ bounded for $x>=2$. A second partial summation gives
$ sum_(p<=x) frac(1,p)=frac(A(x),log x)+integral_2^x frac(A(t),t(log t)^2) dif t. $
The integral involving $R(t)$ converges as its upper endpoint tends to infinity, since $frac(1,t(log t)^2)$ is integrable there. Its tail, and the endpoint term $frac(R(x),log x)$, are $O(frac(1,log x))$. Consequently
$ sum_(p<=x) frac(1,p)=log log x+B+O(frac(1,log x)) $
for a real constant $B$. Even though we only knew $A(x)$ up to a bounded error, division by a second slowly varying weight forced the integrated error to approach a constant.

The value of $B$ is related to Euler's constant through the terms of degree at least two in the logarithm of the Euler product. Put
$ C=sum_p sum_(k>=2) frac(1,k p^k). $
This converges by the bound already proved. For $h>0$, another partial summation yields
$ sum_p p^(-1-h)=h integral_0^infinity (sum_(p<=e^u)frac(1,p))e^(-h u) dif u. $
Here a jump at $u=log p$ is weighted by $e^(-h log p)$. In the integral replace the inner sum by $log u+B$. On each fixed bounded interval the resulting error, after multiplication by $h$, tends to zero because the logarithmic singularity is integrable. On the remainder of the domain the error inside the integral tends uniformly to zero as the lower endpoint tends to infinity. The mass of $h e^(-h u) dif u$ is one, so these two observations justify a total $o(1)$ replacement as $h$ decreases to zero.

Setting $v=h u$ now evaluates the expression as
$ log(frac(1,h))+B+integral_0^infinity e^(-v) log v dif v+o(1). $
The last integral is $Gamma'(1)=-gamma$, as the product for gamma in Chapter 3 shows. On the other hand $log zeta(1+h)=log(frac(1,h))+o(1)$ from the pole of residue one. In its prime-power expansion the terms of degree at least two tend to $C$ by dominated convergence. Comparing constants proves $B+C=gamma$. Exponentiating the sharp finite prime sum now gives
$ product_(p<=x)(1-frac(1,p))^(-1) ∼ e^gamma log x. $
Indeed the logarithm of this product is $sum_(p<=x)frac(1,p)+C+o(1)$. The constant arises by comparing two ways of ordering the arithmetic data, a sharp prime cutoff and an exponentially smoothed prime cutoff. This calculation provides a small-scale example of the need to keep every centering constant when a later estimate is much smaller than the original expression.

In probabilistic language the reciprocal product is the density of integers having no prime factor at most $x$, when $x$ is *fixed* and the density is taken over a long interval of integers. Let $M$ be the product of those primes. Exactly $product_(p<=x)(p-1)$ classes modulo $M$ are coprime to it, by the Chinese remainder theorem. Dividing by $M$ gives the claim. This periodic count explains why multiplying factors for finitely many primes is exact. If $x$ grows with the sample interval, the period can exceed the length of the interval by a very large factor. The existence of the density for every fixed $x$ alone gives no error bound uniform in that simultaneous limit.

== A second use of Möbius inversion <c01s09>

For arithmetic functions $a,b$ define their Dirichlet convolution by $(a star b)(n)=sum_(d divides n) a(d)b(frac(n,d))$. At every integer this is a finite operation. Expanding $((a star b)star c)(n)$ or $(a star (b star c))(n)$ sums the same products over ordered triples with product $n$, proving associativity. Commutativity follows by exchanging complementary divisors. The identity is the function that is one at one and zero at other integers. The divisor identity for $mu$ says that this function equals the convolution of $mu$ with the constant function one. Applying this inverse to $log n=sum_(d divides n)Lambda(d)$ gives
$ Lambda(n)=sum_(d divides n) mu(d) log(frac(n,d)). $
At $n=12$ the contributions are $log 12-log 6-log 4+log 2=0$. At $n=8$ they are $log 8-log 4=log 2$. This gives the sparse prime-power weight through cancellations among values of a slowly varying function.

In a half-plane where two Dirichlet series are absolutely convergent, multiplying them implements this convolution. Fubini's theorem allows all pairs of indices to be grouped by their product. In particular $sum_n mu(n)n^(-s)=frac(1,zeta(s))$ for $Re s>1$. There is a related squarefree counting example that lets us see an exponent with a quite different origin. The indicator of a squarefree integer $n$ is
$ bold(1)_("squarefree")(n)=sum_(d^2 divides n) mu(d). $
For each prime whose square divides $n$ the two choices of whether to include it in $d$ cancel. For a squarefree $n$ the only divisor contributing is one. Therefore the number $Q(x)$ of squarefree positive integers up to $x$ satisfies
$ Q(x)=sum_(d<=sqrt(x)) mu(d)floor(frac(x,d^2))
      =frac(x,zeta(2))+O(sqrt(x)). $
To check the error, the cost of removing the floors is at most the number of terms, $sqrt(x)$. The tail of $sum_d frac(mu(d),d^2)$ has absolute value at most a constant times $frac(1,sqrt(x))$, which is multiplied by $x$. The constant $frac(1,zeta(2))=product_(p)(1-p^(-2))$ agrees with counting integers avoiding square divisibility at each of finitely many primes and then passing to the limit. The absolute convergence of $sum frac(1,p^2)$ is what permits this passage with a simple error.

The Dirichlet series of the same indicator is $frac(zeta(s),zeta(2s))$ for $Re s>1$, as each prime contributes $1+p^(-s)$. For $Re s>frac(1,2)$ its denominator is finite and nonzero by absolute convergence of the Euler product. Thus its possible singularities in this region come entirely from the numerator's pole. The elementary square-root error in $Q(x)$ reflects a cutoff at $d^2<=x$. The square-root scale in the prime-counting problem would reflect the location of zeros of the *unscaled* zeta function through a logarithmic derivative. Similar looking exponents can therefore arise from different analytic statements.

#source-note[See the #link("https://scholarlycommons.pacific.edu/euler-works/72/")[Euler Archive] and #link("https://www.numdam.org/item/JMPA_1852_1_17__366_0/")[Chebyshev's memoir]. The #link("https://www.claymath.org/collections/riemanns-1859-manuscript/")[1859 manuscript collection] and #link("https://www.maths.tcd.ie/pub/HistMath/People/Riemann/Zeta/")[Wilkins's transcription and translation] give Riemann's original argument.]
