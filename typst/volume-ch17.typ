#import "style.typ": *
#chapter[Recovering the centered sum and its exponent]

== Fourier expansion of the local count <c17s01>

Fix a translate, a step $j$ and a top place $t$. Put $a=a_t$, $w=w_j$, and let $A(a,t,w)$ be the sum of the unramified and ramified terms of Chapter 13. Let $G=E_0 times H$, $f=|Phi|=2|H|$ and $v_(t)(g)=c+g+t^+$. For a character $xi$ of $G$, write $g_xi$ for its centered *complex* ramp using the primitive inducing character, with $g_1=G_z$. Let $ell_d$ be the quadratic logarithmic derivative used in Chapter 14. Define
$ M(a,w)=a(log a-1-gamma+ell_d-frac(1,f) sum_(rho in Phi) log w(rho)). $
The finite Fourier identity is
$ A(a,t,w)-M(a,w)=
  frac(1,f) sum_(g in G backslash Phi) sum_(xi in hat(G))
       overline(xi(g)) w(v_(t)(g))g_(xi)(frac(a,w(v_(t)(g)))). $
In this equality the primitive local values at ramified primes are included through inertia. Summing over an inertia coset kills characters nontrivial on inertia. For a character trivial there it gives the coset size times the corresponding Frobenius value. That is precisely the character expansion of the ramified term.

To check the identity first write every uncentered ramp as $w S_(xi)(a/w)$. Expanding the indicators of Frobenius classes by orthogonality gives the right prime-power contributions, including the factor two at the inert primes. Next insert the center of Chapter 8. The untwisted correction equals $a log a-a log w-(1+gamma)a$. The map $g mapsto v_(t)(g)$ is a bijection of the complement of $Phi$ onto $Phi$, so the average of $log w$ is the one in $M$. The nontrivial linear corrections are $-a ell_xi$. The Fourier sum over the complement picks out the quadratic sign character and contributes $a ell_d$ to the main term. This computation identifies the analytic center with the geometric main term *before* any bound is applied.

== Recovering a prime power from the character table <c17s02>

For the calculation it pays to keep the whole finite group visible. Write its elements in coordinates $(r,s,h)$ with $r,s in ℤ slash 2ℤ$ and $h in H$. Let $n=abs(H)$, $G=(ℤ slash 2ℤ)^2 times H$, and $Phi={g:r(g)=0}$. Thus $abs(G)=4n$ and the number of places used for normalization is $f=abs(Phi)=2n$. Complex conjugation on places is addition by $c_0=(1,1,0)$. For a top location $t in H$ put $t^+=(0,0,t)$ and $v_(t)(g)=c_0+g+t^+$. For any $t$, this last map is a bijection from the complementary coset $r=1$ onto $Phi$. The positive weights $w(rho)$ are read only at $rho in Phi$, even though the Fourier expansion runs over elements of its complement. #src("Formalism.ThickAverageLoss.PartnersToFactorsAt")[Place coordinates and the two signs.] #src("Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime")[Partner and local factors.]

Let $p$ be a rational prime. The local datum is an inertia subgroup $I_p$ of $G$ and a Frobenius class modulo $I_p$. Choose a lift $h_p$. A character $xi$ of the finite abelian group takes values on the unit circle. Its primitive coefficient at $p^i$, for $i>=1$, is
$ V_(xi)(p^i)=frac(1,abs(I_p)) sum_(v in I_p) xi(i h_p+v). $
Changing the lift adds $i$ times an element of $I_p$ and permutes the indexing set. If $xi$ is trivial on inertia, this expression equals $xi(h_p)^i$. If $xi$ is nontrivial on inertia, the answer is zero for *every* positive $i$. To prove the latter assertion, choose $v_0$ in inertia with $xi(v_0)!=1$. Translation of the sum by $v_0$ multiplies it by $xi(v_0)$ and leaves its value unchanged. These two properties force its value to be zero. Notice where the exponent belongs. Inertia is averaged as a subgroup at $i h_p$. Averaging $xi(h_p+v)^i$ would raise the inertia character to the $i$th power as well, and could incorrectly restore a character which should have vanished.

Define the local coefficient attached to a group element by
$ K(p^i,g)=frac(1,f) sum_(xi in hat(G)) overline(xi(g)) V_(xi)(p^i). $
Insert the inertia average and use $overline(xi(g))=xi(-g)$. For a given $v$ the inner sum over all characters is $abs(G)$ when $i h_p+v=g$, and zero otherwise. This is finite orthogonality. It follows, for instance, by multiplying the sum at a nonzero element by a character which separates that element from zero. For fixed $g$ the equation for $v$ has exactly one solution if $g-i h_p in I_p$, and none otherwise. Consequently
$ K(p^i,g)=frac(2,abs(I_p)) bold(1)_(i h_p+I_p)(g). $
The factor two is $frac(abs(G),f)$. It comes from the normalization on the half-set of places. A Fourier inversion formula with denominator $abs(G)$ would give half the required geometric count.

At an unramified prime, $I_p={0}$ and there is a single possible $g=i h_p$, with coefficient two. If $r(h_p)=0$ it lies in $Phi$ for every $i$ and makes no contribution to the sum over its complement. If $r(h_p)=1$ it lies in the complement precisely for odd $i$. Its contribution is then twice $log p$ times the positive part of $a/p^i-w(v_(t)(i h_p))$. For a prime in the specified finite set $S_0$, which contains $2$ and the first auxiliary prime, both inertia and the Frobenius lift lie in $Phi$. Every relevant coset lies inside $Phi$ and its entire complementary sum vanishes. Thus a prime in $S_0$ is allowed to have nontrivial inertia. The vanishing uses the location of that inertia and of Frobenius, two separate parts of the local hypotheses.

At the remaining ramified prime $d$, inertia consists of $0$ and $(1,0,0)$. Addition by the latter interchanges the first coordinates. Each Frobenius coset therefore contains exactly one element of the complement, regardless of $i$. The coefficient at that element is $2/2=1$. Both the even and the odd powers of $d$ can occur. Its logarithmic factor is $log d$ throughout. This local computation also explains why it is necessary to keep the primitive inducing characters in a host of higher conductor. Assigning zero at every prime dividing the host modulus would discard the nonzero coset coefficients for all characters that are unramified there. #src("Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia")[The precise local host hypotheses.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance")[Unramified, split-set, and ramified prime computations.]

== A four-element ramified calculation <c17s03>

Here is a finite model of the last computation in which every surviving term can be listed. Use $H={0}$, omit the third coordinate, take $p=7$, and let $I={(0,0),(1,0)}$. Choose the Frobenius lift $h_p=(0,1)$. The four characters are indexed by $alpha,beta in {0,1}$ and have value
$ xi_(alpha,beta)(r,s)=(-1)^(alpha r+beta s). $
Their primitive coefficients at $7^i$ are
$ frac(1,2) ((-1)^(beta i)+(-1)^(alpha+beta i)). $
For $alpha=1$ both vanish for every $i$, including $i=2$. For $alpha=0$ they are $1$ and $(-1)^i$. Since $f=2$, the coefficient after inversion is
$ K(7^i,(r,s))=frac(1,2)(1+(-1)^(s+i)). $
It is one for $s$ of the same parity as $i$ and zero otherwise. Restricting to $r=1$ leaves $(1,1)$ for odd $i$ and $(1,0)$ for even $i$. Replacing $h_p$ by $(1,1)$ interchanges representatives of the same coset and gives the same formula. By comparison, at an unramified prime with Frobenius $(1,1)$ the odd powers pick out $(1,1)$ with coefficient two and the even powers give no complementary group element.

Now put $t=0$, $w(0,0)=2$, $w(0,1)=5$, and $a=343$. The partner adds $(1,1)$ to the chosen complementary element. For $i=1$ that partner is $(0,0)$, giving $(343/7-2)_+=47$. For $i=2$ it is $(0,1)$, giving $(343/49-5)_+=2$. For $i=3$ the coefficient is again one, but $343/343-2<0$, so the positive part is zero. All later terms are zero as well. The complete contribution of this one prime is therefore $49 log 7$. One can check it without the character group by going through the two elements in each Frobenius coset and imposing $r=1$. The agreement tests the sign of the coset, the factor two in the Fourier transform, the size of inertia, and the partner used to evaluate the weight.

There are two ways a term in this calculation can disappear. The sum over characters can make its coefficient zero, as it does at $(1,0)$ for $i=1$. Alternatively its coefficient can be nonzero while the ramp itself is zero, as at $(1,1)$ for $i=3$. This distinction allows the source to fix a single finite integer $N$ above every $a/w(rho)$ at the start. A prime power above $N$ has zero ramp for all places. Enlarging $N$ after this condition is met preserves the count. It is also consistent to keep the ramified term in the formula when $d>N$. In that case every ramp at $d^i$ vanishes by size. These observations concern the finite identity at a single host and make no use of the eventual bounds on the selected auxiliary primes.

== Deriving the global center, including its sign <c17s04>

Let $S_(xi)(y)$ be the uncentered ramp. Explicitly it is the sum through $n<=y$ of $Lambda(n)V_(xi)(n)(y/n-1)$, with $Lambda$ the von Mangoldt function. The convention at $n=y$ is immaterial because the factor there is zero. For $w>0$, multiplying the sum at $a/w$ by $w$ gives exactly the positive-part weights $ (a/n-w)_+$ of the local count. The calculations at each $p^i$ give the finite identity
$ A(a,t,w)=frac(1,f) sum_(g in G backslash Phi) sum_(xi in hat(G))
  overline(xi(g)) w(v_(t)(g)) S_(xi)(a/w(v_(t)(g))). $
Interchanging the finite sums requires no estimate on their signs or sizes. It is enough to truncate at a common $N$. The identity holds for different weights at every geometric place.

For nonprincipal $xi$, the centered function is $g_(xi)(y)=S_(xi)(y)+y ell_xi$, where $ell_xi$ is the logarithmic derivative at one of the primitive character. The principal center is $g_(1)(y)=S_(1)(y)-y log y+(1+gamma)y$. Write $D(a,t,w)$ for the right side of the preceding identity with $S$ replaced by $g$. The difference between $A$ and $D$ can be evaluated explicitly. At the principal character, $w S_(1)(a/w)-w g_(1)(a/w)=a log a-a log w-(1+gamma)a$. The complementary group elements number $f$ and the partner maps them bijectively onto $Phi$. Their normalized contribution is thus
$ a(log a-1-gamma)-frac(a,f) sum_(rho in Phi) log w(rho). $
In particular the weights enter through the logarithm of their geometric mean. A single very small weight affects this expression even if it will later be removed from a different, centered sum.

At nonprincipal $xi$ the correction is $-a ell_xi$, independent of $w$ and $t$. To sum it, choose any $e$ with first coordinate one. The complement is $e+Phi$, so
$ frac(1,f) sum_(g in e+Phi) overline(xi(g))
   = overline(xi(e)) frac(1,f) sum_(v in Phi) overline(xi(v)). $
The last mean vanishes unless $xi$ is trivial on $Phi$. Characters trivial there factor through $G slash Phi$ of order two. Its nonidentity character $chi_(d)(g)=(-1)^(r(g))$ takes value $-1$ on the complementary coset. Thus the lone surviving nonprincipal correction is $(-1)(-a ell_d)=+a ell_d$. This sign is forced already at one fixed translate. The second coordinate sign, the product of the two signs, and any character nontrivial on $H$ have zero mean in this calculation.

Altogether $A-M=D$ with
$ M=a(log a-1-gamma+ell_d-frac(1,f)sum_(rho in Phi) log w(rho)). $
For the arithmetic host $ell_d$ is real. More generally the formal identity works for an arbitrary compatible family of complex constants, since the cancellation that derives it is algebraic. With complex characters it is legitimate to take real parts of the entire identity after summing. Doing so before multiplication by $overline(xi(g))$ would in general change it. For instance $Re(i times i)=-1$ while the product of the two real parts is zero. Conjugation of a Fourier coefficient and taking a real part are different operations. #src("Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime")[Definitions of the complex center and discrepancy.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance")[The identity for any positive weights and a common truncation.]

== Thick weights and a normalized average <c17s05>

Take real parts and sum over steps and top places, keeping the translate fixed. The slope and pointwise loss estimates from Chapter 14 bound this sum. On a thick place replace $w$ by $b$, leaving the argument $y_t=frac(a_t,b)$. For example the function $w mapsto w S_(xi)(a/w)$ is a sum of $(a/n-w)_+$ terms with coefficients $Lambda(n)xi(n)$. Away from the breakpoints its derivative has absolute value at most $sum_(n<=a/w) Lambda(n)$, bounded by a constant times $a/w$ by the elementary Chebyshev upper bound. The linear nonprincipal centering term is independent of $w$ after multiplication by $w$. The derivative of the untwisted logarithmic centering term costs at most $a/w$. Integrating across breakpoints controls this first replacement uniformly over the host characters.

At a thin place one has $a_t/w>=X'/3$. The large-argument estimate in the host gives $|g_(xi)(y)|<=y vartheta_0$ there, with $vartheta_0$ small enough for the scale budget. Thus $w|g_(xi)(a_t/w)|<=a_t vartheta_0$. The analytic and arithmetic data are constructed together so that the error after summing over places meets the same budget. A thin-place character need not satisfy a square-root estimate at the original scale.

Average over all translates $u in A_0$ at the fixed argument $y_t$. Characters nontrivial on $A_0$ vanish exactly. Now transfer $g_(xi)(y_t)$ to $g_(xi)(x)$ for the surviving characters. Only these labels need control of the logarithmic derivative in this second replacement, and $|y_t-x|<=1$. Each thick location contributes the same factor after translation. With $n=|H|$, $n_T=|T|$, $n_2=|T_2|$, the normalization is $frac(b n_2,2n)$ per step and top place. Its denominator comes from $|Phi|=2n$. The residual quadratic twists contribute an error $Sigma(x)<=4o x^(1/2+epsilon)$ by the prime-pair estimate. The remaining error from approximating the top shares is bounded by a fixed multiple of $x^(-1+epsilon)$ times the rough size of a retained centered sum. #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore")[The argument move after the subgroup average.]

Put $G_x=F_(psi)(x)-Sigma(x)$, $X_1=x^(1/2+epsilon)$, $W_0=n_T m b$, and $delta_2=n_2/n$. Combining the local and global comparisons gives
$ W_0 delta_2/2 (G_x-4X_1) <= E_x+2 W_0/x. $
The same positive $W_0$ measures the size of the geometric error. Failing to divide by all $m$ steps here would forfeit a factor of nearly $sqrt(x)$.

== The two finite averages take place on different sets <c17s06>

For a single realization of the geometric comparison let $U$ be the finite set of choices called units in the source. To each $v in U$ are assigned a translate $tau(v) in H$, a nonempty finite set of words $cal(W)_v$, and positive weights for the word average. There are also $m$ successive steps and a finite set $T$ of top places. At a fixed $v$ the weights at the geometric places can depend on the step. Identifying the geometric top labels with $t in T$ and the geometric place labels with $rho in Phi$ gives the equality
$ Delta(tau(v))=sum_(t in T) sum_(j=1)^m
   ( A(a_t,t,w_(tau(v),j))-Re M(a_t,w_(tau(v),j)) ). $
Here $Delta$ is the total discrepancy for one translate, called the gap in the source. The index $j$ enumerates steps rather than the positive twists of the preceding chapter. Taking the real part of the fixed-place identity makes this same number the sum of $Re D$ over $j,t$. A numerical agreement between $m$, $f$, or the number of words cannot replace the bijections used in the identification. In particular the log-weight term in the main expression must sum over precisely the same places on both sides.

The arithmetic quantity $op("Ga")(v)$ is the retained finite-place gain for this choice of $v$. It sums the step gains minus the replacement cost with the normalized coefficient-place weights, as in Chapter 13. For fixed $v$ this sum is common to its word inequalities. In averaging the slope inequality the dimensions weight the word-dependent slopes, heights and losses, so the common gain passes unchanged through this mean. #src("Formalism.LocalRingCardinality.DataParams₂")[The gain as a sum over the supported coefficient-field places.] Two further comparisons at the very same $v$ give
$ op("ASK")(v)-op("Ga")(v)<=L_P, quad op("IO")(v)<=L_P. $
The first transfers an inequality for the word expression to the geometric prime count. The second controls the loss multiplied by a nonnegative slope coefficient in that inequality. Both have a common right-hand side. The theorem named #raw("each_unit_bound_statement") uses these hypotheses for each $v$ and bounds the geometric count by its main term plus the error at $v$. The subsequent size estimates bound that error by the common expression $E_x$. Thus one obtains $Delta(tau(v))<=E_x$ for *every* $v$. None of these operations requires the prime count attached to an individual word to satisfy the bound. #src("Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith")[Pointwise hypothesis and the statement it supports.] #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence")[Application of the two loss inequalities.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop")[Reindexing and the gap at a fixed translate.]

The translate set used in Fourier analysis is a subgroup $A_0$ of $H$. For each $u in A_0$ the construction supplies some $v$ with $tau(v)=u$. Applying the preceding inequality to one such $v$ proves $Delta(u)<=E_x$ on $A_0$. Different choices of representatives do not change $Delta(u)$, since its analytic definition is already a function of $u$. In particular there is no factor $abs(tau^(-1)(u))$ in the Fourier average. Had one averaged over units first, unequal fiber sizes could produce just such a factor. For example, if two preimages map to zero and one maps to one in $ℤ slash 2ℤ$, the sign character has unit-average $1/3$ at their images but subgroup-average zero. Orthogonality needs the latter measure. The coverage and the fixed-translate bound give exactly what is required to use it. #src("Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm")[Choosing preimages of the required translates.]

== Moving a weight and moving an argument <c17s07>

Before averaging over $A_0$, compare the stepped weight function to the common value $b$ on the thick set. The appropriate estimate for an individual character is
$ abs(w g_(xi)(a/w)-w' g_(xi)(a/w'))
   <=frac(3a,min(w,w')) abs(w-w') $
for $a,w,w'>0$, with complex modulus where needed. It is worthwhile to derive it directly. For a nonprincipal character the product $w g_(xi)(a/w)$ equals a finite sum of $Lambda(n)V_(xi)(n)(a/n-w)_+$ plus the constant $a ell_xi$. Interchange $w,w'$ if necessary so $w<=w'$. Only $n<=a/w$ can contribute to the difference. For each such $n$ the positive part changes by at most $w'-w$, since $z mapsto z_+$ is one-Lipschitz. Also $abs(V_(xi)(n))<=1$ by the inertia formula and multiplication of the local coefficients. The elementary Chebyshev estimate $sum_(n<=y)Lambda(n)<=3y$ therefore proves the displayed inequality, including the breakpoints at which $a/w$ is an integer.

For the principal character both the ramp and the logarithm vary. The ramp part $R(w)=sum_n Lambda(n)(a/n-w)_+$ is decreasing. Its drop from $w$ to $w'$ belongs to $[0,3(a/w)(w'-w)]$ by the same elementary estimate. The additional term $a log w$ is increasing, and its increase lies in $[0,(a/w)(w'-w)]$ by $log(1+s)<=s$ for $s>=0$. The net change is the difference of two nonnegative quantities in these intervals. Its absolute value is bounded by the larger upper endpoint, giving the same constant three. Adding the two absolute bounds would give four and would obscure the cancellation used in the principal case. This calculation proves a relative-in-weight estimate. A fixed absolute change in a tiny $w$ can cost much more than the same change in a thick $w$. #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum")[The positive-part and principal log estimates.]

The thick places for a given translate are specified by a subset $T_2 subset.eq A_0$. Their actual weights satisfy $b<=w<=b+eta+1$. At every top $t$, the numerators satisfy $abs(a_t/b-x)<=1$. Thus on a thick place the preceding cost is at most $3(x+1)(eta+1)$ per character. At a thin place $0<w<=2b'$ and $b'X'<=x b$. For $x>=3$ one has
$ frac(a_t,w)>=frac((x-1)b,2b')>=frac(x-1,2x) X' >=X'/3. $
The last inequality includes the endpoint $x=3$. There is an analytic bound at these *large arguments* which holds for every host character, $abs(g_(xi)(y))<=y theta$ for $y>=X'/3$. Consequently a thin place can be deleted at a cost of at most $a_t theta<=(x+1)b theta$ per character. This argument permits a thin weight to approach zero. It uses positivity of that weight, and needs the bound on $g_(xi)$ at all sufficiently large arguments since $a_t/w$ may be arbitrarily large. #src("Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis")[The large-argument input.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia")[The thick and thin size conditions.]

For a bound on the whole normalized Fourier sum there are at most $f$ complementary group elements, $2f$ characters, and a divisor $f$ in front of the sum. Each character has modulus one on group elements and hence its phase incurs no extra norm. Applying the triangle inequality costs at most $2f$ times the bound for a single term. The sum of the thick and thin budgets can be used uniformly, giving
$ 2f(3(x+1)(eta+1)+(x+1)b theta). $
The construction imposes the two inequalities $6 f(x+1)(eta+1)<=b/x$ and $2 f(x+1)theta<=1/x$. Their combined charge is at most $2b/x$ for each top and step, since the second inequality pays for the thin term after multiplication by $b$. Summed over $n_T=abs(T)$ tops and $m$ steps this is $2 n_T m b/x$. This gives the small additive term outside the four-term arithmetic error. Charging the whole cost separately to each geometric word, or omitting the number of characters from the thin estimate, would give a different inequality. #src("Formalism.SizeWindowBrackets.SChain")[The two numerical cost conditions.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore")[The thick-place comparison.]

The replacement just made changes $w$ to $b$. The argument of the remaining function is $y_t=a_t/b$. Moving this argument to $x$ requires a different estimate. For a nonprincipal character with $abs(y_t-x)<=1$ the derivative-integral estimate gives
$ abs(g_(xi)(y_t)-g_(xi)(x))<=log(x+1)+C_D+abs(ell_xi). $
For the principal character the centered derivative-integral estimate charges only $C_D$ on such a unit interval. These estimates use differences of continuous piecewise smooth functions and so still apply across an integer breakpoint. The weights and phases can now be factored before applying these bounds. At a thick place the prefactor is the chosen constant $b$, independent of $t$ and of the step. This makes the later normalization exact. In contrast, moving $a_t/w$ directly to $x$ at a thin place would need an argument estimate over a generally much longer interval. #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum")[Argument differences and weight differences.]

== Characters that survive translation <c17s08>

Define $e_(1)(h)=(1,0,h)$. With thin places deleted, the thick expression for a given translate $u$ and top $t$ is the complex number
$ T_(u,t)(y)=frac(b,f)sum_(s in T_2)sum_(xi in hat(G))
                xi(-e_(1)(s+u-t)) g_(xi)(y). $
The sign and the location of $t$ follow by taking the inverse character at the complementary element determined by the thick partner. To calculate the translate average, write in the group
$ -e_(1)(s+u-t)=e_(1)(t)+(0,0,-s)+(0,0,-u). $
The first coordinate on the left is again one because it has order two. Summing $xi(0,0,-u)$ over $A_0$ gives zero unless $xi$ is trivial on the embedded copy of $A_0$. Denote the set of surviving characters by $Psi_A$. If $xi in Psi_A$, the factor $xi(0,0,-s)$ is also one for every $s in T_2$, since $T_2 subset.eq A_0$. For each top this proves
$ frac(1,abs(A_0))sum_(u in A_0) T_(u,t)(y)
   =frac(b delta_2,2)sum_(xi in Psi_A) xi(e_(1)(t)) g_(xi)(y), $
where $delta_2=abs(T_2)/n$. The factor $1/2$ survives even though every thick place contributes at every step in this normalized expression. It is the same denominator $f=2n$ as in the local identity. #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore")[The finite character sum and the expression after translation.]

The phase $xi(e_(1)(t))$ in general still depends on $t$. Let $K subset.eq Psi_A$ be the retained characters of the target. They satisfy $xi(1,0,0)=1$, so this phase reduces to $xi(0,0,t)$ for those characters. If $xi$ is trivial on the copy of $H$ the remaining phase is identically one. Otherwise the constructed top set has prescribed character shares. In the notation of the comparison put $c=(3o+1)^(-1)$ and $M_0=4o$, where $o$ depends only on the fixed target. The required estimate is
$ abs(sum_(t in T)xi(0,0,t)-c n_T)<= M_0 x^(-1+epsilon)n_T. $
Here $M_0$ is also an upper bound on $abs(Psi_A)$ for this host. The estimate is on complex Fourier coefficients of the actual top distribution. A top set of the right cardinality but concentrated in a single character fiber can violate it. #src("Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia")[The exact hypotheses on retained phases.] #src("Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm")[The constants for the target character.]

Define $lambda_xi=1$ for retained characters trivial on $H$ and $lambda_xi=c$ for the other retained characters. The target in the host and the auxiliary remainder are
$ F=sum_(xi in K)lambda_xi Re g_(xi)(x),
  quad Sigma=sum_(xi in Psi_A backslash K) abs(g_(xi)(x)). $
For the realized primitive host the first expression is exactly $F_(psi)(x)$, as one checks by matching its character labels. The second is a sum of *norms*. At a surviving discarded character the real part of $xi(e_(1)(t))g_(xi)(x)$ is at least $-abs(g_(xi)(x))$, which accounts for its minus sign in the lower bound for the translated signal. This explains the distinction between discarding a character by exact subgroup orthogonality and bounding a survivor by its absolute value. Only the latter costs part of $Sigma$. #src("Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq")[Identification of the retained expression.] #src("Development.AutomorphicArithmetic.PrimitiveCosets.SigALe")[The estimate for the surviving remainder.]

To bound the error in the top shares one needs only a rough bound at $x$. For nonprincipal $xi$ the same argument estimate gives $abs(g_(xi)(x))<=x(log x+C_D+abs(ell_xi))$. For retained nonprincipal characters $abs(ell_xi)<=K_0$ with fixed $K_0$. Consequently replacing the top share by $c$ costs at most
$ M_0 x^(-1+epsilon) x(log x+C_D+K_0) $
per top after normalization of the top sum. The leading $x$ in the rough estimate cancels with $x^(-1)$ in the share error. A share precision of order only $x^(-1/2)$ would leave a square-root cost times a logarithm at this point. The discarded survivors need no share estimate. Their logarithmic derivatives can grow as $C_E log x$, which still permits a unit argument move at logarithmic cost. The proof makes these three cases separately, since applying the fixed bound $K_0$ to discarded characters would assume information never supplied by the prime-pair result.

For fixed $epsilon>0$, the sum of all the unit-move and share errors over at most $M_0$ characters is eventually at most $4x^(1/2+epsilon)$. For example, the share term just displayed is of order $x^epsilon log x$ with a fixed coefficient. Since $log x<=4 x^(1/4)$ for $x>=1$, a second factor $x^(1/4)$ eventually absorbs the fixed constants and the number of characters. The source uses a common lower threshold of this kind. No pointwise square-root estimate for a retained character has entered the deduction. Its real part is precisely the quantity to be bounded by the geometric argument. Writing $G_x=F_(psi)(x)-Sigma$ and summing the thick comparison over all tops and steps now gives
$ (n_T m b) frac(delta_2,2)(G_x-4x^(1/2+epsilon))
  <= E_x+frac(2 n_T m b,x). $
The upper estimate for every translate can be averaged with equal weights on $A_0$, so it contributes only the single error $E_x$ on the right. The left side results from the exact subgroup average followed by the lower bound for the top phases. These inequality directions are what turn the geometric upper bound into a one-sided bound for the target.

== A complete translate calculation in a cyclic host group <c17s09>

A second finite example illustrates the role of the top phase left after subgroup averaging. It uses only the Fourier portion of the comparison. Take $H=ℤ slash 4ℤ$, $A_0={0,2}$, and $T_2={0}$. Then $n=4$, $f=8$, and $delta_2=1/4$. The characters on $G$ can be written
$ xi_(alpha,beta,k)(r,s,h)=(-1)^(alpha r+beta s) i^(k h), $
where $alpha,beta$ are zero or one and $k$ runs through residues modulo four. Fix $t=1$. In the thick expression there is just one value of the index from $T_2$, and at translate $u$ its phase is $(-1)^alpha i^(k(1-u))$. Averaging over $u=0,2$ yields
$ (-1)^alpha i^k frac(1+(-1)^k,2). $
Thus the characters with $k=1,3$ disappear, however large their centered sums may be. For $k=0$ the phase is $(-1)^alpha$ and for $k=2$ it is $-(-1)^alpha$. This leaves eight surviving characters, exactly the characters of the quotient group $G slash ({(0,0)} times A_0)$. Each surviving centered function has prefactor $b/8=b delta_2/2$ times its phase. For instance a vector of test values supported only on $(alpha,beta,k)=(0,0,2)$ with value three gives $-3b/8$ in the mean at this top. Testing a single coordinate in this way checks an equality between complex linear functionals without having to prescribe analytic data having those test values.

One can also see explicitly why $T_2$ must lie in $A_0$ in the simplification of the mean. If instead the lone thick label were the element one, the same calculation for even $k$ would give the additional factor $i^(-k)$. At $k=2$ this would reverse the sign of the term just tested. With the permitted thick label two, the extra factor would be $i^(-2k)=1$ for every survivor, just as for the original thick label zero. Increasing the actual thick set from $\{0\}$ to $\{0,2\}$ doubles every surviving coefficient to $b/4$. Its density doubles as well. This calculation isolates the need for both the inclusion in the translating subgroup and the numerical density in the final estimate.

Suppose we follow one of these survivors, taking $alpha=0$ and $k=2$. Its phase at top $t$ is $(-1)^t$. If the top set contains all four elements of $H$, the average phase is zero. If it contains just the even elements the average phase is one. With $T={0,1,2}$ it is one third. Thus even an exact computation of the translate mean alone leaves open quite different possibilities for the final top sum. In the arithmetic construction the set of tops is chosen to approximate the particular coefficient $c$ for this sort of retained character, simultaneously over the fixed collection. If the actual share differs from its prescribed value by $z$, a constant test value $g_(xi)(x)=z_0$ produces complex error $z z_0$ per top. Its real part can have either sign. Bounding it by $abs(z)abs(z_0)$ is exactly the share-error estimate used above. If the test values depend on $t$, first compare them with their value at $x$ and then use the bound for the share. Factoring a variable value directly from the top sum would incorrectly treat $g_(xi)(a_t/b)$ as independent of $t$.

These two finite examples test different Fourier operations. At a prime, the inertia annihilator and the single Frobenius coset determine a local coefficient before the prime sum is formed. At the global comparison, the subgroup $A_0$ acts on an already centered expression. Its annihilator restricts the remaining character labels, and the top phases then produce the desired real combination. An inertia character disappearing at the prime seven need not disappear at any other prime. A character killed by the final translate average disappears from the entire centered expression at that host. The order allows the local arithmetic at every prime to contribute to each surviving global centered sum.

== Four errors, counted separately <c17s10>

The lower bounds on $m$ and $n_T$ ensure each is at least one, and the common reference weight $b$ is positive. We may therefore divide by $W_0=n_T m b$. The common upper estimate for the discrepancy of one translate has the form
$ E_x<= x^(C_* epsilon)( n_T a_(E)(1+m^2/k)
      +m(2 n m b x^epsilon+frac(n_2 k b x^(2epsilon),n^2))). $
The power outside the parentheses collects the uniform geometric losses. In the construction we can take $C_*=e_D+e_L+3$. The first two costs count top terms and use the common upper size $a_E<=2x b$. The other two have an initial factor $m$ because they have already been incurred at each step. For the fourth term the original formula has denominator $n(n x^(-epsilon))$ and numerator containing $x^epsilon$. Its equivalent form above makes the two powers of $x^epsilon$ easy to track. Replacing this factor by one power would improve the apparent bound without changing any other line in the calculation.

The rank and density requirements used in simplifying the bracket are
$ n_T>= n x^(-epsilon/8)/2, quad x^(-epsilon)<=delta_2<=1, $
$ x^(1/2-epsilon)<=m<=x^(1/2+epsilon/2), quad
        x m<=k<=n^2 x^(1/2-epsilon). $
They hold for the selected even chain length, chosen on the scale $sqrt(x delta_1)$ with $delta_1=x^(-epsilon/8)$.

Write $Y_x=x^(1/2+13epsilon/8)$. The following table presents the four positive terms inside the parentheses. Each number in the last column bounds the *normalized* term. The factor $x^(C_*epsilon)$ has been set aside throughout the table.

#block(width: 100%)[
#set text(size: 9.5pt)
#table(
  columns: (1.1fr, 1.2fr, 1.15fr),
  inset: (x: 4pt, y: 4.5pt),
  align: (left, left, left),
  table.header([Cost in the bracket], [After division by $W_0$], [Upper bound]),
  [$n_T a_E$], [$a_E/(m b)$], [$2x^(1/2+epsilon)$],
  [$n_T a_E m^2/k$], [$a_E m/(k b)$], [$2$],
  [$2n m^2 b x^epsilon$], [$2 n m x^epsilon/n_T$], [$4Y_x$],
  [$m n_2 k b x^(2epsilon)/n^2$], [$(n_2/n_T)(k/n^2)x^(2epsilon)$], [$2x^(1/2+9epsilon/8)$],
)
]

For the first row use $a_E<=2 x b$ and $m>=x^(1/2-epsilon)$. Dividing by the number of steps turns a cost of order $x$ into one of order $x/m$. For the second row the same numerator estimate gives $2 x m/k$, bounded by two because $k>=x m$. Increasing $m$ makes the first of the two terms containing $a_E$ less expensive and the second more expensive when $k$ is held fixed. They also charge the same top count as the signal, so no top-density loss enters either row.

For the third row use $n_T>=n x^(-epsilon/8)/2$ to get $2n/n_T<=4 x^(epsilon/8)$. Next $m<=x^(1/2+epsilon/2)$ supplies the half-power. The extra powers of $x^epsilon$ in this product have coefficients $1$, $1/8$, and $1/2$, whose sum is $13/8$. The first is in the geometric cost, the second is the inverse top density, and the last is the permitted excess in the chain length. Using the *lower* bound on $m$ here reverses the inequality. For the fourth row one again spends the inverse top density, now using $n_2<=n$. The upper bound $k<=n^2 x^(1/2-epsilon)$ then yields the power $1/2+(2-1+1/8)epsilon=1/2+9epsilon/8$. The factor $m$ has canceled completely. The upper bound on $k$ and the lower bound on $k$ in the previous row are used in different places.

Every exponent in the right column is bounded by that of $Y_x$ for $x>=1$. Because $Y_x>=1$, the four numerical coefficients add to $2+2+4+2=10$. In normalized form the arithmetic error is therefore at most $10 x^(C_*epsilon)Y_x$. The table used only upper and lower bounds on the ranks, so it remains valid after an integral rounding satisfying those bounds. The argument would still work for any admissible host satisfying these weakened inequalities. Construction of a host with all the other required properties was the separate existence problem. #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum")[The four inequalities in the size proposition.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop")[The bracket before division.]

There is a quick way to predict which ranks should be sought. Temporarily suppress all powers involving $epsilon$ and suppose $a_E$ has size $x b$ and the top density is bounded below by a positive constant. Two of the normalized expressions then have sizes $x/m$ and $m$. If $m=x^alpha$, their exponents are $1-alpha$ and $alpha$. The larger is at least $1/2$, with equality at $alpha=1/2$. The other two costs require a range of $k$ broad enough to make both small. Under the actual assumptions the second term is bounded by a constant, while the fourth is allowed a half-power. This asymmetry accounts for the different appearances of $k$. Simply asking that $m$ be very large would control the first row at the price of losing the third. The calculation identifies why a nearly square-root chain occurs without asserting an optimality property for an individual arithmetic host, where some costs could be smaller.

== Exponent accounting <c17s11>

Set $P_x=x^(C_*epsilon)$ and $X_1=x^(1/2+epsilon)$. Dividing the averaged inequality by $W_0$ and applying the four estimates gives
$ frac(delta_2,2)(G_x-4 X_1)<=10 P_x Y_x+2/x. $
We have $x>=3$, $P_x>=1$, and $Y_x>=1$. Thus $2/x<=1<=P_x Y_x$. Multiplication by two gives $delta_(2)(G_x-4 X_1)<=22 P_x Y_x$. The arithmetic construction ensures $delta_2>=x^(-epsilon)>0$. Dividing by the actual positive density yields
$ G_x-4 X_1<=22 P_x Y_x/delta_2<=22 P_x Y_x x^epsilon. $
This argument applies to either sign of $G_x-4 X_1$. If one tries to replace $delta_2$ by its lower bound on the left of the previous inequality, the sign matters. Division by the known positive density first avoids that issue.

Since $P_x Y_x x^epsilon=x^(1/2+(C_*+21/8)epsilon)$ and this also bounds $X_1$, we obtain
$ G_x<=26x^(1/2+(C_*+21/8)epsilon). $
Here twenty-two came from twice the sum of ten arithmetic units and one unit for the thick and thin replacements. Four came from the top and character perturbations. The eighths have a different origin from these numerical constants. The $13/8$ in the four costs became $21/8$ when we divided by the thick density. For each fixed $epsilon>0$ and sufficiently large $x$ we have $26<=x^(3epsilon/8)$, so that the coefficient $21/8$ becomes three. This use of a late threshold is legitimate because the geometry and prime-pair construction provide arbitrarily late windows. The threshold generally depends on $epsilon$. The inequality with coefficient one does not follow uniformly as $epsilon$ tends to zero with $x$ fixed. #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum")[The numerical argument in the size bound.]

Finally the prime-pair estimate for the surviving auxiliary characters gives $Sigma<=4o X_1$. It bounds their *sum of absolute values*. Possible cancellation among these characters is unnecessary. The exponent $1/2+epsilon$ is at most $1/2+(C_*+3)epsilon$, so
$ F_(psi)(x)=G_x+Sigma
   <=(1+4o)x^(1/2+(C_*+3)epsilon). $
For the fixed target, $1+4o<=x^epsilon$ eventually. Substitution of $C_*=e_D+e_L+3$ gives the final exponent $1/2+(e_D+e_L+7)epsilon$. In the supplied geometric estimates $e_D=2$ and $e_L=0$, so the coefficient of $epsilon$ is nine. This is a pointwise upper estimate for the retained real centered signal at the physical points for which the comparison data were supplied. It does not assert a modulus estimate for every individual complex ramp in the host. #src("Development.AutomorphicArithmetic.PrimitiveCosets.SigALe")[Uniform cost of the auxiliary survivors.] #src("Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm")[The final target estimate.]

#example[A numerical audit of the powers][Take $epsilon=1/500$ and $C_*=5$. Before the outside geometric factor the largest row exponent is $0.50325$. Multiplication by $x^(5epsilon)$ raises it to $0.51325$. Division by $delta_2$ permits another $0.002$, giving $0.51525$ with the factor $26$. Absorbing that constant costs $3epsilon/8=0.00075$ in the exponent, leading to $0.516$. Removing the auxiliary remainder and absorbing $1+4o$ yields $0.518$. For the numerical constants themselves, the simplification of $26$ by itself requires $x^(0.00075)>=26$. At moderate numerical arguments the explicit version with factor $26$ is the one justified by that part of the argument.]

The one-sided nature of the result is matched to the later oscillation argument. A hypothetical zero in the forbidden half-plane supplies large positive values of the retained real signal on suitably late windows. The role of the cohomological, geometric, and analytic constructions is to make the comparison available on a window on which such a positive value would have to occur. The error computation in this chapter is at an individual point of that window. The ordering of the intervals, characters, and small parameters needed to apply it is the subject of the final chapter.

#source-note[The #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance")[exact Fourier identity], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop")[geometric upper estimate], #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore")[character average], and #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum")[four-term size bound] give #src("Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm")[the final pointwise inequality].]
