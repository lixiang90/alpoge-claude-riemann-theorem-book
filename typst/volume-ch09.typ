#import "style.typ": *
#set par(leading: 0.585em, spacing: 0.64em)
#chapter[How a zero forces a positive excursion]

== A window version of Landau's argument <c09s01>

#claim[Theorem 9.1][Fix a finite positive family as in Proposition 8.1. Suppose $0<theta<1$ and $delta>0$. If for some real $C_0$ there are arbitrarily large $Y$ such that $F(x)<=C_0 x^theta$ at every $x in [Y,Y^(1+delta)]$, no member has a zero with $theta<Re s<1$.]

With an eventual two-sided bound, the defining integral itself would continue the transform. Here an upper bound holds only inside certain intervals. Write $g(u)=F(e^u)$ and let $Phi$ be its Laplace transform. From an eligible interval we will extract a high derivative order $k$ for which the signed Taylor coefficients
$ A_(k)(z)=frac((-1)^k,k!) Phi^((k))(z) $
satisfy a joint upper bound at a real center and a vertical translate. At an isolated pole a calculation with Cauchy's formula supplies a lower bound at those same orders. The proof first works out that local calculation, then derives the interval estimate, and finally selects the two centers. #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindowIneq")[The moment inequality.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow")[The window conclusion.]

A stronger form allows an integrable upper envelope on each interval. The proof below treats both hypotheses in the same calculation. With the pointwise hypothesis of Theorem 9.1 the bound inside the interval follows immediately by integrating a gamma density. With an integrable envelope one retains a small exponential loss until the two radii have been compared.

== A pole is visible in high derivatives <c09s02>

Here is an experiment that can be done before choosing an arithmetic interval. Take real numbers $beta,t$ with $t>0$ and put
$ g(u)=e^(beta u)cos(t u), quad u>=0. $
Its Laplace transform is
$ Phi(s)=frac(1,2)(frac(1,s-beta-i t)+frac(1,s-beta+i t)). $
At a complex center $z$ to the right of both poles, the signed Taylor coefficient of order $k$ is consequently
$ A_(k)(z)=frac(1,2)((z-beta-i t)^(-k-1)+(z-beta+i t)^(-k-1)). $
The sign $(-1)^k$ in the normalization cancels the sign in the $k$th derivative of the reciprocal. For real $z=sigma$ the two summands are conjugate. Their real parts can nearly cancel for individual values of $k$. For $z=sigma+i t$, the denominator of the first term is the positive number $sigma-beta$ and the other has modulus $sqrt((sigma-beta)^2+4t^2)$. The first term eventually dominates in absolute value regardless of $k$. For example, with $sigma=3$, $beta=0.6$ and $t=5$, the ratio of the smaller contribution to the larger is
$ (frac(2.4,sqrt(2.4^2+100)))^(k+1). $
For any height $v$, the difference of the two squared distances is $4v t$. Their order switches as the center crosses the real axis. The parameter $sigma$ in the window proof must also satisfy the kernel estimates below.

In a general meromorphic transform the identity with two rational functions is replaced by a local expansion at a selected pole. Suppose the open region containing a closed disk about $z$ contains just one pole inside the disk, at $rho$, and in a punctured neighborhood of that pole one has $Phi(s)=c/(s-rho)+H(s)$ with $c!=0$ and $H$ holomorphic. Subtract the principal part on the entire disk. The difference extends holomorphically across $rho$ by the given germ. For any circle of radius $r$ in this disk, centered at $z$ with $abs(z-rho)<r$, Cauchy's formula yields
$ abs(A_(k)(z)-frac(c,(z-rho)^(k+1))) <= frac(M_r,r^k), $
where $M_r$ is the maximum modulus of the extended difference on the circle. The same $M_r$ works for every $k$. For a disk with no pole the same argument gives $abs(A_(k)(z))<=M_r r^(-k)$. We compare these exponential rates; the maxima on finitely many fixed circles may be very large without affecting the conclusion.

A distinction from radius-of-convergence arguments is important here. The arithmetic estimate will control moments on a subsequence of orders $k$ chosen by the available intervals. The formula for a single isolated pole provides a lower bound for *every sufficiently large* $k$. A general limsup statement for Taylor coefficients could give a large coefficient on another subsequence entirely. Isolation, and not merely identification of the radius of the Taylor disk, supplies the required quantifier. #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.IteratedDerivLaplace")[Differentiation.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauNearest")[Pole isolation.]

== The integral inequality with a variable majorant <c09s03>

For the family in Chapter 8 put $g(u)=F(e^u)$. Its local regularity suffices for measurability, and $abs(g(u))<=C exp(2u)$ for $u>=0$. For a compact disk in $Re s>2$, take $b>0$ so that $Re s>=2+b$ on the disk. The $j$th differentiated integrand is dominated in modulus by $C u^j e^(-b u)$, which is integrable. This follows either by iterated integration by parts or by absorbing a fixed power of $u$ into $e^(b u/2)$. Differentiation under the integral on the disk is therefore legitimate at any fixed order. Dividing by the factorial gives precisely the coefficients defined above,
$ A_(k)(z)=integral_0^infinity g(u) frac(u^k,k!)e^(-z u) dif u. $
The sign was chosen so that the weight is nonnegative at real $z$. For all $t$ and all $k$,
$ abs(A_(k)(sigma+i t))<=integral_0^infinity abs(g(u))w_(k)(u) dif u, $
where $w_(k)(u)=u^k e^(-sigma u)/(k!)$. Add $Re A_(k)(sigma)=integral_0^infinity g(u)w_(k)(u)dif u$. The algebraic identity $abs(v)+v=2max(v,0)$, valid for real $v$, gives the bound by twice the integral of the positive part. No assumption on a lower bound for $g$ enters. Nor does the right side now depend on $t$.

One can see the purpose of the second coefficient by trying to omit it. Consider $g(u)=-exp(beta u)$, whose values satisfy $g<=0$. Its transform is $-1/(s-beta)$. The absolute value of a vertically shifted coefficient near the pole can be arbitrarily large relative to the bound predicted by an upper estimate for $g$. Adding the real coefficient allows a negative contribution. At a *real pole* of the arithmetic transform this still proves a contradiction, because Chapter 8 showed that its residue is positive. The elementary example explains why the condition on real residues must appear among the assumptions of the general analytic theorem.

The release allows more freedom than the pointwise bound in Theorem 9.1. In the logarithmic variable its hypothesis reads as follows. For every $eta>0$ and every $U_0$ there exist $U>=U_0$ and an integrable weighted majorant on $I=[U,(1+delta)U]$. More precisely a function $R$ on $I$ satisfies $R>=0$, $g<=R$, and
$ integral_I R(u)e^(-theta u) dif u <= exp(eta U). $
A pointwise bound $F(x)<=C_0 x^theta$ gives this with $R(u)=max(C_0,0)e^(theta u)$. Its integral is $max(C_0,0)delta U$. For fixed $eta>0$ the exponential on the right eventually exceeds that linear quantity. In the original $x$ variable the weighted measure is $x^(-theta-1)dif x$; substituting $x=e^u$ accounts exactly for the extra factor $x$ in the Jacobian. An interval in $x$ of endpoints $Y,Y^(1+delta)$ has precisely these logarithmic endpoints.

For $alpha=sigma-theta>0$, the exponential series gives $(alpha u)^k/(k!)<=exp(alpha u)$ for $u>=0$. Hence
$ frac(u^k,k!) e^(-alpha u)<=alpha^(-k). $
The contribution of $I$ to the sum of the two moments is at most $2alpha^(-k)exp(eta U)$. The bound is valid for every order before the order has been chosen. The exterior contribution is bounded by
$ 2C integral_([0,infinity) backslash I) frac(u^k,k!)e^(-(sigma-2)u)dif u. $
These two terms impose different requirements on $sigma$ and $k$. The first controls the interval on which arithmetic information is available. The second contains only the rough global estimate. Its smallness is paid for by the freedom to choose the derivative order after learning the interval.

== Exponential localization, including the constants that must be uniform <c09s04>

We give a normalization that explains the choice. Let $a=sigma-2>0$, let $q=k+1$, and regard $T$ as a positive random variable with density
$ frac(a^q,(q-1)!) u^(q-1) e^(-a u). $
The integral of this density is one by repeated integration by parts. Its mean is $q/a$ and its variance is $q/a^2$, as follows by using the same integral at exponents $q$ and $q+1$. The exterior integral just displayed is $a^(-q)$ times the probability that $T$ is outside $I$. A variance estimate would give only a negative power of $q$ for this probability. We require an exponential bound because the two rates $a$ and $sigma-theta$ in the moments are different.

For $v>1$ use Markov's inequality on $exp(lambda a T)$ with $0<lambda<1$. Its expectation is $(1-lambda)^(-q)$ by direct integration. The upper-tail probability at $v q/a$ is therefore at most $exp(-lambda v q)(1-lambda)^(-q)$. For $0<v<1$ exactly the same expression bounds the lower-tail probability when $lambda<0$; the exponential is now decreasing in $T$, which reverses the event. Setting $lambda=1-1/v$ in each case gives
$ exp(-q I(v)), quad I(v)=v-1-log v. $
The rate is strictly positive away from one since $I(1)=0$ and $I'(v)=1-1/v$. This argument simultaneously supplies the numerical estimate and the direction of each inequality. It is the exponential improvement over the elementary variance bound that makes localization on a single window possible.

Choose $q$ nearest to $a(1+delta/2)U$, increasing $U$ enough to have $q>=1$. The two endpoint ratios $a U/q$ and $a(1+delta)U/q$ tend to
$ v_- = frac(1,1+delta/2), quad v_+ = frac(1+delta,1+delta/2). $
These depend only on $delta$ and lie on opposite sides of one. Choose $c_delta>0$ less than half the smaller of $I(v_-)$ and $I(v_+)$. By continuity, for every sufficiently large $U$ both tails together have probability at most $2e^(-c_delta q)$. The large-$U$ threshold may depend on the eventual value of $a$. The exponent $c_delta$ has already been chosen independently of $a$.

We may now fix $sigma$ large enough that $a(1+delta/2)>2$ and
$ log(frac(sigma-theta,sigma-2))<c_delta. $
The logarithm tends to zero as $sigma$ tends to infinity. The first inequality gives $k>=U$ for large $U$ after integer rounding. The second one gives
$ a^(-q)e^(-c_delta q)<=(sigma-theta)^(-q). $
Thus the exterior term is bounded by a constant times $(sigma-theta)^(-k)$. These choices are made once for the family and the width. For an arbitrarily late eligible $U$ one obtains an integer $k>=U$ and an inequality
$ abs(A_(k)(sigma+i t))+Re A_(k)(sigma)
    <=C_1 (sigma-theta)^(-k) exp(eta U) $
for every real $t$. For the pointwise hypothesis put $C_+=max(C_0,0)$. The interior contribution is at most $2C_+ integral_0^infinity frac(u^k,k!)e^(-(sigma-theta)u)dif u=2C_+(sigma-theta)^(-k-1)$. Thus the same bound for the two coefficients holds without the factor $exp(eta U)$ in Theorem 9.1. With the weaker majorant this factor will be absorbed by a strict gap between two radii.

#example[The width in logarithmic coordinates][For $delta=1/2$ the limiting endpoint ratios are $4/5$ and $6/5$. Their rates are $-1/5-log(4/5)>0$ and $1/5-log(6/5)>0$. As $k$ increases the relative shape of the density at the point $v$ times its mode is $exp(-k I(v))$. This is the function plotted in the kernel figure. The actual interval has length $U/2$, which grows linearly in $U$. An interval with fixed length in the logarithmic variable would put both endpoint ratios progressively closer to one and would lose this fixed positive tail rate.]

#figure(image("kernel.svg", width: 94%), caption: [The positive weight divided by its maximum, plotted against $v=a u/k$. Increasing the derivative order concentrates more of the mass in the shaded interval.])

== Geometry of the two centers <c09s05>

It remains to compare the moment inequality with a pole. Suppose a family member has a zero with $theta<Re rho<1$. Proposition 8.1 makes it a pole of the real-family transform. In $Re s>0$ the only possible poles are zeros of the selected functions or their conjugates. Classical boundary nonvanishing puts all of these in the open strip. Every pole under consideration is to the left of $Re s=sigma$. Put $E=sigma-theta$, so the closed disk of radius $E$ about the real point $sigma$ lies in $Re s>=theta>0$. Only finitely many poles lie in that disk. Define $D$ to be the minimum of $E$ and the distances to those poles, using $D=E$ if the disk is empty. The open disk of radius $D$ is free of poles. Notice the choice of an *open* disk here; a closest pole may lie on its boundary.

Suppose some pole $rho_1$ has horizontal distance $sigma-Re rho_1<D$. At the center $z_0=sigma+i Im rho_1$ this pole has distance strictly less than $D$. Small changes in the height preserve the strict inequality. On a small closed interval of candidate heights, take all poles that could be at distance $D$ or less from a center in that interval. They lie in a compact rectangle contained in $Re s>0$, hence form a finite set. For two distinct candidates $rho_a=x_a+i y_a$ and $rho_b=x_b+i y_b$, equality of squared distances at $sigma+i t$ is equivalent to
$ 2t(y_a-y_b)=(sigma-x_a)^2+y_a^2-(sigma-x_b)^2-y_b^2. $
If $y_a!=y_b$ this excludes at most one height. If $y_a=y_b$, equality of horizontal distances would imply $x_a=x_b$, since both candidates are left of the line. Avoid the finite set of exceptional heights. There is now a unique closest pole $rho$ with $d=abs(z-rho)<D$. Choose $d<r<D$ small enough to exclude every other candidate. This $r$ works both for a pole-free disk at the real center and for a disk with a single pole at the shifted center.

The pole and pole-free Cauchy estimates of #link(<c09s02>)[§9.2] give, for all sufficiently large $k$,
$ abs(A_(k)(z))+Re A_(k)(sigma)
   >=abs(c)d^(-k-1)-C_2 r^(-k)
   >=frac(abs(c),2d)d^(-k). $
No sign is required of the generally complex residue $c$ in this branch. The real coefficient can cost at most its own modulus, which grows at the slower rate because $r>d$. Choose $eta>0$ smaller than $log(E/d)$. Since $U<=k$, the ratio of the upper bound to $d^(-k)$ is at most a constant times $(exp(eta)d/E)^k$, tending to zero. Select successively later intervals at this fixed $eta$. Their integers $k$ are unbounded, so the two estimates contradict one another.

In the other case all horizontal distances are at least $D$. A proposed pole to the right of $theta$ has horizontal distance less than $E$, so $D<E$. The definition of $D$ gives a pole at Euclidean distance exactly $D$ from $sigma$. Euclidean distance is at least horizontal distance, and here horizontal distance is at least $D$. Equality forces zero imaginary part, so the pole must be $beta=sigma-D$ on the real axis. It is the unique pole on that circle because the only point reaching both equalities is the real point just identified. Choose $r$ strictly between $D$ and $E$, sufficiently near $D$ to exclude all other poles. The residue $c$ at $beta$ is real and positive by Chapter 8. Thus
$ Re A_(k)(sigma)=c D^(-k-1)+O(r^(-k)). $
Taking $t=0$ in the moment inequality bounds a quantity at least as large as this positive real part. Choose $eta<log(E/D)$ and let $k$ tend to infinity along the orders supplied by the intervals. The contradiction proves Theorem 9.1 and the analogous conclusion under the integral hypothesis. The positive sign of the real residue supplies the lower bound in this last case.

#figure(image("landau-centers.svg",width: 91%),caption: [Distances in the complex-pole alternative. The larger circle about the real center misses the illustrated pole. At the shifted center a smaller radius reaches it. The actual proof perturbs the height to resolve ties.])

== What the quantifiers say about excursions <c09s06>

Fix a real-family sum $F$, a width parameter $delta>0$, and an exponent $theta$ below the real part of a member's zero and above zero. For *each* positive constant $C_0$ the conclusion of the argument means the following:
$ exists A, forall Y>=A, exists x in [Y,Y^(1+delta)],
             quad F(x)>C_0 x^theta. $
This is the logical negation of the good-window hypothesis for that constant, with the existence of the zero now held fixed. Neither the point of excursion nor the threshold $A$ need be uniform in the height of the zero or in the family. Only the progression from a proposed zero to a contradiction at fixed parameters is used.

The result is stronger than a statement of unbounded limsup along some sequence of points. If all one knew were a sequence of large positive values, the arithmetic side could supply good intervals lying between them. The width and the particular nesting of the quantifiers avert this possibility. Conversely one does not need the good arithmetic intervals to have a positive density, to start at predetermined positions, or to cover the entire axis. Existence of one interval beyond an independently obtained threshold suffices. We can now leave the analytic argument behind and ask how to make such an interval for the specific real family whose coefficients we control arithmetically.


