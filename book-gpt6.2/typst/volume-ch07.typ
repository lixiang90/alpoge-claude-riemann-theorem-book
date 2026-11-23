#import "style.typ": *
#chapter[The theorem and the shape of its proof]

== Where the zeros are <c07s01>

Write $s=sigma+i t$. In the open half-plane $sigma>1$ define
$ zeta(s) = sum_(n>=1) n^(-s)
    = product_(p) (1-p^(-s))^(-1). $
The Euler product is absolutely convergent there. Meromorphic continuation gives a simple pole of residue one at $s=1$. The gamma factor in
$ Lambda(s) = pi^(-s/2) Gamma(s/2) zeta(s) $
removes the zeros at $-2,-4,dots$ and gives the symmetry $Lambda(s)=Lambda(1-s)$. A zero outside that list is called nontrivial. In particular, the origin is not a zero, since $zeta(0)=-1/2$.

#claim[Theorem 7.1 (Riemann hypothesis)][Every nontrivial zero of $zeta$ has real part $1/2$.]

The actual result treats a whole family at once. For $N>=1$, let $chi$ be a character of $(ℤ slash N ℤ)^times$, extended periodically to the integers by zero on nonunits. Its Dirichlet series and Euler product are
$ L(s,chi) = sum_(n>=1) chi(n) n^(-s)
    = product_p (1-chi(p)p^(-s))^(-1) quad (Re s>1). $
Only a principal character gives a pole at one. In a statement about values away from that pole, the notation $L(s,chi)$ means the analytically continued function.

#claim[Theorem 7.2 (Dirichlet characters)][For every modulus $N>=1$ and character $chi$, $L(s,chi)$ is nonzero for $Re s>1/2$ away from the principal pole. Every zero with $0<Re s<1$ lies on $Re s=1/2$. The assertions include primitive, imprimitive, real, and complex characters.]

A character of conductor $f$ is induced by a unique primitive character $chi^*$ of modulus $f$. Deleting the Euler factors at the additional primes gives
$ L(s,chi) = L(s,chi^*) product_(p divides N, p nmid f)
                 (1-chi^(*)(p)p^(-s)). $
When $Re s>0$ the second term in each parenthesis has modulus less than one. Thus the deletion leaves all zeros in the open critical strip unchanged. On its boundary it can introduce zeros. For the principal character mod $2$, for instance, the factor $1-2^(-s)$ vanishes at the points $2 pi i k slash log 2$, $k in ℤ$. The open-strip hypothesis matters.

For a primitive character put $a=0$ or $1$ according as $chi(-1)=1$ or $-1$. With $f$ its conductor, set
$ Lambda(s,chi) = (f/pi)^((s+a)/2) Gamma((s+a)/2) L(s,chi). $
Its functional equation relates it to $Lambda(1-s,overline(chi))$ by a constant of modulus one. Inside the strip the gamma factors are finite and nonzero. A zero strictly to the left of the middle line would produce one strictly to the right for the conjugate character. We may therefore concentrate on right-half-plane nonvanishing.

== From a modulus to its primitive source <c07s02>

A modulus records which integers a character is allowed to see. A conductor records how much information its values on units actually require. Confusing the two changes an Euler product. We work through the change because the theorem about zeros at the end of the book quantifies over every positive modulus.

For positive integers $f divides N$, reduction on unit groups $(ℤ slash N ℤ)^times arrow.r (ℤ slash f ℤ)^times$ is onto. To lift a unit $a$ modulo $f$, keep its residue at every prime power dividing $f$ and choose a unit lift at the higher power of the same prime in $N$. At a prime dividing $N$ and absent from $f$, impose residue one. The Chinese remainder theorem combines these conditions. A character of conductor $f$ factors through this reduction on units. At a prime not dividing $N$ its value is therefore the value of the primitive character. At a prime dividing $N$ the extended character has value zero. These two observations suffice to derive the comparison of the $L$-functions without comparing arbitrary coefficients separately.

Let $P$ be the set of primes dividing $N$ and absent from $f$. In absolute convergence, induction removes from the primitive Euler product exactly the inverses of the factors indexed by $P$. Thus, with $D(s)$ denoting a finite product,
$ D(s)=product_(p in P)(1-chi^(*)(p) exp(-s log p)), $
$ L(s,chi)=D(s)L(s,chi^*). $
The identity extends wherever both sides are meromorphic by uniqueness of continuation. For $Re s=sigma>0$, each complex number subtracted from one in $D$ has modulus $p^(-sigma)<1$. Each factor, and hence $D$, is holomorphic and nonzero in that open half-plane. At a zero of the primitive function inside it, the multiplicity is preserved. To see the last assertion, factor the primitive function locally as $(s-rho)^a u(s)$ with $u(rho)!=0$. Multiplication by $D$ replaces $u(rho)$ by the nonzero number $D(rho)u(rho)$.

At the boundary $Re s=0$ the strict inequality becomes equality. Write $chi^(*)(p)=exp(i alpha)$ with $alpha$ real. One Euler factor has zeros at
$ s=frac(i(alpha+2 pi k),log p), quad k in ℤ. $
Its derivative at any such zero is $log p$. Each individual zero of this factor is simple, though coincidences with other factors may increase the multiplicity in the product. At a primitive pole a zero of $D$ would also require separate order accounting. The only pole under discussion is at one, where $|chi^(*)(p)p^(-1)|<1$. The finite correction never cancels it.

#example[An induced complex character][Three generates the unit group modulo seven. Prescribe $psi(3)=omega$, where $omega=exp(2 pi i/3)$. Since $omega^6=1$, this prescription is consistent. The character is nontrivial and seven is prime, so its conductor is seven. Induce it to modulus thirty-five. The power table $1,3,2,6,4,5$ modulo seven puts $psi(5)=omega^2$. The extra Euler factor is $1-omega^2 5^(-s)$. Its zeros have real part zero and ordinates $(2 pi k-2 pi/3) slash log 5$. At the real point $s=1/2$ this factor is nonzero, and at every point of that vertical line it is bounded below in modulus by $1-frac(1,sqrt(5))$.]

The sign of the correction to a logarithmic derivative is worth recording. At a regular point, differentiating the product gives
$ frac(L'(s,chi),L(s,chi))=frac(L'(s,chi^*),L(s,chi^*))
 + sum_(p in P) frac(chi^(*)(p) p^(-s) log p,1-chi^(*)(p)p^(-s)). $
In the original half-plane the last fraction is a geometric series over powers of $p$. Those are precisely the terms omitted from the imprimitive prime sum when one uses the *negative* logarithmic derivative. This checks the finite-factor formula against the sign of the von Mangoldt weights. Chapter 10 takes powers of a character and then uses their primitive sources. Raising a character to a power can drop the conductor, so this check applies separately to each power.

== The part of the boundary already known classically <c07s03>

Before attempting to exclude a zero by a theta lift, we can determine exactly which part of the complex plane requires that argument. In $sigma>1$ the sum of the absolute values of all logarithmic Euler terms converges. Indeed
$ sum_p sum_(j>=1) frac(p^(-j sigma),j)
 <= frac(1,1-2^(-sigma)) sum_(n>=2) n^(-sigma). $
The logarithm of the product is a convergent complex number, and its exponential is nonzero. This argument applies to complex characters and to the principal character. The prefactor in the estimate grows as one approaches the edge only mildly, but the final series ceases to converge at $sigma=1$.

The boundary $sigma=1$ admits an instructive argument. Let $chi_0$ be the principal character modulo $N$, and write $Z_(N)(s)=L(s,chi_0)$. Use the Euler products for a real $sigma>1$. For $p nmid N$, insert the argument of $chi(p)^j p^(-i j t)$ in the identity $3+4cos v+cos(2v)=2(1+cos v)^2$. Sum with weights $p^(-j sigma)/j$. There is no term at $p divides N$ in any of the three logarithms. Taking real parts and exponentiating gives
$ Z_(N)(sigma)^3 abs(L(sigma+i t,chi))^4
   abs(L(sigma+2 i t,chi^2)) >= 1. $
Here $Z_N$ has a simple pole at one. If $t!=0$, the last factor remains bounded as $sigma$ decreases to one, even if $chi^2$ is principal. A zero of the middle factor at $1+i t$ would contribute at least four powers of $sigma-1$. These outweigh the possible three inverse powers from $Z_N$, giving a contradiction. When $t=0$ the same argument works for every character whose square is nonprincipal. The case left over is that of a nonprincipal real character at one.

There is a direct positivity proof in that last case. The coefficients $a_n$ of
$ D_(chi)(s)=zeta(s)L(s,chi)=sum_(n>=1) a_n n^(-s) $
are multiplicative in the half-plane of absolute convergence. The local series in a variable $z=p^(-s)$ is $(1-z)^(-1)(1-chi(p)z)^(-1)$. For $chi(p)=1$ it has coefficients $1,2,3,dots$. For $chi(p)=-1$ it is $(1-z^2)^(-1)$, with coefficients one at even powers and zero at odd powers. For $chi(p)=0$ all coefficients are one. Thus $a_n>=0$ and $a_(m^2)>=1$ for every positive integer $m$.

Suppose $L(1,chi)=0$. The only pole of $zeta$ in $Re s>0$ would be removed, so $D_chi$ would be holomorphic in this half-plane. Expand $D_(chi)(2-h)$ at $h=0$. The disk $abs(h)<2$ lies in that domain. Absolute convergence justifies termwise differentiation at two: for each fixed $j$, any small power of $n$ dominates $(log n)^j$, and the Dirichlet series is absolutely convergent for every exponent greater than one. Its Taylor coefficients are therefore
$ b_j=frac(1,j!) sum_(n>=1) a_n n^(-2)(log n)^j >=0. $
Set $h=3/2$. The Taylor series converges to a finite number there. All summands are nonnegative, so the order of summation may be exchanged:
$ sum_(j>=0) b_j (3/2)^j
 = sum_(n>=1) a_n n^(-2) exp((3/2)log n)
 = sum_(n>=1) frac(a_n,sqrt(n)). $
The subsum over squares is at least $sum_(m>=1) 1/m$, a contradiction. This completes the boundary argument. It also previews an idea in Chapter 9. Positivity converts analytic continuation at a real point into information about an entire infinite sum.

Combining these steps, a new right-hand zero could only lie in $1/2<Re s<1$. The pole exception in Theorem 7.2 is the conjunction “the character is principal and the point is one.” In particular the assertion includes the value at one for a nonprincipal character. Writing merely “away from one” would discard the last consequence of our boundary calculation.

== Reflection with the character and the height visible <c07s04>

For primitive $chi$, let $a$ denote its parity and $q$ its conductor. With a choice of root number $epsilon_chi$ of absolute value one the completed equation reads
$ Lambda(s,chi)=epsilon_chi Lambda(1-s,overline(chi)). $
In the open strip the arguments $(s+a)/2$ and $(1-s+a)/2$ of the gamma factors have positive real parts. The gamma function is finite and has no zeros there. All powers of the positive number $q/pi$ are nonzero as well. Multiplication or division by these factors preserves the zeros and their orders. It follows that
$ L(rho,chi)=0 quad arrow.r quad L(1-rho,overline(chi))=0 $
when $0<Re rho<1$. The inverse of $chi$ agrees with its conjugate on the unit group. The primitive conductor is preserved under inversion, because any modulus through which one character factors also carries its inverse. This permits an application of a right-half-plane theorem for primitive characters to the reflected function.

A second identity comes from conjugating the original convergent series and then continuing:
$ overline(L(overline(s),chi))=L(s,overline(chi)). $
Taken together, the two identities show that if $rho=beta+i t$ is a zero for $chi$, then $1-overline(rho)=1-beta+i t$ is a zero for the same $chi$. The intermediate identity with $1-rho$ changes both the sign of the height and the character. For a real character both symmetries act on a single zero set. For a complex character, complex conjugation alone can go to a different zero set. Chapter 8 uses this distinction when it forms a real function from a complex prime sum.

The special points zero and one cannot be recovered by substituting them into an identity obtained after dividing by gamma factors. For the principal primitive character the residue of $zeta$ at one is one, and $zeta(0)=-1/2$. At negative even integers the sine in the usual functional equation vanishes while $Gamma(1-s)$ is finite. These are the excluded trivial zeros. In an assertion about *arbitrary* Dirichlet characters we restrict the equality of real parts to the open strip. The factors at primes introduced by a change of modulus have already exhibited zeros on its boundary.

== Which estimate would exclude a zero? <c07s05>

Let $Lambda(n)$ denote the von Mangoldt function. It is $log p$ if $n=p^k$, $k>=1$, and zero otherwise. The context distinguishes it from the completed functions above. For $x>=1$ introduce the ramp
$ r_(n)(x) = max(x/n - 1,0). $
A sum of these ramps has an elementary Mellin transform. After subtracting explicit terms of order $x log x$ and $x$, its singularities to the right of zero include the zeros in question. The analytic task is to turn the presence of one such singularity into a *positive* excursion of the centered real sum.

On the arithmetic side the available inequality concerns one real sum attached to a finite positive combination of characters. For an exponent $theta$ strictly greater than $1/2$, the inequality holds at every point of an interval
$ [Y,Y^(3/2)] $
with $Y$ arbitrarily large. Both the simultaneous validity and the power width matter. Checking the same inequality at an unbounded sequence of individual points would leave room for excursions between those points.

Fix a primitive character $psi$. Powers of $psi$ form a finite cyclic family. Auxiliary quadratic characters enter during the construction of an upper bound. A finite Fourier calculation makes the coefficients of the target family positive. Chapter 17 shows how translation and quantitative estimates remove or control the auxiliary terms. This gives a single arithmetic quantity against which every member of the cyclic family can be tested. It also gives a reason to include the trivial character when studying a nontrivial one.

The square-root exponent enters through chains of integral theta lifts on positive definite unitary groups. At a finite place, a lift may carry divisibility. At infinity its norm costs something. Pairing the same map at all places compares those two quantities. A suitably long chain and a suitable set of places put an upper bound on a weighted prime sum. Galois representations and cohomology supply the degree and covolume control necessary to retain that bound on an entire interval.

== What a single zero requires of an arithmetic estimate <c07s06>

Let a hypothetical zero have real part $beta=1/2+b$ with $b>0$. The argument can be read backwards starting at this $b$. Set $theta=1/2+b/2$. Choose the small parameter $epsilon$ below the construction's thresholds and with $9epsilon<b/2$. We will not take a limit of functions of $epsilon$. For this single, fixed choice, a single sufficiently late interval will give a contradiction. The possibility of choosing the parameter *after* the zero is essential when $b$ is very small.

The relevant estimate concerns a fixed real function $F$ of a positive real argument. To express its quantifiers without abbreviations, fix the target character and $epsilon$. For every starting threshold $A$ there is $Y>=A$ such that at every real $x$ satisfying $Y<=x<=Y^(3/2)$ one has $F(x)<=x^(1/2+9epsilon)$. The prime pair is allowed to depend on the outer scale. The integral data can vary as $x$ runs across its interval. The function $F$ depends on the original character and is the *same function* on every interval. This order of choices is the target of the arithmetic chapters.

For contrast within the argument, consider what happens if one interchanges the existential and universal quantifiers. The condition that for every large $A$ some point $x>=A$ has $F(x)<=0$ is consistent with a very large positive fluctuation on the rest of the axis. Take $F(x)=x^beta cos(log x)$, for example. It is negative at $log x=(2k+1)pi$. Yet its Mellin transform on $[1,infinity)$ has a pole at $beta+i$. On every interval of logarithmic length greater than $2 pi$ there is also a point at which the cosine is one. A window $[Y,Y^(1+delta)]$ has logarithmic length $delta log Y$, which eventually exceeds any fixed oscillation period. In Chapter 9 the frequency of a putative pole is not known in advance, and other oscillations coexist with it. Localization and the two-center argument will give a rigorous replacement for this cosine picture.

A second issue concerns which upper estimate one applies. The analytic theorem is one-sided. If $F$ takes a large negative value it still satisfies the upper inequality. Thus one cannot simply integrate the absolute value of the proposed bound and conclude convergence in $Re s>theta$. A pair of moment integrals, one on the real axis and one off it, will combine so that only the positive part of $F$ requires the sharp estimate. The transform of the arithmetic ramp has the sign at real poles needed for this device.

#note[The two assertions to be joined][For a fixed positive family, a zero to the right of $theta$ forces some $x$ in every sufficiently late power-width interval to exceed the proposed upper bound. For the family attached to a fixed primitive character, the arithmetic argument supplies arbitrarily late intervals of that same width on which all points satisfy the bound. Choosing $theta$ between the zero and the square-root line makes the assertions incompatible.]

The finite family is already useful in the ordinary zeta case. If the target is the character of conductor one, its powers introduce no further characters into the final statistic. The intermediate construction still uses two auxiliary quadratic signs and a varying cyclotomic field. Eliminating those signs is a step in producing the untwisted estimate. One should therefore retain the distinction between the target family and the auxiliary data even when the final conclusion mentions only $zeta$.

#source-note[The five exported conclusions and their domain restrictions are specified in #src("Statements")[the release statements]. The primitive reflection is #src("Formalism.GammaFactorNonvanishing.CritLine")[critLine]. The precise assumption that passes from an arithmetic window to a zero-free half-plane appears in #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow")[the power-window theorem].]

== Two elementary models <c07s07>

#example[A reflection][Suppose $L(s,chi)$ had a zero at $0.37+8i$ with $chi$ primitive. The functional equation gives a zero of the conjugate-character function at $0.63-8i$. Conjugating this value gives a zero of $L(s,chi)$ at $0.63+8i$. The two symmetries together reflect a zero across the critical line for the original character. The functional equation alone already suffices when right-hand nonvanishing is known for every primitive character.]

#example[A choice of exponents][Suppose a zero had real part $0.54$. A bound by $x^0.52$ on arbitrarily late power-width intervals is already strong enough for the analytic argument. If the arithmetic exponent is $1/2+9 epsilon$, taking $0<epsilon<=0.001$ within the admissible range leaves a margin of at least $0.011$ below $0.52$. All thresholds may depend on this choice. The proof never needs a bound with $epsilon=0$ or a common threshold for every character.]

#source-note[The release ends with five public statements. The right-half-plane result implies the open-strip and ordinary versions by the functional equation and the finite Euler-factor calculation above. The exact source declarations for this reduction appear in the concordance.]
