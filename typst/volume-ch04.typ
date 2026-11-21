#import "style.typ": *
#chapter[Characters, completions, and Frobenius]

== Finite Fourier analysis <c04s01>

Let $G$ be a finite abelian group. A character is a homomorphism from $G$ to the nonzero complex numbers. Its values are roots of unity because every element of $G$ has finite order. For a nontrivial character $lambda$, choose $h$ with $lambda(h)!=1$. Translating the sum of its values multiplies the sum by $lambda(h)$ while leaving it unchanged, so it must be zero. Applying this cancellation to the quotient of two distinct characters proves orthogonality for the counting probability measure. A cyclic group of order $m$ has exactly $m$ characters, since the image of a generator may be any $m$th root of unity. Decomposing $G$ into cyclic factors and taking products gives $abs(G)$ characters in all. They have norm one and their number equals the dimension of the space of complex functions on $G$, so they form an orthonormal basis. In multiplicative notation the inversion formula is
$ f(g)=sum_(lambda in hat(G)) hat(f)(lambda)lambda(g), quad
  hat(f)(lambda)=frac(1,abs(G)) sum_(a in G) f(a)overline(lambda(a)). $
For $G=(ℤ slash 4ℤ)^times$ the nontrivial character has values $1,-1$ at $1,3$. The indicator of the residue class $1$ on the unit group is $frac(1+chi,2)$. Extending characters by zero at nonunits gives the usual orthogonality formula on the integers coprime to the modulus. It explains why a question about primes in progressions leads to Dirichlet $L$-functions. The principal character supplies the average and the other characters measure deviations.

A character may be presented with redundant modulus. The nontrivial character mod $4$ can be induced to modulus $12$. Its values there omit the multiples of $3$. The new Euler product is the old one times $1-chi(3)3^(-s)=1+3^(-s)$. At $Re s>0$ this extra factor is never zero. The *conductor* is the minimal modulus and a *primitive* character is already given at that modulus.

== A character table and its two orthogonalities <c04s02>

Every character of a cyclic group of order $m$, written additively, has the form $j mapsto e^(frac(2pi i k j,m))$ for a unique $k$ modulo $m$. Indeed the value at one is an $m$th root of unity and determines every other value. The sum over all $j$ of the character is a finite geometric series. It equals $m$ at frequency zero and zero otherwise. A finite abelian group is a product of cyclic groups. Multiplying their character tables shows that the number of characters equals the group order and that both orthogonality identities hold. They read
$ frac(1,|G|) sum_(g in G) chi(g)overline(eta(g))=bold(1)_(chi=eta), $
$ frac(1,|G|) sum_(chi in hat(G)) chi(g)overline(chi(h))=bold(1)_(g=h). $
The two sums express a single statement about a square matrix scaled by $|G|^(-frac(1,2))$. Its rows and columns are orthonormal. Multiplying the matrix by its conjugate transpose in one order reconstructs a function from its coefficients. Multiplying in the other order establishes independence of the coefficients.

For $G=(ℤ slash 5ℤ)^times$, the residue two is a generator of order four. The ordered powers of two are $1,2,4,3$. Let $lambda(2)=i$. Its character table, with columns in that order, is
#align(center)[#table(columns: 5, align: center, inset: (x: 9pt,y: 2pt), stroke: none,
table.hline(stroke: 0.6pt), [character], [$1$], [$2$], [$4$], [$3$], table.hline(stroke: 0.4pt),
[$1$], [$1$], [$1$], [$1$], [$1$],
[$lambda$], [$1$], [$i$], [$-1$], [$-i$],
[$lambda^2$], [$1$], [$-1$], [$1$], [$-1$],
[$lambda^3$], [$1$], [$-i$], [$-1$], [$i$], table.hline(stroke: 0.6pt)) ]
To count the residue class $2$, weight the four rows by $1,-i,-1,i$ and divide by four. At column two the total is one. At the other three columns geometric cancellation gives zero. For the union of the classes $1,4$, the answer reduces to $frac(1+lambda^2,2)$ because the two complex characters cancel. One therefore has a way of designing exactly which characters survive an average. The specific coefficients used in the proof are chosen with a different objective, to retain *each* power of a target character with a strictly positive coefficient.

Put the counting probability measure on $G$ for functions and its corresponding counting measure on the character coefficients. Parseval's identity is then
$ frac(1,|G|)sum_g |f(g)|^2=sum_(chi in hat(G)) |hat(f)(chi)|^2. $
It follows by inserting the inversion formula twice and using row orthogonality. The coefficient of the trivial character is the mean of $f$. The sum of the squared absolute values of the other coefficients equals the mean of $abs(f-hat(f)(1))^2$, the variance of $f$ about its mean. Thus a mean-square estimate for coefficients has a direct interpretation as a discrepancy in the distribution on classes. The later arithmetic construction requires pointwise errors in the projected class masses. Conversely, one obtains a coefficient error from a uniform class error by summing absolute values.

== Quotients, fibers, and exact projection <c04s03>

Let $A$ be a subgroup of $G$ and form the average
$ (P_A f)(g)=frac(1,|A|)sum_(a in A) f(g a). $
It is constant on each coset of $A$. Applying it to a character multiplies that character by its mean on $A$. This mean is one when the restriction is trivial and zero otherwise. It follows that $P_A$ is an orthogonal projection onto the functions on $G slash A$, regarded as functions on $G$ by pullback. Averaging twice gives the same operator. The factor $frac(1,abs(A))$ is required for this idempotence. If one works over integral coefficients at a prime dividing $|A|$, the *unnormalized* sum is still an integral operator even though the normalized projection can acquire denominators.

A normalized distribution on $G slash A$ pulls back to a distribution on $G$ by sharing each coset mass equally among its $|A|$ elements. If the mass of the coset $b$ is $w_b$, the Fourier coefficient in the expectation convention is
$ sum_(b in G slash A) frac(w_b,|A|) sum_(g in b) chi(g). $
When the restriction of $chi$ to $A$ is nontrivial, the inner sum is zero on every fiber. For other $chi$ there is an induced character $tilde(chi)$ on $G slash A$, and the coefficient reduces to $sum_b w_b tilde(chi)(b)$. This formulation lets the size of the larger group vary freely while the observable Fourier data come from the much smaller quotient.

For example, take $G=ℤ slash 12ℤ$ additively and $A={0,3,6,9}$. At frequency $k$, averaging all translates by $A$ multiplies the character by $frac(1,4)sum_(j=0)^3 e^(frac(2pi i k j,4))$. The surviving frequencies are $k=0,4,8$. The three cosets can be assigned masses $frac(1,2),frac(1,3),frac(1,6)$. At $k=4$ the coefficient is $frac(1,2)+frac(omega,3)+frac(omega^2,6)$ for a primitive cube root $omega$. Its conjugate is the coefficient at $k=8$. Neither depends on a choice of representative for the coset. On changing the masses, the projection and its surviving frequencies stay fixed, while their actual coefficients can change sign or become complex. Positivity of a probability measure alone does not imply positivity of all its Fourier coefficients.

The indicator of one coset has a frequently useful formula. If $I$ is a subgroup and $h I$ a coset, then
$ bold(1)_(g in h I)=frac(|I|,|G|) sum_(chi in hat(G slash I)) chi(g)overline(chi(h)). $
The characters on the right are pulled back along the quotient map. This is column orthogonality on the quotient, whose order is $frac(abs(G),abs(I))$. The same formula recurs for an inertia subgroup $I$. At a ramified prime the coset is canonical even though the choice of a representative depends on a lift.

== The conductor and a finite Fourier transform with an additive phase <c04s04>

A Dirichlet character modulo $q$ is a character of the *multiplicative* unit group, set to zero on all other residue classes. It also defines a function on the *additive* group $ℤ slash q ℤ$. The two Fourier transforms serve different purposes. To form the additive one, put $e_(q)(a)=exp(frac(2pi i a,q))$ and
$ T(b)=sum_(a " mod " q) chi(a) e_(q)(a b), quad tau(chi)=T(1). $
If $b$ is a unit, the substitution $u=a b$ gives $T(b)=overline(chi(b))tau(chi)$. A primitive character has the stronger property that this identity also holds at nonunits, where the right side is zero. The conductor is what ensures that the support of the additive Fourier transform is so well controlled.

#claim[Primitive Gauss sum][For a primitive Dirichlet character $chi$ modulo $q>1$, its additive transform satisfies $T(b)=overline(chi(b))tau(chi)$ for every residue $b$, and $|tau(chi)|=sqrt(q)$.]

#proof[If $d=gcd(b,q)>1$, let $q'=frac(q,d)$. For a unit $u$ with $u equiv 1$ modulo $q'$, the additive factor $e_(q)(a b)$ is unchanged on replacing $a$ by $u a$. There is such a unit with $chi(u)!=1$. Otherwise the character would factor through the image of reduction to units modulo $q'$. To see surjectivity, start with a residue prime to $q'$ and take a lift also prime to every remaining prime factor of $q$, by the Chinese remainder theorem. A factorization through this proper divisor would contradict primitivity. Changing the summation variable now multiplies $T(b)$ by a nontrivial scalar while leaving the sum unchanged, so $T(b)=0$.

For the size, expand the squares and sum first over $b$. Orthogonality of additive characters gives
$ sum_(b " mod " q) |T(b)|^2=q sum_(a " mod " q) |chi(a)|^2=q varphi(q). $
On the other hand exactly $varphi(q)$ unit inputs can contribute, each with absolute value $|tau(chi)|$. Division gives the result.]

At modulus five one can see this norm without estimates. The quadratic character $chi=lambda^2$ has values $1,-1,-1,1$ in the usual order $1,2,3,4$. Pairing conjugate additive phases gives
$ tau(chi)=2cos(frac(2pi,5))-2cos(frac(4pi,5)). $
The right side is positive, so the norm calculation makes it $sqrt(5)$. For the primitive odd character modulo four, the two unit inputs give $tau(chi)=i-(-i)=2i$. The complex phase matters when computing a functional equation. From conjugation of the defining sum one gets $tau(chi)tau(overline(chi))=chi(-1)q$. This identity will make a double application of the functional equation return to the original function.

== A functional equation with its conjugate visible <c04s05>

Choose $a=0$ for an even character and $a=1$ for an odd character, so $chi(-1)=(-1)^a$. For a primitive character of conductor $q>1$ put
$ Theta_(chi)(t)=sum_(n in ℤ) chi(n)n^a exp(-frac(pi n^2 t,q)), quad t>0. $
The factor $n^a$ ensures that the two terms for $n$ and $-n$ add. If it were absent for an odd character the whole theta sum would vanish. For a Schwartz function $f$ split its sum into residue classes modulo $q$. Periodizing $f$ with period $q$ as in Chapter 3 gives
$ sum_(n in ℤ) chi(n)f(n)=frac(1,q)sum_(m in ℤ) T(m) hat(f)(frac(m,q)). $
Indeed the inverse Fourier series on a residue class has coefficients $q^(-1)hat(f)(frac(m,q))$ and values $e_(q)(a m)$. For the Gaussian in the preceding display all exchanges of sums can be justified by absolute convergence.

Use $f(x)=x^a e^(-frac(pi x^2 t,q))$. For $a=0$ its Fourier transform is $(frac(q,t))^(frac(1,2)) e^(-frac(pi q xi^2,t))$. For $a=1$ multiplication by $x$ corresponds to differentiating the Fourier transform and dividing by $-2pi i$. At $xi=frac(m,q)$ the extra factor is $-frac(i m,t)$. Inserting the Gauss sum calculation therefore gives
$ Theta_(chi)(t)=W(chi)t^(-frac(1,2)-a)Theta_(overline(chi))(frac(1,t)), $
$ W(chi)=frac(tau(chi),i^a sqrt(q)), quad |W(chi)|=1. $
The two examples just computed both have $W(chi)=1$. In general the phase need not be one. What the argument needs for the location of zeros is that it is nonzero and that the character on the reflected side is correctly conjugated.

At both endpoints this theta integral now has rapid decay after the explicit power at zero because the constant Fourier coefficient vanishes for a nonprincipal primitive character. The Mellin integral
$ frac(1,2)integral_0^infinity Theta_(chi)(t)t^(frac(s+a,2)) frac(dif t,t) $
is entire in $s$. For $Re s>1$ the Gaussian integral at each $n$ shows that its value is
$ (frac(q,pi))^(frac(s+a,2)) Gamma(frac(s+a,2))L(s,chi). $
For example, for $n>0$ the factor of $n$ from the Mellin integral is $n^(-s-a)$ and the original weight contributes $n^a$, leaving $n^(-s)$. Negative $n$ gives a second identical term, canceled by the factor $frac(1,2)$. Substituting $t mapsto frac(1,t)$ and using the displayed theta law proves the functional equation for the completed function, with multiplicative factor $W(chi)$ and partner $1-s,overline(chi)$. For the character of conductor one the theta series has a constant term. The rational terms from removing it were computed in Chapter 3, and encode the pole at one.

For an imprimitive character modulo $M$ induced by $chi$ of conductor $q$, the Euler product in $Re s>1$ lacks the primes dividing $M$ which do not divide $q$. Thus
$ L(s,chi_M)=L(s,chi) product_(p divides M, p nmid q)(1-chi(p)p^(-s)). $
Continuation transfers the equality elsewhere. For $Re s>0$ every finite factor is nonzero because its second term has modulus $p^(-Re s)<1$. A zero of the primitive function in the interior of the strip remains a zero with the same multiplicity. On the line $Re s=0$ the situation changes. The factor $1+3^(-s)$ in the modulus-twelve example vanishes at $s=frac((2k+1)pi i,log 3)$ for integers $k$. This is one reason the formulation for arbitrary characters explicitly specifies an *open* strip.

== Local fields and residue degrees <c04s06>

For a prime $p$, the valuation $v_(p)(frac(a,b))$ is the exponent of $p$ in $a$ less its exponent in $b$. The absolute value $|x|_p=p^(-v_(p)(x))$ makes high divisibility mean small size. Completing gives the field $ℚ_p$ and its valuation ring $ℤ_p$. A finite extension has its own uniformizer and residue field. For a number field $K$ and a prime ideal $frak(p)$ above $p$, the ramification index records the valuation of $p$ and the residue degree is the degree of the residue field over $𝔽_p$. The logarithm of the norm of $frak(p)$ is its residue degree times $log p$.

A particularly simple case is $K=ℚ(i)$. At $p=5$ the polynomial $X^2+1$ has roots $2,-2$ modulo five, and the prime splits. At $p=3$ it is irreducible and the residue field has nine elements. The map $x mapsto x^3$ sends $i$ to $-i$ there. At two the polynomial has a repeated root and the prime ramifies. These three behaviors recur in explicit prime sums. In an abelian extension the Frobenius of an unramified prime is a well-defined group element. At a ramified prime its natural value belongs to a quotient by the inertia group. This is why a formula that needs group elements sometimes sums over an entire inertia coset.

== Local norms, normalized globally <c04s07>

For a finite extension of $ℚ_p$, the valuation normalized to have value one at a uniformizer can take value $e$ at $p$, where $e$ is the ramification index. If the residue field has cardinality $q=p^f$, let $|a|_v=q^(-v(a))$ with this integer-valued valuation. For an element of a number field $K$, these finite absolute values satisfy
$ product_(v " finite") |a|_v=abs(op("N")_(K slash ℚ)(a))^(-1). $
For an algebraic integer, this follows from the ideal factorization of $(a)$ and the equality between the norm of a principal ideal and the absolute norm of its generator. For general $a$ use a quotient of algebraic integers. At a real embedding use the ordinary absolute value. At a single representative of each pair of complex embeddings use the *squared* absolute value. Their product is $abs(op("N")_(K slash ℚ)(a))$, proving the product formula. An alternative convention uses local absolute values extending the rational ones and then raises them to local degrees in the product. Mixing the conventions introduces an extra degree factor.

Consider the element $a=1+i$ in $ℚ(i)$. Its only nontrivial finite absolute value is $frac(1,2)$ at the ramified prime whose uniformizer is $1+i$. At the complex place its squared absolute value is two. The element two has valuation two at the same prime, and its normalized complex absolute value is four. For the split rational prime five the element $1+2i$ has norm five and generates just one of the two primes above five. Its valuations at the two primes are one and zero respectively. The product formula distinguishes a local divisibility condition involving one of these primes from a condition on a rational scalar divisible by both.

There is a concrete test for the split local decomposition in the example. The residue root $2$ of $X^2+1$ modulo five lifts uniquely to a root in $ℤ_5$. If $F(a)$ is divisible by $p^r$ and $F'(a)$ is a unit, substituting $a+p^r k$ determines a unique $k$ modulo $p$ with $F(a+p^r k)$ divisible by $p^(r+1)$. The terms of degree at least two in the increment are divisible by $p^(2r)$, which is enough when $r>=1$. From $a=2$ the calculation gives $a=7$ modulo $25$, then $57$ modulo $125$. The compatible residues define a limit in the completion. The second root is its negative. At three no root exists even in the residue field, so the quadratic algebra is an unramified quadratic field there. These local distinctions feed the global prime sum through the choice of a Frobenius element or coset. #link("https://www.jmilne.org/math/CourseNotes/ANT.pdf")[Milne's treatment of decomposition, inertia and ideal norm.]

== Cyclotomic characters as functions of Frobenius <c04s08>

For the cyclotomic field $ℚ(zeta_M)$, an unramified prime $p nmid M$ has Frobenius $zeta_M mapsto zeta_M^p$. The identification of its Galois group with $(ℤ slash M ℤ)^times$ turns a character value $chi(p)$ into a value on Frobenius. In a subfield fixed by a subgroup, one passes to the corresponding quotient group. Multiple character requirements on primes can therefore be imposed simultaneously by specifying Frobenius in a compositum of abelian fields.

For any $a in ℚ^times$ unique factorization gives the product formula
$ |a|_infinity product_p |a|_p=1. $
For $a=frac(12,5)$ the nonunit finite factors are $frac(1,4),frac(1,3),5$ at $2,3,5$. They multiply to $frac(5,12)$. Number fields have the same formula with the appropriate local degrees. Its logarithm adds divisibility at finite places to a comparison at the archimedean places. One of the main arguments in this book applies precisely this accounting to determinant lines.

== A Frobenius coset one can list <c04s09>

In a finite Galois extension of number fields, choose a prime ideal above a rational prime $p$. Its decomposition group is the stabilizer of that prime ideal. Mapping an automorphism to its action on the residue field gives a surjection from the decomposition group to the residue-field Galois group. The kernel is inertia. The residue group is cyclic, generated by $x mapsto x^p$ over $𝔽_p$. An element lifting this generator is therefore determined only up to inertia. At an unramified prime the lift is unique for the chosen prime ideal. Changing the prime ideal above $p$ conjugates the lift. In an abelian extension this conjugation leaves the element unchanged. Throughout our elementary examples we use arithmetic Frobenius, the power-$p$ map.

Take $K=ℚ(zeta_(12))=ℚ(i,sqrt(-3))$. The Galois group has four elements labelled $1,5,7,11$ by their action as powers on the twelfth roots of unity. Reduction modulo four gives the action on $i$, while reduction modulo three gives the action on a primitive cube root. At $p=3$, the field $ℚ(i)$ is unramified and inert, and the action on its residue field is complex conjugation on $i$. The field generated by a primitive cube root is ramified, since its polynomial becomes $(X-1)^2$ modulo three and the element $1-zeta_3$ has norm three. Locally this factor is a ramified quadratic extension adjoining a root of an Eisenstein polynomial obtained by translating $X^2+X+1$. The compositum consequently has unramified degree two and ramification index two at three. One may also see this by adjoining a root of the same Eisenstein polynomial to the unramified quadratic completion.

The inertia subgroup consists of those elements acting trivially on $i$, namely $I={1,5}$. The residue Frobenius coset consists of $7,11$, both congruent to three modulo four. For the character coming from modulus four both values on that coset are $-1$. Its normalized coset average is $-1$, exactly the unramified eigenvalue. For the character from modulus three, the two values are opposite, and the average is zero. For their product the average also vanishes. Thus the normalization picks out precisely the characters unramified at three, with the correct Frobenius values for those which survive.

For any one-dimensional complex representation of an abelian decomposition group the same calculation is
$ frac(1,|I|)sum_(u in I)chi(g u)=chi(g) frac(1,|I|)sum_(u in I)chi(u). $
The factor at the right is the dimension of the invariant subspace in this one-dimensional case. The expression can be evaluated without choosing a privileged lift $g$, since changing $g$ inside its coset permutes the terms. For an iterate of Frobenius one takes the coset of its iterate in the *quotient*, namely $g^k I$. The normalized sum is zero for a character nontrivial on $I$ even if $chi^k$ has become trivial there. This matters in comparing a ramified Euler factor with a class sum at a prime power. Taking all the $k$th powers of the elements of a single coset would in general give a different weighted sum.

== Two quadratic tests and a relation between three of them <c04s10>

Consider the field $ℚ(zeta_8)=ℚ(i,sqrt(2))$. The equality follows from $i=zeta_8^2$, $sqrt(2)=zeta_8+zeta_8^(-1)$, and $zeta_8=frac(1+i,sqrt(2))$ for the standard complex embedding. A prime $p!=2$ acts on $zeta_8$ by the power $p$ modulo eight. Its action on $i$ is determined by the reduction modulo four. Its action on $sqrt(2)$ can be read by adding the $p$th and the $-p$th powers of $zeta_8$. With residues in the order $1,3,5,7$, the signs on $i$ are $+,-,+,-$ and those on $sqrt(2)$ are $+,-,-,+$. All four pairs occur as elements of the Galois group.

A third quadratic subfield is generated by $sqrt(-2)=i sqrt(2)$. Its sign at the same residue classes is the product of the first two signs, $+,+,-,-$. It cannot be specified independently of the other two. Requiring a prime to act trivially on both $i$ and $sqrt(2)$ and nontrivially on $sqrt(-2)$ describes the empty set. The obstruction is a character relation on a single group, regardless of the distribution of primes. Conversely the permitted pair which fixes $i$ and changes the sign of $sqrt(2)$ is exactly the residue class five modulo eight. Dirichlet's theorem gives infinitely many such primes.

The general source of such consistency is visible in a compositum $K_1 K_2$ of two Galois extensions of $ℚ$. Restriction maps an automorphism injectively into $Gal(K_1 slash ℚ) times Gal(K_2 slash ℚ)$, since the fields generate the compositum. The two components agree on $K_1 ∩ K_2$. For finite Galois extensions, equality of their restrictions is also sufficient. Indeed, the resulting fiber product of groups has order $frac([K_1 : ℚ][K_2 : ℚ],[K_1 ∩ K_2 : ℚ])$, which by the compositum degree formula equals $[K_1 K_2:ℚ]$. Thus compatible pairs exhaust the image. When several characters are imposed together, one must either verify this compatibility or place them in coordinates of a host group where all their relations are explicit. The later construction chooses an actual abelian field and specifies the averaging subgroup there.

== A number-field zeta function that factors by characters <c04s11>

In $K=ℚ(i)$ every ideal of $ℤ[i]$ is principal. One proof uses the norm $a^2+b^2$. Given two Gaussian integers, divide in $ℂ$ and take the nearest integer to each real component of the quotient. The squared absolute value of the error is at most $frac(1,2)$, so the remainder has smaller norm than the divisor. This Euclidean algorithm gives principal ideals, Bezout identities, and unique factorization up to the four units $1,-1,i,-i$. The norm of the principal ideal generated by $a+b i$ is $a^2+b^2$, as seen from the determinant of multiplication on the integer basis $1,i$.

Define $zeta_(K)(s)=sum_(frak(a)!=0) op("N")(frak(a))^(-s)$ over nonzero integral ideals. For $Re s>1$ the Euler product factors by prime ideals. We can verify the identity
$ zeta_(K)(s)=zeta(s)L(s,chi_4) $
by listing the three possible rational local factors. Here $chi_4$ is the primitive quadratic character of modulus four. If $p equiv 1$ modulo four, its two distinct prime ideals both have norm $p$, and the local factor is $(1-p^(-s))^(-2)$. If $p equiv 3$ modulo four, its single prime ideal has norm $p^2$, so its factor is $(1-p^(-2s))^(-1)$. On the right this is $(1-p^(-s))^(-1)(1+p^(-s))^(-1)$. Finally two is ramified and gives just $(1-2^(-s))^(-1)$, as $chi_(4)(2)=0$. Each of these statements can be read off from $X^2+1$ over the residue field. For odd primes the polynomial has two roots or none according as $-1$ is a square or a nonsquare, which in the cyclic unit group is determined by reduction modulo four.

This calculation has two consequences worth keeping distinct. First, comparison of Dirichlet coefficients counts the lattice points on a circle by the formula
$ r_(2)(n)=4sum_(d divides n) chi_(4)(d), quad n>=1. $
Here $r_(2)(n)$ counts *ordered* pairs of integers with sum of squares $n$. Each nonzero ideal of norm $n$ has four generators, so the four counts its possible unit multiples. For $n=65=5 dot 13$ the formula gives sixteen, including the sign and order variants of $(1,8)$ and $(4,7)$. For $n=45=3^2 dot 5$ it gives eight, the variants of $(3,6)$. For $n=15$ the inert prime occurs to an odd power and the divisor sum vanishes. Thus the same finite character table determines representation numbers and local Euler factors.

Second, differentiating the logarithm of the product makes the contribution at each rational prime power depend on $1+chi_(4)(p)^k$. At a split prime this is two for every $k$. At an inert prime it vanishes for odd $k$ and is two for even $k$, exactly as expected from a prime ideal of norm $p^2$ and logarithmic weight $2log p$. At two there is one contribution at each power. In the later prime-gain calculation one encounters instead the complementary sign $1-chi_(d)(p)^k$, which picks out odd powers at inert primes. Being able to derive both rules from a local factor guards against reversing split and inert contributions.

The character decomposition can also be seen on a complete lattice. For $t>0$, the generating function $sum_(a,b in ℤ) e^(-pi t(a^2+b^2))$ is the square of the one-dimensional Gaussian theta series. Apart from the origin, its coefficients are the $r_(2)(n)$ just computed. Taking its Mellin integral at $Re s>1$ gives
$ integral_0^infinity (vartheta(t)^2-1)t^s frac(dif t,t)
 =4pi^(-s)Gamma(s)zeta(s)L(s,chi_4). $
The integral on the left is over a rank-two Gaussian lattice. Absolute convergence at zero requires $Re s>1$ because $vartheta(t)^2$ grows like $frac(1,t)$. The frame of a quadratic field, the finite Fourier character, and a concrete theta series have now produced the same Dirichlet series. The general theta lifts later in the book involve far more than this binary quadratic form, but the factorization illustrates why such different sources of arithmetic data can agree exactly.

== Removing squares in two residue classes <c04s12>

For reduced $a$ modulo $q$, put $Psi(x,q,a)=sum_(n<=x, n equiv a " mod " q) Lambda(n)$. Inserting the character expansion of the class indicator gives
$ Psi(x,q,a)=frac(1,varphi(q))sum_(chi " mod " q) overline(chi(a)) sum_(n<=x) chi(n)Lambda(n). $
The principal character's sum is $Psi(x)$ with the powers of the primes dividing $q$ deleted. For any fixed $q$ those omissions cost at most $sum_(p divides q) log x$, since one has at most $frac(log x,log p)$ positive powers of each $p$. This error is tiny compared with the main term as $x$ grows. If $q$ varies, its number of prime factors is a separate parameter and the same bound must be used with that dependence visible.

For $q=4$, subtract the two reduced classes. Let $D(x)$ be the resulting difference for $Psi$, and put
$ D_(1)(x)=sum_(p<=x, p equiv 1 " mod " 4) log p
          -sum_(p<=x, p equiv 3 " mod " 4) log p. $
The difference $D-D_1$ includes a particularly large even-power contribution, since every odd square is congruent to one modulo four. More precisely it is the sum of $log p$ over odd primes $p<=sqrt(x)$, plus the signed contributions from exponents $k>=3$. The absolute value of those remaining terms is at most a fixed multiple of $x^(frac(1,3))log x$, by summing Chebyshev's upper bound over at most $frac(log x,log 2)$ exponents. By the prime number theorem the square contribution is asymptotic to $sqrt(x)$. It has a fixed sign despite the fact that the original class difference was formed by subtracting two equally sized classes.

This example explains why keeping prime powers is essential when one wants a square-root-scale assertion. Removing all higher powers is harmless at the scale of the prime number theorem. Removing just the squares can change the main term of a proposed secondary asymptotic. It would be wrong to infer from the positive square contribution alone that $D$ has an eventual sign. The fluctuations of $D_1$ may be comparable. In the ramp argument every local iterate and its character value are retained before the explicit centering is done.


