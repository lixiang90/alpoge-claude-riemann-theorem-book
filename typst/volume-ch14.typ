#import "style.typ": *
#chapter[Slopes, covolumes, and the main term]

== A determinant at all places <c14s01>

An adelically metrized lattice $P$ of rank $r$ has a determinant line. Its normalized Arakelov degree is the negative logarithm of its determinant covolume, with the usual local degrees and field normalization. Its slope $mu(P)$ is that degree divided by $r$. The maximal and minimal slopes measure how far a sublattice or a quotient can depart from the mean. If $P' subset.eq P$ is a full sublattice of finite index $I$ with the same real metric over $ℚ$, then
$ mu(P')=mu(P)-frac(log I,r). $
Over a number field the numerator is an appropriately normalized sum of local lengths times logarithms of residue norms. This is the arithmetic reason that the local gains of Chapter 13 and archimedean norms can appear in the same inequality.

For a nonzero rational section of a metrized line the degree can be computed at any rational generator. Rescaling changes the local contributions by logarithms whose weighted sum is zero by the product formula. In higher rank the same observation applies to exterior powers of maps. A bound for their operator norms gives one side of a degree inequality. A lower bound for their finite divisibility gives the other side. The difficulty is to obtain enough independent image directions after factoring the common divisors.

== Degrees, indices, and the direction of a slope inequality <c14s02>

Let $L$ be a free lattice in a Euclidean space of the same rank $r$. If a matrix $A$ has for its columns a basis of $L$, its covolume is $sqrt(det(A^* A))$. In a square orthonormal coordinate system this is $|det A|$. Changing the basis on the right by an integral unimodular matrix leaves the covolume unchanged. A sublattice $L'$ of finite index $I$ has covolume $I$ times that of $L$. With $op("deg")(L)=-log vol(L)$ and $mu(L)=frac(op("deg")(L),r)$, it follows that $mu(L')=mu(L)-frac(log I,r)$. If the local comparison *enlarges* the lattice by dividing out a common factor, the slope increases. A finite-place gain enters with a plus sign in precisely this direction.

The number-field normalization in the release writes the slope of a good positive-rank lattice as minus the normalized logarithmic covolume divided by rank. The local logarithms contain the degree of the coefficient field and the factor two already seen in Chapter 13. Changing all measures by the same constant in an elementary Euclidean illustration leaves the calculation of a finite index untouched. In the number-field calculation the absolute measures in two different formulas matter, because their period terms must cancel. #src("Formalism.LocalRingCardinality.DataArith")[Normalized covolumes, slopes, and duals.]

For a saturated sublattice $F subset.eq L$, give $F$ the restricted metric and $L slash F$ the quotient metric. Choose a basis for $F$, lift a basis for the quotient, and orthogonally remove the $F$ components of these lifts. The volume of the full parallelepiped is then the volume from $F$ times the volume in the orthogonal complement. This proves additivity of degree in that exact sequence. If the original sublattice is not saturated, a finite index has to be inserted before the quotient is made into a free lattice. The procedure also explains why the slopes of direct factors are averaged with weights equal to their ranks. For example a summand of rank two and slope five and a summand of rank one and slope minus one have total slope three.

For a metrized lattice, the largest slope is measured on sublattices and the smallest on quotients, with the corresponding restricted and quotient metrics. In a diagonal orthogonal example a lattice with basis lengths $e^(-4),e^(-1),e^2$ has degree $4+1-2=3$, hence mean slope one. Its embedded first line has slope four and its quotient by the first two coordinate lines has slope minus two. More generally the dual reverses the roles of subobjects and quotients. An injection of rational vector spaces gives a surjection on their rational duals. For a saturated sublattice $F subset.eq L$, the integral map from $L^∨$ to $F^∨$ is also surjective, since an integral basis of $F$ extends to a basis of $L$. The inclusion $2ℤ subset.eq ℤ$ illustrates the need for saturation. Restriction sends an integral functional to one whose value on the generator two is even. In a basis compatible with the metrics the determinant of the dual metric is reciprocal to the original determinant. The minimum slope of the dual is consequently the negative of the maximum slope of the original, under the lattice hypotheses used here. The fixed target in the period argument is a *dual* lattice, so this change of sign is used when replacing its minimum slope by bounds on the original space.

The slope inequality from the release deals with maps from many source lattices to that fixed target. It measures the total independent image rather than picking the single source with best slope. This is necessary even over the integers. The maps $ℤ arrow.r ℤ^r$ with images the individual coordinate lines can each have operator norm one and generate the whole target only when considered together. Repeating one of the coordinate lines many times changes neither its norm nor its height, but can destroy generation. Rank and overlap estimates accompany the bound on slope for exactly this reason.

== The division and overlap estimates <c14s03>

Fix one geometric realization of a translate of the thick set. Let $W$ be the finite nonempty set of words for this realization, $d_u>0$ the dimension weight of a word, and $h_u$ its map-height allowance. Write $N_u$ for the metrized source lattice after the changes of integral structure, and $P$ for the common comparison lattice. Define
$ s=frac(sum_u d_u (mu(N_u)-h_u),sum_u d_u), quad
  U=max_u (mu_(max)(N_u)-h_u)-s. $
The first quantity measures the average available slope. The second measures the spread. An upper bound $H_0>0$ controls $s-mu_(min)(P)$, with $H_0<=x^(c_H)b$. Three error parameters enter the comparison. A fraction $0<=delta_0<1$ accounts for missing rank, $eta_0>=0$ measures excess overlap, and $0<=e_0<=1/4$ bounds a diagonal error.

#claim[The slope comparison][For the rational maps attached to the admissible chain, the lower estimate for the common slope is
$ s-log|W|- frac(4U log(1+H_0/U)+(eta_0+4sqrt(e_0))H_0,1-delta_0)
      <= mu(P). $
At $U=0$ the continuous value of $U log(1+H_0/U)$ is zero.]

The loss $log|W|$ reflects using many images at once. To understand the overlap terms, view the maps over the complex numbers and form their Gram operators. Apply the relative trace estimates when every word meets the common dimension condition $C_0^(-1)<=d_u Gamma^2/D_*<=C_0$, with $Gamma$ the map normalization. For distinct words the mixed squared Hilbert–Schmidt norm is bounded by $frac((1+eta)d_u d_v,D_*)$, in terms of the source dimensions and the reference dimension $D_*$. A separate estimate controls the diagonal error and the ratio of the full ambient dimension to $D_*$. Expanding the trace of the square of the sum of the operators then bounds the dimension of directions where the images concentrate. Cauchy–Schwarz changes a mean square defect to a square-root error. Applying the resulting dimension inequalities to the slope filtration and summing them gives the logarithmic spread term in the displayed inequality. In the chosen ranges the trace comparison supplies errors with $eta$ and $sqrt(e_0)$ at most $exp(-x^(epsilon/8))$. These survive multiplication by the polynomial factor in $H_0/b$.

The integral comparison also supplies an upper estimate. Put $A=sum_t a_t$, let $T_u>0$ be the auxiliary size attached to a word, and let $F_o$ be the common local correction. With $phi(y)=y log y-y$, one obtains
$ mu(P)+h_u-F_o <= sum_t m(phi(a_t)-a_t log Omega)-A log T_u+E_D. $
Here $log Omega=gamma+log(pi/v)-ell_d$, where $v$ is the period scale and $ell_d=frac(L'(1,chi_d),L(1,chi_d))$. The bound $E_D$ includes a top-place rounding error and a term of order $m(B_0+N_c)x^(e_D epsilon)$, where $B_0,N_c$ are the size budgets for ranks and congruences. This division estimate uses a single rational map to the common lattice and the full-rank identification. Separate bounds for the heights of unrelated maps would not yield it.

== Gram operators and the effective image rank <c14s04>

Let $A_u:H_u arrow.r H$ be maps between finite-dimensional Hermitian spaces. With $Q_u=A_u A_u^*$, one has
$ tr(Q_u Q_v)=norm(A_u^* A_v)_(op("HS"))^2>=0. $
Indeed the cyclic property of trace gives $tr(A_v^* A_u A_u^* A_v)$, the sum of the squared norms of the columns of $A_u^* A_v$. When the $A_u$ are isometries onto their images, $Q_u$ is the orthogonal projector onto that image. Orthogonal images give zero mixed trace. Coincident subspaces of dimension $d$ give mixed trace $d$. Thus the expression sees both dimension and overlap.

Put $S=sum_u Q_u$. Its nonzero eigenvalues $lambda_1,dots,lambda_r$ are positive. By Cauchy–Schwarz,
$ op("rank")(S) >= frac((tr S)^2,tr(S^2)) $
if $S!=0$. Equality occurs exactly when those eigenvalues are all equal. The range of $S$ is the span of the image spaces, since its kernel is the intersection of the orthogonal complements of those images. Consequently a lower bound for $tr S$ and an upper bound for $tr(S^2)$ guarantee independent directions in the fixed target. Expanding the square separates the off-diagonal quantities above from the diagonal terms $tr(Q_u^2)$.

#example[The angle between two image lines][Let $v_1,v_2$ be unit vectors in a two-dimensional Hermitian space with $|chevron.l v_1,v_2 chevron.r|=c$. The sum of the two rank-one projectors has trace two and trace of its square $2+2c^2$. The bound on rank is $frac(2,1+c^2)$. For $c=0$ this returns two. It remains strictly larger than one whenever $c<1$, proving that two distinct lines span a plane. At $c=1$ both the exact rank and the lower bound drop to one. The small eigenvalue $1-c$ controls how poorly conditioned the basis can become while the dimension is still two.]

Another useful consequence concerns a subspace with orthogonal projector $P$ of rank $a$. The inequality $tr(P S)<=sqrt(a tr(S^2))$ follows by Cauchy–Schwarz for the Hilbert–Schmidt inner product. More quantitatively, if $D=dim H$ and $q=frac(tr(S),D)$, write $S=q I+(S-q I)$. Then
$ |tr(P S)-q a|<=sqrt(a) norm(S-q I)_(op("HS")), $
$ norm(S-q I)_(op("HS"))^2=tr(S^2)-frac((tr S)^2,D). $
This bounds how much of the images can concentrate in any subspace in a filtration. It explains the square root of a diagonal error in the slope theorem: a squared Hilbert–Schmidt norm controls a trace deviation via square root. These finite-dimensional inequalities illustrate steps in the comparison. The full theorem also accounts for arithmetic heights and possible defects of rank over the coefficient field.

The hypotheses in the release specify the scale at which these Hilbert spaces are compared. For each word the source dimension is $d_u$, a factor $Gamma$ comes from normalization, and a reference dimension $D_*$ enters. The implication requires $C_0^(-1)<=frac(d_u Gamma^2,D_*)<=C_0$ for all words. Under that balance, the mixed squared norm for $u!=v$ is at most $frac((1+eta_0)d_u d_v,D_*)$. The diagonal squared error from identity is at most $e_0 d_u$. The full ambient dimension is at most $(1+eta_1)D_*$. These are three distinct estimates. A small mixed term alone does not normalize the size of each map; a small diagonal term alone gives no comparison between different words. #src("Formalism.SharpRestriction.GlobalTheoremInputs")[The three Hilbert–Schmidt bounds.]

== Two different averages and a logarithm <c14s05>

Let $z$ index one geometric realization and write $tau(z)$ for its translate. Its words form a finite nonempty set $W_z$ with positive dimensions $d_u$. Write
$ chevron.l X chevron.r_d=frac(sum_(u in W_z)d_u X_u,sum_(u in W_z)d_u). $
The outer mean in the abstract slope theorem, denoted $bb("E")_z$, is uniform over the realizations. For instance two words of dimensions one and nine with values ten and zero have dimension-weighted mean one. A realization with ten words and one with two words receive equal outer weights. Several realizations can map to the same translate. The later Fourier mean gives one weight to each element of the translating subgroup.

Using this notation put $s=chevron.l mu(N_u)-h_u chevron.r_d$, and $U=max_(u)(mu_(max)(N_u)-h_u)-s$. Each maximal slope is at least the corresponding mean, so $U>=0$. The upper range bound $H>0$ satisfies $s-mu_(min)(P)<=H$, where $P$ is the fixed target lattice. In these variables the deficit charged by the slope theorem includes
$ frac(4U log(1+H/U)+(eta+4sqrt(e))H,1-delta). $
The term in the numerator depending on $U$ has value zero at $U=0$. One way to check the limit is to put $v=H/U$ and observe that $frac(log(1+v),v)$ tends to zero as $v$ tends to infinity. It is also useful that $U log(1+H/U)<=H$ by $log(1+s)<=s$.

A sharper elementary bound used for uniform estimates is available when $H<=b x^c$. If $U>=b>0$, then $U log(1+H/U)<=U log(1+x^c)$. If $0<U<b$, the function $u mapsto u log(1+H/u)$ is increasing: its derivative is $log(1+t)-frac(t,1+t)$ with $t=H/u$, nonnegative because the derivative of this last expression with respect to $t$ is $frac(t,(1+t)^2)$ and it vanishes at zero. Thus the left side in this second case is at most $b log(1+x^c)$. Combining both cases gives a bound by $(U+b)log(1+x^c)$, including $U=0$. The advantage is that the average of an upper bound for $U$ can now be used in an expression which initially mixed $U$ and $1/U$ nonlinearly. The denominator $1-delta$ still requires $delta$ bounded away from one.

Two model integrals explain this logarithm. For $U,t>0$ one has
$ frac(U,U+t)<=min(1,U/t)<=frac(2U,U+t). $
For $t<=U$, the middle term is one and $U+t<=2U$. For $t>=U$, the middle term is $U/t$ and $U+t<=2t$. The integral of the smooth expression from zero to $H$ is exactly $U log(1+H/U)$. The integral of the minimum is $H$ for $H<=U$, and is $U+U log(H/U)$ for $H>=U$, by splitting the interval at $U$. At $H=U$ the two integrals give $U log 2$ and $U$, respectively. Thus a bound for the proportion of lost rank by the minimum gives an integrated allowance within a factor two of the smooth expression. The actual slope theorem supplies its own coefficient four and its geometric hypotheses.

== Where the large terms cancel <c14s06>

Write $M_u$ for the comparison lattice before the net local gain is counted. The lower slope bound for $N_u$ has the form
$ mu(N_u)>=mu(M_u)+G_a+F_o-E_u-L_u. $
Here $E_u$ is a contribution from the distinguished places and $L_u$ collects controlled losses. The difference between $E_u$ and $m A ℓ_g$ is small, with $ℓ_g$ the logarithm of the product of the two auxiliary Hecke primes. The count of admissible words supplies, for each word, a lower bound
$ log T_u>=frac(1,f) sum_(j=1)^m sum_(rho in Phi) log(frac(w_(j,rho)v,pi))+m ℓ_g-E_T. $
The sum is over $j=1,dots,m$ and all embeddings $rho in Phi$. Its proof uses the weight dimensions and volume normalizations. The Weyl dimension formula computes dimensions from highest-weight differences, Siegel mass relates the adelic volume to the lattice-class measure, and the CM period comparison supplies the normalization of $Omega$.

Insert the lower bound for $mu(N_u)$ into $s$ and combine the two inequalities for $mu(P)$. Height comparison across words controls the variation of $h_u+A log T_u$. The $F_o$ terms cancel. Substituting the lower bound for $log T_u$ cancels $m A ℓ_g$ against $E_u$. At a single step and top place the surviving main term is
$ a_t (log a_t-1-gamma+ell_d
               -frac(1,f) sum_(rho in Phi) log w_(j,rho)). $
Indeed $-log(pi/v)$ in $-log Omega$ cancels $-log(v/pi)$ from the word count. Rescaling $v$ in both occurrences changes the sum by zero. Multiplying every weight by $lambda>0$ instead changes the main term by $-m A log lambda$. A mismatch of the scale $v$ between the two period comparisons would likewise leave an uncanceled logarithmic term multiplied by $m A$.

== Eliminating the lattice slopes one line at a time <c14s07>

The algebra isolating the main term is short enough to keep every sign. Throughout this calculation fix $z$, set $A=sum_t a_t$, and let $E_D$ be the division error, common as an upper bound for the words considered. Abbreviate the full slope deficit, including $log |W_z|$, by $E_S$. The lower estimate for the modified lattice, followed by the common-target comparison, gives
$ mu(P)>=s-E_S $
$ s>=chevron.l mu(M_u) chevron.r_d+G_a+F_o
          -chevron.l E_u+L_u+h_u chevron.r_d. $
The word dependence of $M_u,E_u,L_u,h_u$ is retained. In this fiber the retained gain $G_a$ and common correction $F_o$ are fixed.

The division inequality for each word, averaged with *the same weights*, reads
$ mu(P)+chevron.l h_u chevron.r_d-F_o
   <=m sum_t phi(a_t)-m A log Omega -A chevron.l log T_u chevron.r_d+E_D, $
where $phi(a)=a log a-a$. Combining the preceding inequalities cancels $F_o$ and the mean height identically, and yields
$ G_a <= m sum_t phi(a_t)-m A log Omega-A chevron.l log T_u chevron.r_d
      +chevron.l E_u chevron.r_d + E', $
where $E'=E_S+E_D+chevron.l L_u-mu(M_u) chevron.r_d$. The remaining estimates control this last quantity from above. The cancellation also explains why a height comparison across words is still needed: even though the mean height has canceled here, the spread $U$, which enters $E_S$, still depends on the individual heights.

The auxiliary local estimate at a single step bounds the difference between its word correction and $A ℓ_g$ by $C_E B_0$. Summing over the $m$ steps shows that $chevron.l E_u chevron.r_d$ differs from $m A ℓ_g$ by at most $m C_E B_0$. The count gives for each $u$
$ log T_u>= sum_(j=1)^m frac(1,f)sum_(rho in Phi)log frac(w_(j,rho)v,pi)
                 +m ℓ_g-E_T. $
Multiplying this *lower* bound by $-A$, with $A>=0$, produces an *upper* bound for the term in the previous display. The resulting $-m A ℓ_g$ cancels the leading part of the auxiliary local correction. If the count were an upper bound here it could not be used in this direction.

Expand $log Omega=gamma+log(pi/v)-ℓ_d$. The weight sum has $f$ terms per step, hence its constant part is exactly $m log(v/pi)$. Together with $-m A log(pi/v)$ it vanishes. Distributing $A=sum_t a_t$ now leaves at step $j$ and top $t$ the main term
$ a_t (log a_t-1-gamma+ℓ_d-frac(1,f)sum_(rho in Phi) log w_(j,rho)). $
The error has increased by $m C_E B_0 + A E_T$. This derivation fixes the signs of $gamma$, $ℓ_d$ and the weight average without appealing to the analytic explicit formula. In Chapter 17 they will appear a second time when that formula is expanded independently. #src("Formalism.RankGapBounds.MeanBoundSecondForm")[Word averages, counts and the main term.] #src("Formalism.LocalRingCardinality.DataParams₂")[The period normalization.]

The cancellation can be tested by varying the two sorts of scales independently. Replacing $v$ everywhere by $kappa v$ with $kappa>0$ changes the contribution from $-m A log Omega$ by $+m A log kappa$. The count contributes $-m A log kappa$ through its logarithmic average. Their sum is zero. By contrast, multiplying all $w_(j,rho)$ by $lambda>0$ increases their log average by $log lambda$ at each step. The total main term changes by $-m A log lambda$. Simultaneously changing $v$ in both its occurrences still contributes zero, so the weight shift survives. Changing the period convention on only one side would also leave a term of order $m A$ for a fixed nonzero logarithmic shift. These are different tests of the normalization.

An individual change of an embedding weight has a more localized effect. Write $lambda_(j,rho)>0$ for its factor and hold the $a_t$ fixed. Summing the preceding logarithms gives a change of
$ -frac(A,f)sum_(j=1)^m sum_(rho in Phi) log lambda_(j,rho). $
For instance, with two steps, four embeddings and top weights two and three, doubling just one of the eight entries subtracts $frac(5 log 2,4)$ from the main term. Doubling all eight subtracts $10 log 2$. If the product of the changes is one, this main term is invariant, although individual character projections or finite-place gain estimates may still depend on which embedding changed. A comparison of just the maximum or minimum weight does not recover the logarithm of this product.

== Exact scope of the mean and pointwise estimates <c14s08>

For each realization $z$, write $Q(z)$ for its arithmetic prime sum and $M(z)$ for its main term. One packaged theorem assumes only that
$ bb("E")_(z)(Q(z)-G_(a)(z))<=P_0, quad bb("E")_z I(z)<=P_0, $
where $I$ is a local correction. With the division, count, slope, height, and error bounds of that theorem, the conclusion is $bb("E")_z Q(z)<=bb("E")_z M(z)+E_x$. Nothing in these two input inequalities bounds each $Q(z)-G_(a)(z)$ by $P_0$. For two realizations, let this difference be $2P_0$ and zero respectively, with $P_0>0$. Their mean is exactly $P_0$ although the first difference exceeds it. A difference of $B$ and $-B$ would even have mean zero for arbitrary $B$. This is a potential logical error when reading an expression simply called an “average loss.”

The stronger pointwise version of the comparison has a distinct hypothesis. It requires $Q(z)-G_(a)(z)<=P_0$ and $I(z)<=P_0$ for *every* realization in the selected family. It also uses the specified pointwise quotient-slope bounds, the word-count and total-correction comparisons specified in this version, and the other division and slope hypotheses. Its conclusion is $Q(z)<=M(z)+E_(x)(z)$ for each such $z$. The theorem attaching this to the character sum uses identifications of the abstract top and embedding sets and the actual weights. At its associated translate $tau(z)$, the discrepancy equals $Q(z)-M(z)$. A common upper bound for the pointwise error, together with coverage of the translating subgroup by $tau$, gives the bound there. One can now use the uniform subgroup mean for Fourier projection. Every version still has a dimension-weighted word mean inside the fiber. The arithmetic construction supplies the hypotheses for the version it invokes. Strengthening the conclusion of the first theorem without these extra inputs would be unjustified. #src("Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith")[LossBounds and PointwiseBoundVariant.] #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence")[The pointwise theorem.] #src("Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop")[Its use in the prime-sum comparison.]

== The geometric covolume input <c14s09>

One further bound keeps the integral covolumes entering these slopes under control. Sections of algebraic automorphic bundles are compared on integral models and their toroidal compactifications. An injective evaluation of small sections bounds the index of a lattice through its determinant. Heights of the relevant cycles are bounded using Chow forms and intersections of hyperplanes. The comparison with Hermitian norms uses Poincaré–Lelong and arithmetic Hilbert–Samuel estimates. Integral extension, point separation, and estimates for the Hodge bundle are needed at the boundary. This part is used as a geometric comparison theorem. Its conclusion is uniform along the selected family after a fixed size threshold, which allows the same constant to be used for every step on the eventual interval.

There are two versions of the resulting bound. Mean bounds for the losses give a mean discrepancy over the geometric realizations, each with its own weighted word average. The construction used in Chapter 17 bounds both losses at every realization. Because these realizations cover the subgroup of translates, that pointwise estimate gives an upper bound at every required translate. Chapter 17 can then average uniformly over the subgroup to perform Fourier projection. The remaining inputs are the congruence lengths on the selected interval and the cost after division by the number of lifts and thick places.

== An arrangement of lines that attains the rank bound <c14s10>

A higher-dimensional example shows exactly how the mixed trace terms can certify the dimension of a common image. Let $v_1,dots,v_N$ be unit vectors in a real or complex Hilbert space and $P_i$ the orthogonal projection onto the $i$th line. The positive operator $S=sum_i P_i$ has image the span of the vectors. Its trace is $N$, and
$ tr(S^2)=N+sum_(i!=j)|chevron.l v_i,v_j chevron.r|^2. $
Indeed $P_i^2=P_i$, and the trace of $P_i P_j$ is the squared absolute value of the scalar product. If every such square for $i!=j$ is at most $c$, Cauchy–Schwarz on the nonzero eigenvalues gives
$ op("rank")(S)>=frac(N^2,N+N(N-1)c). $
The sum uses ordered pairs, so omitting the second order of each pair would make the lower bound too optimistic. With mutually orthogonal vectors $c=0$ and the formula recovers the rank $N$ exactly.

More instructively, let $d>=2$ and take the hyperplane of vectors with coordinate sum zero inside $ℝ^(d+1)$. Write $e_i$ for the standard coordinate vectors and $u$ for the all-ones vector. Put
$ v_i=sqrt(frac(d+1,d))(e_i-frac(u,d+1)), quad 1<=i<=d+1. $
They have unit length, and for $i!=j$ their scalar product is $-1/d$. The subtraction of the common mean removes the direction of $u$ and leaves the span $d$-dimensional. The abstract rank bound with $N=d+1$ and $c=1/d^2$ has denominator $frac((d+1)^2,d)$, giving precisely $d$. Every mixed term is nonzero, yet their controlled size proves that the lines generate the entire specified hyperplane.

One can identify $S$ without any inequalities. On the hyperplane, $chevron.l x,u chevron.r=0$ and $chevron.l x,e_i chevron.r=x_i$ in these real coordinates. Hence
$ S x=frac(d+1,d)sum_i x_(i)(e_i-frac(u,d+1))=frac(d+1,d)x. $
All nonzero eigenvalues are equal, the equality condition in the trace-rank estimate. Remove one vector, say $v_1$. The new operator on the same hyperplane is $(frac(d+1,d))I-P_1$. On its distinguished line it has eigenvalue $1/d$, while on its orthogonal complement it has eigenvalue $frac(d+1,d)$. Its image still has full rank, but the square-root norm underlying the analysis and synthesis maps now sees a weak direction. A filtration concentrating mass on that direction can behave differently after the removal even though the rank is unchanged.

For a quantitative form of that last observation, let a positive operator have eigenvalues $lambda_i$ and let $q>0$ be their mean on the ambient space. If the Hilbert–Schmidt error $norm(S-q I)_(op("HS"))^2$ is at most $B$, at most $frac(B,epsilon^2 q^2)$ eigenvalues can differ from $q$ by at least $epsilon q$, for any $epsilon>0$. Each such eigenvalue contributes at least $epsilon^2 q^2$ to the squared norm. In particular each missing direction costs $q^2$. This bound can still allow a small exceptional subspace with very low slope. It explains why the arithmetic theorem must compare the heights and slopes of the word spaces as well as the trace geometry. In the lines example every vector comes from rank one and the norms were prescribed at a single real place. The actual comparison uses each word's archimedean map, its intrinsic dimension, and its integral source lattice.

== Bounding the spread from data on individual words <c14s11>

We can derive the quantity used for $U$ directly. Fix one realization and put $A=sum_t a_t$, $n_T=|T_"top"|$. At each of the $m$ steps the error comparison gives $|E_(u,j)-A ℓ_g|<=c_E B_0$. Subtract the inequalities for two words $u,v$ and sum over the steps. The common center cancels, giving
$ |E_u-E_v|<=2m c_E B_0. $
For the heights the information is more subtle. The comparison controls the variation of the corrected height $h_u+A log T_u$ across the fiber by $c_(H)(n_T a Λ+m B_0)$. Here $Λ$ denotes the parameter in the geometric slope bound. The independent count estimate gives $|log T_u-log T_v|<=c_C log k$. Subtracting the two logarithms and using $A>=0$ shows that the variation of the ordinary height is at most $c_(H)(n_T a Λ+m B_0)+A c_C log k$. In particular the variation of $F_u=E_u+h_u$ is controlled by
$ V=2m c_E B_0+c_(H)(n_T a Λ+m B_0)+A c_C log k. $
These inequalities compare word heights within the same realization. #src("Formalism.RankGapBounds.MeanBoundSecondForm")[The three comparisons and the variation term.]

In a finite set with positive weights, if $|F_u-F_v|<=V$ for every pair, then $|F_u-chevron.l F chevron.r_d|<=V$, where the mean is taken using these same weights. More explicitly, with $d=sum_v d_v$ one has
$ F_u-chevron.l F chevron.r_d=frac(1,d)sum_v d_(v)(F_u-F_v). $
The claim follows by the triangle inequality. This step requires no independence and allows highly nonuniform weights. Applying it to $F_u$ above is cheaper than controlling each $|E_u|$ and $|h_u|$ separately. A large common offset can occur in those two quantities without increasing their spread.

To make the slope argument explicit, put $S_0=c_S n_T a Λ$ and write $J=G_a+F_o$, which is independent of the word. The two comparisons for the modified lattice read
$ mu_(max)(N_u)-h_u <=mu_(max)(M_u)+J-F_u+c_1 m B_0, $
$ mu(N_v)-h_v>=mu(M_v)+J-F_v-L_v. $
Hold $u$ fixed and average the second inequality over $v$. Subtract it from the first. The $J$ terms cancel. Using $mu_(max)(M_u)<=S_0$, $mu(M_v)>=-S_(0)(1+m/k)$ gives
$ mu_(max)(N_u)-h_u-s
   <= S_(0)(2+m/k)+V+c_1 m B_0+chevron.l L chevron.r_d. $
The bound is independent of the chosen $u$, so it bounds $U$ in that fiber. If only a uniform *realization mean* of the last term is available, an upper bound for the same mean of $U$ follows by averaging at this stage. Bounding each $U$ by an expression containing that global mean would require an additional hypothesis.

The last term can itself be expanded. At word $v$ its four contributions are a multiple of the translate correction $I(z)$, a multiple of $n_T m(a/k+b')log T_v$, a uniform $c_1m B_0$, and a tail $R_v$. The upper bound $log T_v<=c_C m L$ and the mean bound on $I$ give an upper bound for the two successive means of $L_v$,
$ c_1 P_0+c_1 n_T m(a/k+b')c_C m L+c_1 m B_0
        +bb("E")_z chevron.l R chevron.r_d. $
The source substitutes this expression into the bound for the translate mean of $U$. The appearances of $m$ in the second summand have different origins. One comes from summing costs over steps. The other comes from an upper bound for the logarithm of the word dimension factor. If $k$ is chosen much larger than $m$, the term involving $a/k$ gets smaller but the $b'$ term still needs control. #src("Formalism.RankGapBounds.MeanBoundSecondForm")[The loss, its mean bound, and the bound on the spread.]

The tail makes the role of a *lower* count visible. Write $Δ_v=mu_(max)(M_v)-mu(M_v)$. The word contribution has the form
$ R_v=frac(4 f,T_v)(|G_a|+tau+Δ_v+2 f log T_v). $
Its numerator contains a nonnegative slope spread and the gain in that realization. Suppose a family supplies $T_v>=b^(m/2)$ with $b>=1$, and an upper bound $0<=|G_a|+tau+Δ_v+2 f log T_v<=P$ uniform in the relevant fibers. Then $R_v<=4 f P b^(-m/2)$ for all those words. For example if $f P<=C b^a$ for fixed $C,a$ and $m>=2a+4$, this is at most $4 C b^(-2)$. The arithmetic theorem uses its own quantitative bound on $tau$ and the other terms in the numerator. A lower bound on $T_v$ on its own supplies no upper bound when the numerator can grow arbitrarily. Conversely, replacing $T_v$ by its logarithm in the denominator would lose the decay in $m$. The two count estimates thus serve different roles within one expression.

== An adelic check on the sign of a height <c14s12>

A linear map over a number field may be represented in different rational bases. Its determinant comparison must survive that choice. On a line over $ℚ(i)$, take the specific scalar $alpha=2+i$ and the standard lattice $ℤ[i]$. In the integral basis $1,i$ multiplication by $alpha$ has matrix $mat(2,-1;1,2)$. The index of the image lattice is its determinant five. At the complex place multiplication by $alpha$ scales ordinary lengths by $sqrt(5)$ and areas by five. Thus the logarithm of the real covolume of the image increases by $log 5$. A sign convention in which the degree is minus the logarithmic covolume decreases its degree by the same amount, before any normalization by the global field degree.

The adelic product formula explains why changing a *rational generator* carries no intrinsic height. Use the normalized nonarchimedean absolute value for an integral prime ideal, $|alpha|_v=(N v)^(-op("ord")_(v)(alpha))$, and the square of the usual complex absolute value at the one complex place. The only nonunit finite valuation of $2+i$ occurs at the prime ideal $(2+i)$ of norm five, where its absolute value is $1/5$. The archimedean factor is five. Their product is one and the sum of their logarithms is zero. If the sum is divided by $[ℚ(i):ℚ]=2$, those two summands become $-frac(log 5,2)$ and $frac(log 5,2)$. An equivalent convention splits the complex place into two embeddings and assigns the ordinary absolute value at each. The two archimedean logarithms then sum to the same $log 5$ before normalization. Counting both embeddings *and* squaring their ordinary absolute values would double the archimedean term.

These calculations refer to two different operations on a line. Replacing a chosen rational generator by $alpha$ times the generator changes both its finite and infinite measurements. Their summed change is zero. Keeping the fixed ambient norm and replacing the integral lattice itself by its index-five sublattice changes the measured covolume and its degree. This distinction is essential for the period calculation. Dividing its common integral entries by a common ideal enlarges the integral model with an index measured at finite places. Comparing its complex realization with the prescribed theta or Bessel metric is an independent archimedean calculation. Measures and complex embeddings must be counted with the convention chosen for the common period throughout. The same numerical factor may legitimately appear several times when different maps are involved, but changing conventions between its two realizations would prevent the cancellation in the following calculation.

== Where a lower bound on a geometric degree comes from <c14s13>

We describe a calculation behind the bound for $mu(M_u)$. It has a familiar algebraic analogue. Let $L$ be a rank-$r$ lattice of sections and choose $r$ integral linear functionals on it given by evaluations or jets at chosen points. In a basis of $L$ the evaluations form an $r$ by $r$ matrix $A$. If its determinant is nonzero, the evaluations separate this space and give an injection into the coordinate lattice. Over the integers its cokernel has size $|det A|$. At infinity Hadamard's inequality bounds this determinant by the product of the row norms. A bound for these norms therefore yields an upper bound on an index, and hence a lower bound on a slope after the embedding and the reference normalization have been fixed. A family of evaluations separating only a quotient leaves an unseen sublattice on which this calculation gives no information.

For example take the polynomials $1,X,X^2$ and evaluate at zero, one and an integer $a>1$. Subtract the first row from the last two rows. The determinant of the evaluation matrix becomes $a^2-a$. Thus the image in $ℤ^3$ has index $a(a-1)$. Modulo a prime dividing $a(a-1)$ two of the three points coincide, and the reduction of the map has rank less than three. The same evaluation which is injective over $ℚ$ can lose integral information at special fibers. Replacing repeated values by jets gives a confluent Vandermonde determinant with new normalization factors. This example illustrates why the global comparison needs integral extension, separation at the boundary, and control of the chosen metrics, in addition to complex linear independence.

In the geometric theorem, at a component $Z$ let $d_Z>0$ be a degree, $r_Z$ the rank share, and $h_Z$ a possibly signed height. A positive binomial factor $B$ and a dimensionless defect $zeta$ satisfy
$ (1-zeta)r_Z<=B d_Z<=r_Z. $
The Hilbert–Samuel estimate in the release supplies $A>0$, $D>=0$ with controlled $A log(max(A,1))+D$ and a lower bound
$ op("deg")_Z>= B d_Z (L h_Z-c|h_Z|-A log(2+|h_Z|)-D), $
where $c=3(d_F+1)$ for the relevant flag dimension $d_F$ and $L$ is the tensor-power scale. This is a statement about an arithmetic degree, including the metrics. A geometric dimension estimate alone provides neither the term $L h_Z$ nor the error depending on absolute height.

The rank share must multiply $h_Z$ in the right direction. Suppose $0<=zeta<=1$ and there is a common shift $c_s>=0$ with $h_Z+c_s>=0$. Then
$ B d_Z h_Z &=B d_(Z)(h_Z+c_s)-B d_Z c_s \
   &>=(1-zeta)r_(Z)(h_Z+c_s)-r_Z c_s \
   &=(1-zeta)r_Z h_Z-zeta r_Z c_s. $
This simple three-line estimate is valid for either sign of $h_Z$. For $h_Z<0$, directly multiplying the lower share inequality by $h_Z$ would reverse it. The shift introduces a real cost $L zeta r_Z c_s$ when the leading height is multiplied by $L$. This is why the formal height hypothesis explicitly controls a term involving $c_s L zeta$. The same hypothesis compares the shifted height to a shifted component slope and bounds the mean of those slopes below. It bounds $L$ times the permitted comparison errors before passing to the family. #src("Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol")[The rank share, component heights, and Hilbert–Samuel inequality.]

The logarithmic penalty in the geometric inequality can be understood by an elementary calculation. Write $y=|h_Z|$ and $M=max(A,1)$. Since $log u<=u-1$ for $u>0$, applying it to $frac(2+y,2M)$ and multiplying by $A$ gives
$ A log(2+y)<=A log(2M)+frac(A(2+y),2M)-A
            <=A log(2M)+1+frac(y,2). $
The coefficient of $y$ on the right is independent of $A$. The other quantity to control is $A log(2M)=A log M+A log 2$. When $A>=e$ one has $A<=A log M$, while for $0<A<e$ the second summand is at most $e log 2$. Thus the constant loss here is at most an absolute multiple of $1+A log(max(A,1))$. This explains why a bound on precisely this expression together with $D$ is natural even when the coefficients $A,D$ vary from component to component.

There is no need to require that all the $h_Z$ have the same sign to use this estimate. From $h_Z+c_s>=0$ it follows that $|h_Z|<=h_Z+2c_s$. For a nonnegative coefficient $C$, one obtains
$ L h_Z-C|h_Z|>=(L-C)h_Z-2C c_s. $
For $h_Z>=0$ one can remove the shift on the right. For negative heights the shift controls the reversal. If $L>C$, the remaining signed term still has positive coefficient and may then be estimated with the appropriate rank share. This calculation also distinguishes the cost $2C c_s$ from the earlier cost proportional to $L zeta c_s$. They arise from different inequalities and cannot automatically be charged to the same allowance. On summing over components the estimates are weighted by their degree or rank shares; a very unfavorable small component contributes according to its share. An unweighted maximum over all component heights would discard that information.

The construction of these estimates uses geometry at bad reduction as well as at infinity. A toroidal compactification extends the relevant automorphic bundles toward the boundary. Chosen small sections and hyperplane intersections control integral restriction maps. Chow forms compare heights of the resulting cycles. Poincaré–Lelong and arithmetic Hilbert–Samuel estimates relate these algebraic data to metrized volumes. The pinned theorem producing the covolume bound identifies the separate sufficient inputs, including resolution and principalization in characteristic zero, the Hodge bundle comparisons, toroidal extensions, and the inequalities for small sections. Its output is uniform after a fixed threshold on the family and is compatible with all allowable points there. It is used here through that quantified comparison. The elementary evaluation determinant and the signed rank calculation explain why each kind of hypothesis is needed. #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolSlim2Use")[Proof supplying the covolume condition.] #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound")[Its uniform conclusion.]

#source-note[The #src("Formalism.RankGapBounds.MeanBoundSecondForm")[slope, word-count, and division inequalities] state the constants and signs. A #src("Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence")[pointwise deduction] combines them. The #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolSlim2Use")[covolume comparison] records the arithmetic-geometric inputs.]
