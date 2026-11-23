#import "style.typ": *
#front[Appendix A. Three auxiliary comparisons]
#let sub(body) = block(above: 10pt, below: 4pt, sticky: true)[#text(size: 13.2pt, weight: "bold")[#body]]
#sub[A.1. What the good prime pair actually supplies]

Fix the original modulus $M>=1$, an exponent $A>=1$, and $0<epsilon<1/52$. For every sufficiently large $Y$ there are distinct primes $q,d$ of the indicated sizes and congruences, with $(M,q d)=1$. For every base character $xi$ modulo $M$, and $(i,j)$ equal to $(1,0),(0,1)$ or $(1,1)$, let $chi$ be the primitive character agreeing with $xi chi_q^i chi_d^j$ on the units modulo $2M q d$. Throughout $Y<=y<=Y^A$ the same pair satisfies
$ |g_(chi)(y)|<=y^(1/2+epsilon/2), quad
    abs(frac(L'(1,chi),L(1,chi)))<=4 log y. $
There is also a zero-free rectangle for the same three nontrivial choices of $(i,j)$ applied to every real primitive base character of conductor dividing $8M$. With $z=Y^(epsilon/5)$ its conditions are
$ Re s>1-1/400, quad |Im s|<=8M exp(z)exp(z(log Y)^2)^j. $
The height includes the last exponential factor exactly when $j=1$, so a twist by $q$ alone and a twist using $d$ have different guaranteed heights. The target family with $i=j=0$ receives its small-window bound from the theta argument.

The counting proof combines a mean-square estimate over the candidate primes and a count of the exceptional zero boxes. For a finite candidate set $P$ the elementary inequality
$ |{p in P : |D_p|>T}| <= T^(-2)sum_(p in P)|D_p|^2 $
converts a moment into a bound for the bad share. Families of base twists are combined by summing their bad shares. Bounds on primes in progressions give a lower count for $P$, first for the permitted $q$, then for the congruence class of $d$ after $q$ is chosen. Primitive induction ensures that a counted exceptional character is assigned to the correct candidate and twist. The proof budgets the two sorts of exceptions separately and can leave at least half the candidates at both stages. Parameter estimates extend the bounds over the requested range of $y$. This gives a pair by two successive choices from nonempty finite sets.

The large-argument estimate requires three facts about the chosen host. Its auxiliary conductor $Q_S$ has odd part bounded by a fixed $B$, its host modulus $N_H$ satisfies $log N_H<=2 x^(epsilon/5)(log x)^2$, and every real host character whose conductor is divisible by $q$ or $d$ has no real zero $beta>1-1/400$. The third condition follows from the applicable zero boxes. With these hypotheses, a fixed $c>0$ gives, for $x$ above a threshold depending on $B,epsilon$, every prescribed host character and every $y>=frac(exp(x^(epsilon/3)),3)$,
$ |g_(chi)(y)|<=y exp(-c x^(epsilon/8)). $
At $y=frac(a_t,w)$, multiplying by the thin weight gives $a_t exp(-c x^(epsilon/8))$. The small-window estimate for the auxiliary twists and this large-argument estimate for all host characters enter Chapter 17 at different arguments. #src("Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq")[Proof of the host thin-weight estimate.]

#source-note[See #src("Development.AutomorphicArithmetic.CharacterBoxes.PairGood")[the prime-pair specification], #src("Development.AutomorphicArithmetic.MeanSquareBounds.pairEx")[existence of a pair for every sufficiently large starting scale], #src("Development.AutomorphicArithmetic.MeanSquareBounds.StagePow")[the exceptional-set estimate], and #src("Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic")[the host character bound].]

#sub[A.2. A covolume estimate through ranks and heights]

At a given lift the geometric comparison passes to a cover with well-behaved integral lattices of sections. Let $h_Z$ and $d_Z$ be the height and positive degree for a quotient weight on a component $Z$. Denote by $r_Z$ the relevant rank and by $d_F$ the dimension of the flag variety. A large integer $L$ is chosen of the size
$ ceil(P^2 d_F^2 k/m), $
where $P$ is an auxiliary positive scale. Write $B$ for the binomial factor of the resulting section count. Two precise estimates used together are
$ (1-zeta_0) r_Z<=B d_Z<=r_Z, $
$ B d_Z (L h_Z-3(d_F+1)|h_Z|-A log(2+|h_Z|)-D)
       <= op("deg")_Z. $
Here $op("deg")_Z$ is the arithmetic degree of the comparison sections, $A>0$, $D>=0$, and $A log(max(A,1))+D$ is bounded in units of the allowed geometric error. The defect $zeta_0$ has the form $7(d_F^2/L+d_F rho_0)$, where $rho_0$ measures a weight defect. Increasing $L$ reduces the first summand. The weight and level selections bound the second.

If $h_Z<0$, a lower bound on $B d_Z h_Z$ follows by multiplying the *upper* bound $B d_Z<=r_Z$ by $h_Z$. The lower bound on $B d_Z$ would give an upper bound instead. To handle both signs with the same expression the proof supplies $c_s>=0$ with $h_Z+c_s>=0$ and uses the rank estimate on this shifted height. In particular
$ B d_Z h_Z>=(1-zeta_0)r_Z h_Z-zeta_0 r_Z c_s. $
Multiplication by $L$ charges $L zeta_0 r_Z c_s$ when the shift is undone. The hypothesis on heights controls the shift together with the corresponding term involving $rho_0$, and bounds the mean component slope from below. Chapter 14 carries out this signed calculation and the estimate for the logarithmic height penalty. The separate comparison of the core and the actual lattice transfers the resulting lower slope estimate to the integral period argument.

#source-note[The exact #src("Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol")[rank share, height, Hilbert–Samuel, and core slope estimates] specify these normalizations. The #src("Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolSlim2Use")[covolume theorem] supplies them from integral geometry.]

#sub[A.3. Checking the simultaneous scale choices]

Here $x$ denotes the physical scale. Write $n=|H|$ for the auxiliary group order, so that $|Phi|=f=2n$ and $[E:ℚ]=4n$ for the realized Galois field. The raw-to-physical change of variables is proved in Chapter 18. For $delta_1=x^(-epsilon/8)$ the three rank parameters satisfy
$ x^(2+8epsilon)<=n<=2x^(2+8epsilon), $
$ sqrt(x delta_1)<=m<=2sqrt(x delta_1), $
$ x^(9/2+10epsilon)<=k<=2x^(9/2+10epsilon). $
In particular $m$ is of order $x^(1/2-epsilon/16)$. For large $x$ it is between $x^(1/2-epsilon)$ and $x^(1/2+epsilon/2)$. Also $x m<=k$. To verify the upper bound for $k$ used in Chapter 17, observe that
$ n^2 x^(1/2-epsilon)>=x^(9/2+15epsilon). $
The missing factor $x^(5epsilon)$ exceeds two eventually. The actual rank $k$ therefore satisfies both the lower bound needed in the second error term and the upper bound needed in the fourth one.

The rank that determines the *number of cohomological twists* is a fourth integer $t$. Its size does not follow from the three intervals alone. The definition also specifies $r=k+m-1$, $L_x=x^epsilon$ and
$ Q=f+frac(f^(2)(k-1)^3 L_x^2,m), quad
  W=8 ceil(frac(10r Q,8)), $
$ T=ceil(x^377), quad r+t=8f r+4+T W. $
These are natural ceilings of nonnegative quantities. We show $t<=x^400$ throughout the range $0<epsilon<1/52$, $x>=2^100$. This is the inequality used to specialize the cohomological sum to the actual rank. #src("Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows")[The complete rank specification.] #src("Development.AutomorphicArithmetic.CharacterBoxes.EventuallyRankLeRpowOfLtOneDivFiftytwo")[The bound on its twist cutoff.]

Put $y=x^(1/100)>=2$. The rank inequalities give
$ f<=4 y^216, quad k<=2y^470, quad m>=y^49, quad L_x^2<=y^4. $
For example $m>=x^((1-epsilon/8)/2)$ and $(1-epsilon/8)/2>=49/100$. The estimate for $k$ follows from $9/2+10epsilon<=470/100$, and $f=2n$ gives the first bound. Since the rank hypotheses imply $m+3<=k$, one also has $r<=2k<=4y^470$. In the second term of $Q$ the exponents of $y$ combine as $2 dot 216+3 dot 470+4-49=1797$. The coefficient is at most $4^2 dot 2^3=128$, so $Q<=132y^1797$. Rounding $W$ up to a multiple of eight costs less than eight, whence
$ W<=5280 y^2267+8<=5288 y^2267, quad T<=2y^37700. $
The defining rank identity now gives
$ t<=128 y^686+4+10576 y^39967<=10708 y^39967. $
The margin of thirty-three powers absorbs the coefficient, since $y^33>=2^33>=10708$. It follows that $t<=y^40000=x^400$. In particular $t<=floor(x^400)$ because $t$ is an integer. If $t$ equals the floor, the summation range on each side still excludes its upper endpoint. The room between the exponents $39967$ and $40000$ controls the rounding and constants inside the rank construction. The different margin from $400$ to $401$ in Chapter 18 pays for the dilation between the physical and raw variables. #src("Development.AutomorphicArithmetic.ShortNorms.supplyOfAdmOf")[Application of the rank bound to the finite-length sum.]

#source-note[The #src("Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows")[chosen rank ranges] imply the #src("Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis")[windows needed for the last size calculation].]
