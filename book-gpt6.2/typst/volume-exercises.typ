#import "style.typ": *
#front[Appendix B. Problems with solutions]

#heading(level: 2, numbering: none)[Seven problems tracing the argument]
The first seven problems follow the proof from Riemann's counting function to the contradiction. The subsequent study sets revisit particular parts of it in more depth.

#example[Problem 1][Recover $pi(10)$ from $J$ by Möbius inversion. Explain why the term involving a fourth root is zero.]
#proof[The prime powers at most ten give $J(10)=16/3$. Also $J(sqrt(10))=2$ and $J(10^(1/3))=1$. The fourth root is less than two, so all further counts vanish. Substitution gives $16/3-2/2-1/3=4$. At this scale higher powers affect the weighted count even though the original question counts only primes.]

#example[Problem 2][Let $g(u)=e^(beta u)cos(t u)$ for $u>=0$, with $t!=0$. Compute the normalized derivative of its Laplace transform. Fix $sigma>beta$ and choose a height on $Re s=sigma$ at which the pole $beta+i t$ is strictly closer to the differentiation point than its conjugate.]
#proof[The transform is half the sum of $(s-beta-i t)^(-1)$ and $(s-beta+i t)^(-1)$. Multiplying the $k$th derivative by $(-1)^k/(k!)$ replaces both exponents by $-k-1$. At $s=sigma+i t$ with $sigma>beta$, the distances are $sigma-beta$ and $sqrt((sigma-beta)^2+4t^2)$. The first term dominates exponentially in $k$. At height zero the two distances are equal. More generally, at height $v$ the second squared distance exceeds the first by $(v+t)^2-(v-t)^2=4v t$, which also determines which pole is nearer on either side of the real axis. This calculation accounts for the use of the vertically shifted moment.]

#example[Problem 3][A finite counting measure on a cyclic group of order $o$ differs in each of its normalized masses from the distribution $4/(3o+1),3/(3o+1),dots$ by at most $h$. Bound the error in each Fourier coefficient. If $h=x^(-1+epsilon)$, what does this cost when it multiplies $x log x$?]
#proof[Each character has modulus one, so the sum of $o$ mass errors has absolute value at most $o h$. The weighted error is at most $o x^epsilon log x$. For a fixed family $o$ is fixed and this is much smaller than $x^(1/2+epsilon)$. The accuracy of coset shares, even before moment estimates, is therefore enough for this use.]

#example[Problem 4][Let $P=p^2 ℤ e_1+ℤ e_2$ and $P'=p ℤ e_1+p ℤ e_2$ inside $ℤ^2$. Compare their indices, elementary divisors, and slopes with the Euclidean metric.]
#proof[Both have index $p^2$ and slope $-log p$ when the ambient slope is zero. The elementary-divisor exponents are $(0,2)$ and $(1,1)$. Their mean is the same while their largest and smallest exponents differ. Thus a determinant estimate can give the mean slope without controlling the spread used in the common-image inequality.]

#example[Problem 5][In the inert-prime formula of Chapter 13, take $p=3$, constant weight $w=1$ and $a_t=30$. Which powers of three contribute? Compute the total and explain what happens to the power nine.]
#proof[The positive-part test allows $3$, $9$, and $27$. The inert sign at the $i$th power is $(-1)^i$, so the multiplier $1-(-1)^i$ retains $3$ and $27$. Their contribution is
$ 2 log 3 ((30/3-1)+(30/27-1))=frac(164,9) log 3. $
The ramp at nine is positive, but its sign multiplier is zero. This is the arithmetic reason the local gain counts odd powers.]

#example[Problem 6][Let $ℓ$ be prime and $j>=1$. Suppose all local and global invariant groups in the duality identity of Chapter 15 have finite length and the global and local lengths are $a$ and $a_v$. Express the restriction-kernel length in terms of $V_ℓ$. What if all $a_v=a=0$?]
#proof[Additivity gives $len Sha_(ℓ)(E,j)=V_(ℓ)(E,j)+a-sum_v a_v$. If the invariants vanish, the two lengths agree. This explains why a uniform $H^2$ estimate is relevant to a global $H^1$ restriction problem. If invariants remain, dropping the local terms loses a cancellation.]

#example[Problem 7][Assume the arithmetic estimate on arbitrarily late $[Y,Y^(3/2)]$. Test a proposed zero with real part $0.503$. Give an admissible analytic exponent and an arithmetic choice leaving a strict margin.]
#proof[Take $theta=0.5015$. Any sufficiently small positive $epsilon<0.0015/9$ will do. For example $10^(-5)$ gives $1/2+9epsilon=0.50009$ and may be decreased further to meet an earlier family threshold. The selected windows force $F_(psi)(x)<=x^theta$ while the pole forbids that bound on every sufficiently late window. Only one such late arithmetic window is needed after the analytic threshold is known.]
