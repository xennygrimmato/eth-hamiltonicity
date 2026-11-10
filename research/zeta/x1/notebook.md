# x1 lab notebook — first-principles exploration (zeros of zeta on the line / simple)

Tags: [R] proved (proof given here), [N] computed, [C] conjecture / heuristic.
Convention: zeros rho = 1/2 + i*gamma, gamma complex if off the line; the zero set is symmetric
under gamma -> conj(gamma) (functional equation + reality). N = number of zeros in a window, with
multiplicity; r = real gammas (with mult.), r_d = distinct real gammas, s = simple real gammas,
p = number of conjugate PAIRS {gamma, conj gamma} off the line (distinct). L = log(T/2pi).

Caveat on context: I did not read the helpers' folders. I did see the board ANNOUNCE lines when
calling board.py (unavoidable): they mention a "rank-trace device" (Alpoge–Furman) and a proved
ceiling 0.68185 / 0.84093 for "trace + Montgomery energy at support [-1,1]". Idea 1 below was
derived before seeing that; it is evidently the same device in a cruder form. Everything after
Idea 1 is about what is NOT a two-trace bound.

---------------------------------------------------------------------------------------------
## Idea 1. Hermite–Sylvester signature form for zeta ("each off-line pair hides in a (1,1) plane")

Motivation. Explicit-formula *linear* statistics cannot tell a pair gamma ± i y (y << 1/log T) from
a double real zero. Classical algebra has an exact tool for "how many roots of a real polynomial are
real": Hermite's theorem — the signature of the Hankel form of power sums equals the number of
distinct real roots. Power sums of zeta zeros with exponential test vectors are prime sums.

Setup. w real-analytic weight (w(conj z) = conj w(z)), w>=0 on R, localised to [T,T+Delta].
v_gamma(u) = e^{i u gamma}, u in [0,U].  K(u,u') = k(u-u'),  k(v) = sum_gamma w(gamma) e^{i v gamma}.
  K = sum_gamma w(gamma) |v_gamma><v_{conj gamma}|.

[R] Lemma 1 (signature). K is Hermitian. A real zero of multiplicity m contributes m w v v^* (PSD,
rank 1). A pair contributes a|x><y| + conj(a)|y><x|: its quadratic form is 2Re(a <c,x>^- <c,y>),
a product of two independent linear forms, so signature (1,1). n_+ and n_- are subadditive. Hence for
ANY compression C (any subspace, any grid, any taper):
     n_+(C*KC) <= r_d + p,     n_-(C*KC) <= p.
Since N >= s + 2(r_d - s) + 2p, we get r_d + p <= (N+s)/2, i.e.
     s  >=  2 n_+(C*KC) - N.      (simple AND on the line)
(Zeros far outside the window have operator norm < eps: replace n_+ by #{eigenvalues > eps}, N by the
count in the window plus margin.)  Test: e1_toy.py, 400 random conjugate-symmetric configurations with
pairs/double zeros, 0 violations [N].

[R] Lemma 2 (the matrix is arithmetic). By the Guinand–Weil explicit formula (unconditional, exact)
  k(v) = (1/2pi) int w(t) e^{ivt}[Re psi(1/4+it/2) - log pi] dt + w(i/2)e^{-v/2}+w(-i/2)e^{v/2}
         - (1/2pi) sum_n Lambda(n) n^{-1/2} [ W(v - log n) + W(v + log n) ],   W(xi)=int w e^{i xi t}dt.
So k is a central spike of mass N_w plus spikes of width ~1/Delta at ±log n, weight Lambda(n)/sqrt n.
For e^U = T^theta < (edge width of w) different spikes do not overlap: the whole matrix K is explicitly
known, with no hypothesis.

[R-sketch] Two-trace consequence. n_+ >= (tr K)^2 / tr(K^2) (Cauchy–Schwarz on positive eigenvalues;
negative ones only help). tr K = M N_w; tr K^2 = sum over spikes = M N_w^2 (1+delta)(1+theta^2/3)/... ;
result:   n_+ >= N theta/(1+theta^2/3)  ->  3N/4 at theta -> 1,
     s >= (2 theta/(1+theta^2/3) - 1) N  ->  N/2 (Fejér taper); optimal taper 2/1.3275-1 = 0.5066.
This is cruder than the board's 0.6725 = 2 - J (they evidently extract (3-J)/2 for distinct zeros,
which I can only get under RH: m(3-m)/2 <= 1 for integers m>=1, i.e. it uses integrality).
Sanity check that the theta-normalisation is right: for zeta(s+a)zeta(s-a) (all zeros off the line,
2N zeros, p=N) the same computation gives n_+ >= 0.75 N <= p. Consistent.

Numerics: e2_zeta_toeplitz.py (see log below).

Structural remarks (mine, used later):
 (1a) [R] Under RH, n_+(K_theta) = min(theta N, D), D = number of distinct zeros. So NO bound extracted
      from K can exceed s >= 2D/N - 1; the framework is capped by what is known about DISTINCT zeros
      under RH. The enemy is not "off-line zeros" but "multiple zeros/small rank".
 (1b) [R] n_+(K) = n_+(S*KS) for invertible S (Sylvester). So sup over PD R of (tr KR)^2/tr(KRKR) is
      EXACTLY n_+ (take R = K^+). Two traces of K is only R = I. -> Idea 3.
 (1c) [R] Lemma 1 never used that the test vectors are exponentials. Any family F_1..F_d holomorphic
      near the strip gives K_jl = sum_rho w(rho) F_j(rho) conj(F_l(1-conj rho)), same inequalities. -> Idea 6.
 (1d) third trace tr K^3 is also "diagonal" for theta<1 (n1 n2 = n3 exactly); fourth trace is not
      (pattern + - + - gives n1 n3 ~ n2 n4 up to T^{2 theta}); but an odd polynomial cannot minorise
      1_{lambda>0} on R, so tr K^3 is useless without an a-priori bound on the spectrum. Dead.

(After landing Ideas 1 and 6 I read lines ~120-590 of the lead's paper draft for calibration. Their
Lemma (rank–trace): rank P >= 2 tr P + 4 tr Q - 4 n_+(Q) - ||P+Q||_HS^2, which recovers Montgomery's
integrality m^2 >= 3m-2 and gives 2-J instead of my 2/J-1. My Idea 1 is exactly their first-draft
state (1/2 and 3/4 by Cauchy–Schwarz). Everything below is measured against their framework.)

---------------------------------------------------------------------------------------------
## Idea 2. Go past support 1 with an UPPER-bound sieve (only upper bounds on tr K^2 are needed)

Motivation. n_+ >= (tr K)^2/tr K^2 needs only an upper bound for tr K^2, and Brun–Titchmarsh gives
upper bounds for prime pairs. If F(alpha) <= alpha + c(alpha-1) for alpha slightly >1 one would gain:
J(1+eps) = 4/3 - (2/3)eps + c eps^3/3.
What happens. For e^U = T^theta > Delta spikes overlap; the new terms are
   sum_{n} sum_{0<|h|<~ n/Delta} Lambda(n)Lambda(n+h)/n * FT[w^2](h/n),
and FT[w^2](xi) carries the phase e^{i T xi}: the window sits at height T, so sum_h FT[w^2](h/n) is a
Riemann sum for n*w(0)^2 = 0. The mean of Lambda cancels by oscillation; what is left is the VARIANCE of
primes in intervals of length n/T. A sieve bound on absolute values is of size (mean)^2 ~ (n/Delta)^2,
too large by the factor (n/Delta)/log — the number of shifts h. Windows cannot be made longer than T
(T^A just renames T).
Verdict: DEAD [R for the mechanism]. The wall at support 1 is "cancellation in sum_h Lambda(n)Lambda(n+h)
e(hT/2 pi n) over |h| <= n/T", i.e. variance of primes in short intervals; upper-bound sieves see only the mean.
The same computation kills the fourth moment (Idea 8).

---------------------------------------------------------------------------------------------
## Idea 3. Mollify the FORM, not the function: n_+(K) = n_+(S*KS)

Statement. For any PD R: n_+(K) >= (tr KR)^2 / tr(KRKR), with equality for R = K^+. Take
R = I + c*(prime Toeplitz of length T^eta)/L, i.e. R ~ first-order inverse of K.
Constraint. tr(KRKR) has 4-cycles (n1, m1, n2, m2) with n1 m1 ~ n2 m2 up to T^{theta+eta}: clean only if
theta + eta < 1.
Analytic (CUE/Gaussian-trace model, a = -c constant): relative gain eta^2 [c - c^2] <= eta^2/4 at theta=1,
against relative loss eta/2 from theta = 1 - eta.
Test e6_cue_Rmoll.py (N=60, 300 matrices) [N]:
   theta=1.0 eta=0:    0.7485
   theta=0.9 eta=0.1:  0.7101 (unmollified 0.7087)
   theta=0.8 eta=0.2:  0.6692 (0.6593)      theta=0.5 eta=0.5: 0.4943 (0.4615)
   [inadmissible: theta=1, eta=0.5: 0.7902]
Verdict: DEAD. Mollifier length is paid linearly in bandwidth and repays quadratically.

---------------------------------------------------------------------------------------------
## Idea 4. Use Lambda >= 0: Perron/Schur positivity of the prime form

Motivation. K = L*A - G with G "nonnegative". For nonnegative symmetric G, a positive vector p with
G p <= lambda p gives lambda_max(G) <= lambda — no cancellation needed.
[R] Proposition 4. Let G_X[m,n] = Lambda(n/m) (m/n)^{1/2} for m | n, symmetrised, m,n <= X. Then
lambda_max(G_X) <= log X. Proof: p_n = n^{-1/2}; (G p)_n = n^{-1/2}[ sum_{k<=X/n} Lambda(k)/k + sum_{k|n}
Lambda(k) ] <= n^{-1/2}[log(X/n) + log n], using sum_{k<=y} Lambda(k)/k <= log y (y>=1). Schur test. QED.
Numerics e8_schur.py [N]: lambda_max(G_X) - log X = -0.5325, -0.5500, -0.5571, -0.5611, -0.5628 for
X = 1e2, 1e3, 1e4, 1e5, 4e5 (tends to -gamma = -0.5772?); Schur bound = log X to 4 decimals.
Corollary [R up to the standard resolved-spike bookkeeping]. For every Dirichlet polynomial
A(s) = sum_{n<=X} a_n n^{-s} with X <= T^{1-eps} (window at height T, edge width > X):
   sum_rho w(rho) A(rho) conj(A(1 - conj rho)) >= (W(0)/2pi) (log(T/2pi) - log X) sum |a_n|^2/n  > 0,
unconditionally: off-line zeros can never make the Weil form negative on INTEGER-frequency polynomials
of length < T. (The phases n^{-iT} are a gauge on integer frequencies: Lambda(k)k^{-iT} = d_{mk} conj d_m.)
Why it does not help. That subspace has dimension X = T^theta << N = Delta L/2pi. To reach dimension ~N one
needs real frequencies x in [1,X]; the orbit of x under multiplication/division by integers is x*Q_+,
G then contains sum_{k<=x} Lambda(k)k^{-1/2} p(x/k) over ALL k (not only divisors), the gauge is no
longer available at height T, and in the only gauge where the kernel is nonnegative (window centred at
t=0) the Perron direction is the pole of zeta: one is left with Lambda - 1, which changes sign.
Verdict: DEAD for the proportion problem; Proposition 4 and its corollary are true and (to me) pretty.

---------------------------------------------------------------------------------------------
## Idea 5. Avoid truncation: Nevanlinna / Krein–Langer kernel at sigma > 1

-xi'/xi is Herglotz iff RH; the number of negative squares of N(z,w) = sum_gamma 1/((z-gamma)(conj w - conj gamma))
equals the number of off-line pairs (generalised Nevanlinna class). For Im z, Im w = eta > 1/2 every
entry is an absolutely convergent prime series — no cutoff at all.
But 1/(z-gamma) = -i int_0^inf e^{iu(z-gamma)} du: this is the form of Idea 1 with taper e^{-eta u} on
[0,inf). The rank is still seen only through traces, and the Hilbert–Schmidt norm has the same
overlapping-spike terms for n > T, damped by n^{-2 eta}: negligible for fixed eta (but then the Gram
matrix has numerical rank O(1/eta) per unit length, far below the density of zeros), not negligible for
eta ~ c/log T. A unimodular analytic twist f(s) = A(s)/conj A(1-conj s) is the same thing (geometric
tail of frequency shifts).
Verdict: DEAD. A taper is not information; "exact entries" does not mean "known second moment".

---------------------------------------------------------------------------------------------
## Idea 6. Enlarge the evaluation family (remark 1c): blocks zeta'(s)M(s) n^{-s}, zeta(s+i d)M(s+i d) n^{-s}

Motivation. Under RH the best simple-zero results (19/27) come from zeta'(rho)M(rho), not from pair
correlation. Lemma 1 holds for any holomorphic family, so such vectors can be put INTO the Hermitian
form: K_jl = sum_rho w(rho) F_j(rho) conj F_l(1 - conj rho); with a zeta' factor multiple zeros drop out.
Model (CUE; zeros z_a, P = char. poly, M_y = truncation of 1/P at degree y = thM*N, Dirichlet kernels
of d1 = th1*N and d2 = th2*N frequencies): Gram G = D_{d1} + c f f^* o D_{d2},
rho := (E tr G)^2/(N E tr G^2)  (so simple-on-line >= 2 rho - 1 at Cauchy–Schwarz level).
Results [N] (e3_cue.py, e4_cue_moll.py, e5_cue_shift.py, e7_cue_multi.py; N = 40-60):
   baseline th1=1:                                   0.748   (theory 3/4)
   f = P'(z)M(z)   (th1,th2,thM)=(1,.25,.25)/(1,.5,.25)/(1,.5,.5):   0.767 / 0.783 / 0.781
   f = P M at shifts ±0.5 spacing, (1,.5,.5):         0.800
   five shift pairs, (1,.5,.5):                       0.801 ;  (1,1,1): 0.837
   "ideal" f_a = (-1)^a (th1=th2=.5):                 0.856  — NOT attainable: a perfectly mollified
        zeta'(rho)M(rho) is a positive constant, not an alternating sign; e^{i theta(gamma)} = chi^{-1/2}
        is the frequency shift L/2, i.e. plain bandwidth.
   unmollified Z'(gamma) block:                       0.752-0.757 (fourth moment of zeta' too wild)
Compatibility with the sharp lemma: it needs tr P_1 <= s_1, i.e. every on-line zero carrying trace <= its
multiplicity ("flat charge"). Non-unimodular twists break this; unimodular analytic twists are bandwidth
(Idea 5). So twisted blocks only enter at Cauchy–Schwarz level, where one needs rho > 0.841 to beat the
ceiling; realistic lengths saturate near 0.80.
Arithmetic needed: sum_{rho,rho'} f(rho) conj f(rho') |D(gamma-gamma')|^2-type sums (pair correlation
weighted by mollified zeta'), unconditional ranges unknown to me.
Verdict: a real effect in the model (+0.03 to +0.05 in rho) but NOT enough at realistic lengths, and it
does not fit the integrality device. Parked. It would become interesting only with a weighted version of
the rank–trace lemma (charge nu_rho^2 <= 1 pointwise) — none found.

---------------------------------------------------------------------------------------------
## Idea 7. Riemann–Siegel / Hermite–Biehler counting (rediscovery of Siegel–Levinson; obstruction named)

Z(t) = 2 Re[e^{i theta(t)} D_N(1/2+it)] + O(t^{-1/4}), D_N = sum_{n<=sqrt(t/2pi)} n^{-s}. Sign changes of
Re(e^{i theta} D) >= (1/pi)(Delta theta + Delta arg D) = N(T) - 2 #{zeros of D_N right of the line} + ...
So "proportion on the line >= 1 - (zeros of the length-sqrt T partial sum with beta > 1/2)/(N/2)".
Counting those zeros by Littlewood's lemma costs (i) Jensen: mean of log|.| <= log of mean square,
(ii) counting zeros right of 1/2 by zeros right of 1/2 - a/L with a linear weight, (iii) the mollifier
length. That is Levinson's ceiling in my terms. The signature method uses no functional equation beyond
conjugate symmetry but needs length ~T; Levinson uses the functional equation and length <= T^{4/7}.
In the finite model (self-inversive polynomial of degree N) power sums p_1..p_{d-1} with d > N/2 determine
the polynomial, yet PSD of the d x d Toeplitz matrix forces only 2d-N zeros onto the circle (example:
N=3, zeros r, 1/r, -1 with r+1/r<4, d=2: K_2 is PD, one pair off the circle). So no "rigidity" certificate
of Toeplitz-PSD type exists between N/2 and N.
Verdict: no new mechanism; recorded as the map of the two known mechanisms.

---------------------------------------------------------------------------------------------
## Idea 8. What exactly is the cheapest new input? The fourth trace, one-sided.   <-- best lead

Normalise at theta = 1: G = 1 + P on d = N dimensions, P = prime Toeplitz/L = P_+ + P_+^*.
(8a) [R-sketch] tr P = 0, tr P^2 = N/3, tr P^3 = o(N): all three are DIAGONAL, hence unconditional, for
     X < T^{1-eps}. (3-cycle on [0,U]: n1 n2 = n3(1+O(1/Delta)) with n3 <= X < Delta forces equality; then
     Lambda(n1)Lambda(n2)Lambda(n1 n2) lives on prime powers: O(1) against L^3.) So m1, m2, m3 = 1, 4/3, 2.
     The draft's remark (e) allows only X^k <= T^{2-eps}; for the Toeplitz compression k = 3 is free.
(8b) [R] But m3 is useless: tr G(G-1)(G-2) = tr(P^3 - P) = 0, and the extremal configuration of the
     rank–trace lemma has spectrum {0,1,2} — the roots of that cubic. The third moment is exactly neutral.
(8c) [R-sketch + N] tr G^4 = clean terms + 2 tr((P_+ P_+^*)^2), and
        tr((P_+P_+^*)^2) = tr(P_+^2 P_+^{*2}) + (1/2)||[P_+, P_+^*]||_HS^2.
     Only the pattern (+,-,+,-) is not diagonal. Diagonal (Gaussian-trace) value: tr P^4/N = 2*(7/60) + 1/30
     = 4/15, i.e.  m4(diag) = 1 + 6/3 + 4/15 = 49/15 = 3.2667.  The sine-process value is 13/4, so the
     conjectural off-diagonal contribution is exactly -1/60.  The extremal {0,1,2} measure has 10/3.
     (e9_m4.py: CUE N=40: m = 1.000, 1.332, 1.995, 3.2345; independent Gaussian traces: 3.2389.)
(8d) [N] Chebyshev–Markov LP (e10_lp.py): minimise mu((0,inf)) subject to m1=1, m2=4/3, m3=2, m4 <= u;
     then simple-on-line >= 2 n_+ - 1:
        u = 13/4 : n_+ >= 0.8611 -> 0.7222 (=13/18, the draft's HL*(4) value)
        u = 49/15: 0.8542 -> 0.7083
        u = 3.30 : 0.8426 -> 0.6852
        u = 3.32 : 0.8368 -> 0.6736
        u = 10/3 : 0.8333 -> 0.6667   (exactly the two-moment sharp value)
     Only an UPPER bound on tr G^4 is needed (the quartic minorant has negative leading coefficient).
TARGET [C]. Prove unconditionally
        tr P^4 <= (0.305) N      (diagonal 0.2667, truth 0.25),
i.e. the off-diagonal part of 2 tr((P_+P_+^*)^2) is <= +0.038 N. It is conjecturally NEGATIVE (-N/60):
no asymptotic, no sign, only "not more than 2.3 times its size in the wrong direction". This beats the
ceiling 0.68185; <= +0.055 N already beats 0.6725.
Why I could not do it. The off-diagonal is sum over n1 n3 = n2 n4 + h, 0<|h|<= n1n3/T, of
Lambda^4-weights with phase e(hT/2 pi m): again the VARIANCE of (Lambda*Lambda) in intervals of length
m/T, m up to T^2. Montgomery–Vaughan's Hilbert inequality gives (T + 3 pi m) per coefficient: fine for
m <= T/100, exponentially bad beyond. Sieve upper bounds bound the mean square by (mean)^2, too big by
(m/T)/log. Any taper that removes cycles with a1 + a3 > 1 has bandwidth <= 1/2 (rank <= N/2, nothing).
Zero-side bounds (Fujii/Selberg moments of S(t+h)-S(t)) have non-sharp constants and do not control
off-line pairs. So: the cheapest input is a one-sided 14%-accurate bound for a fourth moment of
sum_{n<=T^{1-eps}} Lambda(n) n^{-1/2-it} in the band-limited sense; it is Hardy–Littlewood-type but far
weaker than an asymptotic.

---------------------------------------------------------------------------------------------
## Idea 9. Triple correlation under RH as a source of integrality (heuristic check)

If sum_gamma m_gamma^2 <= J3 N with J3 < 2 the extremal configuration (2/3 simple + 1/6 double points:
sum m^2 = 2N) would be excluded even conditionally. Rudnick–Sarnak support sum|xi_i| < 2 allows a
product of three Fejér kernels of bandwidth a < 1/3; for the sine process this gives
J3 ~ 1 + 3*(2 - ~0.9) + (<= 4.5) ~ 6 >> 2. [C, back-of-envelope]
Verdict: DEAD — the admissible bandwidth 1/3 is too coarse to see multiplicities.

---------------------------------------------------------------------------------------------
## The obstruction, in my own terms

1. An off-line pair is invisible to any linear statistic of bandwidth << distance^{-1}; it is visible
   only as ONE negative square of a Hermitian form (Lemma 1). So the count of on-line simple zeros is
   2 n_+ - N for an explicit arithmetic matrix, and under RH n_+ = min(theta N, #distinct zeros): the
   whole difficulty is a lower bound for the positive index of an explicit Toeplitz matrix whose symbol is
   the truncated -zeta'/zeta.
2. Everything about that matrix that is "diagonal" is known: tr, tr^2, tr^3 at theta<1; all traces at
   theta<1/2 (where the rank is <= N/2 and nothing can be concluded). Diagonal information stops exactly
   where the extremal spectrum {0,1,2} is still consistent (m3 is neutral).
3. The first non-diagonal quantity is the self-commutator ||[P_+,P_+^*]||_HS^2 (boundary/Hankel part of
   the prime Toeplitz operator). Its off-diagonal part is the variance of primes (semiprimes) in intervals
   x/T. Upper-bound sieves and the large sieve bound means and worst cases, not variances; that is the
   common ceiling of support-1 pair correlation and, through mollifier length, of Levinson.

---------------------------------------------------------------------------------------------
## Idea 10. Prime-free congruent form (exact, but no gain)

On L^2[0,U] causal convolutions compress homomorphically (L^2[U,inf) is invariant). With
Z_+ = sum_n n^{-1/2} S_n (S_n = shift by log n) and P_+ = sum Lambda(n) n^{-1/2} S_n one has
P_+ Z_+ = D_+ := sum (log n) n^{-1/2} S_n exactly, and Z_+ is invertible (inverse: mu). Hence
   Z_+^* (L - P_+ - P_+^*) Z_+ = sum_{m,n<=X} (mn)^{-1/2} log(T/2 pi m n) S_m^* S_n =: G~,
and n_+(G) = n_+(G~) by Sylvester [R, in the exact-shift idealisation]. The primes have disappeared;
with a partial mollifier M_y one gets a family G_y = W^* G W, W = [zeta M_y], whose coefficients are
truncated divisor sums (Goldston–Yildirim's Lambda_y), all congruent to G.
Hope: off-diagonal correlations of truncated divisor sums ARE computable (GY, Duke–Friedlander–Iwaniec),
so traces of G_y might be available where traces of G are not.
What happens: each factor G_y carries two long variables instead of one, so tr G_y^2 is a (mollified)
fourth-moment problem and tr G_y^4 an eighth-moment problem (d_4-correlations), while the spectrum of G_y
is more spread than that of G (it is G seen through |zeta M_y|^2). It is Idea 3 with R = W W^*.
Verdict: DEAD as a way to the fourth trace; kept because the identity is exact and explains why "Weil
form at bandwidth theta" and "mollified 2k-th moments" are the same object in two gauges.

---------------------------------------------------------------------------------------------
## Numerics on actual zeros (e2_zeta_toeplitz.py; zeros 700<gamma<4000 from zeros_rs.py, RS + bisection,
## checked against mpmath.zetazero(1000), (2000) to 5e-7)

Window [1500,3000], Gaussian edges H=15, N_w = sum w(gamma) = 1399.36, 1566 zeros incl. margins.
theta=0.6 (U=3.53, primes and prime powers <= 60 only), grid M=1123:
   max |k_zeros(v) - k_primes(v)| = 3.9e-4 (k(0) = 1399.36)   -> Lemma 2 verified [N]
   inertia of the PRIME-side matrix: n_+ = 924, n_- = 0 (threshold 1e-6 lambda_max)
   -> 2 n_+ - N = 282 simple zeros on the line certified from primes <= 60 alone (18%; 2 theta - 1 = 20%)
   rank-trace (tr)^2/HS = 0.553 N_w (asymptotic theta/(1+theta^2/3) = 0.536)
theta=1.0, 1.15: see e2.log.
theta=1.0 (U=5.88, prime powers <= 612), M=1872:
   max |k_zeros - k_primes| = 4.6e-4;  zero-side inertia n_+ = 1508, n_- = 0  -> 2n_+ - N = 1450 of 1566
   (92.6%; the remainder are margin zeros of weight < threshold). The prime-side eigen-decomposition
   timed out on a loaded machine (entries agree to 3e-7 relative, so the inertia above the threshold
   is the same up to the usual perturbation caveat — NOT separately computed).
   rank-trace 0.781 N_w (asymptotic 0.75); normalised m2, m3, m4 = 1.280, 1.838, 2.845 against the
   asymptotic 4/3, 2, 13/4 — at L = 5.9 lower-order terms are large; these numbers only show the trend.
theta=1.15: not completed (machine load).

---------------------------------------------------------------------------------------------
## Summary table

| # | idea | verdict |
|---|------|---------|
| 1 | Hermite–Sylvester signature form, explicit prime Toeplitz matrix | [R]; rediscovery of the rank–trace framework at CS level (1/2, 3/4) |
| 2 | sieve upper bounds past support 1 | dead: variance vs mean, factor (n/T)/log |
| 3 | mollify the form (congruence R) | dead: cost eta/2, gain eta^2/4 [N] |
| 4 | Perron/Schur with Lambda>=0 | Prop. 4 [R]: lambda_max(G_X) <= log X; useless for proportions (dimension, pole) |
| 5 | Nevanlinna kernel at sigma>1 / unimodular twists | dead: taper is not information |
| 6 | enlarged evaluation families (zeta'M, shifted zeta M) | [N] model gain 0.75 -> 0.80; breaks flat charge; parked |
| 7 | Riemann–Siegel / Hermite–Biehler | rediscovery of Siegel–Levinson; no rigidity certificate between N/2 and N |
| 8 | one-sided fourth trace | [N]+[C]: tr P^4 <= 0.305 N would beat 0.68185; diag 4/15, offdiag conj. -1/60; m3 neutral |
| 9 | triple correlation for integrality | dead: bandwidth 1/3 too coarse |
| 10| prime-free congruent form | exact identity, no gain |
