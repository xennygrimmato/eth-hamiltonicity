# x2 lab notebook — first-principles / model-driven exploration

Tags: [R] proved here, [N] computed (script named), [C] conjecture/heuristic.

## 0. Framing in my own terms (before any idea)

Normalise zeros at height T to unit mean spacing: x = gamma*log(T)/(2pi). Write the zero
configuration as a measure mu = sum_j m_j delta_{x_j} (distinct points x_j, multiplicities m_j).
Its reduced second-moment ("pair") measure per unit length is

    kappa*delta_0 + R2(x) dx,   kappa = mean of sum m_j^2 per unit length,   R2 >= 0 off-diagonal pair density,

and the structure function S(alpha) = kappa + FT(R2 - 1)(alpha) (distributional, mean term removed).
Var(sum_j m_j phi(x_j)) = int |phi^|^2 S. Montgomery's theorem (RH) / the explicit formula +
mean-value theorem for Dirichlet polynomials of length T^c gives S(alpha) = |alpha| for |alpha| <= 1.
GUE: S = min(|alpha|,1), kappa = 1.

Counting: if every m_j is in {1,2}, (simple mass fraction) = 2 - kappa; in general
#simple >= sum_j (2 m_j - m_j^2) = (2 - kappa) N, since 2m - m^2 <= 1_{m=1} on Z_{>=1}.  [R] (trivial)

So every "pair-correlation" method is an upper bound for kappa given S on [-c,c] and positivity.
Montgomery (Fejer kernel): kappa <= 4/3 -> 2/3.

Premise check (honest): what I knew before this session: unconditional on-line ~ 41.7% (Pratt et al.),
2/3 simple is Montgomery under RH, 19/27 Bui–Heath-Brown under RH. The board says (Aug 2026)
Alpoge–Furman made 0.6725 unconditional by a "rank-trace"/Sylvester device; I take that as given
and work on the shared obstruction: information = pair statistics at bandwidth 1.

## Idea 1 — Is the bandwidth-1 ceiling a relaxation artefact (DNN vs completely-positive/realizable)?

**Idea.** Every pair-correlation certificate (Montgomery, Cheer–Goldston, CGdL, the rank-trace window
R(psi)) is a dual solution of a *doubly-nonnegative* (DNN) relaxation: the only constraints used on the
unknown pair measure are R2 >= 0 (x-space) and S >= 0 (Fourier space). But the zeros form an actual
configuration with integer multiplicities, so the honest primal is over *realizable* pair measures
(convex hull of autocorrelations of integer measures = a completely-positive-type cone). If the
realizable optimum were far below the DNN optimum, copositive certificates (pointwise inequalities valid
for every configuration, e.g. kernels r with negative parts that no configuration can exploit) would
beat the ceiling with *no new arithmetic input*.

**Exact statements tested.**
(P_DNN, continuum) maximise kappa s.t. S(alpha)=|alpha| on [0,1], S>=0, R2 = 1 + FT(S-kappa) >= 0.
(P_DNN(N)) finite CUE model: N points (with mult.) on R/Z, nu = pair measure on Z_M, nu^(0)=N^2,
  nu^(k)=k (1<=k<=N), nu^(k)>=0, nu>=0; maximise kappa = nu({0})/N.  (M -> infinity.)
(P_real(N)) same data E|p_k|^2 = k, 1<=k<=N, p_k = sum_j m_j e(k theta_j), but over probability
  mixtures of actual configurations.  Column generation; pricing = multistart L-BFGS over positions for
  every multiplicity pattern (parts <= 3).  Returns a *feasible ensemble*, i.e. a lower bound for the
  true realizable optimum (pricing is local).

**Results [N].**  scripts dnn_lp.py, dnn_run.py, circle_dnn.py, circle_real2.py; logs real_*.log
- Continuum DNN, truncating S = kappa beyond A: A=4: 1.29675, A=8: 1.30961 (increasing in A; consistent
  with the board's quoted bandwidth-1 ceiling 2-1.31815 = 0.68185 as A -> inf).
- The DNN extremal (A=8) is *crystal-like*: R2 ~ 0 on |x|<0.9 (hard core), R2 concentrated near
  x = 1,2,3,4 (peaks of height ~5), S = 0 on (1, 3.2), then Bragg-like spikes.  Complementary slackness:
  the optimal certificate r >= 0 vanishes near the nonzero integers (Fejer (sin pi x/pi x)^2 does exactly).
  Exact lattice support is impossible (it would make S 1-periodic, contradicting S=|alpha| on (0,1)),
  so the extremal is a *jittered lattice with multiplicities 0/1/2*.
- Finite model, DNN(N) (M=128N): N=6: 1.22387, N=8: 1.24515, N=10: 1.25876; N=60 (M=16N): 1.308.
- Finite model, REALIZABLE N=6: kappa = 1.221732 (converged, art=0).  DNN(6) = 1.22387.
  => an actual ensemble of 6-point configurations matches CUE's E|Tr U^k|^2 for all k <= N and has
  kappa within 0.2% of the DNN optimum.
- Extremal ensemble at N=6 (ens_N6_K6_simple.pkl; 7 configurations, weights .40,.25,.14,.08,.07,.05,.01):
  every configuration is a *compressed crystal* (gaps 0.89-0.93 in mean-spacing units) with ONE defect:
  either a long gap (all simple) or a double point next to a long gap ("dipole defect": charge 2 + vacancy).
  Verified: E|p_k|^2 = 1,2,3,4,5,6 exactly for k<=6; E|p_7|^2 = 30.6 (CUE value 6): the Bragg peak sits at
  the first frequency above the bandwidth.  [N]
- Same picture in the continuum DNN optimum (A=8): S has a spike of mass 0.83 in (1, 1.1], S=0 on (1.1,1.5).

**Prior art (checked after landing).** The realizability half of this is in Alpöge–Furman §7.2: their
ceiling 0.68185 is proved by an explicit 256-periodic law of marked configurations (LawN256.lean), i.e. a
realizable ensemble, and h3 reproduces it by column generation.  What is mine: DNN ~ realizable (so the cheapest
relaxation is already tight), the crystal/dipole description, the Bragg-mass = edge-term identification
(my continuum spike 0.83 vs their |D(1)| = 0.824), and the N -> inf extrapolation of the DNN value:
N = 40, 80, 160 (M = 12N): 0.6979, 0.6901, 0.6861 -> 0.6820 (linear in 1/N), matching 0.68185.  [N]

**What extra pair information would break it** (finite model N=40, M=640, script circle_dnn_lb.py / circle_dnn_ub.py) [N]:
| extra input on S beyond alpha=1                | simple >=  |
|-----------------------------------------------|-----------|
| none                                          | 0.6973 |
| lower bound S >= 3/2 - alpha on [1,3/2] (GGOS-type) | 0.7015 |
| lower bound S >= 1 on (1,1.25]                | 0.7077 |
| UPPER bound S <= 2 on (1,1.05]                | 0.7255 |
| upper bound S <= 1 on (1,1.10]                | 0.7523 |
| upper bound S <= 2 on (1,1.25]                | 0.7897 |
| upper bound S <= 1 on (1,1.25] (= knowing GUE there) | 0.8138 |
| S = 1 known on (1,1.5] / (1,2]                | 0.877 / 0.938 |
(DNN only; N=40 values sit ~0.015 above the N=inf values, the ordering is what matters.)

**Verdict (Idea 1).** [N] in the finite model, [C] for the continuum: the bandwidth-1 ceiling is NOT a
relaxation artefact.  Integrality, rank, copositivity — anything that only uses the pair statistic at
bandwidth <= 1 — cannot go materially beyond the DNN value, because an actual ensemble of
configurations (compressed crystals with dipole defects) attains it.  The obstruction, in my words:
*bandwidth-1 data cannot see a Bragg peak at alpha = 1+0; a compressed crystal hides each double zero
next to a vacancy.*  The single most valuable extra pair input is an **upper bound** on Montgomery's
F(alpha) for alpha slightly above 1 (anti-crystallinity), even a weak one (F <= 2); lower bounds of
GGOS type are nearly worthless for this purpose.
Why upper bounds on F(1+eps) are hard (my derivation, [C]): F(alpha), alpha>1, is the mean square of a
prime Dirichlet polynomial of length T^alpha > T; the off-diagonal is a positive combination of prime-pair
sums sum Lambda(n)Lambda(n+h), h <= T^{alpha-1}, whose main term ~ x is cancelled by the polar term,
leaving size T log T.  A sieve upper bound (constant 4, or 3.4) multiplies the main term, so it misses by a
factor x/(T log T): one needs prime-pair asymptotics with relative error o(1/log x).
- More sizes (realizable value = min simple fraction found; DNN = lower bound for it):
  | N | realizable (feasible ensemble) | DNN(N) | script/log |
  |---|---|---|---|
  | 6 | 0.77827 (converged) | 0.77613 | circle_real2.py, real_N6_simple.log |
  | 8 | 0.75706 (converged)  | 0.75485 | circle_real3.py, r3_N8_base.log |
  | 16 | 0.72489 (heuristic pricing, 17 configs) | 0.71959 | bigN_cg.py, bigN_16.log |
  Gap realizable - DNN stays at 0.002-0.005 while both decrease toward ~0.682.  [N]

## Idea 4 — Moment information of the characteristic polynomial (Hardy–Littlewood / Ingham analogues)

**Idea.** Unconditional mean values of zeta itself (int |zeta|^2 ~ T log T, int |zeta|^4 ~ T log^4 T/2pi^2)
are not pair-correlation data.  Do they exclude the crystal extremals?  Finite model: add
E_phi E|Lambda(e(phi))|^2 = N+1 and E|Lambda|^4 = (N+1)(N+2)^2(N+3)/12 (CUE values, checked by Monte Carlo).
**Result [N]** (N=6, circle_real3.py --mom 12, r3_N6_mom12.log): simple fraction 0.7788 vs 0.7783 without.
**Verdict: dead, and I can say exactly why.**  The crystal extremals have *tiny* |Lambda| (regular N-gon:
int|Lambda|^2 = 2 << N+1), but |Lambda|^{2k} is heavy-tailed (clustered configurations reach 4^{kN}), so the
LP restores the moment with an exponentially small weight on a few clustered configurations at no cost
in the pair constraints.  Moments can only enter through a *concave* functional (Jensen/Littlewood:
int log|V M| <= (1/2) log int |V M|^2), which is exactly what Levinson's method does — i.e. moment information
is useful only as Levinson-type information, with its own (mollifier-length) ceiling.

## Idea 5 — The finite shadow of Weil positivity (curves over F_q) and why it does not transfer

**Statement [R].** Let z_1..z_n be complex numbers listed with multiplicity, the multiset closed under
z -> 1/conj(z) (functional equation), with D distinct values; c_k = sum_i z_i^k, T_K = (c_{a-b})_{0<=a,b<K}.
If K >= D then rank T_K = D, n_-(T_K) = number of distinct off-circle pairs {w, 1/conj w}, and
n_+(T_K) - n_-(T_K) = number of distinct zeros on |z|=1.  In particular RH <=> T_K PSD.
*Proof.* Group equal values: T_K = sum_w m_w u(w) u(1/conj w)^*, u(w) = (w^a)_{a<K}.  With V the K x D
Vandermonde matrix of the distinct values (full column rank since K >= D), T_K = V B V^*, B block-diagonal
with entries m_w for on-circle w and blocks [[0,m],[m,0]] (signature (1,1)) for each off-circle pair.
Sylvester's law of inertia for the full-rank congruence gives the claims.  QED
For a curve C/F_p of genus g, c_k = (p^k + 1 - #C(F_{p^k}))/p^{k/2} for k <= 2g: the shadow is a
(2g+1)x(2g+1) Toeplitz matrix built from 2g point counts.
**Check [N]** (ff_toeplitz.py): y^2=x^5-x/F_5 (supersingular, z=+1,-1 each double): eig(T) = (0,0,0,8,12),
rank 2 = #distinct; y^2=x^7-x/F_7 (g=3, z=+-i each triple): rank 2; three ordinary curves: rank 4/4/6 = 2g,
T PSD (RH).  The inertia counts *distinct* zeros exactly — multiplicities are visible as rank deficiency.
**Why it does not transfer (my verdict).** For zeta the analogue of T is the compressed Weil form on Dirichlet
polynomials of length X (Gram matrix of (n^{-rho})): the "point counts" are prime sums of length <= X^2, and the
rank is <= X << N(T) = #zeros.  So the exact inertia count is never available; one only has averaged traces
(tr P from the explicit formula, tr P^2 from the mean-value theorem at X <= T), i.e. exactly the pair statistic of
Idea 1, whose ceiling is information-theoretic.  The function-field proof (Hodge index) gives positivity of the
*whole* form; its "finite checkable shadow" for zeta is positivity for test functions of support <= L, which
constrains zeros only at heights with log(height) << L (resolution), hence says nothing about proportions.

### Data check (actual zeros) [N]
9261 zeros in [1e5, 1.06e5] by my vectorised Riemann–Siegel finder (rs_zeros.py; 6 of 9267 missed, accuracy
~1e-3 at t~100 and better higher up), unfolded x = theta(t)/pi.  Tapered periodogram averaged over bins of width
0.05 (data_S.py): S(alpha) = 0.111, 0.266, 0.301, 0.380, 0.512, 0.609, 0.710, 0.839, 0.894 at alpha = 0.12..0.93
(GUE min(alpha,1)); S = 1.042, 0.962, 1.034, 0.985, 1.035 at alpha = 1.02..1.43; mean S on (1,1.15] = 1.07,
whereas the extremal crystal needs ~8 there.  43.6% of gaps are < 0.9 mean spacing (extremal: 0% distinct gaps
below 0.9).  So zeta is as far from the extremal as it can be in exactly the region that bandwidth-1 data cannot see.

## Idea 2 — Which single extra piece of information breaks the ceiling (bandwidth as a resource)

(The table under Idea 1 is the main result; here the bandwidth curve and the averaged version.)
**Exact statement tested.** DNN finite model, data S = |alpha| on (0,1], plus one of: S known (= GUE value 1)
on (1,c]; S <= U pointwise on (1,1+d]; S >= L on (1,1+d]; averaged (1/d) int_1^{1+d} S <= B.
**Results [N]** (circle_dnn.py, circle_dnn_ub.py, circle_dnn_lb.py, circle_dnn_avg.py; N=20/40, M=16N):
- known on (1,c]:  c = 1, 1.25, 1.5, 2, 3, 4  ->  0.697, 0.814, 0.877, 0.938, 0.978, 0.990 (N=40);
  the flat-window value 1 - 1/(3c^2) (board, h1) is 0.667, 0.787, 0.852, 0.917, 0.963: positivity (DNN) adds
  0.02-0.03 at every c.
- averaged upper bound, mass m = B*d on (1,1+d] (N=40):  d=0.05: B=1 -> 0.7265, B=10 -> 0.7084, B=20 -> no gain;
  d=0.1: B=1 -> 0.7490, B=5 -> 0.7188, B=10 -> no gain; d=0.25: B=1 -> 0.788, B=2 -> 0.744.  So the gain
  appears exactly when the allowed mass just above 1 drops below the extremal's Bragg mass (~0.5-0.8 at N=40).
- Consistency with A–F's ceiling law: their edge term |D(1)| = 0.824 (paper §7.2, LawN256.lean) is the same
  object as my continuum Bragg mass 0.83 in (1,1.1].
**Verdict.** [N]+[C].  The trivial positivity bound gives int F(a) Delta_d(a-1) da <= 1 + d^2/3 (the "1" is the
density^2 term), i.e. it allows mass ~1 just above alpha = 1; beating the ceiling needs a bound that is better
than trivial by a factor ~2 there, while the truth (GUE) is mass d.  Arithmetic meaning (my derivation, [C]):
F on (1,1+d] = mean square of prime polynomials of length T^{1+d} = prime-pair correlations at shifts
h <= T^d at the scale of their fluctuations; sieve upper bounds lose the factor x/(T log T); MV gives
F(alpha) << T^{alpha-1}, useful only for alpha - 1 << 1/log T, while the extremal can park its Bragg peak at any
fixed 1+d.  This is "the" obstruction in my language: **ζ in the t-aspect is a family whose size equals its
conductor, so the duality (large sieve / MV) inequality saturates exactly at bandwidth 1**; Dirichlet families
have size Q^2 vs conductor Q and get bandwidth up to 2 (consistent with h5's family results).

## Idea 3 — Rudnick–Sarnak-range 3- and 4-point data
**Statement tested.** Finite model with pair rows plus  tri: E Re p_a p_b conj p_{a+b} = 0 (a+b <= N);
quad: E|p_a|^2|p_b|^2 = ab(1+[a=b]) (a+b <= N)  (Diaconis–Shahshahani values; the model form of RS96).
**Results [N]** (circle_real3.py; logs r3_N6_*.log, r3_N8_tri.log), min simple fraction found:
| N | pair | +quad | +tri | +tri+quad |
|---|---|---|---|---|
| 6 | 0.7783 | 0.7788 | 0.7989 (not fully converged, red 2e-2) | 0.8126 (running) |
| 8 | 0.7571 | — | running | — |
Independent confirmation of h1's finding (h1/ceiling_class.md §4, their rows l <= N-1: N=8 0.686 -> 0.709,
N=12 0.684 -> 0.706): **3-point data raise the model ceiling by ~0.02; 4-point data add almost nothing.**
**A correction to my own intuition.** I first expected the 3-point gain to vanish as N -> infinity by a CLT
argument (many independent defects make window sums Gaussian).  That is wrong: the RS constraint is on the
*extensive* bispectrum (third cumulant per unit length), B(alpha,beta) = 0 on the triangle alpha,beta>0,
alpha+beta<1, not on the normalised skewness; a crystal with dipole defects has an O(1) bispectrum per unit
length (self-term sum m_j^3 = 8 per double), so the gain can persist.  The 4-point (trispectrum) rows are also
extensive, but empirically do not bind.
**Verdict.** The only "free" correlation data that move the ceiling are 3-point RS data (+0.02 in the model);
that is h1's line, so I stop here.  A cheap analytic handle I worked out: a 3-point Montgomery bound
kappa_3 = E sum m^3 per unit <= [rho^(0,0) + int over the 3 lines rho^ |xi|]/int rho^ with rho >= 0, rho^ supported
in the hexagon; with rho^ = autocorrelation of the indicator of hexagon/2 it gives kappa_3 <= 8/3, but one needs
< 1 + 3*0.318 = 1.95 to beat the pair ceiling by this route alone — so the 3-point gain must come from the
*interaction* of pair and triple rows (as the LP shows), not from a stand-alone triple bound.  [C]

## Idea 6 (short) — What do proportion methods "see" that distinguishes zeta from Davenport–Heilbronn?
**Reasoning [C].** For f = sum c_j L(s,chi_j) (same functional equation), near height T one L_j dominates by a
factor exp(c sqrt(loglog T)) on most of the line (Selberg CLT for log|L_j|), so the zeros of f are, locally and
for most t, perturbations of the zeros of the dominant L_j: same local (GUE) statistics, 100% on the line
(Bombieri–Hejhal, conditionally), and only ≍ T (= o(N)) off-line zeros (known to exist).  Hence DH-type
functions are *not* counterexamples to any proportion statement < 1; they only show that no purely statistical
(proportion-type) method can reach RH itself.  What the methods need from the Euler product is exactly the
explicit formula with prime coefficients Lambda(n), used through mean values of length <= T; DH has no such
formula for log f, which is why Montgomery/A–F do not apply to it — not because its statistics differ.
**Verdict:** irrelevant to the 2/3 barrier; dropped.
A related toy that *is* instructive: zeta(s)^2 (degree 2, all zeros double).  In its own normalisation its
known bandwidth is 1/2 and S = 2 min(2|alpha|,1) = 4|alpha| on [0,1/2], versus |alpha| for a degree-2 L-function
with simple zeros: multiplicity is visible to bandwidth-limited data *only through the slope at alpha -> 0*,
i.e. through the global density/variance balance — which is why the crystal can hide doubles by pairing each with
a vacancy (dipole), restoring the slope.

## Idea 7 — The crystal's other weak spot: it has no close *distinct* pairs (hard core)
**Observation.** The pair-extremal has R2 ~ 0 on |x| < 0.9 (all its small gaps are doubles = gap 0).  Actual zeros:
43.6% of gaps < 0.9 (data above).  Known small-gap theorems count gaps with multiplicity, so a double zero
is a "gap 0" and they cannot exclude the crystal.
**Exact statement tested [N]** (circle_dnn_gap.py, DNN model N=40, M=640): add the row
(1/N) E #{ordered pairs of DISTINCT points with 0 < |x_j - x_k| < g} >= c.
| g | c=0 | 0.05 | 0.10 | 0.20 | GUE value |
|---|---|---|---|---|---|
| 0.5 | 0.6973 | 0.7255 | 0.7542 | 0.8121 | c=0.226: 0.8275 |
| 0.9 | 0.6973 | 0.6987 | 0.7001 | 0.7030 | c=0.898: 0.7374 |
So a *distinct-small-gap* theorem with a tiny constant (5% of zeros have a distinct partner within half a mean
spacing) would beat the ceiling by ~0.03 in the model.  Close pairs at distance < 0.5 are what the crystal cannot
afford (pairs at 0.5-0.9 matter much less).
**Verdict [C].** This is a clean target statement, but I see no unconditional or RH route to it that does not
already contain multiplicity information: two sign changes of Hardy's Z within 0.5 mean spacings would do it,
and Selberg-type methods detect sign changes only with tiny constants (the relevant mollified shifted moment
int Z(t)Z(t+h)|M|^2 differs from int Z^2|M|^2 only at order h^2).  Recorded as a "would suffice" statement.

## Summary (x2) — best three ideas
1. **The bandwidth-1 ceiling is a compressed crystal with dipole defects** [N].  Pair data S = |alpha| on [0,1]
   (+ any positivity/integrality/rank/copositive reasoning) cannot exclude an ensemble of near-crystals of spacing
   ~0.9 in which each double zero sits next to a vacancy; DNN relaxation = realizable optimum up to 0.002-0.005;
   N -> inf value 0.6820 (= A–F's 0.68185); Bragg mass 0.83 at alpha = 1+0 (= A–F's edge term |D(1)| = 0.824).
2. **What would break it, ranked** [N]: (a) an upper bound on F just above 1 — even F <= 2 on (1,1.05] gives
   +0.028 (N=40 and N=80 alike); averaged mass bound int_1^{1+d} F <= m needs m below the Bragg mass (~0.5);
   lower bounds (GGOS-type) give ~+0.004; (b) a distinct-small-gap theorem (5% of zeros with a distinct partner
   within 0.5 mean spacing): +0.03; (c) RS 3-point data: +0.02 (replicates h1); 4-point data and moment data
   (Hardy–Littlewood/Ingham analogues): nothing (heavy tails).
3. **The precise obstruction in one line** [C]: zeta in the t-aspect is a family whose size equals its conductor,
   so mean-value/duality inequalities saturate at bandwidth exactly 1, and everything beyond needs prime-pair
   (short-interval variance) information at square-root precision; the crystal is the configuration that
   exploits exactly that blind spot.  Finite shadow (curves over F_q) [R]: Toeplitz inertia counts distinct zeros
   exactly when the rank is not dimension-limited; for zeta rank <= X << N(T).

### Stability of the gains in N (ub_N80.py, DNN model, M=12N) [N]
| row added | N=40 | N=80 | gain N=40 / N=80 |
|---|---|---|---|
| none | 0.6973 | 0.6901 | — |
| S <= 2 on (1,1.05] | 0.7255 | 0.7183 | +0.028 / +0.028 |
| S <= 1 on (1,1.25] | 0.8138 | 0.8098 | +0.117 / +0.120 |
| GGOS lower bound 3/2-alpha on [1,3/2] | 0.7015 | 0.6947 | +0.004 / +0.005 |
| distinct pairs within 0.5 >= 0.05 N | 0.7255 | 0.7205 | +0.028 / +0.030 |
Gains are N-independent while the base value drifts to 0.6820; so in the limit: F <= 2 on (1,1.05] -> ~0.710,
distinct-small-gap(0.5, 5%) -> ~0.712, GUE knowledge on (1,1.25] -> ~0.80.
Final 3-point runs (killed when converging slowly): N=6: 0.7983 (+0.020), N=8: 0.7779 (+0.021, red 2e-2).

---------------------------------------------------------------------------------------------------------
# Lead task (after hand-back): "a positive proportion of zeros have a DISTINCT zero within lambda"

## L1. Trade-off tables [N]
Row added to the finite model: (1/N) E #{ordered pairs of distinct points with 0 < |x - x'| < lambda} >= c
(implied by "a proportion c of the zeros, with multiplicity, have a distinct zero within lambda";
a proportion g of consecutive distinct gaps < lambda gives the row with c = 2g).  Gains are linear in c and
N-independent (N=40 vs 80), so I quote gain = slope*c.  Scripts gap_table.py (DNN), gap_table_M.py
("Montgomery class": certificates r >= 0 with r^ supported in [-1,1], i.e. the A–F window class; primal drops
S >= 0 beyond 1), logs gap_table_N*.log, gapM_N*.log.

| lambda | DNN slope (N=80) | Montgomery-class slope (N=80) | GUE fraction of gaps < lambda |
|---|---|---|---|
| 0.3 | 0.85 | 0.82 | ~0.01 |
| 0.5 | 0.61 | 0.56 | 0.096 (data, t~1e5) |
| 0.7 | 0.22 | 0.19 | ~0.24 |
| 0.9 | 0.056 | 0.049 | 0.436 (data) |
Full table (N=80, value / gain), DNN base 0.6901 (-> 0.6820 as N->inf), Montgomery base 0.6843 (-> ~0.673):
DNN  lam=0.3: c=.01 .6986(+.0085) .02 .7070(+.0169) .05 .7325(+.0423) .10 .7750(+.0849)
     lam=0.5: .6962(+.0060) .7022(+.0121) .7205(+.0304) .7513(+.0611)
     lam=0.7: .6923(+.0022) .6945(+.0044) .7011(+.0110) .7121(+.0220)
     lam=0.9: .6907(+.0006) .6913(+.0011) .6929(+.0028) .6957(+.0056)
Mont lam=0.3: +.0082 +.0164 +.0409 +.0819 ; lam=0.5: +.0056 +.0112 +.0281 +.0562 ;
     lam=0.7: +.0019 +.0038 +.0096 +.0191 ; lam=0.9: +.0005 +.0010 +.0024 +.0049
Reading: in the DNN class every c > 0 breaks 0.68185 (base = ceiling), but that class is not provable; in the
provable (Montgomery/A–F window) class, base 0.6725, breaking 0.68185 needs c > 1.2% (0.3), 1.7% (0.5),
4.9% (0.7), ~19% (0.9); beating the record 0.6736 needs c > 0.14%, 0.2%, 0.6%, 2.3%.  Small lambda is far more
valuable: the crystal has nothing below 0.9, and the window kernel decorrelates beyond ~0.7.

## L2. Pair data cannot produce distinct close pairs at all [N]
hardcore.py: the DNN with R2 = 0 on (0, lambda) is feasible for every lambda < 1 (bisection at N=40:
lambda* = 0.9999, i.e. up to the grid), and imposing a hard core up to 0.9 does not even change the optimum
(0.6973 at N=40).  So pair-correlation data at bandwidth 1 are consistent with NO two distinct zeros closer than
(1-eps) mean spacings.  This is the precise model form of the suspicion of Bui–Goldston–Milinovich–Montgomery
(arXiv:2208.02359, after Thm 2) that the pair-correlation, Montgomery–Odlyzko and Selberg methods "are incapable
of proving mu_d < 1": every published small-gap result (MO, CGGGH 0.77, Soundararajan 0.6876, Wu 0.6653,
BGMM Thm 1 0.6039, Inoue, Bondarenko–Heap / Durkan–Pearce-Crump 1/2 (2610.26038, 2610.28527)) counts gaps
with multiplicity, and the crystal realises all of them with double zeros.  Lamzouri 2610.26841 (13/20
c-isolated, unconditional) goes in the opposite direction (isolated zeros = few close pairs).
The only distinct-gap result I found is BGMM Thm 2 (RH): mu_d <= 0.991, via the sign test
sum_gamma Z'(gamma) Z(gamma + 2 pi a/log T) |M(rho + i eta)|^2 < 0 (non-pair input: discrete mollified moments of
zeta' at zeros, Conrey–Ghosh–Gonek / Heap–Li–Zhao), giving >> T^{1-eps} gaps, NOT a positive proportion, and
pairs (simple, odd multiplicity), not (simple, simple).

## L3. What can be proved — my assessment
(a) **Pair-only methods: provably useless** for this (L2): DNN-consistent laws with no distinct pair below 1-eps.
(b) **BGMM's sign test** (RH): X_gamma = Z'(gamma) Z(gamma + 2 pi a/log T) |M|^2 is >= 0 at every simple on-line gamma whose
next odd-order zero is beyond a, so sum X < 0 certifies a distinct pair within a.  *Positive proportion* would
follow by Cauchy–Schwarz,  #{gamma : X_gamma < 0} >= (sum X)^2 / sum X^2,  provided
sum_gamma |zeta'(rho) zeta(rho + i a') M(...)|^2 |M(...)|^2 << T log T * (typical size)^2  — a mollified discrete moment of
degree 4 in zeta; an upper bound of the right order (not an asymptotic) is what is needed, and Harper / Kirila-type
sharp conditional upper bounds make this plausible under RH.  [C]  **But** the first-moment sign test only works where
the weighted mean of X changes sign, which with mollifiers of length T^theta, theta < 1/2, is a ~ 0.991 (BGMM):
the weight is smooth on the scale 1/(theta log T) ~ 2/theta mean spacings and cannot single out close pairs.  At
lambda ~ 1 the coupling gain is c * kappa_MT(1)^2 ~ 0.002c: useless.  Getting lambda <= 0.7 would need a
*local* detector (resonators give only sparse sets; ratio-type objects zeta(rho+ia)/zeta'(rho) are ratios-conjecture
territory).  The test also yields (simple, odd) pairs, and Theorem A.1 below needs (simple, simple).
(c) **Selberg-type sign changes in short intervals** (two sign changes of Z in a window of length lambda < 1): requires
P(B opposite to both A and C) > 0 for A,B,C = mollified Z at t, t+lambda/2, t+lambda.  Second moments (shifted mollified
moments, unconditional for theta < 4/7) cannot force that (degenerate laws match any covariance); fourth moments are
known only with very short mollifiers (theta ~ 1/4).  [C]: no positive proportion at lambda < 1 from this route as it stands.
(d) **Unconditional version**: any sign test reads Z' only at on-line zeros; off-line zeros have to be controlled as a
secondary term, exactly as Lamzouri does for isolated zeros (Conrey's mollified second moment + Littlewood's lemma).
So unconditional = RH version + an off-line term of the Lamzouri type; this part looks routine.  [C]
**Verdict:** the statement is the right target (it is exactly what the crystal lacks and it couples rigorously, L4),
but nothing in the current literature, or in the obvious adaptations, reaches lambda < 0.9 with a positive proportion.

## L4. Rigorous coupling for zeta (not only in the model)
**Conditional theorem [R, given h1's Theorem A.1 (h1/method.md §3, [R] modulo the routine edge estimate)].**
Hypothesis H(c, lambda): for large T there are at least (c/2 - o(1)) N(T,2T) pairwise disjoint pairs {rho, rho'} of
SIMPLE zeros on the critical line with gamma, gamma' in [T,2T] and 0 < |gamma - gamma'| <= 2 pi lambda/log T
(e.g. a proportion c of consecutive gaps between simple on-line zeros are <= lambda).  Then, for every admissible
even window psi >= 0 on [-1/2,1/2] and lambda <= 1,
    N_0^s(T,2T) >= (2 - R(psi) + c kappa_psi(lambda)^2 - o(1)) N(T,2T),
    N_d(T,2T)   >= (1/2)(3 - R(psi) + c kappa_psi(lambda)^2 - o(1)) N(T,2T),
kappa_psi(d) = int psi(u) cos(2 pi d u) du / int psi.
*Proof.* Theorem A.1: N_0^s >= (2-R)N + sum_{l in spec Gamma} phi(l-1) - o(N), Gamma = (kappa(gamma_rho - gamma_rho'))
over simple on-line zeros (PSD, unit diagonal), phi(a)=a^2 (a<=1), 2a-1 (a>1).  A -> tr phi(A - I) is a convex trace
function, so by pinching (Lemma A.2) it does not increase when Gamma is replaced by its block-diagonal part for the
partition into the given pairs and singletons.  Singletons give phi(0)=0.  A pair block [[1,k],[k,1]], k = kappa(gamma-gamma'),
has eigenvalues 1 +- k, |k| <= 1, so contributes phi(k) + phi(-k) = 2k^2.  For d <= 1 and |u| <= 1/2, cos(2 pi d u) is
decreasing in d, hence kappa is decreasing on [0,1] and k^2 >= kappa(lambda)^2 when kappa(lambda) >= 0.  Summing over
>= (c/2)N pairs gives >= c kappa(lambda)^2 N.  The distinct-zero line is identical with the factor 1/2.  QED
With psi_MT = cos(sqrt2 u) (2-R = 0.672501): kappa^2 = 0.754, 0.437, 0.166, 0.026 at lambda = 0.3, 0.5, 0.7, 0.9
(pinch_gain.py; optimising psi jointly changes the 4th decimal at most).

| lambda | c=1% | 2% | 5% | 10% | c to beat record 0.67364 | c to beat ceiling 0.68185 |
|---|---|---|---|---|---|---|
| 0.3 | 0.6800 | 0.6876 | 0.7102 | 0.7479 | 0.15% | 1.24% |
| 0.5 | 0.6769 | 0.6812 | 0.6943 | 0.7162 | 0.26% | 2.14% |
| 0.7 | 0.6742 | 0.6758 | 0.6808 | 0.6891 | 0.69% | 5.6% |
| 0.9 | 0.6728 | 0.6730 | 0.6738 | 0.6751 | 4.5% | 37% |
If the GUE values held (fraction of consecutive gaps < lambda ~ 0.096 at 0.5, 0.24 at 0.7), the bound would be
~0.714-0.716; the pinching certificate is within ~20% of the LP slopes in the Montgomery class (L1), so little is
lost by using only disjoint pairs.
Caveats: (i) the pairs must be simple–simple and on the line; sign-change (odd–odd) pairs would need an extra
count of triple+ zeros; (ii) the gain is on top of the Alpoge–Furman base 0.6725, not necessarily on top of the other
refinements behind the record 0.6735.
