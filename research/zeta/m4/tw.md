# T8 finished: Hypothesis TW (zeta'-weighted pair data) — status, finite-model ceilings, verdict

m4 (successor of h4), 10 Nov 2026. Builds on h4/T8_hypothesis_TW.md, h4/T2_import_RH_gains.md §1, §4, h4/tw_model.py, h4/tw_moll.py
(copied to m4/). New scripts: `m4/tw_lp.py` (determined weights, one- or two-sided rows, depth-robust column scaling as in
h1/ceiling_deep.py), `m4/tw_free.py` (free weights: what a Cauchy–Schwarz/certificate proof can use). Outputs `m4/out/le_*`,
`m4/out/free_*`, `m4/out/twE_*`. Tags as in TEAM.md. Model numbers are column-generation values = upper estimates of the LP
minimum; non-monotone pairs in the tables show the noise is up to ~0.005 (0.01 for free weights).

## 0. Verdict (short)
**Dead as a route past 0.68185, for an exact reason (unconditionally), and nearly worthless even on RH at N = 12.**
1. [N] The large model gains reported earlier (0.714 / 0.785 / 0.74–0.76) come from rows that reach the bandwidth endpoint
   alpha = 1 (x = T, model frequency j = N). The *unweighted* pair row at alpha = 1 alone does the same (0.758 at N = 8, 0.736 at
   N = 12). In the continuum this is the Bragg peak of the extremal crystals at alpha = 1+0 (x2), i.e. support-beyond-one data, not TW.
2. [N] Restricted to x in [1, T) (strictly inside), determined weights give +0.014 (N = 8) and +0.024 (N = 12) over the base;
   but the gain (a) needs the TW upper bound constant-sharp (10% slack: +0.002 at N = 8), (b) disappears when the weights are
   treated as what a proof knows about them (free weights + f = 0 at multiple zeros + BHB's S1): **0.6878 vs base 0.6860 with
   off-line pairs allowed** (N = 8), 0.6858 vs 0.6851 (N = 12). On RH the free-weight data give +0.014 at N = 8 but nothing at
   N = 12 (0.6851), so even the RH version shrinks with N. The determined-weight gain is information the model has because it
   knows f as a function of the configuration (Hadamard product), which no certificate can use. The adversary uses shallow off-line pairs carrying
   O(1) weight on both members ("weighted pseudo-doubles"); allowing even 2% of the zeta'B second moment on off-line zeros
   already brings the ceiling to <= 0.690.
3. Exact reason (lemma form, §4): TW data are Hermitian squares in the values f(rho); a Hermitian square cannot distinguish a
   shallow off-line pair carrying weights (u, v) from two on-line simple zeros carrying (u, v). The only zeta-specific fact
   that separates them is h4's anti-alignment f(rho*) ~ -f(rho) = O(delta) on shallow pairs (T2 §4.1), which is a pointwise
   statement at off-line zeros; using it needs Lemma O1 (an unconditional bound for sum over off-line zeros of |zeta'B(rho)|^2),
   which is not available. With Lemma O1 (or RH) this escape is closed, but the free-weight data then still give only +0.014
   (N = 8) and ~0 (N = 12): the residual determined-weight gain lives in the Hadamard-product dependence of zeta'(rho) on the
   other zeros, which no known certificate can use.

## 1. What is unconditional today (and for what lengths)
Notation: f = zeta'B, B(s) = sum_{k<=y} b(k) k^{-s}, y = T^theta; sums over T < gamma <= 2T (or 0 < gamma <= T).

| statement | status | lengths / ranges | source |
|---|---|---|---|
| Landau–Gonek: sum_{0<gamma<=T} x^rho = -(T/2pi) Lambda(x) + O(x log 2xT loglog 3x + log x min(T, x/<x>) + log 2T min(T, 1/log x)) | [K] unconditional, uniform in x > 1, T > 1 (x < 1 by rho -> 1 - conj rho) | all x | Gonek, Contemp. Math. 143 (1993); used uniformly by BGST |
| Montgomery's F(alpha) over all complex zeros (analytic form), alpha in [-1,1] incl. the endpoint | [K] unconditional | bandwidth one | Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh arXiv:2306.04799 Thm 1, Lemma 5 (read by h3, T1f) |
| sum zeta'(rho) ~ (T/4pi) log^2 T (Shanks) | [K] unconditional | — | Conrey–Ghosh–Gonek (1988); Fujii; alternative proof arXiv:2601.18025 (abstract read) |
| sum chi(rho) X^rho, uniform in X, three regimes X < T, X ~ T, X > T | [K] unconditional | all X | arXiv:2601.18025 (abstract read; statement per h4) |
| sum |zeta'(rho)|^2 ~ T L^4/(24 pi) | [K] on RH (Gonek, Invent. Math. 75 (1984)); the *analytic* sum sum zeta'(rho)zeta'(1-rho) by the same contour computation: [C] unconditional, not checked in print | — | |
| mollified S1 = sum f(rho), S2 = sum f(rho) f(1-rho), b(k) = mu(k)P(log(y/k)/log y) | [K] unconditional asymptotics ((19/24) N L, (57/64) N L^2 at the optimum); RH used only to read S2 as sum |f|^2; GLH of CGG 1998 removed by a generalised Vaughan identity | **theta < 1/2** | Bui–Heath-Brown arXiv:1302.5018 (abstract read by me; "all the analysis is unconditional" checked by h4, T2 §1) |
| sum zeta^{(m)}(rho+alpha) X(rho) Y(1-rho), X, Y Dirichlet polynomials | [K] asymptotic formula; RH only for the applications (abstract) | lengths T^theta, theta < 1/2 in Ng's version (I have not checked BEN's exact length conditions) | Ng arXiv:0706.1763; Benli–Elma–Ng arXiv:2311.13554 |
| **TW: int r(u) |sum_rho f(rho) e^{i u gamma_rho}|^2 du** (two-point, f-weighted; = sum_{rho,rho'} f(rho) f(1-rho') r^(gamma - gamma'), a Hermitian square and analytic) | **not in print [C]** | — | h4 T8 §1.1 |

What one can realistically expect for TW [C]: A(u) := sum f(rho) x^{rho - 1/2} (x = e^u) is evaluated pointwise by AFE + Landau–Gonek +
the chi(rho)X^rho theorem; its main term is a sum of spikes of width 1/T in u at the rationals x = k n m / (...) generated by
b(k), log n and Lambda(m). The mean square is **diagonal (Montgomery–Vaughan) when the spikes are separated**, roughly for
x in [T^{2 theta + eps}, T^{1 - eps}]; for x < T^{2 theta} rationals with denominators up to y collide (shifted mu-convolution sums,
Kloosterman-type), and x >= T is beyond bandwidth one (Hardy–Littlewood type). The model (§3) says the strictly-inside gain needs
**both** the diagonal range and the small-x range (neither alone gives anything), with a constant-sharp upper bound.

## 2. Model (all rows analytic in the zeros and Hermitian squares)
N-periodic configurations, total multiplicity N (k1 simple on-line, k2 double, k3 off-line pairs t +- iy). Objective E[k1]/N.
* pair rows |S(l)|^2 = l, 1 <= l <= N-1 (bandwidth one; alpha = l/N < 1);
* TW rows V_j = |sum_rho f_rho e(j tau_rho/N)|^2, with f_rho = g_rho B(z_rho), g_rho = prod_{rho' != rho} (1 - z_rho'/z_rho) (zeta'(rho)
  analogue, 0 at doubles), B = sum_{k<=K} c_k h_k z^{-k} (h_k = coefficients of 1/Lambda, the mu analogue; c = RH-optimal mollifier,
  K = theta N), targets = CUE Monte Carlo; j in [0, N] <-> x in [1, T] in the zeta'-frame; j = N is the endpoint alpha = 1;
  K = 0 is h4's unmollified Z'-weight (Z'-frame |l| <= N/2 = zeta'-frame 0 <= j <= N).
* SIDE=le: rows <= target (one-sided upper bounds — the direction that survives arbitrarily deep pairs, since deep pairs only
  increase Hermitian squares; numerically pairs of depth <= 3 never appear deep in the optimal laws).
* "determined" weights (tw_lp.py): f computed from the configuration (the model knows the Hadamard product);
  "free" weights (tw_free.py): f is a free complex vector on the simple zeros (and on pair members, unconditional mode),
  constrained only by S1 = E sum f (two-sided, BHB) and the TW upper bounds; pricing over f is explicit
  (f = (nu/2) A^{-1} 1, A = sum_j mu_j conj(E_j) E_j^T). Free weights are what a Cauchy–Schwarz-type certificate can use.

## 3. Results [N]
N = 8 base: 0.6860 (two-sided/RH, h3); one-sided pair rows give the same. N = 12 base 0.6837 (h3); one-sided le run 0.6851.
Pairs: off-line pairs of depth <= 3 allowed unless "RH".

**(a) Rows reaching alpha = 1 (endpoint artefact)**
| N | rows added to the pair rows | value |
|---|---|---|
| 8 | unweighted pair row l = N (alpha = 1) only, le | **0.7579** |
| 12 | same | **0.7356** |
| 8 | mollified K = 3, j = 0..8, le | 0.7645 (DELTA = 10%: 0.7528); two-sided depth <= 1 (h4): 0.785 |
| 8 | mollified K = 1 / K = 2, j = 0..8, le | 0.7435 / 0.7472 |
| 8 | mollified K = 1, j = 8 only | 0.7000 |
| 12 | mollified K = 2, j = 0..12, le | 0.7324 |
| 8 | unmollified Z', all |l| <= 3N/2 (includes x < 1), two-sided depth <= 1 (h4) | 0.714 |

**(b) Strictly inside: x in [1, T) (j <= N-1)**
| N | weights | rows | value | gain over base |
|---|---|---|---|---|
| 8 | det., K = 0 (unmollified, Gonek-type) | j = 0..7, le | 0.6882 | +0.002 |
| 8 | det., Z'-frame |l| <= 4 incl. endpoints, two-sided, depth <= 1 (h4 code, m4 run) | | 0.6944 (RH 0.6943) | +0.008 |
| 8 | det., K = 1 | j = 0..7, le | **0.6998** | **+0.014** |
| 8 | det., K = 1 | j = 0..7, le, **10% slack** | 0.6883 | +0.002 |
| 8 | det., K = 1 | j = 0..3 / j = 3..7 (diagonal range) | 0.6902 / 0.6885 | +0.004 / +0.002 |
| 8 | det., K = 2 | j = 0..2 / j = 5..7 | 0.6883 / 0.6879 | ~0 |
| 8 | det., K = 3 | j = 0 / j = 0..4 / j = 7 | 0.6875 / 0.6892 / 0.6877 | ~0 |
| 12 | det., K = 2 | j = 0..11, le | **0.7092** | **+0.024** |
| 12 | det., K = 2 | j = 0..11, le, 10% slack | 0.6899 | +0.005 |
| 8 | **free, RH** (f on simple on-line zeros) | K = 3, j = 0..7 | **0.6996** | +0.014 |
| 8 | **free, unconditional** (f also on pair members) | K = 3, j = 0..7 | **0.6878** | **+0.002** |
| 8 | free, uncond., + cap sum_{off-line}|f|^2 <= c N | c = 0.02 / 0.1 / 0.3 | <= 0.6903 (all three; non-monotone values = noise) | <= +0.004 |
| 12 | **free, RH** | K = 2, j = 0..11 | **0.6851** | **~0** (base le run 0.6851) |
| 12 | **free, unconditional** | K = 2, j = 0..11 | **0.6858** | **~0** |
| 8 | free, RH / uncond., with the endpoint j = 8 | K = 3, j = 0..8 | 0.7521 / 0.7403 | endpoint artefact |

Optimal laws in the free unconditional runs put 40% of the mass on configurations with shallow pairs (depth 0.001–0.003) carrying
weight: the "weighted pseudo-double".

## 4. The exact obstruction [R] (elementary) + what would be needed
**Lemma (pseudo-doubles).** Let Q be any of the data used here — S1 = sum f(rho), or any Hermitian square
|sum_rho f(rho) phi(rho)|^2 with phi continuous (TW rows, pair rows with f = multiplicity). Replace two on-line simple zeros
1/2 + i t1, 1/2 + i t2 carrying weights u, v by the off-line pair 1/2 + delta + i t, 1/2 - delta + i t carrying u, v. As
(t1, t2, delta) -> (t, t, 0) every such Q is continuous, and the pair rows converge to those of a double zero at t.
Hence for **free** weights the data cannot distinguish "two simple on-line zeros merging" from "an off-line pair": any law
of on-line configurations in which doubles are allowed to carry weight is approximated, with the same data, by laws whose
simple on-line count is the k1 of the configuration without those doubles. So
  free-weight unconditional ceiling <= ceiling of {pair rows + TW rows, weights allowed on doubles} (numerically = base + noise).
On RH, doubles must have f = 0, which is exactly the information TW adds. *Proof*: continuity of finite sums; the pair-row
statement is h3's depth -> 0 limit.

**What breaks the obstruction.** A statement that forces f to be small on off-line zeros. For zeta it is true pointwise
(h4 T2 §4.1: f(rho) = delta (EB)(rho), f(rho*) = -delta (EB)(rho*), E = zeta/((s-rho)(s-rho*))), but uniformity is the issue:
**Lemma O1** (h4 T2 §1): unconditionally, sum over off-line zeros T < gamma <= 2T of |zeta'B(rho)|^2 <= eta N L^2 with small eta.
The model says eta must be very small (2% already lets the ceiling fall to <= 0.690). Lemma O1 is a discrete moment of zeta' at
zeros off the line: no technique gives it without zero-density input sharper than anything known near the line (a shallow pair at
depth delta has |f|^2 ~ delta^2 |EB|^2 and the number of such pairs is not controlled by density theorems for delta ~ 1/L).

## 5. Answers to the three items
1. Unconditional today: Landau–Gonek (all x), BGST's F on [-1,1], Shanks' sum, sum chi(rho)X^rho, BHB's mollified S1/S2 and
   Ng/BEN twisted discrete means for mollifier/twist lengths theta < 1/2. Two-point zeta'-weighted sums (TW): nothing in print.
   The diagonal range x in [T^{2theta+eps}, T^{1-eps}] looks provable by BGST's method with zeta' weights [C]; the range x < T^{2 theta}
   needs off-diagonal mu-convolution sums; constant-sharp is required.
2. Model: with the endpoint alpha = 1 excluded and off-line pairs allowed, TW raises the ceiling by +0.014 (N = 8) / +0.024 (N = 12)
   with determined weights, needs <10% sharpness (+0.002 / +0.005 with 10% slack), and by **+0.002 / +0.001 (nothing)** with free
   weights (the form a proof can use); on RH free weights give +0.014 / ~0.
   The 0.71–0.79 numbers are the alpha = 1 endpoint (an unweighted alpha = 1 row gives 0.758/0.736).
3. Verdict: **not worth a proof attempt as an unconditional route.** Exact reason: §4 Lemma — Hermitian-square data in the
   values f(rho) cannot tell a weighted shallow off-line pair from two simple on-line zeros; only Lemma O1 (unavailable) would.
   Even the conditional variant is weak: on RH, free-weight TW data inside [1, T) give +0.014 at N = 8 and ~0 at N = 12
   (0.6851), and on RH the competitor is 19/27 = 0.7037 (BHB) anyway. The determined-weight gain (+0.024 at N = 12) is real
   information in the model, but it is carried by the dependence of zeta'(rho) on all the other zeros, which enters no known
   certificate; a proof would need a configuration inequality that uses zeta'(rho) as a function of the zeros (Hadamard
   product), i.e. a genuinely new zero-side mechanism, plus constant-sharp TW (10% slack leaves +0.005 at N = 12).
