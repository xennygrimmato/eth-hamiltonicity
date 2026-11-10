# Does the three-point gain vanish as the allowed off-line depth goes to infinity? (closes h1/three_point.md §4)

m4, 10 Nov 2026. Scripts in `m4/`: `threept_deep.py` (= h1/ceiling_deep.py, plus env `SMIN/SMAX` to keep only bispectrum rows
with SMIN <= a+b <= SMAX), `ray_check.py` (explicit deep clusters tested against a saved dual). Outputs `m4/out/cd*`, `m4/out/dual_*`.
Model and rows exactly as in h1/ceiling_npoint.py: N-periodic, total multiplicity N, 2-pt rows E|S(l)|^2 = l (1 <= l <= N-1),
3-pt rows E Re S(a)S(b)conj S(a+b) = 0 (1 <= a <= b, a+b <= N-1); off-line pairs t +- iy enter S(l) with weight 2cosh(2 pi l y/N).

**Answer: yes, in the model the gain vanishes at infinite depth** (N = 8: to within 5e-4; N = 12: to within 1.2e-3, i.e. LP accuracy).
The finite-depth plateau h1's rescaled runs seemed to show is a pricing artefact. The exact reason is the lemma below.

## 1. The numbers [N]

N = 8 (2-pt ceiling 0.6860, same with pairs at any depth, h3/h1). "Value" = cost of the best law found (upper estimate of the ceiling).

| depth allowed | rows | value | source |
|---|---|---|---|
| 0 (RH) | 2pt + all 3pt | 0.7088 | h1 np_8_3 |
| <= 1.5 | 2pt + all 3pt | 0.6896 | h1 cd_8_3_1.5 |
| <= 3 | 2pt + all 3pt | 0.6881 | h1 cd_8_3_3 |
| <= 5 | 2pt + all 3pt | 0.6879 | h1 cd_8_3_5 |
| <= 10 | 2pt + all 3pt | 0.68857 | m4 out/cd_8_3_10.out |
| <= 20 | 2pt + all 3pt | 0.68856 | m4 out/cd_8_3_20.out |
| <= 20 | 2pt + 3pt with a+b >= 5 | 0.68722 | m4 out/cd_8_3_20_smin5.out |
| <= 20 | 2pt + 3pt with a+b <= 4 | 0.68761 | m4 out/cd_8_3_20_smax4.out |
| **0 (RH)** | **2pt + 3pt with a+b <= 4 = N/2** | **0.68646** | m4 out/cdon_8_smax.out |

N = 12 (2-pt ceiling 0.68369-0.68388): RH, 2pt + 3pt with a+b <= 6 = N/2: **0.68487** (out/cdon_12_smax.out); full 3pt on RH: 0.7051 (h1).

The depth 10 and 20 runs are not monotone in the row set (the a+b <= 4 run at depth 20 is *above* the same rows on RH, which is
impossible for the true minimum since allowing more configurations can only lower it); so they are not converged, and
§2 shows exactly which configurations the pricing misses.

## 2. Lemma (deep clusters kill the upper half of the bispectrum) [R in the model; one generic-solvability step checked numerically]

Write an off-line pair as the two points zeta = e(tau/N) with tau = t +- iy; the outer point is v = e^{2 pi i t/N} e^{2 pi y/N}.
For a configuration made of k pairs only (cost 0 simple zeros), S(l) = sum_i v_i^l + O(1) for l >= 1 (the inner partners have modulus < 1).
Put v_i = R w_i, R = e^{2 pi Y/N} -> infinity, and write q_l = sum_i w_i^l. Then

  2pt row l:  R^{2l} |q_l|^2,          3pt row (a,b):  R^{2(a+b)} Re q_a q_b conj q_{a+b}     (up to O(R^{2l-1})).

**Lemma.** Let s0 >= N - k + 1. Choose w with q_l = 0 for s0 < l <= N-1 and q_{s0} = eta = e^{i phi}/R, q_a q_b != 0 for some
a + b = s0 (N - s0 <= k - 1 complex conditions on k points: solvable with |w_i| ~ 1, checked numerically for N = 8, k = 4,
s0 = 5, 6, 7). Then the feature vector of this zero-cost configuration is
  R^{2 s0 - 1} ( Re q_a q_b e^{-i phi} )_{a+b = s0}  +  O(R^{2 s0 - 2}),
i.e. after rescaling it is a **ray of either sign** (phi free) in the 3-point rows with a+b = s0, and zero in every other row.
(Rows with l > s0 vanish identically at leading order; rows with index < s0 are O(R^{2 s0 - 2}).)
*Consequence.* Every 3-point row with a + b >= N - k + 1 can be moved to any value at zero cost by an epsilon-mass of such clusters.
With k = N/2 (all multiplicity in pairs) this covers **all rows with a + b >= N/2 + 1**. So at unbounded depth
  ceiling(2pt + all 3pt)  =  ceiling(2pt + 3pt rows with a+b <= N/2)  <=  the same on RH.
For s0 <= N/2 the construction fails: k points cannot have k consecutive vanishing power sums (Vandermonde), so the top rows
cannot be nulled while q_{s0} is kept small.

**Numerical confirmation** (`ray_check.py`): against the saved dual of the depth-10 run (all rows), explicit clusters with
s0 = 5, 6, 7 at Y = 5..20 give reduced cost -6.9e-3, -6.2e-3, -1.6e-5 (violations), s0 <= 4 none; against the dual of the
depth-20 run with rows a+b >= 5, violations -2.9e-3 (s0 = 5), -2.5e-3 (s0 = 6). The LP had already learned s0 = 7 (its multipliers
for a+b = 7 are 0) but not s0 = 5, 6, which need the higher-order nulling — this is the plateau.

## 3. Conclusion
* [N] With the upper half of the bispectrum removed (as the Lemma permits at infinite depth), the remaining "half-band" rows
  a + b <= N/2 add almost nothing **even on RH**: +0.0004 at N = 8 (0.68646 vs 0.6860), +0.001 at N = 12 (0.68487 vs 0.6838).
  Hence the infinite-depth three-point ceiling lies in [0.6860, 0.6865] at N = 8 and [0.6837, 0.6849] at N = 12:
  **the three-point gain vanishes as depth -> infinity**, to LP accuracy. (Consistent with Tyagi's half-bandwidth cubic and with
  the rank cap 1/2 for half-band traces, h1 §7.)
* So h1's §3 parity obstruction (spectral certificates) extends to all LP certificates using the 3-point rows: unconditionally
  (no depth bound) the bandwidth-one bispectrum carries no usable information beyond the two-point data in this model.
  Under a depth bound y <= Y0 the gain is real and decreasing in Y0 (h1: +0.021 at Y0 = 0.5, +0.007 at 1.0, +0.004 at 1.5).
* [C] Transfer to zeta. The killing clusters have depth ~ N/(2 pi) mean spacings in the N-periodic model (R = e^{2 pi y/N} >> 1),
  i.e. they are rare clusters of many zeros at macroscopic depth. They are needed only with epsilon mass and their row features grow
  like e^{4 pi alpha y} (alpha = s0/N > 1/2), while Selberg-type density bounds only give e^{-c y} with c ~ pi/2 per mean spacing;
  so known density theorems do not exclude the mechanism (in line with h1 §3 last bullet). A bounded-depth (box) hypothesis does.
* Caveat: column generation gives upper estimates; the half-band RH values could be slightly high, which only strengthens the
  conclusion. N = 16 half-band run was started but not converged (killed for CPU).
