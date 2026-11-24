# b1 notebook: can the flat-case bound of "VP ≠ VNP over every field" be pushed from ℓk^{3/2} to ℓk²/log k?

24 Nov 2026. Source: Anthropic, *VP ≠ VNP over every field*. I read the pdftotext (scratchpad `vpvnp/paper.txt`),
Appendix A.1–A.3 (spectral points, Lemma A.2 = exponents of wires, Lemma A.3 = lem_hubs), Appendix D.1 (the flat
hypothesis) and Appendix E (Prop. E.1 through Thm E.11). Labels: lem_balanced = Lemma E.4, lem_hubs = Lemma A.3,
lem_few = Lemma E.7, prop_cube = Prop. E.9, prop_flat_rate = Prop. E.10. I did not need the Lean sources, so I did
not clone them.
Tags: [R] proved here, [K] known (source named), [N] computed (script named), [C] conjecture.
Scripts are in `b1/scripts/` and outputs in `b1/*.out`.

## 0. Answer in brief

* **Where the √k comes from [R].** The 1/√k hub distance is not the cause. The cause is a discrepancy. Normalise
  every wire to length 1 and let z_ab be the unit direction of wire ab. To first order the method's ratio for a
  balanced set S is the length of Z_S = Σ_{a∈S, b∉S} z_ab. This is a sum of about 2k²/9 unit vectors, which must
  stay long for *every* balanced S at once. A second-moment argument over random S makes that impossible beyond
  k^{3/2}.
* **The obstruction, stated sharply [R, Theorem A].** Take the regime of the paper's proof: all wires pass through
  one common point and the hub pairs sit there (or, more generally, every hub segment lies on all wires). Then
  log L ≥ ℓ·R + O(k^{3/2}) with
  R ≤ Λ_k := sqrt(k·s₀(k−s₀)/2), where s₀ = ⌈k/3⌉, so Λ_k ≈ k^{3/2}/3.
  Equality is attained by the simplex configuration of Prop. E.5. No balanced-set system, weighting or embedding
  in this regime can do better. Unbalanced families (sizes in (t,2t]) are worse: about √t·k.
* **Leaving that regime does not help in the numerics [N, C].** Theorem B (a Crofton-formula reduction, [R])
  bounds every Euclidean configuration by a supremum of local first-order ratios. I optimised general
  configurations jointly (ends plus two free hubs per split, any dimension) for k = 4–7. Every run converged to
  Λ_k − O(ε), with the hubs collapsing to the minimum separation allowed. Conjecture [C]: Λ_k is the optimum over
  all Euclidean configurations. The Euclidean hub method would then be capped at about ℓk^{3/2}/3. The constant
  can improve from 1/16 towards 1/3; the exponent 3/2 cannot.
* **Upper-bound calibration [K + R-level remark].** The bound is not 2^{Θ(ℓk²)}. Anthropic's 3-SAT counting engine
  is an oblivious algebraic algorithm (barrier note, discussion after prop:meta), so it is an arithmetic circuit
  over ℚ. It gives
  **log L ≤ O(ℓk²/√log k)**: pieces with ρ = 1/√2 exist (Thm B there), which gives α′ = 1/2. 1/log k is *not*
  proved. It needs ideal pieces with ρ = 1/2 (Majdoddin's Open Problem 1), and it is the floor for grid
  algorithms (Majdoddin Thm 4.13). The circuit target therefore lies between ℓk^{3/2} and ℓk²/√log k. Under the
  flat hypothesis the Euclidean ratio must anyway satisfy R_max(k) = O(k²/√log k), because otherwise it would
  contradict the engine.

## 1. The inequality chain with every constant

**Setting [K].** f_{k,ℓ} has tensor T_{k,ℓ} = Π_{a<b} ⟨2^ℓ⟩_{(a,b),(b,a)} on the N·2 ends (N = C(k,2)). Lemma E.4
writes T = Σ_{S balanced} t_S, where t_S is a sum of ≤ L products across S. By Lemma A.3, t_S is a restriction of
T_S = Π_{a∈S} ⟨2^ℓ⟩_{(a,b),o_S} · ⟨L⟩_{o_S,o′_S} · Π_{a∉S} ⟨2^ℓ⟩_{(a,b),o′_S}. For a spectral point φ, Lemma A.2
gives log₂ φ(product of wires) = Σ (bits)·d_φ.

* Prop. E.5 bounds the cover by φ(T) ≤ 2^k max_S φ(T_S).
* Prop. E.10 uses Lemma E.7 instead: φ(T) ≤ 2^{k·g_φ(ℰ)} max_S φ(T_S).

In both cases, multiplying by the scale c and using c·d_φ ≈ Euclidean gives the following for some S:

  ℓ·Σ_e |e| ≤ k·G + ℓ·Σ_p |p − hub_S(p)| + |o_S − o′_S|·log L + (δ-errors),   G = c·g_φ(ℰ),

that is,

  **log L ≥ (ℓ·saving_S − k·G − errors)/|o_S o′_S|**,   saving_S := Σ_e|e| − Σ_p|p − hub_S(p)|.   (★)

**Prop. E.10 numerically [R, every step rechecked by hand; see the script check below].**

* Ends: (a,b) at ½e_a and (b,a) at −½e_a for a<b, so every wire has length 1.
* w_S = Σ_a ±c_a e_a with Σ c_a = |S|(k−|S|) ≥ 2k²/9. By Cauchy–Schwarz, ‖w_S‖ ≥ (2/9)k^{3/2}.
* Hubs: ±o_S = ±η w_S/‖w_S‖ with η = 2/(9√k).
* Per end, ‖r − o‖ ≤ ½ − 2r·o + η² for ‖r‖ = ½ and ‖o‖ = η. Hence Σ_p|p − hub| ≤ N − 2η‖w_S‖ + k²η², so
  **saving ≥ 2η‖w_S‖ − k²η² ≥ (8/81)k − (4/81)k = (4/81)k**.
* G ≤ √k + δ (Prop. E.9, facet centres), with δ = 10⁻³/k.
* The naming term is k(√k + δ) ≤ 1.5k^{3/2} ≤ 0.015ℓk, using ℓ ≥ 100√k.
* The δ-terms total at most 1.5δk²ℓ = 0.0015ℓk.
* Hence (2η+δ)·log L ≥ ℓk(4/81 − 0.015 − 0.0015) = 0.03288ℓk ≥ ℓk/31.
* With 2η + δ ≤ 0.4444k^{−1/2} + 10⁻³k^{−1} ≤ 0.446k^{−1/2}, this gives log L ≥ ℓk^{3/2}/13.9 ≥ ℓk^{3/2}/14, and
  the statement uses /16.

**Where each factor comes from [R].** The saving is first order in η with coefficient ‖w_S‖ (the gain of the
crossing wires) minus a second-order loss k²η². The loss comes from all 2N ends being pulled sideways by η.

* Optimising gives η* = ‖w_S‖/k² ≈ k^{−1/2}. This is the "hub distance of order k^{−1/2}".
* The saving at η* is ‖w_S‖²/k² ≈ k. This is the "fixed fraction of k".
* The ratio saving/(2η) → ‖w_S‖/2 + O(…) as η → 0 is the real exponent. In fact the ratio is decreasing in η.
  η is kept at k^{−1/2} only so that the *absolute* saving ℓ·k beats the naming term k·G ≈ k^{3/2}; that is
  where ℓ ≥ 100√k comes from.

So the exponent 3/2 is ‖w_S‖ ≈ k^{3/2}. It sums C_S ≈ 2k²/9 unit vectors (each crossing wire contributes ±e_a)
spread over k orthogonal directions, so the average cosine with the hub axis is about k^{−1/2}. The hub distance
and the "fraction of k" are consequences of this, not causes.

## 2. The obstruction in the linear regime (Theorem A) [R]

**The linear regime.** Fix an antisymmetric unit field z_ab = −z_ba (z_ab is the direction of wire ab from end
(a,b) to end (b,a)). Put every wire through a common point m and take hubs m ∓ (h/2)u. Then, exactly:

* every non-crossing wire loses O(h²),
* every crossing wire gains h·u·(±z_e) + O(h²),

so saving_S/|oo′| → u·Z_S with Z_S := Σ_{a∈S, b∉S} z_ab. The best direction u gives **|Z_S|**. The "infinite
lines" limit, where the ends go to infinity along lines through arbitrary offsets, gives the same formula with no
O(h²) term. So does Corollary B1 below. Note that Z_S = Σ_{a∈S} Z_a with Z_a = Σ_{b≠a} z_ab, because internal
wires cancel by antisymmetry, and Σ_a Z_a = 0.

**Theorem A.** For every k ≥ 3 and every antisymmetric unit field z_ab in any Hilbert space,

  min_{S balanced} |Z_S| ≤ Λ_k := sqrt(k·s₀(k−s₀)/2),   s₀ = ⌈k/3⌉,

with equality for the simplex field z_ab = (e_a − e_b)/√2 of Prop. E.5. That field has |Z_S|² = k|S|(k−|S|)/2 for
*every* S. Thus Λ_k = k^{3/2}/3 when 3 | k.

*Proof.*

1. *Triangle bound.*
   Σ_a |Z_a|² = Σ_a Σ_{b,c≠a} z_ab·z_ac = k(k−1) + Σ_{triples {a,b,c}} 2(z_ab·z_ac + z_ba·z_bc + z_ca·z_cb).
   With x = z_ab, y = z_bc, w = z_ca, the bracket is −(x·y + y·w + w·x) = (3 − |x+y+w|²)/2 ≤ 3/2. Hence
   Σ_a|Z_a|² ≤ k(k−1) + 3C(k,3) = k²(k−1)/2.
2. *Random S of size s* (sampling without replacement; uses Σ Z_a = 0):
   E|Σ_{a∈S} Z_a|² = [s(k−s)/(k(k−1))]·Σ_a|Z_a|² ≤ k·s(k−s)/2.
   So some S of size s has |Z_S|² ≤ k·s(k−s)/2.
3. *Choice of s.* Take s = s₀, the balanced size that minimises s(k−s).
4. *Equality.* For the simplex field, Z_a = (k e_a − 𝟙)/√2, so |Σ_{a∈S} Z_a|² = (k²s − 2ks² + s²k)/2 = k s(k−s)/2.
   Equality holds in step 1 because x+y+w = 0 on every triangle. □

Verified by [N] `scripts/lin_regime.py` (k = 4–10, all S) and `scripts/lin_k50.py` (k = 10–50, sampled S; output
`lin_k50.out`).

* The simplex identity holds to 10⁻¹¹.
* Gradient-optimised random fields reach only 0.84–0.89·Λ_k.
* The E.10 field gives min_S‖w_S‖ = 2.45, 3.16, 3.74, 5.29, 6.08, 6.78, 8.72 for k = 4…10, against
  Λ_k = 2.83, 3.87, 4.90, 6.48, 7.75, 9.00, 10.95.

**Consequences [R].**

* (i) In the linear regime the ratio is at most Λ_k ≈ k^{3/2}/3 < C_S ≈ 2k²/9 by a factor of about √k.
* (ii) *Other balanced-set systems.* Lemma E.4 works with any window (t, 2t]: sets larger than 2t recurse, and
  the larger factor has more than t blocks. The same proof gives min_S|Z_S| ≤ sqrt(k s(k−s)/2) ≈ √(t/2)·k for
  |S| ≈ t. So t = k/3 is already the best window. The naming term also shrinks, from k to about 2t·log k, but
  that only matters for the threshold on ℓ.
* (iii) *Weights.* Restricting f_{k,ℓ} to edge weights ℓ_e ≤ ℓ replaces z by w_e·z with w_e ∈ [0,1]. The
  triangle bound still caps Σ|Z_a|² at k²(k−1)/2, so this gives no gain.
* (iv) *Best constant reachable by this route.* As ℓ → ∞ at fixed k, log L ≥ (Λ_k − o(1))·ℓ ≈ ℓk^{3/2}/3,
  against the paper's /6 (E.5) and /16 (E.10).
  [C] The explicit-threshold version for the simplex field would need a G-bound like Prop. E.9 for the points
  ±½u_ab, which are not facet centres. I did not check whether the midpoint argument of Lemma E.8 adapts.

## 3. General Euclidean configurations (Theorem B, numerics)

**Theorem B (Crofton reduction) [R].** Let ends p_i ∈ ℝⁿ and hubs o ≠ o′ be given. Write u = (o′−o)/|o′−o|,
ε_i = +1 for the ends routed to o (a ∈ S) and −1 otherwise. Then

  saving_S / |oo′| ≤ ∫₀¹ L_S(o + λ(o′−o), u) dλ,   L_S(x,u) := ½ u·W̃_S(x) − P(x,u),

where:

* W̃_S(x) = −Σ_i ε_i (p_i − x)/|p_i − x|, the signed sum of the 2N unit vectors from x to the ends;
* P(x,u) = Σ_e Pr_θ[the hyperplane through x with normal θ does not separate the two ends of e] ≥ 0, with θ having
  density ∝ |θ·u| on the sphere.

*Proof.*

1. *Crofton.* |y − y′| = μ(hyperplanes separating y, y′). Integrate the defining sum of saving_S hyperplane by
   hyperplane.
2. *Non-separating hyperplanes.* A hyperplane not separating o, o′ contributes cut(X) − (number of ends on the
   side away from the common hub) ≤ 0. Here X is the set of ends on one side.
3. *Separating hyperplanes.* Orient X to o′'s side. A separating hyperplane contributes
   F_S(X) = #{crossing wires cut correctly} − #{other crossing wires} − 2·#{internal wires wholly on the wrong side}.
4. *Parametrise the separating hyperplanes.* They are exactly {θ·y = θ·x_λ} with λ uniform on [0,1] and θ weighted
   by |θ·(o′−o)|, and this measure has total mass |oo′|.
5. *Expand F_S in the side signs s_i = ±1.* For a crossing wire, 2·1[correct] − 1 = −½(1 + s_ps_q) + ½(s_q − s_p).
   For internal wires the identities are analogous. With E_θ[s_i] = u·(p_i − x)/|p_i − x| (exact for the
   |θ·u|-weighted law), this gives E_θ F_S = ½u·W̃_S(x) − Σ_e ½E(1 + s_ps_q) = L_S(x,u). □

Checked by [N] `scripts/crofton_check.py` (`crofton_check.out`): Monte Carlo, with the formula and the direct
E F_S agreeing to about 10⁻², and the inequality holding in every trial.

**Corollary B1 [R].** Suppose every hub segment [o_S, o′_S] consists of points lying on all wires. Then R ≤ Λ_k.

*Proof.* At such an x, û_{(a,b)} = −û_{(b,a)}, so ½u·W̃_S(x) = u·Z_S for the field of wire directions, and P = 0.
Two distinct points on all wires force all wires onto one line. Either way the field z is the same for all S, and
Theorem A applies. □

This covers the paper's configurations, the "all wires parallel/tournament" configuration and the infinite-line
limit.

**What an improvement would need [R, from B].** It would need, for each S, points x_S at which the local
unit-vector field U_a(x) = Σ_b û_ab(x) is correlated with the sign pattern of S, while the penalty P(x_S,·) stays
o(k^{3/2}). Each wire missing x_S costs a probability of order its angular deficit. So x_S must lie close to
almost all wires, and must still "see" the ends in S-dependent directions.

**Numerics [N].** `scripts/general_opt.py` is a joint SLSQP over the ends in ℝ^d (d = k, 6, 7) and a free hub pair
for every split, with constraints saving_S ≥ t|o_So′_S|, |o_So′_S| ≥ ε = 0.01 and wires of length ≤ 1. It used
random restarts plus one simplex start. Outputs: `gen_k5_k6.out`, `gen_k7.out`, and k = 4 inline in this notebook.

| k | best feasible R | Λ_k | trivial min_S C_S |
|---|---|---|---|
| 4 | 2.812 (all 6 restarts) | 2.828 | 4 |
| 5 | 3.843 | 3.873 | 6 |
| 6 | 4.855 | 4.899 | 8 |
| 7 | 6.403 | 6.481 | 12 |

In every converged run the hub separations sat at the lower bound ε. The optimum wants infinitesimal hubs, which
is the linear regime. Runs that ended infeasible (status 3) had true ratios below Λ_k. These k are too small to
separate k^{3/2} from k², but the optimum *equals* the linear-regime value, not something between it and C_S.

**Conjecture C1 [C].** For every Euclidean configuration, min_S sup_{hubs} saving_S/|o_So′_S| ≤ Λ_k. Then the
Euclidean hub method with Lemma E.4 is capped at log L ≤ (1/3 + o(1))ℓk^{3/2} of provable bound, and it can
never reach ℓk²/log k.

A proof would need to control the S-dependence of U_a(x) on the low-penalty set {x : P(x,·) small} in Theorem B.
I did not finish it. Two partial routes failed:

* the first-order bound at the midpoint, which is too weak when hubs are far apart;
* the per-hyperplane supremum, which is too weak in high dimension because halfspaces realise every partition.

What works is averaging over the Crofton law, which is Theorem B.

## 4. Upper-bound calibration

* **Trivial circuits [R].** Sequential contraction of the K_k network gives log L ≤ ℓ(k²/4 + O(k)): the blob of
  j nodes has j(k−j) open legs. Majdoddin's width bound puts the best contraction trees at about (2/9)ℓk²
  [K, `engine3-open-door.md` §1.1, AKK].
* **Rank-based circuits [K].** Circuits of the form Σ_i Π_a ⟨u_{a,i}, x_a⟩ have size ≥ the tensor rank ≥ 2^{ℓ⌊k²/4⌋}
  (flattening), and Zhou 2026 shows the asymptotic rank equals the flattening floor (`engine3-literature.md`). So
  rank methods are stuck at Θ(ℓk²).
* **Anthropic's engine [K + check].** The barrier note (after prop:meta) records that the recursion is an
  oblivious algebraic algorithm: a straight-line program over ℚ in the table entries whose products and sums are
  fixed in advance. A straight-line program that is correct on all rational inputs computes f_{k,ℓ} as a formal
  polynomial, so it is an arithmetic circuit. The imported Theorem A/B of the barrier note bounds it by
  2^{e_K K²λ}(K(λ+B))^{C₀K²} with e_K ≤ 0.85ρ^ℓ, log K_ℓ = (3x₀+6)2^ℓ − O(ℓ), and pieces with ρ = 1/√2:
  - so **e_K = O((log K)^{−1/2})**, i.e. log L ≤ O(ℓk²/√log k) + O(k² log(kℓ)), for K on the tower K_ℓ. [C] for
    general K: I expect it via Lemma 8, not checked.
  - The constant is only useful for astronomically large K: e < brute force needs log K ≳ 170.
  - Char 0 is safe. [C] for other fields: the pieces divide by scalars d.
* **Correction to the brief.** "e_K ≈ c/log K" is the *ideal-piece* rate (ρ = 1/2, Majdoddin Open Problem 1). It
  is also the proven floor for grid algorithms (Majdoddin Thm 4.13: 1/e ≤ log₂K). The proven rate is
  (log K)^{−1/2}. `engine3-literature.md` line 17 says "(3x₀+6)/log K with ρ = 1/√2", which conflicts with the
  barrier note line 349 (α′ = 1/2). I believe line 17 is a slip.
* **Calibration verdict.** The best algebraic upper bound is 2^{O(ℓk²/√log k)} = 2^{o(ℓk²)}, so ℓk² is *not* the
  right circuit target. The truth lies in [Ω(ℓk^{3/2}) (flat case only), O(ℓk²/√log k)]. ℓk²/log k would be the
  right target if ideal pieces exist.
* **Consistency remark [R].** If the flat hypothesis holds, the chain (★) together with the engine forces
  R_max(k) ≤ O(k²/√log k) for every Euclidean configuration. A Euclidean configuration with R ≫ k²/√log k would
  therefore refute the flat hypothesis outright. Conjecture C1 says no such configuration exists.

## 5. Status and dead ends

* Theorem A (linear-regime optimum Λ_k, sharp) [R]; Theorem B (Crofton reduction) [R]; Corollary B1 [R].
* Conjecture C1 (general Euclidean optimum = Λ_k) [C], with numerical support for k ≤ 7 [N].
* No improvement of the exponent 3/2 was found. Every variant tried — other windows, weights, finite hubs,
  off-centre hubs — gives ≤ Λ_k.
* Not tried: decompositions into r ≥ 3 factors (depth-4 style). The naming cost there is about r·log L·G, which
  looks no better by a rough estimate. Also not tried: non-Euclidean prices (tree metrics are CAT(0), but they are
  not known to be prices).
* Comic: `b1/comic.svg`.
