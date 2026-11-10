# T1g: the mixture kernel closes the small-depth hole of D_CGdL — reduction, numbers, and the conditional ζ theorem   [h5]

Builds on h3/T1b_depth_lemma.md (§4b, §6–12: tail-cancellation Lemma T_h3, Lemma C, cell criterion R4) and on
h5/T1c_transfer.md (Lemma T: mixture transfer). Scripts are in `h5/t1g/`: `mix_kernel.py`, `mix_scan.py`, `mix_smally*.py`
and `*.out`. Kernel data: h3's `cgdl_r_64.npz`, a near-continuum periodic CGdL LP with N = 64, M = 256 and value 0.679358.

## 1. Reduction [R]
Let r_MT := ψ⋆ψ/(∫ψ)² with ψ = cos(√2 s)1_{[−½,½]}; this is the MT kernel, K_MT = |ψ̂|²/ψ̂(0)² ≥ 0. Let r_C be CGdL-admissible
(K_C = r̂_C ≥ 0, r_C ≥ 0 on [−1,1], r_C ≤ 0 off it, K_C(0) = 1). For ε ∈ [0,1] put r_ε := (1−ε)r_MT + εr_C. Then:
- (a) r_ε is CGdL-admissible: K_ε = (1−ε)K_MT + εK_C ≥ 0; r_ε ≥ 0 on [−1,1]; r_ε ≤ 0 off it, since r_MT vanishes there.
- (b) The data-form certificate of r_ε is the mixture (1−ε)·MT + ε·CGdL. Its value is (1−ε)v_MT + εv_C, because the value
  is linear in r. Its unconditional validity is exactly Conjecture D_τ of T1c with τ = (1−ε)/ε.
- (c) Hence h3's reduction applies verbatim to r_ε. Lemma T_h3 (tail cancellation) and Lemma C (comparison with doubles)
  use only (a). So **single-pair D_τ ⟸ LHS_ε(B,y) := self_ε(y) + 4Σ_b m_b G^ε_y(t−t_b) + E^ε_B ≥ 0 for every real background
  B**, where G^ε_y(x) = Re K₁^ε(x+iy) − K₁^ε(x) + K_ε(x).
- (d) By h3's packing lemma this follows from **R4_ε(y) < 1** (the sum of the cell charges of {G^ε_y < 0}, divided by self_ε(y)).
- (e) Structural reason the mixture helps: CGdL's stiff wells sit at the zeros of K_C (x ≈ 1.048, 1.935, 2.082, …). There
  K_ε ≥ (1−ε)K_MT(x) > 0, so for small y the corresponding cells disappear once y²|β''| < (1−ε)K_MT(x). Only *common* zeros of
  K_MT and K_C survive the limit y → 0. Without common zeros on |x| ≤ X, G^ε_y ≥ 0 there for y ≤ y₀(X). Then the y → 0 regime
  needs **no difference-set lemma**, which is the hardest open piece of h3's pure-CGdL route.

## 2. Numbers [N] (near-continuum periodic model, N = 64)
Pure CGdL (ε = 1) against mixtures. Entries are R4(y) (h3's criterion, |x| ≤ 31.5 unless stated). The criterion passes iff R4 < 1.

| y | 0.001 | 0.003 | 0.01 | 0.03 | 0.1 | 0.3 | 0.5 | 0.8 | 1.0 | 1.5 | 2 | 3 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ε = 1 (CGdL) | **4.60** | **1.39** | 0.996 | 0.849 | 0.864 | 0.806 | 0.737 | 0.883 | 0.775 | 0.404 | 0.050 | 2e−4 |
| ε = 0.5 (τ = 1) | 0.122 | 0.098 | 0.644 | 0.805 | 0.840 | 0.815 | 0.777 | 0.922 | 0.816 | 0.419 | 0.051 | 2e−4 |
| ε = 0.2 (τ = 4) | 0.096 | 0.127 | 0.714 | 0.799 | 0.828 | 0.823 | 0.803 | 0.956 | 0.844 | 0.430 | 0.052 | 2e−4 |

Fine y-scan (`mix_scan.py`: 12 points on [3e−4, 0.03] and steps of 0.04/0.025/0.1 up to 3). sup R4_ε over y ∈ [3e−4, 3]:

| ε | τ | value (N=64) | continuum value | sup R4 (where) | max over y ≤ 0.03 |
|---|---|---|---|---|---|
| 0.95 | 0.05 | 0.67902 | 0.6789 | 1.48 (y = 3e−4) | 1.48 |
| 0.9 | 0.11 | 0.67868 | 0.6785 | 1.29 (3e−4) | 1.29 |
| 0.8 | 0.25 | 0.67800 | 0.6779 | 1.12 (3e−4) | 1.12 |
| 0.7 | 0.43 | 0.67732 | 0.6772 | 0.968 (3e−4) | 0.968 |
| 0.5 | 1 | 0.67597 | 0.6759 | **0.927** (y = 0.725) | 0.805 |
| 0.3 | 2.3 | 0.67461 | 0.6745 | 0.950 (0.75) | 0.800 |

Reading.
- For ε ∈ [0.3, 0.7] the criterion passes at every sampled y ∈ [3e−4, 3]. Pure CGdL fails it for y < 0.01, which is h3's hole.
- There is a trade-off. More MT weight helps small y but slightly hurts y ≈ 0.75, where the MT part's own negative lobes are
  relatively deeper (0.88 → 0.92 → 0.96).
- The sweet spot is ε ≈ 0.5, with worst margin 7% at y ≈ 0.73. Its continuum value is 0.6725 + 0.0067/2 = **0.67585**, above the
  record 0.67364.
- **Resolution limit of the numerical kernel.** h3's LP kernel satisfies K_C ≥ 0 only to tolerance about 3e−6 (min −3.1e−6 at
  x = 1.05). For y ≲ 1e−4, R4 computed from it blows up like y^{−2}, at points where the numerical K_ε < 0 (`mix_smally*.out`).
  This is an artefact: the exact K_ε is ≥ 0. Settling y → 0 needs a certified kernel with K_C > 0 off its exact zeros (T1c).
  In that limit only exact common zeros of K_MT and K_C matter. Numerically there is a near-common zero at x ≈ 3.02
  (K_MT ≈ 7e−10, K_C ≈ −3e−8), and its cell contributes R4 ≈ 0.07–0.14 for y ∈ [1e−3, 3e−3]. The first CGdL zero, 1.048, is only
  weakly lifted (K_MT(1.048) ≈ 6.7e−5), so the lift acts only for y ≲ 3e−3. That is fragile but quantified.

## 3. The ζ theorem this would give (conditional) [C]
**Theorem M(ε) (conditional on Lemma Z_ε).** Let r_ε be as in §1, with r_C the CGdL20 kernel (value v_C = 0.6792…). Suppose:
- **(Z_ε)** (zero side, h3 §11 with kernel K₁^ε): for every finite conjugation-symmetric multiset Z of complex points with
  multiplicities, and Montgomery weights Ω_t(γ) = 2/(1+(t−γ)²),
  Σ_{ρ,ρ′} m m′ Ω_t(γ)Ω_t(γ′) K₁^ε((γ−γ′)L/2π) ≥ Σ_{on-line} m² Ω_t² + Σ_pairs 4|Ω_t(γ)|² − o(Σ m|Ω_t|²).

Then liminf_{T→∞} N₀ˢ(T)/N(T) ≥ (1−ε)(2 − c_MT^{−1}) + εv_C. At ε = ½ this is ≥ **0.67585**.
More generally ≥ 0.672500 + 0.0067/(1+τ).

Proof skeleton:
1. Apply Z_ε to Z(T) = {0 < Re γ ≤ T} (conjugation-symmetric), with Ω = Ω_t, and integrate in t. The left side becomes
   (T log T/2π) ∫ r₁^ε F_T. The right side becomes N* = 2N − N₀ˢ + (higher-multiplicity terms ≥ 0), using m² ≥ 3m − 2 and
   4 per off-line pair.
2. **Prime side.** BGST24 Thm 1 gives F_T(α) = (1+o(1))T^{−2|α|}log T + |α| + o(1) uniformly on [−1,1] for the complex-zero form factor.
   Since r₁^ε is continuous on [−1,1] with r₁^ε(±1) = 0, ∫ r₁^ε F_T = r_ε(0) + ∫|α| r_ε + o(1). (h3 is checking the exact
   uniformity statement.)
3. Normalisation: K_ε(0) = 1 gives value 2 − r_ε(0) − ∫|α|r_ε. This is linear in ε, and the MT end equals 2 − c_MT^{−1}.
   No Gram matrix, no grid and no edge buffer are needed, so the Arias de Reyna U = √T issue does not arise.
4. Edge/height truncation: Z(T) is symmetric and finite, and the tail-cancellation identity (T_h3) holds for any finite
   symmetric configuration.

Inputs and status:

| input | status |
|---|---|
| MT kernel, closed form | [K] |
| CGdL20 kernel and value | [K]; a certified continuum version is h3's T1c (open) |
| BGST24 Thm 1, uniform on [−1,1] | [K], exact statement under check by h3 |
| Lemma T_h3, Lemma C, packing lemma | [R] (h3) |
| mixture reduction §1 | [R] (here) |
| single-pair D_τ in the near-continuum model | [N] (§2) |
| multi-pair D_τ | open; h3's T1e, same kernel substitution |
| continuum Lemma Z_ε with Montgomery weights, incl. raw-deep zeros | open; h3's T1f |
| certified kernel, y-Lipschitz bounds, tails |x| > 31.5, y > 3 asymptotics | open (as in h3 §12) |

## 4. What this changes in the plan
- The single-pair proof (T1d) should be done for K_ε with ε ≈ ½ instead of pure CGdL. Its small-y part then becomes "positivity of
  K_ε off exact common zeros" plus a finite cell sum, with no difference-set lemma. The price is ≈ 0.0034 in the final constant:
  0.6759 instead of 0.6792, still a record by 0.0022.
- The certification work is the same as h3's T1c/T1d, applied to one extra explicit kernel (MT is closed form).
- Conjecture G (Gram depth lemma, T1c note) is **not needed** on this route: the MT part enters as a CGdL-admissible kernel, not
  through the Gram/rank–trace slack. Lemma S/S′ remain useful as the "ε → 0" robustness statement.
