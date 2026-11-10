# T1f: the ζ-side statement of D_CGdL (Lemma Z), with BGST checked against the source (h3)

Source read: Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of
zeros of the Riemann zeta function*, arXiv:2306.04799v1 (= Acta Arith. 214). I read the text from the arXiv PDF.

## 1. [K] What BGST actually prove (quoted; numbering of 2306.04799v1)
- **(1.2)–(1.3).** F(x,T) := Σ_{ρ,ρ′: 0<γ,γ′≤T} x^{ρ−ρ′} w(ρ−ρ′), with w(u) := 4/(4 − u²). Zeros are counted with multiplicity, and
  the sum runs over **all** nontrivial zeros ρ = β + iγ with 0 < γ ≤ T, on or off the line.
  F(α) := (T log T/2π)^{−1} F(T^α, T).
- **Theorem 1.** F(α) is real, even and nonnegative. As T → ∞,
  F(α) = T^{−2α}(log T + O(1)) + α + O(1/√log T), **uniformly for 0 ≤ α ≤ 1** (endpoint included, following [GM87, Lemma 8]).
- **Lemma 3 (exact identity).** F(x,T) = (2/π) ∫_R |Σ_{0<γ≤T} x^{ρ−1/2}/(1 − (ρ − (1/2 + it))²)|² dt. This is the source of F ≥ 0. The weight
  factorises before the t-integration, and the sharp ordinate cut 0 < γ ≤ T is compatible with it, because ρ ↦ 1 − ρ̄ preserves γ.
- **Lemma 5.** Let r be real, even, in L¹(R), supported in [−1,1] and Lipschitz at 0. Then r̂(z) = 2∫₀¹ r(α)cos(2πzα)dα is even and
  analytic, and
  Σ_{0<γ,γ′≤T} r̂(i(ρ−ρ′)log T/2π) w(ρ−ρ′) = (T log T/2π)(r(0) + 2∫₀¹ α r(α)dα + O(1/√log T)).
  **This is exactly the prime-side input we need, with r = r₁.** r₁ = r·1_{[−1,1]} is supported in [−1,1], even, continuous and
  Lipschitz at 0. No window decomposition and no "linearity" step is needed: BGST already did it.
- Translation to our notation. Put γ_ρ := (ρ − ½)/i, which is complex for off-line ρ, and z_ρ := γ_ρ log T/2π. Then
  i(ρ − ρ′)log T/2π = −(z_ρ − z_ρ′), so r̂(…) = K₁(z_ρ − z_ρ′) because K₁ is even. Also w(ρ−ρ′) = 4/(4 + ((γ_ρ − γ_ρ′))²·…) evaluated
  at complex differences, and the normalisation T log T/2π ~ N(T). **It is the F our Lemma Z produces** (§2).

## 2. [R] Lemma Z: reduction of the ζ statement to a configuration inequality with NO localisation weights
For an admissible CGdL function r (even, continuous, r̂ ≥ 0, r ≤ 0 on |α| ≥ 1, r ≥ 0 on [−1,1], ∫r = 1), and T ≥ 3, define the
**T-kernels** on normalised differences z ∈ C (|Im z| < log T/2π):
  K₁^{(T)}(z) := K₁(z)·W_T(z),  K^{(T)}(z) := K(z)·W_T(z),  W_T(z) := w(2πiz/log T) = 4/(4 + (2πz/log T)²).
**Lemma Z.** Assume the configuration inequality
 (CI_T) for every finite conjugation-symmetric multiset Z of points z (with multiplicities m),
  Σ_{z,z′∈Z} m m′ K₁^{(T)}(z − z′) ≥ 2N(Z) − s₁(Z),
where N(Z) = Σ m and s₁(Z) is the number of real points of multiplicity 1. Then
  N₀ˢ(T) ≥ (2 − r(0) − 2∫₀¹ α r(α)dα − O(1/√log T)) N(T).
*Proof.* Apply (CI_T) to Z(T) = {z_ρ : 0 < γ ≤ T}. This multiset is conjugation-symmetric (ρ ↦ 1 − ρ̄ fixes the ordinate) and finite.
For it, s₁ = N₀ˢ(T) and N = N(T). The left side is the left side of BGST Lemma 5 with r = r₁. ∎
*Remarks.* (i) **There is no edge buffer and no tail lemma.** The sharp cut is part of the configuration, and (CI_T) is asked for
every finite configuration. The Arias de Reyna fn. 1 issue (U = √T in the paper's I′) belongs to the Gram-grid construction, which is
not used. (ii) There are no localisation weights b_t: the Montgomery weight is absorbed into the kernel. Equivalently, by BGST
Lemma 3, Σ w K₁ = (2/π)∫dt ∫ r₁|S_t|², with factorised Poisson weights. Either form works; the kernel form is cleaner. (iii) The
counting step 2N − s₁ ≤ N* is now built into (CI_T). The target is **2N − s₁ = Σ_{on-line} (2m − 1_{m=1}) + Σ_{pairs} 4m_p**,
which is weaker than N* for multiplicities ≥ 3. That matters, see §4.

## 3. [R] The real-configuration base and the tail-positivity identity survive the T-modification
- W_T > 0 on R, so K^{(T)} = K·W_T ≥ 0 on R. Hence for **real** Z, Σ K^{(T)} ≥ Σ m² ≥ 2N − s₁. This is CGdL under RH, now with Montgomery's weight.
- Lemma T for the T-kernels: K₁^{(T)} − K^{(T)} = r̂₂·W_T. Its Fourier transform is (r₂ * p_T) ≥ 0, where p_T ≥ 0 is the inverse Fourier
  transform of W_T (a two-sided exponential of width ≍ 1/log T). So for every finite symmetric Z,
  Σ K₁^{(T)}(z−z′) = Σ K^{(T)}(z−z′) + ∫ (r₂*p_T)(β)|S_Z(β)|²dβ, with |S_Z|² ≥ 0 by symmetry.
  (For complex z the identity is the same Fourier computation; W_T is analytic in |Im z| < log T/π, which covers all zeros.)
- Self-block of an off-line pair at normalised depth y: 2K₁(0) + 2K₁(2iy)W_T(2iy), with W_T(2iy) = 1/(1 − (2πy/log T)²) ≥ 1.
  Pairs are charged at least as in the unweighted model.
- **So (CI_T) is D_CGdL for the kernel pair (K^{(T)}, K₁^{(T)})**, which converges to (K, K₁) locally uniformly as T → ∞.
  All of T1b §1–10 applies verbatim, with W_T ≡ 1 + O((z/log T)²) on any fixed window. The proof must still be uniform in T, because Z(T)
  spans up to log T/2π·T normalised units, while the kernels decay. Decay is what makes this a local statement. W_T only helps at large
  separation (it adds the factor ≤ 1 far away, where K ≥ 0 terms are reduced, so the real-base inequality uses only W_T ≥ 0).

## 4. [N] Correction to T1b: monotonicity under y → 0 fails at high multiplicity, but the inequality does not
`t1b_highmult.py` (periodic N = 32 CGdL certificate): put an on-line point of multiplicity m at distance x ≈ 0.78 from a shallow pair.
- For m ≥ 4, the pair beats the double: δ(y) − δ(0) = −3.6e−5 (m = 4, y = .02) … −8.98e−2 (m = 14, y = .2).
- But δ(0) itself is +0.32 (m = 4), +1.25 (m = 7), +5.57 (m = 14). So δ(y) stays ≫ 0, and **the certificate is not violated**.
- Reason: with target 2N − s₁ (not N*), a point of multiplicity m ≥ 3 carries its own slack m² − 2m.
**Packing lemma, corrected [R].** Take points with multiplicities m_b in a set where K ≥ κ (κ ≤ 1 = K(0)), with total mass M ≥ 2. Their
self + mutual contribution to [Σ K − (2N − s₁)] is ≥ κ Σ_{b≠b′} m m′ + Σ_b (m_b² − 2m_b)₊ ≥ κ(M² − 2M).
(For m_b ≤ 2 use Σ m² ≤ 2M; for m_b ≥ 3, m_b² − 2m_b ≥ κ(m_b² − 2m_b).) So the cell criterion R4 of T1b §9 holds for **all**
multiplicities. Lemma C must be stated with target 2N − s₁: replace N* by 2N − s₁ and keep the slack Σ_b (m_b² − c(m_b)).

## 5. [N] T1c: an explicit 5-term kernel, value 0.677610 (scripts `t1c_explicit2.py`, `t1c_opt5.py`, `t1c_kernel5.py`, `t1c_k5_tests.py`)
**Kernel.** c = 3/2, and on [−3/4, 3/4]
  f(u) = 2/3 + 0.53044 cos(4πu/3) + a₂ cos(8πu/3) + 0.347412 sin(4πu/3) − 0.178443 sin(8πu/3),  ∫f = 1,
  with a₂ = −0.136227748726 fixed by r(1) = 0 exactly (`t1c_fix_r1.py`; then r(1) = 2e−18, value unchanged at 0.677610).
Set r := f * f (autocorrelation) and K := r̂ = |f̂|². Then:
- **K ≥ 0 on R automatically** (it is a square). So the real-configuration base (CGdL under RH) needs no numerical check at all.
- r ≤ 0 on [1, 3/2] and r ≥ 0 on [0,1], checked on 2001 points each by Gauss quadrature. The joint constraint forces r(1) = 0; after
  rounding the coefficients to 6 digits the residual is r(1) ≈ +3.9e−7, so T1c must pin down one coefficient exactly (one
  quadratic equation). τ = ∫_{|α|>1}|r| = 0.0112.
- **Value 2 − r(0) − 2∫₀¹ α r = 0.677610** (CGdL-type, so this is an RH theorem with an explicit kernel; CGdL's optimum is 0.6792).
  The odd part matters: with even f only, the same 5-mode LP gives far less.
  Simpler families: 3 modes (1, cos, sin) give at most 0.649 (c = 1.6); 5 modes give 0.6778 at c = 1.5–1.6.
- **One-body criterion R4 for this kernel** (cells of {G_y < 0} on |x| ≤ 15.5, corrected packing lemma):
  R4 = 0.762 (y = .002), .766 (.005–.02), .781 (.05), .809 (.1), .826 (.2), .782 (.3), .731 (.5), .888 (.7), .797 (1.0), .458 (1.5),
  .172 (2.0), .0008 (3.0). **R4 < 1 at every sampled y, including y → 0.** Here K has few near-zeros: 16 cells at small y, against 56 for
  the LP-extremal CGdL kernel, where small y was the delicate regime. So this kernel is the right candidate for a human-checkable
  single-pair proof (T1d). What remains for it: interval arithmetic for K, K₁ and G_y on |x| ≤ 15.5; a decay bound for |x| > 15.5; a Lipschitz
  bound in y between grid points; y → 0 and y → ∞ asymptotics.
- With a₂ pinned, the periodic N = 16 certificate (`k5f_16.npz`, value 0.678523) has adversarial min reduced cost −1.5e−14, i.e. 0 to
  rounding. It is **tight** on a real configuration (s₁ = 0, doubles). With pairs allowed the min is the same, at depth 0. The rounded
  coefficients had given −7.7e−7, from r(1) = +3.9e−7; the check is that sensitive. N = 32, depths ≥ 0.3: +0.066.
- Periodic versions (exact on real configurations by Poisson, since K ≥ 0): N = 16 value 0.678524, N = 32 value 0.677839, saved as
  `k5r_16.npz`, `k5r_32.npz`. Off-line adversarial checks: see §6.

## 6. Status
- **[R] given [K] BGST Lemma 5: Lemma Z** (§2). The ζ statement is exactly the configuration inequality CI_T, with Montgomery-weighted
  kernels. No buffer, no tail lemma, no localisation weights. Real-configuration base and tail positivity hold verbatim (§3).
- [R] Corrected counting target (2N − s₁) and the corrected packing lemma for all multiplicities (§4). [N] High multiplicity breaks
  pointwise monotonicity, but not the inequality.
- [N] Explicit kernel, value 0.677610, single-pair criterion R4 < 1 on all sampled depths (§5).
- Open: CI_T itself, i.e. a rigorous single-pair proof (T1d) plus several pairs (T1e), uniformly in T.
- **Where T1e will break if done in position space [N]**: two off-line pairs of equal depth y. With the pair–pair term assigned in
  position space, the best case is (2·self + 4[G_{2y} + K](x))/(2·self) = +0.495 (y = .3), +0.312 (.5), +0.097 (1.0), +0.041 (1.5),
  +0.022 (2.0), at distance x ≈ 0.55–0.8. It stays positive but tends to 0. Reason: for equal deep depths both G_{2y} and the self term are
  dominated by the α = ±1 edge, Re K₁(x + 2iy) ≈ K₁(2iy)cos(2πx). So with ≥ 3 deep pairs, pairwise position-space bounds cannot work.
  The edge part must be treated on the Fourier side, where it is Σ_{p,q} C_p C_q cos(2π(t_p − t_q))·(edge mass) = |Σ_p C_p e^{2πit_p}|²·(…) ≥ 0.
  Proposed T1e structure: split r₁ = r_edge + r_bulk, with r_edge supported in [1−ε, 1] and handled by Fourier positivity; r_bulk has
  exponentially smaller growth e^{2π(1−ε)y} and is handled by the cell/packing argument.
