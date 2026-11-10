# Fabbian's two Zenodo preprints: exact statements, and whether they exclude our route  [m3, 10 Nov 2026]

Read in full from the PDFs that h2 downloaded (`scratchpad/zn/fab/depth.pdf` 34 pp., `barriers.pdf` 46 pp.; text extracted
with pdftotext). I checked the Zenodo API on 10 Nov: both records are still at version 1.0 and have no later version.
Tags: **V** = I read it in the primary source; **[N]** = my computation (`m3/fabbian_tests.py`, `m3/fixedcharge_check.py`);
**[C]** = my assessment. Both papers are self-published and unrefereed. Fabbian states in both that AI agents of the Claude
family wrote them, and that no human mathematician has reviewed them.

Records:
- **P1** = G. Fabbian, *A bounded-depth positivity inequality for zeta-zero configurations and simple critical zeros under
  a narrow-box hypothesis*, doi:10.5281/zenodo.22778066, v1.0, dated 13 Sep, published 15 Sep 2026. The files are the
  preprint PDF, a source zip and `Reproducibility_v1.zip`, so **the code and records are public**.
- **P2** = G. Fabbian, *Structural barriers for band-limited and low-order certificate methods for simple zeros of the
  Riemann zeta function*, record 23198632, concept DOI 10.5281/zenodo.23198631, v1.0, published 7 Oct 2026. Its files
  include `reproducibility.zip` (4.3 MB), so **the code is public**.
- The same author has further records that I did **not** read beyond the abstract:
  - 23027645 (29 Sep): an optimised Lamzouri/Gram-type inequality S(Z) ≥ x + (|Z|−x)²/N_m, giving "simple or real" in
    short intervals conditional on Wang 2609.07918. It is not a CGdL-type kernel and not relevant to 0.6776.
  - 23025218: MT constant 0.6725 for weight-2 newforms of prime level, on harmonic average, without GRH.
  - 22839423 and 23027727 (Li coefficients), 23027282 (Möbius in short intervals) and 23782485 (Mertens product / Robin).

## 1. Normalisation (both papers)
- **Configuration.** A configuration is a finite multiset Z ⊂ ℂ with multiplicities m_z, invariant under conjugation with
  multiplicities.
  - |Z| = Σ m_z.
  - κ(Z) = #{real points of multiplicity 1}.
  - **depth** dep(Z) = max |Im z|.
  - E_Z(a) = Σ m_z e(za), with e(t) = e^{2πit}.
- **Zeta dictionary (P1 Lemma 4.1).** Take z_ρ = (γ − i(β−½)) log T/(2π) for the zeros with T < γ ≤ 2T.
  - The unit is one mean spacing, and the depth of a zero is |β−½| log T/2π.
  - κ(Z_T) = N₀ˢ(T,2T].
  - Without any hypothesis, dep(Z_T) < log T/4π.
- **Kernel class G (P1 Def 3.3).** g : ℝ → ℝ is even, supported in [−1,1], and its distributional g'' is a finite signed
  measure. Then g is Lipschitz and g(±1) = 0.
  - V(g) = g(0) + 2∫₀¹ a g(a) da, and the **value** is 2 − V(g).
  - S_g(Z) = ∫_{−1}^{1} g |E_Z|² = Σ_{z,s} m_z m_s R_g(z−s), with R_g = ĝ entire.
  - Φ_g(Z) = S_g(Z) − (2|Z| − κ(Z)).
- **(C)_Y[g]** is the statement Φ_g(Z) ≥ 0 for every configuration with dep(Z) ≤ Y (P1 Def 3.6).
- **Admissible extension (P1 Def 3.4).** q is even, continuous, piecewise linear with nodes in Z/40, and supp q ⊂ [−3,3].
  It satisfies (Q1) q ≥ 0 on [−1,1] and q ≤ 0 off it; (Q2) q(±1) = 0; (Q3) ∫q = 1; (Q4) R_full = q̂ ≥ 0. Then g = q·1_{[−1,1]}.
  - OB(x) = ∫_{|a|>1} |q| e(xa) and U = OB(0).
  - Dictionary with h3: g ↔ r₁, q ↔ r, R_full ↔ K, R_g ↔ K₁, ∫q = 1 ↔ K(0) = 1.

## 2. P1: what is proved
**Theorem A (bounded-depth positivity; computer-assisted).** g_A is an explicit even piecewise-linear kernel with nodes
k/40. It is the restriction of q_A with exact rational node values N_k·10⁻¹⁸ (Appendix A, k ≤ 120, support [−3,3]). For it,
∫_{−1}^{1} g_A |E_Z|² ≥ 2|Z| − κ(Z) **for every configuration Z with dep(Z) ≤ 33/200**.
- There is no restriction on the number of points, their positions or multiplicities, the mixture of depths in (0, 33/200],
  or the local density.
- This is the inequality behind the RH arguments of Montgomery and CGdL, extended to off-line points of depth up to 0.165.
- The value is 2 − V(g_A) = 0.679204126438574037586… (exact rational, Prop 3.5(c)).
- Kernel data:
  - g_A(0) = 1.00386651; U = 0.0145095.
  - 16π²m₂ = 23.4188, the self-term coefficient of a pair (self ≈ 23.4 y²).
  - R_full vanishes exactly on 40ℤ∖{0}.
  - C(x) > 9·10⁻⁷ certified (Prop 3.5(b)).

**Theorem B (transfer).** Let g ∈ G and Y > 0, and assume (C)_Y[g]. Assume also that every zero with T < γ ≤ 2T satisfies
|β−½| log T ≤ 2πY for all T ≥ T₀. Then N₀ˢ(T,2T] ≥ (2−V(g)) N(T,2T] − C_g T.
- C_g depends only on Lip g, ‖g‖_∞, ‖g‖₁ and ‖g''‖_TV.
- **Remark 4.7(b): if (C)_Y[g] holds for every Y, the bound is unconditional.**
- Corollary 4.9 sums dyadic windows to get liminf N₀ˢ(T)/N(T) ≥ 2 − V(g).

Inputs to Theorem B: the functional equation, Riemann–von Mangoldt, Landau's explicit formula, Montgomery–Vaughan, the PNT
and the Korobov–Vinogradov zero-free region. It uses **no density estimate, no RH and no edge buffer**. The steps are:
- **Exact removal of Montgomery's weight** (Lemma 4.2, after Lamzouri 2609.02882 Lemma 3.2):
  ĝ(ζ) = w(u)[ĝ(ζ) − ĝ''(ζ)/(4L²)], where w = 4/(4−u²) and ζ = iuL/2π. This uses only |Re u| < 1.
- So S_g(Z_T) = (TL/2π)[∫F_W g − (1/4L²)∫F_W dg''] (Lemma 4.3).
- The window form factor is F_W(α) = T^{−2α}L + α + O(1/L + T^{α−1}) on [0,1] (Prop 4.7), proved directly for the window
  (T,2T] in Lemmas 4.4–4.6.

Corollary C: under WB(33/200) (all zeros in (T,2T] within 0.165 mean spacings, for every large T), the proportion is at
least 0.6792041264. The hypothesis WB implies Lindelöf and a zero-free half-plane (Section 10.2).

**What the computer covers (Sections 7–9, Table 1).** Lemma 5.2 (reduction to separated configurations), Lemma 5.4 (the
collapse identity), Prop 6.2 (certificate lemma) and Theorem 9.1 are proved by hand.
- **Collapse identity.** Each pair x±iy is compared with a real double at x, with parameters t(y), u(y) and a PD kernel Ψ₁:
  Φ(Z) = OB(ν + Σ t_p δ_{x_p}) + Σ u_p u_{p'} Ψ₁ + E*(Z).
  - E* is a sum of the one-body terms σ(n_j) = n² − (2n − 1[n=1]) and self(y), plus two-body terms R_full (real–real),
    V^{(y)} (real–pair) and W_{yy'} (pair–pair).
- **Certificate.** There are 680 cells (diameter ≤ w = 27/50, inside |r| > w) and fixed charges λ_k(y) = s L_{ik}. Each
  pair pays for the negative lobes of V and W in its cells out of its own self term (C0–C2).
  - The near field (|d| ≤ w) is positive and is redistributed to crowded cells (K1, K2).
  - A lone triple point is paid for by σ(3) = 3 (K3).
- **Certified computations.** The finite list (E1)–(E11) has 503,946 checks, 26 depth boxes and 351 box pairs, verified in
  Arb ball arithmetic at 200 bits. A separately written second certifier reports "ALL_OK". Both are AI-written and share
  the data and definitions.
  - The smallest margin in (C0) is 0.521%.
  - Only the combinatorial core of an alternative proof of Prop 6.2 is in Lean, for abstract data (Remark 6.4).
    **Theorem A is not formally verified.**

**Limits that he states (Section 10.4).**
- (a) With this certificate format, numerical LP finds no certificate at depth 0.17. The format with t ≡ 2, u ≡ 0 stops
  near 0.13. Any format that puts each negative lobe in one cell of diameter ≤ w is impossible beyond about 0.27.
- **Conjecture 10.3:** (C)_Y[g_A] holds for every Y, i.e. 0.6792 unconditionally. This is open. About 10⁵ floating-point
  searches (depth up to 1, and up to 3 for a nearby kernel) found no counterexample.
- (c) Kernels of value up to 0.6793163 exist, but Theorem A has not been proved for them.

## 3. P2: the barrier theorems, with the exact classes excluded
Except where noted, everything is for g = g_A and for **common-depth** configurations D(y), i.e. reals plus pairs x_p ± iy
all at one depth y. Two definitions are used throughout:
- **Comb deficit** ε_c := 4(g(0) − 1) = 0.0155 for g_A. Lemma 2.2: the comb C_N = {k ± iy : |k| ≤ N} has
  Φ(C_N)/(2N+1) → ε_c for every y > 0.
- **Collapse kernels** (2.1): V_t, W_t and self_t, with u ≡ 0.

| result | excluded class (exact) | witness | status |
|---|---|---|---|
| **Thm 3.4** | **Homogeneous two-point certificates M_y.** These are even symmetric 2×2 Λ with (i) Λ ≤ H = g·1_I·ww^T, w = (1, 2c_y)^T, in Loewner order; (ii) Λ̂₀₀, Λ̂₀y, Λ̂yy ≥ 0 on ℝ; (iii) Λ̂₀₀(0) ≥ 1, Λ̂yy(0) ≥ 4. Such a Λ would prove HOM_y, the fractional-mass version. M_y = ∅ **for every y ∈ [0.055, 0.6]**. | Prop 3.3, fractional chain: unit reals at 0, 2, …, 2N and pairs of mass ε ≈ 0.16 at the odd sites. Remark 3.5, integer version: triples at odd sites and pairs 2j ± iy* with y* = arccosh(3/2)/π = 0.3063. For that one HOM fails but (C) holds, because σ(3) = 3. | certified, 2 implementations |
| Cor 3.8 | Typed two-point (Delsarte) certificates with types r1, r2, r3, P | same | follows from Thm 3.4 |
| Thm 3.9 | Continuous elements of the relaxed class (only N̂₀₀(0) ≥ 1 is used): empty for y ≥ 14/25 | Loewner budget | certified |
| Rem 3.10 | Smoothing certificates (ω, N): excluded by Thm 3.4/3.9. For the relaxed inequality with pairs not charged they fail for y > 0.3062 (Poisson smoothing: y > 0.1276) | | single certification |
| Prop 3.6, 3.7 | Further proofs of Thm 3.4 on [0.085, 0.5] that need (ii) only at one point or at the integers 0..40 | dual matrices | certified |
| **Thm 4.5** | **Fixed-charge two-point data (Def 4.1):** t ∈ [0,2]; PD pair kernel K = ∫cos(2πξx) dc(ξ) with spectrum in [−3,3]; disjoint cells, each inside a unit window J_k = (k−½, k+½], k ≠ 0; fixed charges λ_c ≥ 0. Admissible means (a) K(0) + Σλ ≤ self_t, (b) 2(K − W_t)(d) ≤ λ(d) + λ(−d), (c) −8V_t(d) ≤ λ(d). **There are no such data at y = 27/100 or 3/10.** At y = 3/10 with t ∈ [2/5, 3/5] there are none with spectrum [−10,10] either. Lemma 4.2: P1's certificate is in this class whenever its cells lie in unit windows, Ψ₁ has spectrum in [−3,3] and t ∈ [0,2] (true for P1's design). | Farkas certificates for the necessary conditions (4.1) K(0) + Σ max(s_k, u_k) ≤ self_t and (4.2), the comb row Σ(s_k − (K − W_t)(k)) ≤ ε_c | certified |
| Evidence 4.9 | The same class reaches only about 0.23–0.24 for g_A. A joint LP over kernel nodes and data finds (4.1) **infeasible at y = 0.32 for every admissible kernel with 2 − V ≥ 0.674**; a kernel of value 0.6738 stays feasible up to about 0.31. | dual "fractional star": the first-shell atom at the drifted bottom of W_t | **numerical, not certified** |
| Rem 4.8 | **Not covered:** cells straddling half-integers; configuration-dependent charges; bookkeeping OB(αν + tπ) with α < 1; spectrum outside [−3,3]; t ∉ [0,2] | | |
| **Thm 4.13** | **Block sums of a local kernel (Def 4.10):** Φ_g(Z) = Π + Σ_p v_pᵀ K_p v_p + R, where each block sees the real points and its own pair and **no block sees another pair**, t ∈ [0,2]. Excluded **at every depth y ≥ 0.032**. | Prop 4.11: the comb forces K(∗,∗) ≤ ε_c. Lemma 4.12: one pair with real doubles at X needs K(∗,∗) ≥ −F_t(X), and F_t(X) < −ε_c is certified with 2–4 points | certified |
| Thm 5.2 | **Energy strengthenings** S_g ≥ 2|Z| − κ + θE_W with W ≥ 0, inf_{|x|≤w₀} W > 0, any θ > 0, required at all depths and densities. Remark 5.4: any augmentation growing like s^α, α > 3/2, on clusters of s simple reals is excluded. | j-gons of pairs cancelling every in-band mode of a real cluster | proof |
| **Prop 6.1** | **Removal bounds:** Φ_g(Z) ≥ Φ_g(Z_{≤Y}) − F(Z_{>Y}) for any function F and any Y ≥ 0, for every g ∈ G, g ≢ 0. Not covered: penalties that also depend on the shallow part, and bounded local shallow mass (Rem 6.4). The deficit form Φ ≥ −D n_{>Y} itself is not refuted. | one real point of multiplicity M plus one pair u ± iy with B_y(u) = 2Re R_g(u+iy) < 0. Then Φ(Z_M) − Φ(Z_{≤Y}) = 2M B_y(u) + C_y − 4 → −∞, while Φ(Z_M) > 0 | proof + ball arithmetic |
| Thm 7.1 (Gebendorfer) | Clipped-Gram class C₂₅: value < 0.674034. P2 tightens this to < 0.674033066. | two periodic words | P2 verifies the computation |
| **Thm 8.6** | C₂₅ extended by strict level-3/4 statistics (Σ\|ξ\| < 2) of class (nz), genuine, i.e. level-4 off the pairing planes, with Gaussian/Wick or any permutation-symmetric values: the symmetrised statistics vanish identically and κ < 0.6740331 | phase lemma 8.5 | proof |
| **Thm 8.8** | The same with all (nz) statistics and the Wick numbers t^G: κ < 0.6764851. This needs t_Φ = t^G_Φ, which is established only on the product subrange (Rem 8.2b). | mixture of the four lattices with spacings 1, 1.001, 1.027, 2. A lattice of spacing d ∈ (1,2] is blind to every strict level-3/4 statistic with nonzero frequencies. | ball arithmetic |
| Thm 9.2 | Single-window inertia class: exact class constants, e.g. simple-or-on-line = 0.8876200 = Lamzouri's C₂ | | proof |
| **Prop 9.9** | Single-window certificate s₁ ≥ (2+Δ)N − T₂ + Σ y_i Φ_{F_i}, with closed-range (Σ\|ξ\| ≤ 2) statistics of level ≥ 3 and min\|ξ\| ≥ δ: Δ ≤ c(0) + 2c(½) − 2 = 7.11·10⁻⁴ for the MT window. A cap on the proportion needs v ≤ 0 (Rem 9.10). | real doubles at spacing 2 | proof |
| Prop 10.2, 10.3 | CGG/BHB mollified moments (S₁, S₂) without RH: realisable on n+1 = o(N) off-line pairs; weighted Gram certificates are capped at max(0, 2R_w − N) | | proof |
| Prop 11.1 (positive) | (C) holds for g_A at y ∈ {0.13, 0.2, 0.25, 0.3, 0.4, 0.5} on integer-site configurations with at most one object per site | de Bruijn potential, r ≤ 2 | certified |
| Rem 11.3 | About 10⁵ searches found no Z with Φ_{g_A} < 0. Smallest per-point values: 5.7·10⁻³ with a pair of depth ≥ 0.1 held fixed; 0.09 with depths in [0.4, 1.1] | | numerical |

The escape conditions he lists (Section 11.1):
- (i) Be inhomogeneous in the pair masses, i.e. use that a pair has multiplicity 1. At y ≈ 0.306, also use σ(3).
- (ii) Treat the first neighbour shell exactly: configuration-dependent charges, blocks that see other pairs, or 3-point
  couplings between the nearest windows.
- (iii) Use energies growing ≤ s^{3/2}, or a uniform margin δ|Z|.
- (iv) Use removal penalties that depend on the shallow part.
- (v)–(vii) For the higher-level statistics: zero-frequency or merged-frequency statistics, several windows, support beyond 1,
  constraints on off-line values.

He states explicitly: **"No result here says that (1.1) is false at any depth."**

## 4. Is our route excluded?
Our route: one explicit CGdL-type kernel (h3's k5, value 0.677610, or h5's mixture (1−ε)MT + ε·CGdL, value 0.67585). We
would prove the single configuration inequality for **all** conjugation-symmetric configurations, by:
- a cell/packing argument for single pairs (T1d), and
- an edge/bulk Fourier split for several deep pairs (T1e).

**(a) Zeta side, Lemma Z.** This is prior art; see §5. Fabbian's Theorem B + Remark 4.7(b) is the same reduction, in a
better form: it needs the **T-independent** (C) for g, with no Montgomery-weighted T-kernels.
- Membership in G, for h3's kernel: r₁ = (f∗f̃)·1_{[−1,1]} with r(1) = 0 is even and continuous, and r₁'' is a finite
  measure (r is smooth on (−1,1), with kinks at ±1). So r₁ ∈ G.
- Membership in G, for the mixture: the MT kernel Q₀ ∈ G (P1 §4.7(b)), so the mixture is in G too.
- **Neither kernel is excluded on the zeta side.** We should cite Theorem B rather than re-prove it. h3 should also note
  Fabbian's warning about BGST Thm 1 (see §5).

**(b) The MT part.** Q₀ satisfies (C) at all depths: Lamzouri 2609.02882 Prop 2.1, used in P1 §4.7(b).
- Φ_g is **linear in g** (the target 2|Z| − κ does not depend on g). Hence Φ_mix = (1−ε)Φ_MT + εΦ_C exactly, and h5's
  Lemma T is just Φ_C ≥ −((1−ε)/ε)Φ_MT.
- **Prop 6.1 does not exclude this.** On the removal witness Z_M, both Φ_MT and Φ_C are positive quadratics in M.
- [C] Prop 6.1 **does** kill the lead's suggested split in its removal form: "shallow part by Fabbian's Thm A, deep pairs
  paid by MT slack at a cost depending only on the deep pairs". A valid version must compare Φ_C with Φ_MT
  configuration-wise, including the shallow mass near each deep pair (Remark 6.4(i) leaves exactly this open).

**(c) What the barriers say about the proof of the configuration inequality** [N]/[C]. The barriers are kernel-specific
(g_A), so I evaluated the same witnesses on our kernels (`m3/fabbian_tests.py`; Gauss–Legendre transforms, floating point):

| witness | MT (value 0.672501) | k5 (0.677611) | mix ε=½ (0.675056) |
|---|---|---|---|
| g(0), comb deficit ε_c = 4(g(0)−1) | 1.00613, **+0.0245** | 1.00601, **+0.0240** | 1.00607, +0.0243 |
| fractional chain min_ε D(ε,y) < 0 (Thm 3.4 mechanism) | for y ≥ 0.06 (D = −0.0067 at 0.1, −0.091 at 0.3) | y ≥ 0.055 (−0.0069 at 0.1) | y ≥ 0.06 |
| integer-triple chain 25/2·g(0) − 13 | −0.423 | −0.425 | −0.424 |
| one pair + doubles at ±r: min F₂ vs −ε_c (Thm 4.13 mechanism) | −0.027 at y = 0.05 (< −0.0245) | −0.033 at y = 0.05 (< −0.0240) | −0.030 at y = 0.05 |
| fixed-charge (4.1) with **K = 0 only**: Σ max(s_k,u_k)/self | 1.06 (y = .165), 1.55 (y = .3) | 0.97 (.165), 1.08 (.2) | not run |

How to read the table:
1. **The comb deficit is positive for our kernels**, so the comb does not refute (C) for them. Note that g(0) < 1 would
   make (C) false at every depth y > 0; any new kernel must have g(0) = r(0) ≥ 1.
2. **The MT kernel fails the fractional-chain and block-sum witnesses**, although its inequality (C) is true at all depths
   (Lamzouri). So Thm 3.4 and Thm 4.13 are barriers to *proof classes*, and they also block every LP/Delsarte-type proof
   and every pair-by-pair proof of the *true* MT statement. The MT proof escapes because it uses integrality through
   rank/inertia (Sylvester).
3. **Consequences for T1d (single pair)**: none. A one-pair cell/packing argument with integer multiplicities is
   inhomogeneous, which is allowed. But Thm 4.13 says **it cannot be extended pair by pair**: a sum of one-pair blocks that
   never see another pair fails for y ≥ 0.032 for g_A, and by the [N] row above also for k5 and the mixture. The pairs in
   the comb leave only ε_c ≈ 0.024 per pair.
4. **Consequences for T1e (several pairs)**: "edge part = PD form over pairs + bulk by fixed per-cell charges inside unit
   windows" is **exactly Def 4.1** when the edge form K has spectrum in [1−ε, 1] ⊂ [−3,3] and t ∈ [0,2]. Thm 4.5 and
   Evidence 4.9 then predict failure from about y ≈ 0.24–0.32 for every kernel of value ≥ 0.674. (That evidence is
   numerical and for P1's piecewise-linear kernel class, but our kernels have support ⊂ [−3,3].) To escape, T1e must use
   one or more of:
   - charges that depend on the configuration (first neighbour shell treated exactly);
   - cells straddling half-integers;
   - OB(αν + tπ) with α < 1;
   - t ∉ [0,2], or spectrum outside [−3,3];
   - for the MT component, the rank/inertia argument instead of a cell certificate.
5. Energy (Thm 5.2), clipped-Gram (Sections 7–8) and single-window (Section 9) classes do not apply. Our inequality has no
   clipped trace, no gap pressure and one fixed target (P2 §7.3 says the same of (1.1)).

**Verdict [C].** The route is **not excluded as a statement**. No result of P2 says (C) is false for any kernel at any
depth, and the comb test is passed. It **is** constrained as a proof technique:
- single pairs are fine;
- many pairs need inhomogeneous, configuration-dependent pair–pair bookkeeping (Fabbian's own certificate does this with
  crowding constants, but only to depth 0.165);
- the edge/bulk split must not reduce to fixed per-cell charges.

The most promising escape is to treat the MT part by rank/inertia rather than by cells. That is the one mechanism known to
prove (C) at **all** depths.

## 5. Prior art for "Lemma Z" and the values 0.677610 and 0.67585 (task 2)
- **Lemma Z.** It is prior art: **Fabbian P1, Theorem B + Remark 4.7(b) + Corollary 4.9** (15 Sep 2026), building on the
  counting principle of Goldston–Suriajaya 2511.20059 Thm 3 and the exact weight removal of Lamzouri 2609.02882 Lemma 3.2.
  P2 (W2) restates it. Fabbian's version differs from h3's in three ways:
  - (i) the weight is removed exactly, so the needed inequality is the plain (C)[g], not CI_T with T-kernels;
  - (ii) it works on dyadic windows (T,2T] and sums them;
  - (iii) it does **not** use BGST Thm 1 / Lemma 5 as a black box. He notes (P1 §2.1, §4.7(c)) that **the proof of BGST
    2306.04799 Thm 1 as printed was corrected in BGST arXiv:2501.14545v3 §3, the error credited to Garunkštis–Paliulionytė**,
    and that the route through BGST Lemmas 1, 3, 4 needs a prime-side mean value with an added O(x log x) term.

  So h3's T1f should cite Fabbian Thm B, or 2501.14545v3, not 2306.04799 as printed. Devine (Zenodo 22066689, (26)–(27))
  has a Hilbert-space analogue of the collapse identity; I did not read it.
- **0.677610 (h3's 5-term trig kernel f on [−3/4,3/4], r = f∗f̃).** Not found anywhere. I searched:
  - the web, for "0.677610", "0.67761" and "0.6776";
  - Zenodo, with full-text queries for "Chirre" + zeta (4 hits, all irrelevant), "simple zeros" + zeta since 15 Oct
    (12 hits), and all zeta-zero records 7–10 Nov (about 50 titles);
  - GitHub repository search;
  - riemannzeta.fun (record 0.6736388767, Knausgård, 9 Nov; no entry above 0.674 and none of CGdL type);
  - the arXiv API (math.NT, simple zeros / critical line / pair correlation, newest first);
  - Hexagon (q = zeta, zeros, simple zeros, critical line).

  The nearest objects are Fabbian's g_A (0.6792041, bounded depth only) and his remark that kernels of value up to
  0.6793163 exist without a theorem. **The number 0.677610 and an explicit smooth trig-square CGdL kernel appear in none
  of them.** As an RH theorem it is weaker than CGdL's 0.6792. It is new only as an explicit closed-form kernel, and
  unconditionally only if the configuration inequality is proved.
- **0.67585 (mixture ½MT + ½CGdL).** Not found. No source mixes the MT and CGdL kernels. The idea "MT satisfies (C) at all
  depths, so mix it in" is implicit in P1 §4.7(b): Q₀ ∈ G and is valid for all configurations. But Fabbian does not
  state the mixture.
- **Repositories cited in Knausgård 2610.08965 §1.** These are ainta, AMTOPA, tawanerguo-cn, trmdy, Zhaoyi-Tian, Oliverds321
  (D'Souza), GettysburgResearch PR 888, RakitinD, and the Zenodo records of Gebendorfer ×3, Singh, Schäfer, Shi ×2, Chandru,
  Santibáñez-Leal, Devine and Yang–Yang. All are Gram/rank-trace refinements with values 0.6730–0.6736, or claims
  conditional on box/density hypotheses (Devine: 0.6792 under a vanishing box or BOX-DENS). **None proves a CGdL-type
  inequality off the line.** I did **not** re-open every repository today; I rely on h2's reads of them plus the titles and
  abstracts in Knausgård's bibliography and in P2 Table 2.

## 6. What I could not read
- X/Twitter and Lean Zulip: not reachable.
- rStation: the paper list has no dates and the post bodies did not load.
- GitHub API reads of repositories not attached to this session are refused. I used raw.githubusercontent.com for READMEs.
- Fabbian's records 23027645 and 23025218: abstract only.
- Devine 22066689: not read.
