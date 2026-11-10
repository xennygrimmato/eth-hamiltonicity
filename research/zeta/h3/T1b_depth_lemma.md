# T1b: the depth lemma (Conjecture D) — status (h3)

Scripts (in h3/): `t1b_cg_fast.py` (batched column generation for the ceiling), `t1b_cgdl_periodic.py` (the CGdL certificate in
the periodic model), `t1b_check_cert.py` (adversarial test of any certificate against off-line pairs),
`t1b_random_cert.py` and `t1b_counterex_check.py` (test of general transfer, plus a counterexample), `t1b_local_criterion.py`.
Model: as in T1_extremal.md §6 (N-periodic, total multiplicity N, off-line pair t ± iy has frequency weight 2cosh(ω_l y),
ω_l = 2πl/N). Data-form certificate: s₁/N ≥ c₀ − Σ_{0<l<N} a_l |Ŝ(l)|², with a_l ≥ 0. Write F := Σ a_l|Ŝ_l|² = Σ_{b,b'} m_b m_b' k(t_b − t_b'),
where k(x) = Σ_l a_l cos(ω_l x).

## 0. Answers to the lead's framing questions
- **Same object as the paper's PairCeiling and Knausgård's Thm 7.7?** Yes, for the RH part. The model is the one of
  `LawN256.lean`: N-periodic laws of marked configurations, marks m ∈ {1,2}, rows 256·S(j) = j, i.e. E|Ŝ(j)|² = j for 0<j<N.
  The ceiling value is min E[#simple]/N. At N = 256 the paper's value is 0.6818287 and Knausgård's is 0.6818277. My runs are
  the same programme at small N: 0.685996 (N=8), 0.683689 (N=12), **0.682867 (N=16, converged, fast CG)**. The values decrease
  towards 0.6818. The new ingredient is the extra mark "off-line pair", with weight 2cosh(ω_l y).
- **Does proving D give a theorem in one step? No — two caveats.**
  (1) D is **false for general certificates** (§2). It must use properties of the specific certificate.
  (2) Even under RH, nobody has proved that the **ceiling-optimal** dual is valid on real configurations. The paper and
  Knausgård give only the primal side, i.e. a law. What *is* proved on real configurations (under RH) is the **CGdL** certificate, 0.6792.
  So the right one-step target is **D for the CGdL certificate** (§3). It would give 0.6792 unconditionally, against the record 0.6736.
  Encouragingly, the ceiling dual and the CGdL certificate have nearly the same shape (§3).

## 1. [R] Exact depth-variation identity and the local criterion
Take a configuration with a double at t, and the other points b with weights w_b(l) (on-line: m_b; pairs: 2cosh(ω_l y_b)).
Put H_l := Σ_b w_b(l) e^{iω_l(t−t_b)}. Replace the double by the pair t ± iy, and write C_l = cosh(ω_l y). Then exactly

  F(y) − F(0) = 4 Σ_l a_l (C_l − 1)(C_l + 1 + Re H_l) = 2y² D₂(t) + O(y⁴),

  D₂(t) = Σ_l a_l ω_l² (2 + Re H_l) = −2k''(0) − (μ_bg * k'')(t) = 2|k''(0)| − ¼ ∂²_t F,

where μ_bg is the measure of the other points and ∂²_t F is the second derivative of F under moving the double.
*Proof.* |A + 2Cu|² − |A + 2u|² = 4(C² − 1) + 4(C − 1)Re(Āu) with A = Ŝ_l − 2u, and Āu = H_l. Expand cosh, and use
k'' = −Σ a ω² cos. Moving the double gives F = const + 4Σ_b m_b k(t − t_b) + 4k(0), hence ∂²_t F = 4(μ_bg*k'')(t). ∎

**Local criterion.** At an on-line configuration that is stationary for the adversary, a double prefers to go off-line
iff ∂²_t F > 8|k''(0)| there, i.e. iff its potential well is too stiff. A sufficient global condition for one pair, valid for all y,
is Re H_l ≥ −2 for every l with a_l > 0, because then (C−1)(C+1+Re H) ≥ (C−1)² ≥ 0.

## 2. [N] D fails for general nonnegative certificates (counterexample, N = 8)
Take a = (0.00102, 0.027434, 0.00522, 0.009571, 0.002453, 0.005684, 0.00029), a random positive certificate. Set c₀ = min over
**all on-line** configurations of s₁/N + F = 0.0715276, attained at 4 doubles at t ≈ (0, 1.0039, 6.0101, 7.0139). The grid
search at step 0.05 plus polishing confirms it (`t1b_counterex_check.py`). So the certificate is valid and tight on real configurations.
With off-line pairs, min F = **0.0711238**: doubles at 0 and 6.999, and pairs at 0.9754 and 1.9764 of depth 0.0991. So the
certificate is violated by **4.0·10⁻⁴**.
This is explained by §1: at the on-line minimiser, D₂ = −0.0205 for two of the doubles and +0.163 for the other two
(the finite-difference check agrees to 5 digits). **So "every certificate valid on real configurations stays valid
unconditionally" is false.** Conjecture D has to be stated for a specific certificate.
(This is a single random trial; the other 8 random trials completed by then showed no violation.)

## 3. [N] The CGdL certificate in the periodic model: nonnegative weights, and it survives off-line pairs
Periodic CGdL: take K(θ) = Σ_{|l|≤M} r_l e^{ilθ} ≥ 0 with r_l ≤ 0 for N ≤ |l| ≤ M, normalised K(0) = 1. On real configurations,
s₁ ≥ 2N − N* and N* ≤ Σ_l r_l|Ŝ_l|² ≤ r₀N² + 2Σ_{0<l<N} r_l|Ŝ_l|², the second step dropping |l| ≥ N because those terms are ≤ 0.
This gives the data form c₀ = 2 − N r₀, a_l = 2r_l/N. LP optimum, with M = 4N:

| N | 8 | 12 | 16 | 32 | ∞ (CGdL20) |
|---|---|---|---|---|---|
| periodic CGdL value | 0.683095 | 0.680978 | 0.680239 | 0.679533 | 0.6792 |
| same LP, support < N (MT/CCLM class) | 0.677283 | 0.674628 | 0.673696 | 0.672803 | 0.6725 |
| r_l ≥ 0 for |l| < N (so a_l ≥ 0)? | yes | yes | yes | yes | — |
| adversarial min reduced cost, pairs allowed (depth ≤ 1) | +1.48e−3 | +1.42e−3 | +0.94e−3 | +0.92e−3 | — |
| depth of the worst pair-containing configuration | 0 | 0 | 0 | 0 | — |

Every minimum is ≥ 0, and every worst case collapses to depth 0. The certificate is not tight on-line in this model:
its own on-line slack is about 1.3·10⁻³. But in every run the best configuration with pairs was a depth-0 configuration,
i.e. an on-line one.
Forced depth (N = 16): y_min = 0.03 → margin 2.5e−3; y_min = 0.1 → 8.2e−3; y_min = 0.5 (depth range up to 3) → **+0.457**. Depth is penalised, and deep pairs very strongly.
**Shape:** normalised by a₁, the ceiling-optimal dual at N = 16 has
a/a₁ = 1, .952, .881, .808, .734, .649, .564, .482, .402, .322, .248, .182, .122, .070, .031. The CGdL data form has
1, .961, .903, .832, .751, .668, .585, .505, .426, .348, .272, .200, .135, .079, .033 (a₁ = 0.00813 vs 0.00772). **The
ceiling dual is a slightly reweighted CGdL certificate.**
Ceiling dual at N = 16 against pairs (`t1b_check_cert.py cgfast_16_rh.npz`, 4×400 starts): the on-line min reduced cost is
−2.9e−8, i.e. tight. With pairs the min is **+1.24e−4, attained at depths (0,0,0)**. So D holds numerically for the converged N = 16 ceiling
certificate too. That is the closed-form pattern: r* ≈ r_CGdL·1_{[−1,1]}.

## 4. The precise target (Conjecture D_CGdL) and what passing to ζ needs
**Conjecture D_CGdL [C].** Let r be CGdL-admissible: even, continuous, r̂ ≥ 0, r ≤ 0 on |α| ≥ 1, and r ≥ 0 on [−1,1] (true for the
extremal and its periodic analogues). Put r₁ = r·1_{[−1,1]}. Then for every locally finite, conjugation-symmetric configuration
with the paper's localisation,
  s₁ ≥ 2N − (1/r̂(0)) Σ_{ρ,ρ'} m_ρ m_ρ' r̂₁(γ_ρ − γ_ρ') − o(N).
Under RH this is CGdL's argument. Unconditionally the intermediate step Σ r̂ ≥ N*·r̂(0) is false (h4 Prop 2), but the final
inequality survives every test in §3. Mechanically, the dropped tail −Σ_{|α|>1} r|Ŝ|² is exactly what grows like cosh² for
deep pairs. Combined with the unconditional form factor on [−1,1] (BGST24 Thm 1; A–F Thm HS, extended by linearity from windows to
continuous r₁ supported in [−1,1]), D_CGdL gives **N₀ˢ/N ≥ 0.6792 unconditionally**.
Any admissible r with value > 0.6736 would already be a record.

What changes in the paper / Lean (cf. h5/T5_lean_map.md §2):
- The zero side must be replaced: `LinAlg` Lemma R and `ZeroSide/RankTraceMult` (P = Σ m v v*, ‖v‖ ≤ 1) and the seam
  inequality. They use positive-definiteness through the Gram/Poisson structure, with window φ² ≥ 0. A non-PD kernel r̂₁ has no
  Gram realisation, so a genuinely new zero-side inequality is needed. **This is all of D_CGdL.**
- The prime side is reusable. `count_certificate` takes κ abstractly. The needed number is r₁(0) + ∫|α| r₁, an exact asymptotic
  for a signed combination of window terms; `ThmD` gives the window asymptotics, and linearity plus approximation of r₁ by
  windows' differences does the rest.
- Localisation: the factorised-weight positivity (T1_extremal §5(ii)) is what makes the dropped tail ≥ 0. It must be set up
  with the same localisation as `Tail*`.

## 4b. [R] Reduction of D_CGdL to an exact identity: the negative tail cancels
Periodic model. Let X = B ∪ {t ± iy} with B on-line (m_b ∈ {1,2}), N*(X) := Σ_B m_b² + 4 (= 2N − s₁), and
Φ_data(X) := Σ_{|l|<N} r_l |Ŝ_l(X)|². Put K₁(z) := Σ_{|l|<N} r_l e^{iω_l z} (the truncated kernel), C_l = cosh(ω_l y), and
τ := Σ_{|l|≥N} |r_l| ≥ 0, so that Σ_{|l|<N} r_l = 1 + τ. Then exactly
  Φ_data(X) − N*(X) = [Φ_data(B) − N*(B)] + 4(Σ_{|l|<N} r_l C_l² − 1) + 4 Σ_b m_b Re K₁(t − t_b + iy).
The first bracket s_B is ≥ 0 by the RH-type CGdL argument applied to the real configuration B. The second term is ≥ 4τ ≥ 0
and grows like cosh². Only the truncated kernel K₁, with r_l ≥ 0 for |l| < N, appears. The negative CGdL tail
that kills h4's intermediate inequality has cancelled exactly against the tail energy dropped in the data form.
**So single-pair D_CGdL ⟺ for every on-line B: inf_{t,y} [4(Σ r_l C_l² − 1) + 4(μ_B * Re K₁(·+iy))(t)] ≥ −s_B.** This is a
one-body problem in the background field μ_B * Re K₁. At y = 0 it is the RH statement for B plus a double (true).
Several pairs add pair–pair terms 2Re[K₁(x + i(y+y')) + K₁(x + i(y−y'))] in the same way.
Natural route: Re K₁(x+iy) − K₁(x) = Σ r_l(C_l − 1)cos(ω_l x) =: β_y(x) is a localised kernel, of size O(y²) and decaying like K₁''.
Its sum over B is bounded by local masses, and local excess mass is paid quadratically in s_B, since K ≥ c > 0 near 0.
The constants decide whether this closes. A crude Cauchy–Schwarz over frequencies loses a factor √N, so the argument must
be done in position space.

## 5. Proof plan, and what I could and could not do
1. One pair against an on-line background, small y: §1 reduces it to D₂(t) ≥ 0 at the adversary's critical configurations.
   For the CGdL kernel this needs a bound on Σ_b m_b (k''(t − t_b))_+ ≤ 2|k''(0)|, where k = r̂₁. The hard part is clustered
   backgrounds. They have large F, so this must be combined with the on-line slack: a **coupled** argument, not done.
2. Large y: the self-term 4Σ a sinh²(ω y) dominates, since the cross term is linear in C and the self term quadratic.
   Making this quantitative needs |H_l| ≤ (C_l + 1), the sufficient condition of §1. Not done in general.
3. Several pairs: the pair–pair cross terms involve C·C'. The N = 8 counterexample in §2 uses exactly two adjacent deep pairs,
   so this is where a proof can fail for bad kernels.
I have no proof of D_CGdL. What is rigorous: the §1 identity and criterion, and the elementary sufficient condition. What is
numerical: §2 and §3.

---------------------------------------------------------------------------------------------------------------
# Round 2: toward D_CGdL in the continuum (after the lead's second message)

New scripts: `t1b_kernel_study.py` (continuum-like CGdL kernel from the periodic LP at N = 64, M = 256), `t1b_onebody.py`,
`t1b_onebody2.py`, `t1b_onebody3.py` (one-body minimisation over free real backgrounds in R), `t1b_lattice_bg.py`, `t1b_cell_criterion.py`,
`t1b_cell_R3.py`, `t1b_cell_R4.py` (sufficient cell criteria), `t1b_robust_cgdl.py` (pointwise-robust LP), `t1b_cluster_test.py`, `t1b_adjacent_deep.py`.

## 6. [R] Lemma T (tail cancellation) and reconciliation with h4 Prop 2
Let r be CGdL-admissible, K = r̂ ≥ 0, r₁ = r·1_{[−1,1]}, r₂ = −r·1_{|α|>1} ≥ 0, so that K₁ = r̂₁ = K + r̂₂. Let X be any finite
conjugation-symmetric configuration (complex points z, multiplicities m), and S_X(α) = Σ_z m e^{2πiαz}. Symmetry gives
S_X(−α) = conj S_X(α). Hence, exactly,

  Σ_{z,z'} m m' K₁(z − z') = Σ_{z,z'} m m' K(z − z') + ∫_{|α|>1} r₂(α) |S_X(α)|² dα.        (T)

**h4 Prop 2** says K(2iy) → −∞, so Σ K ≥ K(0)·N* (the CGdL *intermediate* inequality) fails for one deep pair. That is correct and it
does apply to Σ K. **It does not apply to Σ K₁** (the CGdL *final*, data-form inequality). The second term of (T) contains, for
the pair's own block, ∫ r₂ · 4cosh²(2παy) dα, which is exactly −2·(negative tail part of K(2iy)) + 2∫r₂. The pair's self-block in
Σ K₁ is 2K₁(0) + 2K₁(2iy) with K₁(2iy) = ∫_{−1}^{1} r(α)cosh(4παy)dα ≥ K₁(0) > 0, because r ≥ 0 on [−1,1].
So the only correct unconditional target is Σ K₁ ≥ N*. Its single-pair form is the exact identity of §4b.

## 7. [R] Lemma C (comparison with doubles) and the one-body inequality (*)
Write G_η(x) := Re K₁(x + iη) − K₁(x) + K(x) = K(x) + β_η(x). For X = B ∪ {t ± iy}, with B on-line and X₀ the configuration where the pair
is replaced by a double at t:
 Σ_X K₁ − N*_X ≥ LHS(B,y) := 2(K₁(2iy) − K₁(0)) + 4Σ_b m_b G_y(t − t_b) + Σ_{b≠b'} m_b m_b' K(t_b − t_b').        (*)
*Proof.* Σ_X K₁ = Σ_{X₀} K₁ + [2(K₁(2iy) − K₁(0)) + 4Σ m_b β_y]. Then Σ_{X₀}K₁ = Σ_{X₀}K + T(X₀) ≥ N*_{X₀} + (off-diagonal K-energy of X₀),
with N*_{X₀} = N*_X and K(0) = 1. The double–background part of that energy is 4Σ m_b K(t − t_b). ∎
So **single-pair D_CGdL ⟸ LHS(B,y) ≥ 0 for every real background B (masses ≤ 2, any positions) and every y ≥ 0.** This is a
statement about one real line and two explicit kernels.
Multi-pair version, also [R] by the same computation: add Σ_{p≠q, ordered} 2[G_{y_p+y_q} + G_{|y_p−y_q|}](t_p − t_q) and one self-term per pair.

## 8. [N] Kernel facts (near-continuum CGdL, N = 64; value 0.679358)
- r(α) at α = 0, .1, …, 1 is 1.004, .972, .877, .764, .620, .499, .382, .250, .148, .054, 0. It is ≥ 0 on [−1,1] and ≤ 0 beyond (−0.020 at
  α = 1.1), with τ = ∫_{|α|>1}|r| = 0.0141.
- min_R K₁ = −0.0048 (K₁ is not ≥ 0; K is ≥ 0 by the LP). K has (near-)zeros at x ≈ 1.048, 1.935, 2.082, 2.65, 2.93, 3.02, 3.19, …
  There K₁''(x)/|K₁''(0)| = +0.312, +0.051, +0.048, −0.018, +0.016, +0.018, +0.008, … (K₁''(0) = −5.846).
- min_x Re K₁(x+iη): −0.0049 (η = .02), −0.010 (.1), −0.040 (.2), −0.113 (.3), −0.49 (.5), −6.9 (1.0), attained near x ≈ 1 → 0.63.
  Relative to the self term K₁(2iη) this ratio is −0.5% to −4.6%.

## 9. [N] One-body inequality (*) holds in the near-continuum, with margin
- **Free-background minimisation** (`t1b_onebody2.py`, `t1b_onebody3.py`, up to 24 points of mass 1 or 2 in [−15,15], multistart Adam).
  min LHS/self(y) is 0.30 (y = .005–.02), 0.28 (.05), 0.23 (.1), 0.21 (.15), 0.20 (.2), 0.25 (.3), 0.49 (.5), 0.76 (.8), 0.96 (1.2, 8 points).
  The minimisers are doubles placed at the near-zeros of K (±1.04, ±2.08, ±3.1, ±4.1, …). That is exactly the "stiff well" mechanism,
  and it never reaches 0.
- **Lattice-of-doubles family**: much costlier (ratio ≥ 0.36), because the mutual K-energy is not zero.
- **Rigorous-style sufficient criterion R4** (`t1b_cell_R4.py`). Cover {G_y < 0} ∩ [−15.5, 15.5] by its connected components C
  (diameter ≤ 0.68, so K is decreasing on [0, diam]). In C, with worst depth g_C and κ_C = K(diam C), any mass M ≤ 2 contributes ≥ −8g_C,
  and M ≥ 2 contributes ≥ κ_C(M² − 2M) − 4g_C M ([R] packing lemma: Σ m² ≤ 2M). Everything else is ≥ 0. Hence (*) holds at depth y
  if R4(y) := Σ_C h_C / self(y) < 1.
  Computed: R4 = 0.975 (y=.01), .842 (.02), .837 (.05), .850 (.1), .850 (.2), .794 (.3), .684 (.4), .728 (.5), .813 (.6), .866 (.7), .879 (.8),
  .773 (1.0), .625 (1.2), .404 (1.5), .050 (2.0), .0033 (2.5), .0002 (3.0). **So R4 < 1 on [0.01, 3]**, and large y is
  asymptotically safe: the cluster gain is ~e^{4πy}y^{−2k−2}, against a self term ~e^{4πy}y^{−k−1}.
  For y < 0.01, R4 → ≈1.1–1.3, because the crude bound lets every near-zero of K hold a free double. Restoring the inter-cell
  K-energy (R2, `t1b_cell_criterion.py`) gives 0.70 at y = .005 and 0.65 at y = .01. In the limit y → 0 the criterion becomes a
  finite difference-set problem: max Σ_{j∈S} K₁''(x_j)_+ over sets S of zeros of K with S − S ⊂ Z(K) ∪ {0}, which must be < |K₁''(0)|.
  Numerically it is ≈ 0.70|K₁''(0)| (S = {±1.048}, plus small additions).
- **Pointwise route is dead**: requiring G_η ≥ 0 for all x (`t1b_robust_cgdl.py`) costs the value: 0.6795 → 0.597 (Y = 0.1) → 0.268 (Y = 0.25).
  Packing/charging is necessary.

## 10. [N] Several pairs, deep pairs, clusters: no violation found
- Periodic N = 32, depths forced ≥ 0.3 (≤ 3): min reduced cost +0.066 (worst: one pair at the minimal depth). N = 16, depths ≥ 0.5: +0.457.
- Explicit adjacent-deep family (`t1b_adjacent_deep.py`, N = 32): k = 1…8 pairs at common depth y ∈ [0.2, 2] and spacing
  d ∈ {½, ¾, 1, 3/2} (d = ½ cancels the α = 1 edge term), with simple points elsewhere, then local optimisation.
  **Every run flowed to all depths 0**; worst +6.8e−4 > 0.
- Deep pair plus clustered on-line background (`t1b_cluster_test.py`, N = 32, y ∈ [0.8, 2.5], clusters up to mass 16 at the best
  distance ≈ 0.6–0.72): reduced cost +7.9, +565, +4.7e4, +4.3e6, +1.4e9. The self term wins.
So the §2 counterexample mechanism (stiff well, D₂ < 0) does **not** occur for the CGdL kernel at the adversary's optimum.
The relevant stiffness sup is the y → 0 difference-set quantity max_S Σ_{j∈S} K₁''(x_j)_+ ≈ 0.70|K₁''(0)|. The threshold is |K₁''(0)|.
I therefore did not need to compute a "constrained" unconditional CGdL optimum: the unconstrained one passes.

## 11. ζ-side statement (what replaces rank–trace) and the prime side
**Zero-side lemma needed (Lemma Z) [C].** Let Ω be holomorphic in |Im| ≤ ½ (raw units), with Ω(z̄) = conj Ω(z) and Ω ≥ 0 on R.
Take Montgomery's Ω_t(γ) = 2/(1 + (t − γ)²), so that ∫Ω_t(γ)Ω_t(γ')dt ∝ w(γ − γ') = 4/(4 + (γ − γ')²). For every finite
conjugation-symmetric multiset Z,
  Σ_{ρ,ρ'∈Z} m m' Ω(γ_ρ)Ω(γ_ρ') K₁((γ_ρ − γ_ρ')L/2π) ≥ Σ_{on-line, distinct} m²Ω² + Σ_{pairs} 4|Ω(γ)|² − o(Σ m|Ω|²).
Apply it to Z(T) = {0 < Re γ ≤ T}, which is conjugation-symmetric, with Ω = Ω_t, and integrate over t ∈ R. The left side becomes
(T log T/2π)∫ r₁(α)F_T(α)dα, where F_T is Montgomery's form factor over **all complex zeros**. The right side becomes the
w-weighted N*, with w(0) per on-line point and ∫|Ω_t(γ)|²dt ≥ w(0) per off-line point.
- **Prime side**: BGST24 Thm 1 gives F_T(α) = (1+o(1))T^{−2|α|}log T + |α| + o(1) uniformly on [−1,1] for complex zeros, and F_T ≥ 0.
  Because r₁ is continuous on [−1,1] with r₁(±1) = 0, ∫ r₁F_T = r₁(0) + ∫|α|r₁ + o(1), by uniform convergence plus the δ-like
  peak. No windows or Gram matrices are needed, so linearity is trivial in this formulation.
  The A–F Thm HS route (windows ψ*ψ) would need r₁ approximated by window differences in sup norm, which is also fine but unnecessary.
  Status [K]: this rests on the uniformity in BGST Thm 1 up to |α| = 1. I did not check that uniformity from the paper.
- **Edge buffer**: Arias de Reyna 2610.24612 footnote 1 (on his p. 15) says the paper's choice U = √T for the buffer I' makes the
  boundary-zero contribution U√T log T ≍ N, too large; he takes U = T^θ, θ < ½. That issue belongs to the Gram-grid tail lemma
  (e^{L/2} = √T amplification of off-line zeros near the window edge). **In the Montgomery-weight formulation above there is no
  grid and no buffer.** The sum is over the sharply truncated, symmetric Z(T), and positivity of the tail term in (T) survives truncation
  because (T) holds for any finite symmetric configuration. What needs care instead is Lemma Z's error term for raw-deep zeros
  (|β − ½| ≫ 1/L), where Ω_t(γ) and Ω_t(γ̄) differ by O(1) relatively. There the margins are exponential (§9 at y ≥ 2), so a crude bound
  should do. Not written.
- **Lean**: replace `LinAlg` Lemma R, `ZeroSide/RankTraceMult` and the seam inequality by Lemma Z. `count_certificate` is reusable with
  κ = r₁(0) + ∫|α|r₁. The prime-side package changes from `TracesBoundsD` to a BGST-type form-factor statement, which is not in the
  repository as far as h5's map shows.

## 12. Status and split
Proved [R]: Lemma T, Lemma C (one pair and several pairs), the packing lemma, the local criterion (§1), and the counterexample
mechanism (§2). Numerical [N], with floating-point kernels from a periodic N = 64 LP: (*) holds for all real backgrounds at sampled
y ∈ [0.005, 3], via a free search and via the sufficient criteria R4 (y ≥ 0.01) and R2 (y ≤ 0.01). No violation of the full
certificate with any number of pairs or clusters. Not done: rigorous kernel (continuum r with interval bounds), continuity in y,
the tail |x| > 15.5, the y → 0 difference-set lemma, the multi-pair proof, and Lemma Z's weight errors.
Proposed board subtasks: T1c (rigorous continuum CGdL kernel: r, K, K₁, zeros of K, interval bounds), T1d (single-pair proof:
R4 on [0.01, 3] with interval arithmetic and y-Lipschitz bounds, the small-y difference-set lemma, y > 3 asymptotics), T1e (multi-pair:
extend R4 to pair–pair terms G_{y_p ± y_q}), T1f (ζ write-up of Lemma Z plus BGST uniformity check).
