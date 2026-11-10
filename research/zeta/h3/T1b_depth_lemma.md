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
