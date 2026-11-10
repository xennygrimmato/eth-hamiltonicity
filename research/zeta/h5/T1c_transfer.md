# T1c: where positive-definiteness enters, and two transfer lemmas for Conjecture D   [h5]

Context: h3/T1_extremal.md §5–6 and h3/T1b_depth_lemma.md (the periodic model, the exact depth identity, D false for general
certificates, target D_CGdL). This note does not repeat h3's numerics. Scripts are in `h5/t1c/`.

## 1. Where the proof needs the Gram / PD structure (paper and Lean)
The zero side never uses positivity of a kernel as such. It uses a **matrix realisation** of the second moment: a Hermitian
G whose Frobenius norm *is* the certificate's quadratic form and which is a congruence of the zero configuration:
G = Σ_ρ m_ρ v_ρ v_ρᵀ, with v_ρ = (φ̂(γ_ρ − α_k))_k. This structure is used in three places.
1. **Realisation, ‖G‖²_F = Σ m m′ K(γ − γ′) with K = Φ², Φ = (φ²)^.** This is the identification of the zero-side Gram matrix
   with the explicit-formula matrix: `Hypotheses/GzGp.lean: ZeroConfig.Gz_eq_Gp` and the Poisson–Gabor identity `PoissonSq`. It
   forces the kernel class r = ψ⋆ψ with ψ = φ² ≥ 0. Mixtures of such certificates (averaging the scalar inequalities) give
   r = Σ θ_i ψ_i⋆ψ_i, i.e. diagonal sums of a **completely positive** matrix W = Σ θ_i ψ_i ψ_iᵀ, with ψ_i ≥ 0 and Σψ_i = 1.
2. **On-line points are PSD rank one.** This needs v_ρ ∈ ℝ^d, i.e. φ even and real. Lean: `ZeroSide/RankTraceMult.lean`
   (`Pmat = W Wᴴ`, `Pmat_posSemidef`), `ZeroSide/Mult.lean: blockP_eq_Pmat`, and ‖v‖² ≤ 1 from `PoissonSq`.
3. **Off-line pairs are blocks of signature (1,1), and the Frobenius norm is spectral.** Inertia under pull-back (`LinAlg/Inertia.lean`,
   `Sylvester.lean`) gives n₊(Q′) ≤ s₂ + p. Lemma R (`rank_trace_mult`, `rank_trace_mult_k_le`) is a statement about eigenvalues:
   it uses that ‖·‖_F is unitarily invariant, through von Neumann's trace inequality (`LinAlg/VonNeumann.lean`).
   In the k_c form, a pair is charged exactly like a double: c² = 4 at c = 2. That is why the rank–trace certificate never
   distinguishes pairs from doubles.

**Consequence [R, trivial].** Suppose a certificate (c₀, a) (data form s₁/N ≥ c₀ − Σ a_l|Ŝ_l|²) is coefficientwise dominated
by a mixture of rank–trace certificates, i.e. c₀ ≤ c₀^G and a ≥ a^G. Then it is valid unconditionally. But its value is
≤ 2 − min R = the MT value, by convexity of R. So any certificate above MT, the CGdL and ceiling duals included, is **outside**
the class that the paper's zero side can handle verbatim. A new zero-side inequality is unavoidable, and the most one can hope
for from the existing machinery is a *perturbative* statement: the Gram certificate plus a small non-Gram correction, paid for by
slack in Lemma R. That is the content of §2 and §3.

## 2. Lemma S (the rank–trace slack is at least 2 tr Q′₋) [R]
**Lemma S.** In the setting of A–F §6 (P₁ = simple on-line part, Q′ = Ĝ − P₁), and in the periodic model exactly,
  N₀ˢ ≥ rank P₁ ≥ 4 tr Ĝ − 2N − ‖Ĝ‖²_F + 2 tr (Q′)₋,
where (Q′)₋ is the negative part of Q′.
*Proof.* This is A–F Lemma 3.2 with one discarded term kept. In the step
Σ_{i≤r}(2(p_i−n_i)−1) + Σ_{i>r} n_i² ≥ 2tr P − r − 4tr Q₋, the authors use −2n_i ≥ −4n_i for i ≤ r (slack 2n_i) and
n_i² ≥ −4n_i for i > r (slack n_i² + 4n_i ≥ 2n_i). So the slack is ≥ 2Σ_i n_i = 2 tr Q₋. The remaining steps of A–F §6
(tr P₁ + 2(s₂+p) ≤ N) are unchanged. ∎
**Isolated pair.** A pair t ± iy contributes the block B = u wᴴ + w uᴴ, with u = D^{1/2}e_z and w = D^{1/2}e_{z̄}.
Its eigenvalues are Re⟨u,w⟩ ± ‖u‖‖w‖ = 1 ± ‖u‖‖w‖. So tr B₋ = ‖u‖‖w‖ − 1 = 2y² Var_ψ(ω) + O(y⁴) (Cauchy–Schwarz).
For a pair whose negative direction is not absorbed by other blocks, the rank–trace certificate therefore has a built-in
**quadratic depth penalty** of 4y² Var_ψ(ω)/N per pair (s₁/N units).
[N] (`t1c/lemma_s_check.py`, N = 8, periodic MT-type window, p_MT(8) = 0.67728 as in h3):
- the inequality holds on 3000 random configurations with up to 3 pairs; minimum surplus 0.051 ≥ 0;
- the isolated-pair formula matches: tr B₋ = 6.05e−4, 1.52e−2, 6.16e−2 at y = 0.01, 0.05, 0.1, against 2y²Var = 6.05e−4, 1.51e−2, 6.05e−2;
- per pair this is ≈ 1.5y² in s₁/N units, the same order as h3's measured penalty 1.8y² for the ceiling dual.
So the "≈ 14y² per pair" that h3 observes is not mysterious: the Gram part of any near-Gram certificate already carries a y² charge
for each unabsorbed pair.


**Lemma S′ (full Q′-slack) [R].** Keeping *all* the Q′-terms discarded in Lemma R (the steps n_i² ≥ −4n_i and q² ≥ 4q − 4) gives
  N₀ˢ ≥ 4trĜ − 2N − ‖Ĝ‖² + f(Q′),
  f(Q′) := 2 tr Q′₋ + Σ_{λ>0}(λ − 2)² + 4(b − n₊(Q′)) = ‖Q′₊‖² − 4b − 2 tr Q′₋ ≥ 0,
where b = s₂ + p and the sum runs over the positive eigenvalues of Q′. (The second form uses tr Q′ = 2b: each double and each
pair block has trace 2 by Poisson.) So the Gram certificate is tight only if Q′ has exactly b positive eigenvalues, all ≈ 2, and
Q′₋ ≈ 0.
*Absorption does not help the adversary.* A double placed within ≈ √2·y of a pair can cancel the pair's negative eigenvalue
(tr Q′₋ → 0). But then the two positive eigenvalues of the 2-block are ≈ 4 and ≈ 0, which costs (4−2)² + (0−2)² ≈ 8, i.e. 8/N in s₁/N
units. **Conjecture G (Gram depth lemma) [C]:** f(Q′(Z)) ≥ c(ψ)·Σ_pairs min(y_p², 1) − (something controlled by
f(Q′(Z⁰)) and the collapsed defect). This is the natural first statement to prove, since it concerns only the MT/Gram certificate.

## 3. Lemma T (mixture transfer: Gram certificate plus a non-PD perturbation, with quantitative loss) [R]
Let C_G be a rank–trace certificate, unconditionally valid with defect δ_G(Z) := s₁/N − c₀^G + Σa^G_l|Ŝ_l|² ≥ 0 for every
configuration Z (pairs allowed). By Lemma S, δ_G(Z) ≥ (2/N) tr Q′₋(Z). Let C be any data-form certificate with defect δ_C. Define
  τ(C) := sup over configurations Z with δ_C(Z) < 0 of (−δ_C(Z))/δ_G(Z)   (τ := 0 if C is unconditionally valid).
**Lemma T.** For 0 ≤ ε ≤ 1/(1+τ(C)), the certificate C_ε := (1−ε)C_G + εC is unconditionally valid. Its kernel is
a^G + ε(a − a^G), i.e. a Gram kernel plus an ε-small, possibly non-PD perturbation. Its value is val_G + ε(val_C − val_G).
*Proof.* The defect is affine in the certificate: δ_{C_ε} = (1−ε)δ_G + εδ_C. Where δ_C ≥ 0 this is ≥ 0. Elsewhere
δ_C ≥ −τδ_G, so δ_{C_ε} ≥ (1 − ε(1+τ))δ_G ≥ 0. ∎
**Why this matters.**
- *Any* finite τ for C = (periodic or continuum) CGdL yields an unconditional improvement over MT:
  proportion ≥ 0.6725 + (0.6792 − 0.6725)/(1+τ).
- That beats the current record 0.6736 iff τ < 5.1, and reaches 0.6792 iff τ = 0 (= Conjecture D_CGdL).
- So D_CGdL can be replaced by the **weaker, quantitative** target δ_CGdL(Z) ≥ −τ δ_MT(Z). With Lemma S, a sufficient target is
  δ_CGdL(Z) ≥ −(2τ/N) tr Q′₋(Z): the CGdL certificate may fail, but only by an amount that the MT certificate's pair penalty
  can pay for.
- Locally (one pair at depth y → 0 against a background, h3 §1): δ_C(Z) − δ_C(Z⁰) = 2y²D₂^C(t) + O(y⁴) and
  δ_G(Z) ≥ 4y²Var_ψ(ω)/N + δ_G(Z⁰). Hence, for unabsorbed pairs at configurations with δ_C(Z⁰) = 0,
  τ_loc ≤ N·max(0, −D₂^C(t))/(2Var_ψ(ω)), which is finite.
- The only way τ can be infinite is a configuration where δ_C < 0 while δ_G = 0. That requires Z to be *exactly extremal*
  for the MT certificate, including tr Q′₋ = 0: every pair's negative direction is absorbed by positive blocks
  (e.g. a double within √2·y of the pair).
**Precise lemma to prove next (D_τ) [C].** There is an absolute τ < 5 such that, for every conjugation-symmetric configuration,
δ_CGdL(Z) ≥ −τ δ_MT(Z). In the periodic model this is a finite-dimensional inequality between two explicit quadratic-plus-
integer functionals. It is equivalent to the unconditional validity of the mixture C_{1/(1+τ)}, so it can be tested with
h3's `t1b_check_cert.py` on the mixed certificate. That is a stronger test than D itself, because the mixture has less slack.

## 4. Break attempts (targeted, not random) [N]  (`t1c/attack.py`)
Method: (1) build a pool of on-line local minima of the reduced cost rc = s₁/N − c₀ + Σa|Ŝ|² over all compositions, from
random, near-lattice and **clustered-double** starts; (2) at each near-extremal configuration compute h3's exact local criterion
D₂(t) for every double; (3) convert every double, **every pair of doubles** (h3's counterexample mechanism: adjacent deep pairs)
and all doubles to off-line pairs, at depths 0.02/0.1/0.3/0.6, and re-optimise all positions and depths (L-BFGS-B with analytic
gradient). Certificates are h3's files, used read-only.

| certificate | N | value | on-line min rc | best rc with pairs (depths) | min D₂ at near-extremal doubles | verdict |
|---|---|---|---|---|---|---|
| **validation:** h3 random certificate (known to fail) | 8 | — | −4.9e−8 | **−4.04e−4** (2 pairs, depth 0.0992) | **−0.0205** | violation recovered exactly as in h3 §2 |
| periodic CGdL (`cgdl_8`) | 8 | 0.683095 | +1.477e−3 | +1.449e−3 (depth 0, 0) | +0.698 | no violation; pairs collapse |
| ceiling dual (`cg_8_rh`) | 8 | 0.685996 | −2.6e−8 | −2.6e−8 (depth 0) | +0.875 | no violation; pairs collapse |
| periodic CGdL (`cgdl_12`) | 12 | 0.680978 | +1.529e−3 | +1.514e−3 (depth 0, 0) | +0.317 | no violation; pairs collapse |
| ceiling dual (`cgfast_16_rh`) | 16 | 0.682867 | −2.9e−8 | −2.9e−8 (depth 0) | +0.428 | no violation; pairs collapse |

Reading.
- The targeted search *does* find the known counterexample, at the right depth, and it flags it by D₂ < 0. So it has teeth.
- Against CGdL and the ceiling duals, every pair-containing optimum collapses to depth 0. At every near-extremal on-line
  configuration, every double has D₂ > 0 with margin (0.3–0.9). By h3's identity this means no shallow pair can beat its
  double there.
- I found no counterexample to Conjecture D (ceiling dual, N = 8, 16) or to D_CGdL (N = 8, 12).
- Not exact: the pricing is local optimisation from structured starts. An exact certificate would need interval
  branch-and-bound in up to 2N real variables. I estimated it as infeasible here (≥ 1e10 boxes at N = 8 for the required accuracy 1e−4).

**Lemma T on the counterexample certificate** (`t1c/tau_example.py`). At a violating configuration of h3's random certificate
(rc = −1.2e−4 after Nelder–Mead polishing), the periodic MT defect is +1.38e−2. So τ ≳ 0.009 there, and the mixture with only 1%
MT weight already repairs that configuration. The failure mechanism (two adjacent shallow pairs) is cheap to pay for with Gram slack.
This supports pursuing D_τ (§3) rather than D itself.

## 5. What to do next
1. Prove Conjecture G (Gram depth lemma, §2). It is pure linear algebra on Q′ = Σ 2uu* + Σ(uwᴴ + wuᴴ) and needs no knowledge
   of CGdL.
2. Then prove D_τ for some τ < 5 in the periodic model, by combining h3's exact identity
   δ_C(Z) − δ_C(Z⁰) = 4Σa(C−1)(C+1+Re H) with δ_MT(Z) ≥ f(Q′)/N. The dangerous region is Re H_l < −2 (anti-phase background).
   The question is whether f(Q′) is large there.
3. For ζ: Lemma T and Lemma S transfer verbatim, because the MT certificate is the paper's. What remains is the zero-side
   statement D_τ for configurations of complex points with the paper's localisation. The prime side needs only r ∈ {MT, CGdL₁},
   both supported in [−1,1] (h3 §4).
