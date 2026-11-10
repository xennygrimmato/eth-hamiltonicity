# T1: the extremal problem behind 0.6725 / 0.8362 (h3)

Scripts: `h3/t1_window_qp.py` (window QP, support dependence, B-model; output `t1_window_qp.out`),
`h3/t1_ceiling_cg.py` (periodic-model ceiling by column generation, RH vs unconditional; outputs `cg_*.out`).
Source: paper-v5-draft18.tex, §2.2–2.3, Lemma 3.2 (rank–trace), Lemma 5.x `lem:Rpsi`, Thm `thm:HS`, §7.2.

## 1. Exact statement of the extremal problem

Data that the proof uses (bandwidth one, i.e. X = T/2π, supp(φ*φ) ⊂ [−L, L]):
- tr G̃ = (1+o(1)) N, with each simple on-line zero contributing ≤ 1 to tr P₁ (Poisson–Gabor, Lemma 2.1);
- ‖G̃‖²_HS = (R(ψ)+o(1)) N (Thm HS), where ψ = φ²(L·) is the window;
- block structure: P₁ ⪰ 0 with rank ≤ s₁; n₊(G̃ − P₁) ≤ s₂ + p; s₁ + 2s₂ + 2p ≤ N.

Certificates: N₀ˢ ≥ (2 − R(ψ))N and N_d ≥ ½(3 − R(ψ))N, where

  R(ψ) = [∫ψ² + ∬|u−v| ψ(u)ψ(v) du dv] / (∫ψ)²,  ψ ≥ 0 even on [−½, ½].

In form-factor language: with r = ψ*ψ (supp ⊂ [−1,1], r̂ = ψ̂² ≥ 0) and F(α) = δ(α) + |α| on [−1,1],
R(ψ) = ∫ r dF / ∫ r. The extremal problem is

  (EP)  minimise R(ψ) over admissible windows ψ.

What makes ψ admissible. The kernel that the matrix puts on pairs of zeros is
⟨v_ρ, v_ρ'⟩ = L·(|φ|²)^(γ−γ'). Being a Gram kernel, it is positive definite on R, so (Bochner) the window
ψ = |φ|² must be ≥ 0. This holds for every complex φ, and for every compression of W
to any family of modulated copies of a fixed φ. Stacking several windows (V_ρ = (v_ρ¹, …, v_ρᴶ)) only adds their
kernels, giving the window Σ|φ_j|². So "a single compression + Lemma 3.2" means exactly (EP) over ψ ≥ 0.

## 2. [R] Montgomery–Taylor is the unique optimum of (EP), even with no sign condition

**Proposition 1.** For every real ψ ∈ L²[−½,½] with ∫ψ ≠ 0, R(ψ) ≥ c_MT⁻¹ = ½ + (1/√2)cot(1/√2) = 1.3274992963…,
and equality holds iff ψ ∝ cos(√2 u). Hence 2 − c_MT⁻¹ = 0.6725007037… and ½(3 − c_MT⁻¹) = 0.8362503518… are optimal for
the certificates 2 − R(ψ) and ½(3 − R(ψ)) (both are decreasing in R).

*Proof.* Let A be the operator with kernel δ(u−v) + |u−v| on [−½,½]. The paper (proof of Lemma `lem:Rpsi`) shows Aψ_MT ≡ G₀
(a constant), where ψ_MT = cos(√2 u) and G₀ = cos(1/√2) + (1/√2)sin(1/√2). Scale ψ so that ∫ψ = ∫ψ_MT, and set η = ψ − ψ_MT,
so that ∫η = 0. Then ⟨ψ,Aψ⟩ = ⟨ψ_MT,Aψ_MT⟩ + 2G₀∫η + ⟨η,Aη⟩ = ⟨ψ_MT,Aψ_MT⟩ + ⟨η,Aη⟩.
Put H(u) = ∫_{−½}^{u} η. Then H(±½) = 0, and integrating by parts twice gives ∬|u−v|η(u)η(v) = −2∫H². So
⟨η,Aη⟩ = ∫H'² − 2∫H² ≥ (π² − 2)∫H² ≥ 0 (Wirtinger with Dirichlet conditions on an interval of length 1), with equality iff η = 0. ∎

This proves the CCLM17 Cor. 14 statement used in the paper, directly and for the class needed. It also gives:

**Proposition 1'.** (Support c; data F = δ + |α| on [−c, c]; window on [−c/2, c/2].) For c < π/√2 the optimum is
again cos(√2 u), now on [−c/2, c/2], with R_diag(c) = c/2 + (1/√2)cot(c/√2). The proof is the same: Wirtinger on an interval of length c needs π²/c² > 2.
This covers the paper's λ < 1 remark (the flat window gives 1/λ + λ/3 ≥ R_diag(λ) > c_MT⁻¹). At c = 1,
d(2 − R_diag)/dc = ½(csc²(1/√2) − 1) = 0.6849.

## 3. [N] Numerical reproduction and support dependence
(see §3 table below, filled from t1_window_qp.out)

## 4. [R] What an averaged bound on F just beyond α = 1 would give

Let c > 1. Use a window ψ ≥ 0 on [−c/2, c/2]. Then r = ψ*ψ is supported on [−c, c]. For 1 < |α| < c,
r(α) ≤ ‖ψ‖²_∞ (c − |α|), so ∫_{1<|α|<c} r ≤ ‖ψ‖²_∞ (c−1)². This is **second order** in c − 1. The gain from the
wider support, on the other hand, is **first order**: slope 0.6849 (Prop. 1').

**Lemma 2.** Suppose that for ψ_c = cos(√2 u)·1_{[−c/2,c/2]} the second moment obeys
‖G̃_{ψ_c}‖²_HS ≤ N·[r(0) + ∫_{|α|≤1}|α| r + B ∫_{1<|α|<c} r]/∫r + o(N) for some B ≥ 1. Equivalently, F ≤ B on (1, c)
on average against r. Then the chain (1.4) gives

  N₀ˢ/N ≥ 2 − R_diag(c) − (B−1)(c−1)²/(2 sin²(c/√2)) − o(1).

*Proof.* R_B(ψ_c) = R_diag(ψ_c) + ∬_{|u−v|>1}(B − |u−v|)ψψ/(∫ψ)². Use (B − |u−v|) ≤ B − 1 and ψ ≤ 1 there, the fact that the region
|u−v| > 1 in [−c/2,c/2]² has area (c−1)², and ∫ψ_c = √2 sin(c/√2). Everything else in the chain is unchanged: Lemma 3.2 and
Prop. `block` do not see the support. ∎

Best value over c, using the cruder constant B in place of B − 1 (rigorous lower bounds; [N] for the maximisation):

| B (bound on averaged F on (1,c)) | 1 | 2 | 3 | 5 | 10 | 100 |
|---|---|---|---|---|---|---|
| simple-on-line ≥ | 0.7429 | 0.7140 | 0.7018 | 0.6909 | 0.6821 | 0.6735 |
| optimal c | 1.24 | 1.13 | 1.09 | 1.06 | 1.03 | 1.003 |

So an averaged bound F ≤ 10 on (1, 1.03) would already beat the bandwidth-one ceiling 0.68185. Any finite B beats
0.6725, and B ≲ 60 beats the current record 0.67364.

Status for ζ [C/K]. Unconditionally only the trivial F(α) ≪ T^{α−1+o(1)} is known on α > 1 (Montgomery–Vaughan
with length X^c > T). Two things block a bound like this:
(a) prime side: the off-diagonal Σ_h Σ_n Λ(n)Λ(n+h) at h ≤ T^{c−1} needs Hardy–Littlewood **in mean**. Upper-bound
sieves give Λ(n)Λ(n+h) ≤ (4+ε)𝔖(h)n, but that converts to F ≲ 3·(#h) ≍ T^{α−1}, not O(1), because the HL main term
**cancels** the diagonal growth;
(b) zero side: the RH Fejér-shift trick ∫F(α)Δ(α−b) ≤ ∫FΔ uses |e^{ib(γ−γ')}| = 1. With off-line zeros of normalised
depth y the weights grow like cosh(2πα y), and F can be exponentially large beyond 1 while F = |α| on [−1,1].
(This matches the periodic model of §6, where an off-line pair has frequency weight 2cosh(2π l y/N).)
So Lemma 2 turns T4 for ζ into the question of an O(1) averaged bound on F just beyond 1. For families
(large sieve, h2/h5) the analogous bound is available, and §3 gives the resulting curve.

## 5. Headroom at bandwidth one: what limits the device, and what does not

Known so far (h2/novelty.md): proved unconditional record 0.673538 (Knausgård 2610.08965) / 0.6736389 (Lean leaderboard), from
local "stability" refinements whose own ceiling is 0.67383. The bandwidth-one ceiling for all two-moment data is
0.68185 (A–F §7.2, Knausgård Cor. 7.9). Under RH, CGdL reach 0.6792.

(i) [R] **A single compression is exhausted by MT.** Gram kernel ⇒ ψ = |φ|² ≥ 0 (Bochner); stacking windows adds kernels;
a congruence S G̃ S* with non-scalar diagonal phases makes the per-zero trace weight oscillate in γ. In Lemma 3.2
that oscillation costs max − mean, because tr P₁ enters with coefficient −2 and needs a uniform per-zero bound.
So "one Weil compression + Lemma 3.2" is exactly (EP), and Prop. 1 closes it at 0.6725.

(ii) [R] **Unconditional positivity of the form factor (factorised weights).** Let w be entire with w(z̄) = conj w(z), and set
S(α) = Σ_ρ m_ρ w(γ_ρ) e^{iαγ_ρ}. Then conj S(α) = Σ_ρ m_ρ w(γ_ρ) e^{−iαγ_ρ} (reindex ρ ↦ 1−ρ̄), so
Σ_{ρ,ρ'} m m' w(γ)w(γ') e^{iα(γ−γ')} = |S(α)|² ≥ 0. Hence Σ_{ρρ'} m m' w w' f̂(γ_ρ'−γ_ρ) ≥ 0 for every f ≥ 0, with no RH
(cf. BGST24 Thm 1; also h1 Prop 2.1, h4). But for the device this only gives **lower** bounds on ‖G̃‖²_HS, because
r = ψ*ψ ≥ 0 off [−1,1]; that is the wrong direction. CGdL's kernels (r ≤ 0 off [−1,1]) need ψ to change sign, and then
r̂(iy) → −∞, so deep off-line pairs break the zero-side inequality (h4 Prop. 2, h1).

(iii) [N] **But the data themselves do not punish off-line zeros** (periodic model, §6). The optimal bandwidth-one dual
certificate (the LP dual of the ceiling problem) stays valid when off-line pairs are allowed. In the adversarial search
the worst pair always collapses to depth 0, i.e. to an on-line double. So the unconditional ceiling equals the RH ceiling
in the model, and the gap 0.6736 → 0.6818 is a gap of **proof technique**, not of information. The optimal
certificate has the form s₁/N ≥ c₀ − Σ_l a_l |Ŝ(l)|², with a_l > 0 decreasing to 0 at l = N. That is a **nonnegative but
not positive-definite** kernel (N = 8: the Fourier series of (a_l) has min −0.0117 at θ = π). It is therefore outside the
rank–trace (PD/Gram) class, and outside the CGdL class too (which needs r < 0 somewhere). The proof target is:

> **Problem T1★.** Prove, for conjugation-symmetric configurations, an inequality s₁ ≥ c₀N − Σ_{ρρ'} m m' K(γ_ρ−γ_ρ')
> with K = r̂, r ≥ 0 supported in [−1,1] but r not of the form ψ*ψ, beating 2 − c_MT⁻¹.

## 6. [N] Periodic model: RH ceiling vs unconditional ceiling (script `t1_ceiling_cg.py`, `t1_dual_check.py`)

Model. An N-periodic configuration with total multiplicity N per period. Its marks are simple on-line (weight 1),
double on-line (weight 2), and off-line pairs t ± iy, which have weight **2cosh(2π l y/N)** at frequency l (from
e^{2πil(t±iy)/N}). Write Ŝ(l) = Σ_a w_a(l)e^{2πilt_a/N}. The rows are E|Ŝ(l)|² = l for 0 < l < N (F(α) = α on (0,1)). This is
the model of `Zeta23/PairCeiling/LawN256.lean`, with pairs added. The paper's rank–trace certificate holds **exactly**
in this model, pairs included: G_{jk} = √(ψ_jψ_k) Ŝ(j−k) is Hermitian, a pair is a signature-(1,1) block, and tr = N exactly.
It reads s₁/N ≥ 2 − N r(0) − (2/N)Σ_{l≥1} r(l)|Ŝ(l)|², with r = ψ*ψ and Σψ = 1 on N frequencies. Column generation:
an LP master over laws, plus pricing by multistart L-BFGS over positions (and depths ≤ 2).

| N | MT-type certificate p_MT(N) (rigorous lower bound) | RH law found (upper bound) | unconditional law found | worst config with pairs vs RH-optimal dual |
|---|---|---|---|---|
| 8  | 0.67728 | 0.685996 | 0.685996 (same dual) | −2.6e−8 (= numerical 0), depth → 0 |
| 12 | 0.67462 | 0.683689 | 0.683733 (42% of law weight on pair-configs, all at depth exactly 0) | −5.4e−6, depth → 0 (an on-line double config the RH pricing had missed) |
| 16 | 0.67370 | 0.682987 (pricing not fully converged) | — | rerun: −7.5e−5 (pairs, depth 0) vs −1.4e−4 (on-line): pairs never beat on-line; depth → 0 |
| 256 | — | 0.681829 (A–F/Knausgård law) | — | — |

Reading. (1) Allowing off-line pairs does not lower the ceiling. Every pair-containing configuration that tries to break the
RH dual collapses to depth 0, i.e. it becomes an on-line double. Intuitively, cosh ≥ 1 only adds high-frequency mass,
and the optimal dual penalises every frequency (all λ_l < 0). (2) The optimal dual has λ_l < 0 for all l, but its kernel
is not positive-definite. As a fraction of the max of its Fourier series, the min is −1.1% at N = 8, −0.6% at N = 12 and −0.5% at N = 16.
So the ceiling certificate is "almost" a Gram (rank–trace) certificate plus a small non-PD correction, and the
correction is where the 0.6725 → 0.6818 headroom lives.
Caveat [C]: the pricing is heuristic. The laws are genuine upper bounds (exact LP feasibility, slack 0), while the claim that pairs
never help is a numerical search result, not a proof.

**Depth penalty [N].** I forced every pair to have depth ≥ y_min and minimised the reduced cost against the RH-optimal dual
(`t1_dual_check.py N R 2.0 y_min`):

| y_min (mean spacings) | 0.02 | 0.05 | 0.1 | 0.2 | 0.5 |
|---|---|---|---|---|---|
| N = 8: min margin (units s₁/N) | 7.1e−4 | 4.4e−3 | 1.82e−2 | 6.9e−2 | 0.95 |
| N = 12 | — | 3.1e−3 | 1.22e−2 | 4.3e−2 | — |

So margin ≈ 1.8y² (N = 8) and ≈ 1.2y² (N = 12), which is **≈ 14 y² per off-line pair in units of zeros**, nearly independent of N.
A pair at depth y is strictly worse for the adversary than a double, with a quadratic penalty. That would be the content of a
"depth lemma" making the RH-ceiling certificate unconditional:

> **Conjecture D [C].** For the ceiling-optimal bandwidth-one certificate (c₀, r), r ≥ 0 on [−1,1]:
> c₀N − Q_r(config) ≤ s₁ holds for conjugation-symmetric configurations. More precisely, the defect of a configuration
> exceeds that of the configuration with every pair t ± iy replaced by an on-line double at t by ≳ Σ_pairs y² (normalised depth).

Proving Conjecture D, or even a version for the simple class "r ≥ 0, K = r̂ with small negative part", is the route from
the record 0.6736 to the ceiling 0.6818. The rank–trace lemma proves it only for K = |ψ̂|² (MT class), and
Knausgård's local stability proves it only for interactions among simple points (cap 0.67383).

## 7. Summary of T1 answers
1. Exact problem: (EP), the min of R(ψ) over ψ ≥ 0 on [−½,½]. Constants reproduced: 1.3274992963 → 0.6725007037 / 0.8362503518 [N].
2. Optimal for its constraints: yes. Prop. 1 [R] gives a unique optimum even without ψ ≥ 0, and §5(i) [R] shows the single-compression class is exactly (EP).
3. Proportion vs support c: R(c) = c/2 + cot(c/√2)/√2 for the diagonal datum (Prop. 1' [R]); for the GUE datum F = min(|α|,1) see h1/support_curve.py, which agrees with my t1_window_qp.py at c ≤ 1.3 (0.7323, 0.7782, 0.7972, 0.8141 at c = 1.1, 1.2, 1.25, 1.3).
   The gain is first order (slope 0.6849) and the cost beyond |α| = 1 is second order. Lemma 2 [R] gives explicit gains from any averaged bound F ≤ B on (1,c).
4. Headroom at bandwidth one: the data allow up to 0.6818 even unconditionally (§6 [N]: off-line pairs never help the adversary,
   with a quadratic depth penalty). The obstruction is proof technique; Conjecture D / Problem T1★ is the precise target.

Next steps I would take: (a) push the column generation to N = 32–64 with a smarter (vectorised, multi-composition) pricer, to
get the continuum dual r* and its negative part K₋. (b) Test Conjecture D in its simplest instance: one pair against a
fixed on-line background, expanding the defect to second order in y and checking the sign of the y² coefficient
analytically, using the cosh expansion and Lemma 3.2's remainder (h1 Prop 1.5).
