# Referee report on h5/T3_families.md (family average via the rank–trace device)   [h1]

Refereed version: `h5/T3_families.md` as of 02:01 (`h5/T3_family_theorem.md` had not landed when this was written).
Verdict in one line: **no step is broken; the constant K = 3/(2𝔖) is correctly derived from the primary source; the numbers
0.7523 / 0.8761 are reproduced independently; the result is still a sketch at steps (c)-localisation, (e) and the Gevrey tail.
Free improvement found: Preissmann's constant gives K = 2.7453 and 0.763 / 0.881.**

## 1. The large-sieve constant, re-derived from the source
* [K, checked against the scan] Montgomery–Vaughan, "The large sieve", Mathematika 20 (1973) 119–134, Theorem 1, (1.6):
  `Σ_r |S(x_r)|² (N + (3/2)δ_r^{-1})^{-1} ≤ Σ|a_n|²`, `δ_r = min_{s≠r}‖x_r−x_s‖`; and their (2.6) (proof of Cor. 1):
  `Σ_{q≤z} (N + (3/2)qz)^{-1} Σ*_{a mod q} |S(a/q)|² ≤ Σ|a_n|²`, using `‖a/q−a'/q'‖ ≥ 1/(qq') ≥ 1/(qz)`.
  (The TME-EMT wiki attributes the weighted form to MV "Hilbert's inequality" 1974 Thm 1; the Hilbert-inequality lemma is there,
  the large-sieve statement is (1.6) of the 1973 paper. Either way the constant is 3/2 and the direction is as used.)
* [K] Primitive characters: `Σ*_{χ mod q}|Σ_n c_nχ(n)|² ≤ (φ(q)/q) Σ*_{a mod q}|S(a/q)|²` (Gallagher; e.g. Montgomery, Topics, Thm 6.2 proof).
* [R] Hence, for any set 𝒬 ⊂ (Q₀, Q] of moduli and coefficients supported on an interval of length N:
  `Σ_{q∈𝒬} φ(q)^{-1} Σ*_χ |Σ c_nχ(n)|² ≤ Σ_q q^{-1}Σ*_a|S(a/q)|² ≤ max_{q∈𝒬}(N/q + (3/2)Q)·Σ|c_n|² ≤ ((3/2)Q + N/Q₀) Σ|c_n|²`.
  (Restricting the Farey set to q ∈ 𝒬 only increases the δ's, so (2.6) applies verbatim.) With `Q₀ = Q^{1−ε}`, `N ≤ Q^λ`, `λ<2−ε`:
  `≤ (3/2)Q(1+o(1))‖c‖²`. Diagonal value for prime-power-supported c: `Σ_q φ*(q)/φ(q)·Σ_{(n,q)=1}|c_n|² = 𝔖Q(1+o(1))‖c‖²`,
  `𝔖 = Π_p(1−p^{-2}−p^{-3}) = 0.4791453` (CLLR (2.3)). Ratio `K = 3/(2𝔖) = 3.1306`. **Correct.**
* [K] **Improvement.** Preissmann (Enseign. Math. 30 (1984) 95–113) proves the weighted inequality with
  `c = (1 + (2/3)(6/5)^{1/2})^{1/2} = 1.3154…` in place of 3/2 (quoted on the TME-EMT wiki; I have not read the paper itself).
  Then `K = 2.7453` and [N] the window QP gives **0.7618 (λ=1.4), 0.7631 (λ→2)** simple-on-line, **0.8816** distinct.
  The conjectured c = 1 would give K = 2.087.
* Constant choice of weights: with `ω_χ = w_q/φ(q)` the bound is `(3/2)Q·max w / (𝔖 Σ w φ*/φ)`-type, minimised by constant `w`;
  so within MV/Preissmann nothing is gained by reweighting q. A-F's 1.263 needs a genuinely sharper Farey large sieve.

## 2. Independent numerical check [N]
Own QP (active set for ψ ≥ 0, `F̃ = α` on [0,1], `Kα` on (1,λ]): K = 3.1306: 0.7434 (λ=1.2), 0.7521 (1.4), 0.7532 (1.6), 0.7533 (1.99).
Agrees with h5's 0.7523. (My earlier `support_curve.py` solved the unconstrained QP; at large Kλ the constraint ψ ≥ 0 is active.)

## 3. Transfer of the device, step by step
| step | claim | verdict |
|---|---|---|
| per-χ zero side | `v_{1−ρ̄} = conj v_ρ`, `G̃_χ` real symmetric, P ⪰ 0, pair = (1,1) block | **OK** [R]: zero ρ of L(s,χ) ⇒ 1−ρ̄ zero of the *same* L(s,χ) (functional equation + conjugation), so the pairing stays inside one χ; φ̂ real on ℝ. Complex χ causes no problem (zeros not symmetric under γ ↦ −γ is irrelevant). |
| per-χ chain | `s₁ ≥ 4trG̃ − 2N(I') − ‖G̃‖²` holds for each χ with whatever value `tr G̃_χ` has | **OK** [R]: uses only `tr P₁ ≤ s₁` (real vectors, truncation only decreases), `rank P₁ ≤ s₁`, `n₊(Q') ≤ b`, `s₁+2b ≤ N(I')`. No lower bound on the individual trace is needed. |
| summation | weights ω_χ ≥ 0, linear | **OK**. |
| (b) trace from the prime side | `Σω tr G̃ = Σω N_χ(I) (1+o(1))` | **OK in principle, and necessary.** I confirm h5's warning: with T = (log Q)^B an off-line zero within D₀ of an edge can change `v_ρ·v_ρ` by up to X^{1/2} ≫ N_χ, so [AF] Prop 4.2 fails per χ and `tr G̃_χ` may be far from N_χ, even negative, for individual χ. Only the family sum is controlled: `tr(G̃+Ẽ)` is *exactly* `(aL²)^{-1}Σ_k∫φ̂(τ−α_k)²ν_χ`, μ-part = `N_χ(I)+O(L log)` (RvM for χ), prime part = `Σ_n a_nχ(n)·c_n` with `|c_n| ≲ 1/(L·min(log n, L−log n))`; after averaging, `|Σ_q φ(q)^{-1}Σ*_χ χ(n)| ≤ Σ_{d|n−1} φ(d)Σ_{q≡0(d)}1/φ(q) ≪ τ(n−1)log Q`, total `≪ X^{1/2}(log)^2 = o(Q)` iff λ<2. Trivial bound `Σ_{n≤X}Λ(n)τ(n−1) ≪ X log X` suffices (no Brun–Titchmarsh needed). **Gap:** n = 1 is absent, but the term must be written with the pole-free ν_χ and with the truncation k∈[0,d) (geometric sum over k) — not yet written. |
| tail Ẽ | Gevrey taper, D₀ = (log Q)³ | **Plausible, unproved here.** Needs `|φ̂(x+iy)| ≤ e^{L|y|/2}·exp(−c|x|^{1/2})`-type decay beating X^{1/2}=e^{λ log Q/2} at |x| ≥ D₀, i.e. D₀^{1/2} ≫ log Q: D₀=(log Q)³ is enough; and D₀ = o(T) so that N(I')−N(I) = o(N). Real zeros near s=1 (Siegel) have Re γ = 0 ∉ I' and sit in Ẽ: harmless. Uniformity in q of `N_χ(t,t+1) ≪ log(q(|t|+2))` is classical. |
| (c) 𝓜[P,P], 1<α | `≤ K·diagonal` | **OK** [R given §1]. Remark: no per-scale localisation is needed for this range: apply §1 to `c_n(y) = b_n Î(y−log n)` with N = X; then `∫ g(y)|Î(y−log n)|²dy = 2πT g(log n)(1+O(1/TL))`. |
| (c) 𝓜[P,P], α ≤ 1−ε | diagonal dominance | **OK with the stated localisation**: split `c(y) = near + far`; far has relative ℓ²-mass O(1/(Tδ)); `(A+B)² ≤ (1+η)A²+(1+1/η)B²` and bound B by §1. Near part, n,m ≤ Q^{1−ε/2}: `|Σ*_χ χ(n)χ̄(m)| ≤ Σ_{d|(q,n−m)}φ(d)`, averaged `≪ τ(n−m) log Q`, total off-diagonal `≪ Q^{1−ε/2+o(1)}‖c‖²` = o(Q‖c‖²). The strip 1−ε<α≤1 is charged Kα; its cost → 0 with ε. **Needs writing with explicit ε, δ, η.** |
| (d) sum-frequency and μ×P terms | negligible | **Plausible**; same first-moment mechanism as (b). Not checked line by line. |
| (e) reduction errors E₁, E₂ | replace sup|ν|² by family mean square | **OK idea**; by `2|νν'| ≤ |ν|²+|ν'|²` and the pointwise-in-τ large sieve the family average of |P_χ(τ)|² is ≪ L², giving E₁ ≪ L⁵log L, E₂ ≪ L⁶ log L per unit family weight against a main term ≍ T L⁵. So T ≫ L log L suffices (h5 asks T ≫ L² log L: safe). |
| normalisation | units of log Q; log q ∈ [(1−ε)log Q, log Q]; T = (log Q)^B | **OK**, costs O(ε) + O(log log Q/log Q). |

## 4. Attempts to break it
1. *Edge zeros* (off-line, within D₀ of T or 2T): break the per-χ trace, not the family trace (see (b)). They also make individual
   `‖G̃_χ‖²` huge, but that is included in the prime-side evaluation of the family sum. No contradiction.
2. *Small conductors*: excluded by q > Q^{1−ε}; in §1 the factor N/q is where they would hurt.
3. *Imprimitive characters*: not in the family; Gallagher's inequality is for primitive χ only and is used only there.
4. *Is K·α the right shape for α slightly above 1?* Yes for an upper bound; but note F̃ jumps from α to Kα at α=1, and the
   window optimum responds by thinning ψ near the ends — the QP handles it.
5. *Dimension*: for λ>1 the matrix has dimension λN_χ > N_χ; nothing in the chain needs d ≤ N.
6. *A hidden use of GRH*: none found. The only arithmetic inputs are the explicit formula, RvM for χ, MV/Preissmann, and trivial
   divisor bounds.

## 5. What remains before [R]
(i) write (b) with the truncated grid sum; (ii) Gevrey tail lemma for L(s,χ) with q-uniform constants; (iii) explicit ε,δ,η
bookkeeping in (c); (iv) cite Preissmann and state the theorem with K = c/𝔖 for any admissible weighted-large-sieve constant c
(3/2 proved in MV73; 1.3154 Preissmann). Prior art to cite and compare: D'Souza (0.7235 hypothesis-free, 0.9059 with density
theorems; per h2, unrefereed) — h5's 0.7523/0.763 is between the two and uses no density estimate.
