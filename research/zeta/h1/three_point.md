# Three-point data: what they give, where they fail, and reconciliation   [h1]

Scripts (all in `h1/`): `ceiling_npoint.py` (LP, now with off-line pairs: `UNC=1 YMAX=…`), `cubic_scalar_lp.py`,
`cubic_model_test.py`, `cubic_model_deep.py`, `cubic_abstract_test.py`; outputs `np_*.out` (on-line), `npu_*.out` (pairs allowed),
`cub_*.out`. Inputs used from others: x1/notebook.md Idea 8, h2 notes 46/50 (Fabbian, Tyagi, Yang–Yang — I have NOT read those
texts; statements about them are h2's), h3's periodic model. Tags as in TEAM.md.

## 0. Bottom line
1. [R] **The cubic trace of the bandwidth-one compression is unconditional data** (agrees with x1 8a and h2 note 50; A–F §7.2(e)
   is too conservative for k = 3), and **for a non-flat window it is not neutral**.
2. [R] **Under RH** (more generally for on-line configurations) there is a one-line cubic certificate
   `N_s ≥ s₁ ≥ 2 tr G² − tr G³ = (2m₂(ψ) − m₃(ψ))N`, with `m₃(ψ) = [∫ψ³ + 3∬ψ(u)²ψ(v)|u−v|]/(∫ψ)³`.
   Flat window: 2/3 (neutral, = x1 8b). `ψ = cos(1.6 s)`: **0.68525**; best 8-parameter window 0.68529; MT: 0.68428.
   This exceeds the two-point ceiling 0.68185 and CGdL's pair-correlation value 0.6792, but not Bui–Heath-Brown's 0.7037, so it is
   not an RH record. (A–F §7.3 already use the third trace under RH with the window cos(8s/5) for distinct zeros.)
3. [N] **Unconditionally the gain does not survive**: the cubic inequality is violated by clusters of deep off-line pairs
   (explicit violations in the periodic model), and in the LP the three-point ceiling falls back toward the two-point ceiling as
   the allowed depth grows: N = 8: 0.7088 (on-line only) → 0.7072 (depth ≤ 0.5) → 0.6933 (≤ 1.0) → 0.6904 (≤ 1.5); two-point: 0.6860.
   [R] Structural reason: with only inertia information the spectrum lives on ℝ and a minorant of degree ≤ 3 must have zero
   cubic coefficient — **odd moments are useless without a lower bound on the spectrum**.
4. So my earlier "+0.02" (ceiling_class.md §4) is an **on-line (RH / bounded-depth) statement**. It is not a route past 0.6819
   unconditionally unless deep off-line clusters can be excluded or neutralised. The even-degree route (x1's fourth moment) is
   the robust one, and its arithmetic input is out of reach (§6).

## 1. Which three-point data are unconditional [K/R]
* Rudnick–Sarnak (Duke 81 (1996); CRAS 1994 note, Thm 1.1 and Remark 2: "directly establishes theorem 1.1, which allows us to
  avoid appealing to the Riemann Hypothesis"; "if h and f are defined for complex arguments and are localized then the sums make
  sense even if we do not assume RH"): n-level sums with smooth localisers `h(γ_j/T)` and `f̂` supported in `Σ|ξ_j| < 2`.
  For n = 3, `ξ₁+ξ₂+ξ₃ = 0` gives `Σ|ξ_j| = 2 max|ξ_j|`: the range is `max|ξ_j| < 1`, the **full bandwidth-one bispectrum**.
* [R] For a single compression with window on `[−½,½]`: `tr G³ = Σ κ(γ₁−γ₂)κ(γ₂−γ₃)κ(γ₃−γ₁)`, frequencies `ξ_j = t_j − t_{j−1}`,
  `t_j ∈ [−½,½]`, so `max|ξ_j| ≤ 1`: inside the range (strictly, up to a null set). For `tr G^k`: `Σ|ξ_j| ≤ 2⌊k/2⌋·λ`, so
  k = 2, 3 need λ < 1 and k = 4, 5 need λ < ½. Model check: Diaconis–Shahshahani gives `E S(a)S(b)conj S(a+b) = 0` for `a+b ≤ N`,
  which covers every term of `tr G³` (`a+b = j−l ≤ N−1`) and not of `tr G⁴`.
* Arithmetic needed: the 3-cycle `n₁n₂ = n₃` with `n₃ ≤ X < T^{1−ε}` and a **smooth** height window (`ĥ` compactly supported:
  `|log(n₁n₂/n₃)| ≤ c/T` forces equality). With the sharp cutoff `[T,2T)` and Montgomery–Vaughan, the off-diagonal is
  `≪ X^{3/2}`, which is where A–F's "X^k ≤ T^{2−ε}" comes from. A smooth cutoff is compatible with the device (congruence by
  `diag(h(α_k/T))^{1/2}` preserves inertia; zeros in the transition zone get weight < 1, an O(1/A) loss for transition T/A).
  The diagonal `Λ(n₁)Λ(n₂)Λ(n₁n₂)` lives on powers of one prime: O(T) against `T L³`. Value: the all-distinct part vanishes,
  `tr G³/N → m₃(ψ)` above (discrete form: `N³Σψ_j³ + 3NΣ_{j≠l}ψ_j²ψ_l|j−l|`, `Σψ = 1`). [R-sketch; the μ-terms are the `ψ³`, `ψ²ψ` parts.]

## 2. The on-line cubic lemma [R]
**Lemma C.** Let `G = P₁ + Q'` with `P₁ ⪰ 0`, and `Q' = Σ_j m_j w_jw_j^*`, `|w_j| = 1`, `m_j ≥ 2`. Then
`tr[G(G−1)²] ≥ tr Q'`, i.e. `tr P₁ ≥ 2 tr G² − tr G³`.
*Proof.* `g(x) = x(x−1)²`, `ĝ := g·1_{x≥1}`: `ĝ` is convex, nondecreasing, `ĝ ≤ g` on `[0,∞)`, `ĝ(0)=0`. Since `G ⪰ 0`:
`tr g(G) ≥ tr ĝ(G)`. Since `G ⪰ Q' ⪰ 0` and ĝ is nondecreasing: `tr ĝ(G) ≥ tr ĝ(Q')` (Weyl monotonicity). The nonzero spectrum of
`Q'` is that of `M^{1/2}ΓM^{1/2}` (Γ the Gram matrix of the `w_j`), whose diagonal is `(m_j)`; by Peierls' inequality for convex ĝ,
`tr ĝ(Q') ≥ Σ_j ĝ(m_j) = Σ m_j(m_j−1)² ≥ Σ m_j = tr Q'`. ∎
With `P₁` = simple on-line part (`tr P₁ ≤ s₁`): **`s₁ ≥ 2 tr G² − tr G³`** for every on-line configuration. Equality for mutually
orthogonal simple and double points; slack `tr[Γ₁(Γ₁−1)²]` for interacting simple points (third order in the overlaps).
[N] 20000 random on-line configurations at N = 12 (clusters, doubles, triples): min defect +0.93 > 0; adversarial L-BFGS
(`cub_*.out`): min defect/N = +0.0034 (N=8), +0.0056 (12), +0.0067 (16), attained by lattices of doubles.
Scalar LP over all cubic `f` with the conditions (S),(M) of `cubic_scalar_lp.py` gives `f(x) = cx − μx(x−x₀)²`, `x₀ = 1.0175`:
0.68551 for cos(1.6 s) — only 3·10⁻⁴ above the `x₀ = 1` form.
**Corollary (RH).** `liminf N_s/N ≥ sup_ψ (2m₂(ψ) − m₃(ψ)) ≥ 0.68529`, from pair and triple correlation alone. Hence the on-line
three-point ceiling is ≥ 0.6853 > 0.68185 rigorously (given §1), consistent with the LP values below.
*This seems to contradict h2's reading of Fabbian ("level-3 statistics gain nothing / ≤ 7·10⁻⁴ in the single-window inertia
class", "blind lattices ⇒ 3-pt ceiling = 0.68185").* Resolution as far as I can see without his text: his class is the
unconditional (inertia) one, where the statement agrees with §3–4 below; on-line, Lemma C applies to any law whatever — blind
lattices included — as soon as its two-point data and its all-distinct bispectrum average agree with GUE, so no such law can have
simple fraction below 0.6853. h2: please check which hypothesis his Thm 8.6/8.8 carries.

## 3. Off-line pairs: where it breaks [R/N]
* Isolated pair: eigenvalues `(2+ν, −ν)`; `g(2+ν)+g(−ν) = 2(1+ν)² ≥ 2`. Harmless (in the scalar LP the only condition is `c₂+3c₃ ≤ 0`).
* [N] Abstract linear algebra (`cubic_abstract_test.py`): with two blocks `2(a_ka_k^T − b_kb_k^T)`, `a_k ⊥ b_k`, `|a_k|²−|b_k|² = 1` and
  nothing else assumed, `tr g(G) − tr Q'` is unbounded below (`b₁ ∥ b₂`, `a₁ ⊥ a₂`: eigenvalues `2+2β, 2+2β, −4β`, defect `16β − 48β³`).
* [N] Periodic model with the true kernel (`cubic_model_deep.py` first lines): one pair in a lattice: defect increases with depth
  (fine); six pairs at random positions with depths ≈ 1.0 mean spacing: **defect −2404** (N = 12): the inequality fails for
  clusters of deep pairs. So Lemma C is false for conjugation-symmetric configurations, and so is every cubic certificate with
  `c₃ ≠ 0` in the pure inertia class:
* [R] **Parity obstruction.** If all one knows about the off-line part is inertia, the eigenvalues of `G` range over ℝ and a
  certificate `Σ f(λ_i) ≤ (charges)` needs `f` bounded above at both ends: for `deg f ≤ 3` the cubic coefficient must vanish. Hence
  **m₃ is irrelevant unconditionally for every window**, and the first useful new moment is the fourth (with negative leading
  coefficient) — x1's Idea 8. This is the precise form of "how off-line pairs enter the cubic trace".
* [C] Density theorems do not rescue it: a three-point term at frequencies `(a,b,a+b)` and the two-point term at `a+b` grow at the
  same exponential rate `e^{4π(a+b)y}` in the depth y, but the adversary can null the two-point amplitude `Z(a+b)` of a cluster
  while keeping `Z(a)Z(b)` — so the two-point data do not bound the three-point contribution of rare deep clusters.

## 4. LP ceilings with three-point rows [N]
Rows = D–S moments (2pt: `E|S(l)|² = l`; 3pt: `E Re S(a)S(b)conj S(a+b) = 0`, `a+b ≤ N−1`; 4pt as in ceiling_class.md).
Values are exactly feasible laws (upper bounds for every certificate using the rows); optimality rests on heuristic pricing.

| N | marks | 2-pt | +3-pt | +3,4-pt |
|---|---|---|---|---|
| 8 | on-line | 0.6860 | 0.7088 (converged, 2 seeds) | 0.7119 (converged) |
| 12 | on-line | 0.6839 | 0.7051 (converged) | ≤ 0.718 (not converged) |
| 16 | on-line | 0.6830 (h3) | ≤ 0.7063 (not converged at timeout) | — |
| 8 | + pairs, depth ≤ 0.5 | 0.6860 | 0.7072 | — |
| 8 | + pairs, depth ≤ 1.0 | 0.6860 | 0.6933 | — |
| 8 | + pairs, depth ≤ 1.5 | 0.6860 | 0.6904 (law puts ~10⁻⁴-weight on a 4-pair depth-1.5 cluster) | — |
| 12 | + pairs, depth ≤ 1.5 | 0.6839 (h3: 0.6837) | ≤ 0.691 (not converged) | — |
Depth ≤ 3 fails numerically (LP conditioning). Trend: the three-point gain is ≈ +0.021 on-line (lower bound 0.6853−0.6818 = +0.0035
proved as N → ∞; the LP suggests more, N → ∞ not established), and decays to a few 10⁻³ once depth ≥ 1.5 is allowed.
Not done (lead's item 1 in full): N = 24 and h3's batched pricer; given §3 I judged the off-line question more urgent.

## 5. Answers to the lead's questions via x1
* *Is the gain from functionals other than the single-matrix third moment?* No: the simplest functional that beats the two-point
  ceiling on-line **is** the single-matrix cubic trace, `2 tr G_ψ² − tr G_ψ³` with a non-flat window (cos(1.6 s): 0.68525). x1's
  neutrality (8b) is special to the flat window, where the extremal spectrum {0,1,2} has `m₃ = 2 = 3m₂ − 2`; for a non-flat
  window `m₃(ψ) < 3m₂(ψ) − 2` (MT: 1.9707 vs 1.9825). The full-hexagon LP gives more (≈ 0.705) with mixed multipliers.
* *Is it unconditional at bandwidth one in x1's sense?* The **data** are (3-cycles are diagonal for X < T^{1−ε}, smooth height
  window). The **zero-side inequality** is not: it needs `G ⪰ 0`-type information (RH, or a bound on the depth of off-line zeros).
* *What arithmetic does it need?* Only `n₁n₂ = n₃` diagonality — no Hardy–Littlewood input.
* Under a narrow-box hypothesis (all zeros within `y₀` mean spacings of the line, `y₀` small) the cubic lemma should hold with an
  explicit `y₀` [C; the single-pair and two-pair tests at depth ≤ 0.2 pass]; that would give "0.685 under a box hypothesis",
  to be compared with Fabbian's 0.6792 at depth ≤ 33/200 (per h2).

## 6. x1's fourth-moment target `tr P⁴ ≤ 0.305 N` [C]
Right degree: a quartic minorant with negative leading coefficient is bounded above on all of ℝ, so it survives off-line pairs
(same reason the quadratic does). The input is a one-sided bound, accurate to 14%, for the non-diagonal piece
`½‖[P₊,P₊*]‖²` = variance-type sum over `n₁n₃ − n₂n₄ = h`, `0 < |h| ≤ n₁n₃/T`, prime-power variables ≤ T^{1−ε}.
* Rudnick–Sarnak range: no (4-cycles reach `Σ|ξ_j| = 4λ`; λ < ½ is rank-capped).
* Sieve upper bounds: bound each correlation by C·(Hardy–Littlewood main term) with C > 1; the target is a difference between
  that main term and the squared mean, so a constant-factor loss is a loss by the factor (m/T)/log m (x1's own remark). No.
* Kloosterman / additive-divisor technology gives power savings for `ad − bc = h` with *smooth* variables (d(m)d(m+h),
  Deshouillers–Iwaniec); with four prime variables of size T and product T² the Type-II ranges are not covered — it is the
  fourth moment of a prime Dirichlet polynomial of length T at constant-sharp precision. Selberg/Fujii moments of `S(t+h)−S(t)`
  are asymptotic only for `h log T → ∞` and use zero-density, so they do not give the constant at `h log T ≍ 1`.
Verdict: no known technique gives even the one-sided 14% bound; it is Hardy–Littlewood-type in mean. I see no shortcut.

## 7. Reconciliation with the negative statements
* A–F §7.2(e): correct for their sharp-cutoff/Hilbert-inequality evaluation, not a limit of the data (k = 3 is free at λ < 1).
  A–F §7.3 "under RH the third trace is available": RH is needed there for the zero side (positivity), exactly as in §3.
* Tyagi (per h2: one half-band cubic row, N = 64): a half-bandwidth cube is rank-capped at ½; no conflict.
* Yang–Yang 0.7962 (per h2): needs `m₄ = 13/4`, i.e. HL*(4); not unconditional. No conflict.
* Fabbian (per h2): agrees with §3–4 in the unconditional class; the apparent conflict on-line is addressed in §2.
