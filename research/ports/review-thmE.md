# Referee report: Theorem E (cut regime of K_{2,3}(w)) and §§5–7 of `k2m/notes.md`

Date: 26 Nov 2026. Scope: `k2m/notes.md` §5.1–5.4, §6, plus the parts of §1 used by Corollary E. §§0–4, the
note on the K_{2,3} rate and §7 were taken as already refereed. All recomputations use my own code in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refE/`; the notes' scripts were read but not reused.
Scripts: `common.py`, `vec.py` (independent implementations of books, hubs, exit vectors, Br′ from angles, Br′ in the
certificate-spec form), `item1_cuts_flow.py`, `item2_calib.py`, `item2_adv.py`, `item3_min.py`, `item4_books.py`,
`item4_toyoda.py`, `item4_own5pt.py`, `boxcheck.py`, `item6_hard.py`; outputs `*.out` next to them.

## Overall verdict

**Theorem E and Corollary E are correct as stated.** I re-derived Proposition C′, (X1), (X2), (V1), (V2), the
frustrated and unfrustrated cases, and the cubic, and found no gap. No numerical violation turned up anywhere: not in
the calibration, not in the bracket, not in the five-point inequality. The upper bound (one flattening rank) and the
duality step are fine. The conditional statements of §5.4 (Lemma R, S(λ₂) ⇒ threshold (3−2λ₂)/λ₂, (CL\*\*₀) ⇒ (★))
follow as claimed. The certificate domain 𝓕′₁ is specified precisely enough to run. §6 Prop. T is correct. There
are a few overstatements and loose ends, all minor. They are listed first, weakest point first.

## Weak points (weakest first)

1. **§6.2, last line of Prop. T ("Non-regular H: the same with capacities deg_H(v_i)")** is asserted without a
   formula, and the constant is not "the same". Averaging gives Σ_i deg(v_i)(A_i+B_i) ≥ 2κ(w′)(Σ_H + (|E|/3)w′D)
   with w′ = 3w/|E|, i.e. the regular formula with mr replaced by 2|E|. This should be written out or dropped. It is
   not used anywhere.
2. **§5.4 table / `hardregion2.out`.** Near λ = 12/13 the minimum of Br′ over 𝓕′ sits at σ = 0, where Br′ = 3τ − η.
   At λ = 0.92 this gives +0.015755. The recorded +0.016280 is slightly too high: that search did not reach σ = 0.
   This is harmless (it is not a claim of the theorem). It does show that for λ₂ near 12/13 the margin of S(λ₂) is set
   by the non-smooth centre, not by the "v₁ becomes linear" boundary. For λ₂ = 9/10 and 6/7 the boundary minimum is the
   smaller one (0.0627 < 3τ − η = 0.1077), as stated.
3. **Prop. B (book principle)** says "minimum". Strictly it is an infimum: the minimising books are often degenerate
   (ρ_i → 0, points on the spine). For example, my book minimisation at w = 1.26 and 1.3 approaches the cut value only
   in the limit ρ → 0 (excess 9·10⁻⁶ and 5·10⁻⁶). Degenerate books are allowed as books, so the minimum is attained
   on the closed parameter set. Saying so in one sentence would be enough.
4. **§6.3 K_{3,3}: "the proved part of 𝒱₃ gives its maximum 3/√10 at w = 1"** is correct. I checked: 3λ+η equals 3.7947
   at the arc point and 3+λ₁ = 3.7666 at the Theorem-E corner. Along the conjectured arc 3λ+η keeps growing up to
   w = 3, so a better K_{3,3} bound needs the arc beyond w = 1 or the cut line beyond λ₁. That matches the numbers
   quoted for S(9/10) (0.975) and (★) (51/52).
5. **Remark 2 of §5.3** ("(V1) is tight at σ = 0 and (V2) on vertices with exits ≈ (1,−1)") is heuristic. Fine as a
   remark.

None of these affects Theorem E, Corollary E, Lemma R or the certificate implications.

## Item 1: the upper bound and the comparison values. Verdict: correct

- **Crossing wires** of X = {u₁, v₁}: supply u₁v₂, u₁v₃, u₂v₁ (3). Demand v₁v₂, v₁v₃ at rate f and u₁u₂ at rate wf
  (2 + w). The flattening of S^{⊗n} across X has rank 2^{3n}, and the flattening of the demand has rank
  2^{2a_n+b_n}. Matrix rank cannot increase under restriction, is multiplicative under ⊗, and takes the value r on the
  unit tensor ⟨r⟩ (GHZ type), over any field. So it is a spectral point and also bounds asymptotic restriction. This
  gives 2a_n + b_n ≤ 3n + o(n), i.e. (2 + w)f ≤ 3.
- **All 15 bipartitions** (`item1_cuts_flow.py`): the minimum cut ratio is min(1, 3/(2+w), 3/w), which equals
  3/(2+w) exactly when w ≥ 1. It is attained by the six cuts {u₁,v_i} and {u₁,v_i,v_j}. Each {u₁,v_i,v_j} is the
  complement of {u₂,v_k}, so these are the three cuts {u_k,v_i} up to complement and the v-relabelling.
- **Crossing with W5:** 3/(2+w) = 3/√(9+w²) ⇔ 4w + 4 = 9 ⇔ w = 5/4 (brentq gives 1.2500000000000004).
  For K_{2,4}: 4/(4+w) = 8/√(144+4w²) at w = 5/2.
- **Routing:** max-concurrent-flow LP solved directly (multicommodity arc formulation, HiGHS). It gives 3/(3+w) at
  every w tested (0.600000 at w = 2) and 4/(6+w) for K_{2,4}, as in Theorem K_m.3.
- **K_{2,4}:** the cut {u₁,v₁,v₂} has 4 supply wires against 4 + w. It is the minimum cut for w ≥ 2 (for w < 2 the
  cut {v_i} with ratio 2/3 is smaller), so at w ≥ 2w₁ it is the right one.

## Item 2: Proposition C′. Verdict: correct

Re-derived from scratch.

- A_i ≥ ⟨a_i,(ρ_i,a_i)⟩ and B_i ≥ ρ_i b_ix + (D − a_i) b_iy hold for any vectors of norm ≤ 1 (Cauchy–Schwarz).
- The only inequality beyond Cauchy–Schwarz is ρ_i(a_ix + b_ix) ≥ λρ_iP_i. It uses ρ_i ≥ 0 and the relaxed (5.1).
- Next come (3.3), the substitution b_iy = (a_iy+b_iy)/2 − λQ_i/2 and Σ_iQ_i = E₂ − E₁. Then Σ_S − λΣd^Z − ηD equals
  D·(Σ(a_iy+b_iy)/2 + (λ/2)Σ|ε_ij| − η) plus non-negative terms. No length is left over, so nothing is dropped with
  the wrong sign.
- The three choices of vectors check out:
  - |μ| ≤ κ: the old α, β, and (a_y+b_y)/2 = cos κ cos μ = cos(κ−|μ|) − sin κ sin|μ|.
  - μ > κ: a = (0,1) and b_y = 1 − λQ ∈ (−1,1), and a_x + b_x ≥ λP ⇔ 2Q ≥ λ|V|² ⇔ sin μ ≥ sin κ.
  - μ < −κ: the mirror image.
- The sine form for m = 3 is right. cos κ cos μ = ½√((1−λ²)P² + (σ−σ′)²) holds identically (because
  P² + (σ−σ′)² = 4cos²μ and |V| = 2cos d). So C = cos(κ − |μ|) ≤ 1 everywhere, C ≤ N, and C = N exactly on curved
  vertices.
- **Degenerate cases.**
  - Hubs at spine ends: (3.2) is the one-sided optimality condition of the convex function f_i + f_j on [0,D], and the
    ε terms enter only through y_ijε_ij = Dε_ij[y_ij = D].
  - v_i on the spine at its hub: any subgradient σ_ij works, since f_i(y_ij) = 0 = ρ_ic + (a_i − y)σ.
  - V_i = 0: κ = 0, N = 1, and N is continuous there.
  - D = 0: handled separately, using Σ_vv ≤ Σ_S and λ < 1.

**Numerics.** `item2_calib.py` uses my own book, clipped hub y = (ρ_ja_i+ρ_ia_j)/(ρ_i+ρ_j) and exit vectors, on
60 000 random books (six families, including near-collinear books and points beyond the spine ends). In 51 765 of
them at least one hub is at a spine end.

| (λ, η) | min over books of (true slack)/D − Br′ |
|---|---|
| (3/4, 3/2), w = 2 | +9.1·10⁻⁴ |
| (λ₁, 3 − 2λ₁) | +8.5·10⁻⁴ |
| (6/7, 9/7), w = 1.5 | +5.2·10⁻⁴ |
| (3/3.3, ·), w = 1.3 | +3.3·10⁻⁴ |
| (3/3.1, ·), w = 1.1 | +1.2·10⁻⁴ |
| arc, w = 1.2 | +2.6·10⁻⁴ |

The explicit vectors violate (5.1) or the unit-norm bound by at most 4.4·10⁻¹⁶.

`item2_adv.py` minimises the gap adversarially (Nelder–Mead over ρ = eˣ and free a, 300 starts per (λ, η)). The
minimum gap is −1.7·10⁻¹⁵ at λ₁ and −1.4·10⁻¹⁵ at w = 2, both at the symmetric book a = ½, and −2.2·10⁻¹⁵ at
λ = 0.9 on an asymmetric book. So C′ is tight on some books and is never violated beyond rounding. The open range
1 < w < w₁ is covered by the same runs: the inequality C′ holds for every (λ,η). Only the sign of Br′ depends on λ.

## Item 3: Br′ ≥ 0 for λ ≤ λ₁. Verdict: correct; the numerical threshold of the bracket is 12/13

**Line by line.**
- (5.2) is Br′ ≥ 0 rewritten with η = 3 − 2λ.
- (X1): Σ|ε| ≥ |Σε| = |ΣQ_i| = Σ|Q_i|.
- (X2): X ≤ 2min(−σ₁₂,σ₂₁) + 2min(−σ₁₃,σ₃₁). It is in fact the identity
  X = 2min(−σ₁₂,σ₂₁) + 2min(−σ₁₃,σ₃₁) − 2(−σ₂₃−σ₃₂)₊, which is (5.3).
- (V1): g is concave, g(0) = cos κ − τ ≥ 0, and g(κ) ≥ (1−τ)(1−λ). Both endpoint values checked, and
  t = tan(κ₀/2) = (1−τ)/λ.
- (V2): sin(κ/2) = λ sin(φ/2)cos(φ/2)/cos(κ/2) ≤ λ sin(φ/2), and h′ ≥ 0 because 0 ≤ κ−μ ≤ φ−μ ≤ π/2. Also μ ≥ 0
  follows from Q ≥ 0, and the larger exit sine of v₂ is ≥ σ₂₁.
- Unfrustrated case: 3(1 − τ) ≤ 2λ ⇔ λ ≤ 12/13.
- Frustrated case: the convex combination max(x,y) ≥ αx + (1−α)y with α = (1−τ)/(2λ). The v₁ terms cancel exactly,
  leaving (λ(1−α) − λ²)·[…].
- λ(1−α) ≥ λ² ⇔ G(λ) = 2λ(1−λ) − 1 + τ ≥ 0. Squaring τ = 1 − 2λ + 2λ² gives λ(4λ³ − 8λ² + 9λ − 4) = 0. This adds no
  spurious root, because 1 − 2λ + 2λ² > 0. The derivative 12λ² − 16λ + 9 has negative discriminant.
- Values: λ₁ = 0.7665884174654595, w₁ = 1.9134429005838356. The cubic and G vanish there to 4·10⁻¹⁶.
- The symmetries (page permutations, σ ↦ −σ) preserve N_i, |Q_i| and |ε_ij|.

**Attack** (`item3_min.py`). For each λ: 1.6·10⁶ structured random samples, 150 bounded Nelder–Mead polishes and
6 differential-evolution runs (popsize 40, polished) over σ ∈ [−1,1]⁶, with η = 3 − 2λ. The value was cross-checked
in both the angle form and the spec form.

| λ | w | min Br′ found | where |
|---|---|---|---|
| 0.70 | 2.286 | −2·10⁻¹⁶ | face zero (cut-type, X = 4) |
| λ₁ − 0.01 | 1.965 | −4·10⁻¹⁶ | face zero |
| λ₁ | 1.913 | −4·10⁻¹⁶ | face zero |
| λ₁ + 0.01 | 1.863 | −4·10⁻¹⁶ | face zero |
| 0.80 | 1.75 | −4·10⁻¹⁶ | face zero |
| 0.85 | 1.529 | −4·10⁻¹⁶ | face zero |
| 0.90 | 1.333 | −4·10⁻¹⁶ | face zero |
| 0.92 | 1.261 | −4·10⁻¹⁶ | face zero |
| 12/13 | 1.25 | −6·10⁻¹⁶ | σ = 0 and faces |
| 0.93 | 1.226 | **−0.0373** | σ = 0 (3τ − η) |
| 0.95 | 1.158 | **−0.1633** | σ = 0 |

So the inequality Br′(·; λ, 3 − 2λ) ≥ 0 itself appears to hold up to λ = 12/13 and fails just above, at the centre,
for the unfrustrated reason. λ₁ is only where the proof method stops (§5.3 Remark 2 and §8 [X] 7 say so). Nothing
fails at λ₁ + 0.01, consistent with the bracket's true threshold being 12/13.

## Item 4: the five-point inequality directly. Verdict: Theorem E confirmed; the conjectured threshold 5/4 is consistent

(a) **Three-page triangle books** (`item4_books.py`). These are exact CAT(0) configurations, and by Prop. B they
contain the infimum. The ratio R_w was minimised with 400 Nelder–Mead starts per w, D = 1.

| w | book min R_w | 3/(2+w) | κ(w) | min of Σ_S − λ(Σ_vv + wD), λ = 3/(2+w) |
|---|---|---|---|---|
| 2 | 0.750000000 | 0.750000000 | 0.832050 | +3·10⁻¹⁵ (line metric v₁ = u₁, v₂ = u₂, v₃ on [u₁u₂]) |
| 1.92 | 0.765306122 | 0.765306122 | 0.842271 | +2·10⁻¹⁵ |
| 1.5 | 0.857142857 | 0.857142857 | 0.894427 | +1·10⁻¹³ |
| 1.3 | 0.909092471 | 0.909090909 | 0.917556 | +5·10⁻⁶ (degenerate limit) |
| 1.26 | 0.920248291 | 0.920245399 | 0.921982 | +9·10⁻⁶ (degenerate limit) |
| 1.25 | 0.923076923 | 0.923076923 | 0.923077 | 0 (W5 and cut tie) |
| 1.24 | 0.924166880 | 0.925925926 | 0.924167 | **−0.0150** (W5) |
| 1.2 | 0.928476691 | 0.937500000 | 0.928477 | **−0.0785** (W5) |
| 1.1 | 0.938876316 | 0.967741935 | 0.938876 | **−0.268** (W5) |

The equality set of Theorem E is larger than "the cut metric of {u₁,v₁}". It includes the whole one-parameter family
of line metrics (v_i = u₁, v_j = u₂, v_k anywhere on [u₁,u₂]), which the minimiser keeps landing on. The faces of
zeros of Br′ in item 3 are the calibrated image of that family. This is worth one sentence in the notes.

(b) **Toyoda box-feasible five-point metrics.** By Toyoda 2020, triangle plus Gromov–Sturm ⊠ inequalities
characterise five-point subsets of CAT(0) spaces.
- `item4_toyoda.py` (tensorlab `min_ratio`, families triangle + box, 600 starts) returned the W5 value at every w:
  0.832050 at w = 2, …, 0.928477 at w = 1.2. My own ⊠ check (`boxcheck.py`, Hilbert-identity form over all
  4-permutations) confirms box feasibility to 6·10⁻¹⁵. This optimiser never reaches the degenerate cut point, so for
  w > 5/4 it only gives an upper bound on the minimum, and that bound is above the cut value. It is a local method.
- My own penalised optimiser (`item4_own5pt.py`: triangle + ⊠ via exact `box_min`, starts at all cut metrics, W5,
  mixtures, random) finds, after normalising Σ_vv + wD = 1:
  - w = 2: −1.7·10⁻⁶, at the line metric above, within the penalty tolerance. Value 0.
  - w = 1.92: −1.7·10⁻⁶, same.
  - w = 1.5, 1.3, 1.25 and 1.2: the same picture. See the addendum, including the caveat that this optimiser misses W5
    at w = 1.2.
- A bug I found in my own first version (wrong tuple index, which skipped the ⊠ penalty) produced −0.15 at the graph
  metric of K_{2,3}. That metric is not CAT(0): it violates ⊠ on (u₁,u₂; v₁,v₂) by 0.01. tensorlab reports this
  correctly, so this was my error, not a problem with the claim.

Conclusion: at w = 2, 1.92 and 1.5 the five-point minimum is 0, attained at cut and line metrics, as Theorem E says.
At 1.3 and 1.25 it is also 0, numerically, which supports the conjectured threshold w ≥ 5/4. Below 5/4 it is
negative, at W5, as it must be.

## Item 5: duality and corollaries. Verdict: correct

- **Rational w = p/q (§1).** Strassen's spectral theorem applies to T_{p,q}^{⊗a} versus S^{⊗b}. The rate on v_iv_j is
  aq/b and on u₁u₂ it is ap/b = w·(aq/b). log₂F(T_{p,q}) = q(Σ_vv + wD)(d_F).
- So f* ≥ inf_F R_w(d_F). Every d_F is an AN price, hence CAT(0) by C.3, so Theorem E gives R_w(d_F) ≥ 3/(2+w).
  Points F with Σ_vv + wD = 0 impose no constraint.
- **Irrational w ≥ w₁:** monotonicity in w, plus rational w′ ↓ w with w′ ≥ w₁, gives f*(w) ≥ 3/(2+w′) → 3/(2+w).
  w₁ itself is irrational and is covered the same way.
- Together with the cut, f*(K_{2,3}(w)) = 3/(2+w) for every field and every w ≥ w₁, with no hypothesis.
  At w = 2: 3/4 against routing 3/5. Remark 3 (0.75n and 1.5n against 0.6n and 1.2n) checks out.
- **K_{2,4}:** each v lies in 3 of the 4 triples and each pair in 2. Applying Theorem E at weight w′ to each triple
  gives 3Σ_S ≥ λ′(2Σ_vv + 4w′D).
  - With w′ = w/2: Σ_S ≥ (2λ′/3)(Σ_vv + wD), and 2λ′/3 = 2/(2 + w/2) = 4/(4+w). The condition is w/2 ≥ w₁, i.e.
    w ≥ 2w₁ = 3.8269.
  - The matching cut is {u₁,v₁,v₂}: 4 supply wires against 4 + w.
- **Remark for m ≥ 5:** averaging over triples gives m/(m(m−1)/3 + w) < m/(⌊m²/4⌋ + w). Correct.
- **§5.1 table:** I recomputed the chord between (3/√10, 3/√10) and (λ₁, 3 − 2λ₁) intersected with η = wλ. It gives
  0.9246, 0.8908, 0.8395, 0.7939 at w = 1.1, 1.25, 1.5, 1.75, as listed.

## Item 6: Lemma R and the certificate specs. Verdict: implications hold; the spec is runnable

- **Lemma R.**
  - The unfrustrated case needs η ≤ 3τ.
  - Frustrated at v₁ with v₁ linear: (V2) at v₂, v₃ plus (5.3) gives Br′ ≥ 3 − 2λ − η + (λ − λ²)[…] ≥ 3 − 2λ − η.
  - v₂, v₃ linear: (V1) at v₁ gives 1 − N₁ ≤ ((1−τ)/2)[(1+σ₁₂)+(1+σ₁₃)], and (1−τ)/2 ≤ λ.
  - The complement of 𝓕′ is exactly the union of these cases. Weak inequalities are fine: a configuration that is not
    unfrustrated is frustrated at some vertex, and it suffices to argue at that vertex.
- **S(λ₂) ⇒ threshold (3−2λ₂)/λ₂.** S(λ₂) on 𝓕′ plus Lemma R (with η = 3 − 2λ₂ ≤ 3τ₂ for λ₂ ≤ 12/13) gives Br′ ≥ 0
  on the whole cube at λ₂. Proposition C′ and (3.1) then give Σ_S ≥ λ₂Σ_vv + (3−2λ₂)D. No interpolation of
  certificates is involved: 𝒱₃ is convex and contains (0,3), because A_i + B_i ≥ D. The segment between them is
  {(λ, 3 − 2λ) : 0 ≤ λ ≤ λ₂}, so a single certified λ₂ covers every w ≥ (3−2λ₂)/λ₂: 4/3 for 9/10, 3/2 for 6/7.
  Corollary E.2 then holds for w ≥ 2(3−2λ₂)/λ₂.
- **(CL\*\*₀) ⇒ (★) ⇒** w ≥ 5/4 for K_{2,3} and w ≥ 5/2 for K_{2,4}. Correct.
- **(CL\*\*) ⇒** Theorem 5_w for 1 ≤ w ≤ 5/4. Here η = 3τ = λw, and 3τ ≤ 3 − 2λ holds exactly for λ ≥ 12/13, so
  Lemma R applies. Then Theorem B for w ≤ 5m(m−1)/24. For m = 4, 5·12/24 = 5/2 = w_c(4), so together with (★) this
  is Conjecture W for m = 3, 4. Correct.
- **Domain 𝓕′₁.**
  - Six variables, five closed polynomial-plus-square-root constraints, in the spec's own notation:
    Q₁ ≤ 0, Q₂ ≥ 0, Q₃ ≥ 0, 2|Q₁| ≤ λW₁, 2Q₂ ≤ λW₂.
  - It contains the image of closure(𝓕′) under the symmetries: S₃ on the pages, σ ↦ −σ, and the swap of pages 2 and 3
    for "v₃ curved".
  - On it N₁ = C₁ and N₂ = C₂ (on the boundary C = 1 = N). For v₃, using C is a valid lower bound because C ≤ N.
  - "Curved" ⇔ 2|Q| < λW, with W = |V|², matches the definition.
  - N is continuous, including at V = 0.
  - This is a well-posed interval problem. Point (2) of the spec (the treatment near σ = 0 for (CL\*\*₀)) is a plan, not
    a specification, and the certifier will have to work it out. That is acknowledged in the notes.
- **Numerical margins** (`item6_hard.py`: DE plus polish, with exact feasibility filtering):

| λ | min Br′ over 𝓕′₁ | notes |
|---|---|---|
| 0.8 | +0.161941 | +0.1619 |
| 6/7 | +0.103517 | +0.1035 |
| 9/10 | +0.062716 | +0.0627 |
| 0.92 | +0.015755 | +0.016280 (`hardregion2.out`; their search missed σ = 0) |
| 12/13 | 0 | 0, at σ = 0 |

  The minimisers for 0.8, 6/7 and 9/10 have σ₂₁ = −σ₁₂ = −σ₂₃ and sit on the boundary "v₁ becomes linear", as stated.

## Item 7: §6. Verdict: correct as stated, apart from weak point 1

- **Prop. T.**
  - Σ_{t∋i}x_t = r/2, from 2Σ_{t∋i}x_t = Σ_{e∋i}Σ_{t∋e}x_t = r.
  - Σ_tx_t = mr/6, from 3Σx_t = |E|.
  - The weighted sum of Theorem 5_{w′} gives (r/2)Σ_S ≥ κ(w′)(Σ_H + (mr/6)w′D).
  - 2κ(w′)/r = 2m/√(m²r² + 4w²), with the condition w′ = 6w/(mr) ≤ 1.
  - Equality at W_{m+2}(ℓ, 2wℓ/(mr)) is Cauchy–Schwarz.
  - "Pinned" follows because W_{m+2} ⊂ (m-pod) × ℝ is forced (Theorem A.2 / Lemma H_m).
  - Octahedron (x_t = ½ on all 8 faces, r = 4, m = 6): 12/√580 = 0.498273. Flow 6/13, from the symmetric routing load
    2f + f/6 and the K_{2,6} path metric 12/26.
- **Prop. B:** (3.1) leaves A_i, B_i, D, and hence every two-apex supply term, unchanged. It can only enlarge v_iv_j
  demand terms, and books are CAT(0) by Reshetnyak. Correct, with "minimum" read as in weak point 3.
- **f_pod ≥ f_book:** in the pod the hub is unconstrained on ℝ, so d^pod ≤ d^Z. Correct. Conjecture P is properly
  tagged [C].
- **§6.3 table:** the [R] rows follow from the stated theorems. The K_{3,3} counting (each cross wire in 4
  sub-instances, each inside pair in 3 + 1) is correct, and so is the bound (3λ+η)/4.
- **Asserted beyond proof:** only the non-regular sentence of Prop. T (weak point 1). The [N] rows are tagged [N].

## Addendum: remaining w of the own five-point run

`item4_own5pt.py` (outputs `item4_own.out`, `item4_own_125.out`, `item4_own_120.out`), normalised minimum of
Σ_S − λ(Σ_vv + wD) over triangle + ⊠ feasible five-point metrics:

| w | minimum found | at |
|---|---|---|
| 2 | −1.7·10⁻⁶ | line metric |
| 1.92 | −1.7·10⁻⁶ | line metric |
| 1.5 | −1.8·10⁻⁶ | line metric |
| 1.3 | −1.9·10⁻⁶ | line metric |
| 1.25 | −1.9·10⁻⁶ | line metric |
| 1.2 | −2.0·10⁻⁶ | line metric |

The −2·10⁻⁶ is the slack allowed by the penalty tolerance; the exact value at a line metric is 0. Nothing went below
the cut value at any w.

**Caveat on this run:** at w = 1.2 it did *not* find the known negative value κ(1.2) − 3/3.2 = −0.009 at W5, although
one start was a perturbed W5. So this penalised optimiser is weak: it finds the degenerate cut and line minima and
misses smooth interior ones. tensorlab's `min_ratio` does the opposite (finds W5, misses the cut). The book
minimisation finds both. Taken together, the three searches give min = min(κ(w), 3/(2+w)) at every tested w, with no
configuration of any kind below the cut value for w ≥ 5/4. That is numerical support for Theorem E (w ≥ w₁, proved)
and for Conjecture W at m = 3 (w ≥ 5/4, open). It is not a certificate.
