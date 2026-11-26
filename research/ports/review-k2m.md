# Referee report: Theorem K_m (K_{2,m}, weighted demand)

Object: `research/ports/k2m/notes.md` §§0–4 ("the notes"), with `note-k23-rate.md` ("the note") §§1–3 as the
refereed m = 3 base. Paper citations refer to the pdftotext copy `scratchpad/fm/paper.txt` ("AN").
Own scripts (the author's scripts were not imported):
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refk2m/`
- `lemP.py`: Lemma P over F_q with own field arithmetic; push-forward ranks over F₂; maximum families.
- `lemPprime.py`: Lemma P′ brute force in Mat₄(F₂).
- `calib.py`: Prop. C₃ and Prop. C on random books.
- `nearcollinear.py`: the §3.6 counterexample with small ρ > 0.
- `bookmin.py`: minimisation over m-page books.
- `flowcut.py`: flow LP, metric LP, cuts, table values, collinear counterexample.

**Verdict.** I found no fatal gap. Theorem K_m holds as stated:
- f* ≥ R_m(w) over every field for 0 < w ≤ m(m−1)/6;
- f* ≤ R_m(w) for every w > 0 when Contracting(k) fails;
- f_flow < R_m(w) < f_cut in the stated range.

It rests on the same imported statements as the refereed m = 3 theorem: AN C.3, C.4(a), C.4(f), Thm C.1 and
`thm_alt_rank_price`. The new ingredients are correct:
- Lemma P (the matrices over F_q);
- Lemma H_m (m pages instead of three);
- the weighted calibration;
- Theorem D, now an analytic proof checked in Lean;
- Theorem B (averaging over triples of pages).

There are two small defects, one numerical typo and one expository step; both are listed below.

## 0. Weakest points, in order

1. **§1, weighted duality for non-integer w (correct with fix, expository).** The notes say the argument of the note
   §1.1–1.2 "applies verbatim" to the weighted demand. That is true for the upper bound (§1.2(b)) at every real
   w > 0. The inequality a_nΣ_vv + b_nD ≤ nΣ_S is linear, and dividing by n gives f(Σ_vv + wD) ≤ Σ_S. The lower
   bound, f* ≥ min over prices, needs one more step that is not written down. Strassen's theorem applies to a single
   tensor a, so first take w = p/q rational and a = ⊗_{i<j}⟨2^q⟩_{v_iv_j} ⊗ ⟨2^p⟩_{u₁u₂}. Then
   log₂F(a) = qΣ_vv + pD, and f*(w) = inf_F Σ_S/(Σ_vv + wD) follows as in the note.

   For irrational w, combine two facts:
   - Monotonicity: ⟨2^b⟩ ≥ ⟨2^{b′}⟩ for b′ ≤ b, so f*(w) ≥ f*(w′) for w′ > w.
   - Continuity: G(w) := min_d Σ_S/(Σ_vv + wD) is continuous, because 1/G(w) is a maximum of affine functions of w
     over a compact set of normalised prices, hence convex and finite on (0,∞).

   Hence f*(w) ≥ lim_{w′↓w, w′∈ℚ} G(w′) = G(w). (The top of the range, m(m−1)/6, is rational, so rational w′ > w
   inside the range exist.) **Fix:** add these three lines to §1. The definition of the weighted rate in §1
   (a_n/n → f, b_n/n → wf) is fine as written.
2. **§4 table, row m = 6 (wrong number, harmless).**
   - R_6(1) = 12/√904 = **0.399114**, not 0.399557.
   - R_6/f_flow = **1.0643**, not 1.0655.
   - The m = 3, 4, 5 rows are right.

   My book minimisation gives 0.3991140631 (`bookmin.py`), and so does the formula. The value 0.399557 does not match
   any expression in the notes.
3. **§3.6, the word "forced" (cosmetic).** In the collinear book (all ρ_i = 0) the minimiser y_ij of f_i + f_j is
   not unique: it can be any point of [a_i, a_j]. The interior choice gives the stated vertical exit vectors. This
   does not weaken the counterexample:
   - (CL\*_m) is a statement for all exit angles, so a single admissible choice refutes it;
   - for nearby books with small ρ_i > 0 the hubs are unique, and Br stays negative (see item 7).

   Suggest "can be taken" in place of "forced", or cite the ρ > 0 perturbation first.
4. **Stale cross-reference (cosmetic).** `lean/NOTES.md` (CLStar section) still says "There is no `k2m/notes.md` in
   the tree". It now exists.

## 1. Lemma P (§2.1) — correct

- **Idempotents.** rk t = rk(I−t) = 1 ⇔ t = uxᵀ with xᵀu = 1. This uses det(I − uxᵀ) = 1 − xᵀu. Such t are in
  bijection with ordered pairs (im, ker) of distinct points of P¹, so there are (q+1)q of them. The difference
  formula t − t′ = [u u′]·diag(1,−1)·[x x′]ᵀ gives: t − t′ is invertible ⇔ the images differ and the kernels
  differ. Correct.
- **Derangement.** π(0) = ∞, π(∞) = 1, π(1) = 0, π(a) = a+1 on F_q∖{0,1}. The map a ↦ a+1 maps F_q∖{0,1} onto
  itself, and a+1 ≠ a. So π is a fixed-point-free permutation of P¹ with q+1 points. By hand I checked
  im/ker of t_0, t_∞, t_1, and that t_a = [a+1 1; a²+a a] has image [1:a] and kernel [1:a+1]. This agrees with the
  general formula (a+b)⁻¹[b 1; ab a] at b = a+1, where a+b = 1.
- **Brute force** (`lemP.py`, own GF(2^r) arithmetic, r = 1,…,5, q = 2,…,32). For each r:
  - the family has q+1 members;
  - every t is idempotent with rk t = rk(I−t) = 1;
  - every pairwise difference has rank 2.

  The push-forward ranks were computed directly over F₂ in Mat_{2r}(F₂): rk ι₂(t) = rk ι₂(I−t) = r,
  rk ι₂(t−t′) = 2r and rk ι₂(I) = 2r. On 300 random A per r, rk_{F₂}ι₂(A) = r·rk_{F_q}(A).

  An exhaustive search for q = 2, 4, 8 finds exactly (q+1)q matrices with rk X = rk(I−X) = 1, and the largest family
  with pairwise invertible differences has exactly q+1 members. The author's `fqpods.py` also runs and reports ALL OK.
- **Rank scaling.** ι₂(A) is the matrix of the F₂-linear map x ↦ Ax on F_q² ≅ F₂^{2r}. Its image is an F_q-subspace
  of F_q-dimension rk A, so its F₂-dimension is r·rk A. ι₂ is additive. So the distances are
  - |0 I| = |t t′| = √(2r),
  - |0 t| = |I t| = √r,

  that is, √r·√(graph metric of K_{2,m}). This is N5 scaled.
- **Range μ ≥ 3 of `thm_alt_rank_price`.** In Theorem A's proof μ = max(2r, 3), and Corollary P covers μ ≥ 2r via
  a ↦ diag(a,0). So r = 1 (m = 3) uses Mat₃ ⊃ Mat₂, as in the note. Failure of contracting gives the rank price
  for every μ ≥ 3: AN l. 1712, "Suppose that the contracting hypothesis fails, and fix μ ≥ 3". The Lean signature
  quoted in the note has `(hμ : 3 ≤ μ)`. Correct.

## 2. Lemma P′ (§2.2) — correct; not used in the theorem

- The proof is right:
  - Ω = im W ⊂ U_i + im(W−t_i), and the dimensions force equality, so U_i ⊂ Ω;
  - U_i ⊕ U_j = Ω for i ≠ j, so the sets U_i∖0 are disjoint and m(2^k−1) ≤ 2^{2k}−1.
- Brute force (`lemPprime.py`): in Mat₄(F₂) with W = I there are 560 matrices with rk t = rk(I−t) = 2. The largest
  family with pairwise rank-4 differences has exactly 5 members (= 2²+1).
- Theorem A uses only Corollary P, and Theorem B uses nothing from §2. So P′ enters only the "exactly 2^{⌊μ/2⌋}+1"
  remark.

## 3. Lemma H_m (§2.3) and Theorem A (§2.4) — correct

- **Step 1.** (x,y,v,u) = (n, t_i, s, t_j) has four sides a and two diagonals √2·a, which is the hypothesis of the
  refereed Step 1 of Lemma H. Only these four points are used.
- **Step 2.** c = mid(n,s) is unique by C.4(a), and [n,s] lies in every Q_ij. The diagonals of Q_ij cross at
  Φ_ij(½,½). So c is the same point for every pair.
- **Step 3.**
  - The half-square is the union of the segments from the corner t_i to the points of the diagonal. Images of
    segments are geodesics, and geodesics are unique. So Φ_ij(half-square) = Δ_i, which is defined without j.
  - Two parametrisations, from Q_ij and from Q_ik, agree on the side [n,s] (same endpoints, unique geodesic). They
    then agree on every segment from the vertex t_i to a point of that side.
  - So ψ_i is independent of the partner page. Correct.
- **Step 4.** For points on legs i ≠ j, both points lie in Q_ij. Ψ restricted to Δ_i ∪ Δ_j is Φ_ij (by Step 3, with
  the same orientation of σ on both halves), and Φ_ij is a scaled isometry for distances measured in Y. So the
  distance is √((τ+τ′)² + (σ−σ′)²). On one leg it is √((τ−τ′)² + (σ−σ′)²). An isometric embedding is a condition on
  pairs of points, so no three-page statement is needed. Correct.
- **Theorem A.**
  - Pull back ρ_μ and rescale by 1/√r (a nonnegative multiple).
  - Apply C.3 (the distances are positive, so the pull-back is injective).
  - Apply Lemma H_m with a = 1.
  - The metric of the price space is a price (AN l. 1601–1602, definition of price space), so finite subsets of the
    diamond carry prices.
  - Translation and scaling handle 𝕋_{m,∞} × ℝ.
- **Optimum (2.1).** Σ_S/(Σ_vv + wD) = 2m√(ℓ²+h²)/(m(m−1)ℓ + 2wh). By Cauchy–Schwarz this is
  ≥ 2m/√(m²(m−1)²+4w²), with equality iff h/ℓ = 2w/(m(m−1)). This holds for every w > 0, so item 3 of Theorem A
  holds for all w > 0. W_{m+2}(ℓ,h) ⊂ D_m iff max(ℓ,h) ≤ a/√2. Correct.

## 4. Proposition C, C₃ and Theorem D (§3.2–3.4) — correct

- **General m, recomputed by hand.**
  - Because λ < 2/(m−1) and |V_i| ≤ m−1, ν_i = arccos(λ|V_i|/2) is defined.
  - Sum-to-product gives cos α + cos β = λP_i, sin α − sin β = λQ_i and sin β = M_i − λQ_i/2.
  - (3.3) uses Σ_iQ_i = Σ_{i<j}ε_ij and y_ijε_ij = Dε_ij[y_ij = D].
  - Subtracting λ(Σd^Z + wD) leaves D·(ΣM_i − λw + λE₂ − (λ/2)(E₂−E₁)) = D·Br. All ρ_i and a_i cancel.
- **m = 3 specialisation.**
  - |V_i| = 2cos δ_i, and 1 − 9cos²δ/(9+w²) = (w² + 9sin²δ)/(9+w²). So M_i = (κw/3)·cos μ_i·√(1 + (9/w²)sin²δ_i).
  - The factors κw ↦ 3 and κ/2 ↦ 3/(2w) give Φ_w.
  - The σ form follows from (c_ij+c_ik)² + K(σ_ij−σ_ik)² = 4cos²μ(cos²δ + K sin²δ) = 4cos²μ(1 + (9/w²)sin²δ) with
    K = 1 + 9/w², and cos μ_i ≥ 0.
  - The convention for V_i = 0 (μ = 0, opposite vertical exits) is consistent with the σ form, which gives √K there.
- **Numerics** (`calib.py`: own hub formula by unfolding, subgradient choices satisfying (3.2), and assertions that
  (3.2) holds). Books included ρ_i = 0, v_i = u_k and near-collinear cases; 40 000 books for each w.

  | w | min of [Σ_S − κ(w)(Σd^Z + wD)] − D·Br | max \|D·Br − (κw/3)·D·Φ_w\| |
  |---|---|---|
  | 0.05 | +3.2e-7 | ≤ 3e-14 |
  | 0.2 | +6.3e-5 | ≤ 3e-14 |
  | 0.5 | +1.4e-3 | ≤ 3e-14 |
  | 0.8 | +6.3e-3 | ≤ 3e-14 |
  | 1 | +3.3e-3 | ≤ 3e-14 |

  So there were no violations, and the bracket identity holds to rounding. For m = 4, 5 at λ = R_m, Prop. C (the
  inequality lhs ≥ D·Br) also held on every book.
- **Theorem D.** I re-derived the six-line proof:
  - hexagon telescoping;
  - c ≥ √(1−m²);
  - one linearisation with sin χ = 3m/√(9+w²), so cos χ ≥ √(1−m²);
  - E ≥ mE;
  - 3(1−m²) + 3m²/w ≥ 3.

  It is correct. Lean `PortsLean.CLStar.clstar_weighted` states exactly (3.5_w): ½Σ√((c+c)² + (1+9/w²)(σ−σ)²) − 3 +
  3/(2w)·Σ|σ_ij+σ_ji|, for 0 < w ≤ 1 and |σ| ≤ 1, with the same vertex and pair grouping as in §3.2. I compiled
  `lake env lean PortsLean/CLStar.lean` myself: exit 0, about 13 s, and no `sorry` warning. So the statement used in
  §3.4 is the one proved.
- **Theorem 5_w.** The D = 0 case uses κ(w) < 1. The D > 0 case is (3.1) → C₃ → D. Correct.

## 5. Theorem B (§3.5) — correct

- **The m-page book is not needed.** Theorem 5_{w′} is a statement about any five points of a CAT(0) space. The proof
  applies it to u₁, u₂, v_i, v_j, v_k in the original price space, and that is all it uses. The m-page reduction
  §3.1 serves only Prop. C for general m (the dead route of §3.6) and the numerics.
- **Counting.**
  - Each v_l lies in C(m−1,2) triples, each pair in m−2 triples, and the D term appears C(m,3) times.
  - Dividing by C(m−1,2) gives coefficients 2/(m−1) and (m/3)w′.
  - Hence Σ_S ≥ (2κ(w′)/(m−1))·(Σ_vv + (m(m−1)/6)w′D).
  - 2κ(w′)/(m−1) = 6/((m−1)√(9 + 36w²/(m²(m−1)²))) = 2m/√(m²(m−1)²+4w²).
  - w′ ≤ 1 ⇔ w ≤ m(m−1)/6.

  The Lean file also has this step (`k2m_average`, `R_eq`, `k2m_rate`), and it compiled with the rest.
- **Equality.** Each triple of W_{m+2}(ℓ, 2wℓ/(m(m−1))) is W5(ℓ, w′ℓ/3).
- **Numerics** (`bookmin.py`, Nelder–Mead, 150 starts). The minimum over m-page books equals R_m(w) to about 1e-16 for:
  - m = 3: w = 0.3, 0.7, 1;
  - m = 4: w = 0.5, 1, 2;
  - m = 5: w = 1, 2, 10/3;
  - m = 6: w = 1, 5.

## 6. Duality chain (§1) — correct with fix

See weakest point 1. The other parts are fine:
- every F ∈ 𝒳 is an AN price, and AN prices bound protocols (the note §1.2, which does not depend on the number of
  parties);
- S ≥ ⟨2⟩ on all parties, because K_{2,m} is connected;
- C.3 has no restriction on |V|.

Prices satisfy Theorem 5_w on each five-point subset via the pull-back or directly in the price space; both are
valid. The minimum in (1.1) is attained: after normalising Σ_vv + wD = 1 and bounding Σ_S, all distances are bounded
through the connected supply graph, and the AN class is compact.

## 7. §3.6 [X] and §4 — correct, except the table typo

- **Counterexample to (CL\*_m)** (`flowcut.py`, `nearcollinear.py`). Collinear book, v_i at heights i/(m+1), D = 1,
  λ = R_m(w):

  | m | w | Br | true lhs |
  |---|---|---|---|
  | 4 | 1 | −0.658 | +2.03 |
  | 6 | 1 | −0.399 | +3.61 |
  | 5 | 2.5 | −0.213 | +2.17 |
  | 5 | 10/3 | −0.581 | +1.84 |
  | 5 | 1 | +0.50 | (positive) |
  | 7 | 7 | −1.21 | (positive) |

  - For m = 5, Br is positive at w = 1 and negative at w = 2.5. This matches the threshold
    m(m−1)/(2√(m²−1)) = 2.041.
  - With ρ_i ≈ 1e-4 (unique hubs), Br = −0.650 for m = 4, w = 1, and the true lhs is +2.03. So the scalar inequality
    fails while the true inequality holds.
  - Br = −λw for even m, and 1 − λw for odd m. The threshold algebra is right.
- **Routing.** I solved the edge-formulation max-concurrent-flow LP (undirected capacity 1, both arc directions) at
  w = 1. The metric LP is the dual, a minimum over all pseudometrics on m+2 points.

  | m | flow LP (w = 1) | metric LP | 2m/(m(m−1)+2w) |
  |---|---|---|---|
  | 3 | 0.75 | 0.75 | 0.75 |
  | 4 | 0.571429 | 0.571429 | 0.571429 |
  | 5 | 0.454545 | 0.454545 | 0.454545 |
  | 6 | (not run) | 0.375 | 0.375 |

  The metric LP also matches the formula at (m,w) = (4,2), (5,3), (3,0.5). The explicit routing (each v_iv_j half
  through u₁ and half through u₂, and u₁u₂ split over the m vertices v_j) loads each edge with f((m−1)/2 + w/m).
  Correct.
- **Cuts.** Brute force over all 2^{m+2} subsets agrees with min(2/(m−1), m/(⌊m²/4⌋+w)) for m = 3–6 at w = 1 and at
  the three other (m,w). The minimising cuts are:
  - a = 0: X = {v_i}, with ratio 2/(m−1);
  - a = 1: X = {u₁} ∪ ⌊m/2⌋ of the v's, with ratio m/(⌊m²/4⌋+w).

  For m = 3, w = 1 both give 1. The strictness algebra is correct: w_c = (m²(m−1)² − 4β²)/(8β), with w_c(3) = 5/4,
  w_c(4) = 5/2, w_c(5) = 16/3. The bound w_c ≥ (3m−2)(m−2)/8 > m(m−1)/6 holds for m ≥ 4, strictly, since
  5m² − 20m + 12 has no integer root.
- **Table.** The m = 6 row is wrong (weakest point 2). The other claims check out:
  - the gain (m(m−1)+2w)/√(m²(m−1)²+4w²) increases in w for w < m(m−1)/2, so it is largest at the top of the
    range, where it equals 4/√10;
  - f_cut/R_m(1) = √(1 + 4/(m²(m−1)²)).

## 8. Summary of verdicts

| Item | Verdict |
|---|---|
| 1 Lemma P / Corollary P, μ ≥ 3 handling | correct |
| 2 Lemma P′ | correct; not used in Theorem K_m |
| 3 Lemma H_m, Theorem A, optimum (2.1) | correct |
| 4 Prop. C, C₃, Φ_w translation; Theorem D statement = Lean `clstar_weighted` | correct |
| 5 Theorem B (averaging) | correct; the m-page book is not needed |
| 6 Weighted Strassen duality | correct with fix (rational w, then monotonicity and continuity) |
| 7 §3.6 counterexample, flow, cuts, strictness | correct; table row m = 6 wrong (0.399114, 1.0643) |
