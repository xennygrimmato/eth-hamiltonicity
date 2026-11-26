# Referee report: the five-point theorem (hull notes §3, §2 chain, §4)

Object: `research/ports/hull/notes.md` (line numbers refer to it), §3.1, §3.2, §3.3, the duality paragraph of
§2 (l. 175–184), §4. Paper citations are to the pdftotext copy `scratchpad/fm/paper.txt` ("AN" below).
Scripts: `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/ref5/` (own code; the
author's scripts were not imported).

**Verdict.** I found no gap, fatal or repairable, in the chain
C.3 → C.4(a) → book bound (2) → Prop. 3.2 → (CL\*) → Strassen duality.
(CL\*) is now covered by interval certificates (item 6). With that, the five-point theorem and
f\*(K₂,₃; k) ≥ 3/√10 over every field are a computer-assisted theorem. Its trust base is listed in §8.

## 0. Weakest points, in order

1. **The trust base of the certificate (§6, §8).** `ivcheck` re-checks every leaf without searching. But it
   links the same crate as the prover: the same problem encoding (`src/problems/clstar.rs`), the same
   interval library and the same AD/gain-test code. So it is independent of the search, not of the
   implementation. I checked the encoding of Φ by hand against Prop. 3.2 (§6a), and it matches exactly.
   The rounding and the gain-test logic I only spot-checked: sqrt of an interval that reaches below 0 returns
   INVALID, and domain and bound are compared bit-for-bit with the problem definition. A second, separate
   implementation (e.g. Arb/MPFI or a Lean interval check) would remove this single point of trust.
2. **The two analytic lemmas outside the checker**: the corner lemma, and the covering logic that glues
   `clnear` × 8, the corner regions and `clstar` together. Both are correct (§6b). They are short enough to
   be written into §3.3 of the notes verbatim, and they should be.
3. **Minor, §4 item 2 (l. 356–360) and the word "min" in l. 179.** The infimum over Strassen's spectrum
   𝒳 need not be attained. 𝒳 is compact, but it is not closed under F ↦ F^a, so the ratio
   log F(S)/log F(T) can approach its infimum along F with F(T) → 1. Then "f\* = κ iff some point of 𝒳 has
   R = κ" needs "inf" in place of "some point", or an argument that the infimum is attained. Over the AN
   class, which is closed under φ ↦ φ^a, the minimum is attained after normalising Σ_T = 1. The lower bound
   f\* ≥ κ is unaffected.
4. Cosmetic: §3.1 (l. 208–211) argues the "geometric reading" (d^Z = book distance), which the proof never
   uses. Only inequality (2) enters Prop. 3.2, as the text itself says. Keep it as a remark.

## 1. Book reduction (§3.1) — correct

AN Lemma C.4(a) (paper l. 1641–1645): "Let Y be a CAT(0) space. (a) For x, v ∈ Y and t ∈ [0,1] exactly one
point γ(t) has the distances t|xv| from x and (1 − t)|xv| from v, and
|zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|² for every z ∈ Y."

- This is a statement **inside a CAT(0) space**. For a general price on five points the segment points do
  not exist, so one must first pass to a price space. The notes do this: l. 194, "It uses of CAT(0) only AN
  C.4(a), so it holds for every AN price on five parties (C.3)". AN Prop. C.3 (l. 1608): "Every price on a
  set V is the pull-back of the metric of a price space". A price space is "a CAT(0) space whose metric is a
  price" (l. 1601–1602). The pull-back may identify points, which is harmless. Recommendation: move the C.3
  sentence to the start of §3.1, so that c_t visibly lives in Y.
- Substituting z = v_i, x = u₁, v = u₂ gives h_i(t)² exactly as in l. 201. By Stewart, h_i(t) is the
  apex-to-base distance in the comparison triangle. The triangle exists by the triangle inequality, so
  h_i² ≥ 0.
- (2) uses the **same** point c_t ∈ [u₁,u₂] for both i and j, together with the triangle inequality in Y.
  Correct.
- D = 0 (l. 198): u₁ = u₂ in the pseudometric, so B_i = A_i and Σ_S = 2ΣA_i ≥ Σ_{i<j}(A_i + A_j) ≥ Σ_T.
  Correct.
- Degenerate pages need no special treatment: collinear u₁,u₂,v_i (ρ_i = 0) and v_i = u_k (A_i = 0 or
  B_i = 0) fall under the same formulas. My Prop. 3.2 test includes them.
- Book geometry (attack 1, second half). The question is moot, because only (2) is used. For the record,
  the answer is yes. Each page is convex and contains the straight segment from v̄_i to any spine point.
  Pages meet only on I. A detour through a third page re-enters I and is no shorter than the chord of I. So
  the book distance is min_t(h_i + h_j).

## 2. Calibration, Prop. 3.2 (§3.2) — correct; independent recomputation

Setup: page coordinates (ρ,a), u₁ = (0,0), u₂ = (0,D), v_i = (ρ_i,a_i), ρ_i ≥ 0, f_i(y) = |v_i − (0,y)|.

1. f_i′(y) = −(a_i − y)/f_i = −σ_ij at the hub, where e_ij = (v_i − c(y))/f_i = (cos ψ_ij, sin ψ_ij) and
   ψ_ij ∈ [−π/2, π/2] because ρ_i ≥ 0. The minimiser of the convex function f_i + f_j on [0,D] satisfies:
   - interior: σ_ij + σ_ji = 0;
   - y = D: the derivative is ≤ 0 there, so ε_ij ≥ 0;
   - y = 0: ε_ij ≤ 0.

   The signs in l. 225–227 are right.
2. f_i(y) = ⟨e, v_i − c(y)⟩ = ρ_i c_ij + (a_i − y)σ_ij. Summing over the pair gives
   d_ij = ρ_ic_ij + ρ_jc_ji + a_iσ_ij + a_jσ_ji − yε_ij. In the three cases y·ε_ij equals 0, D·ε_ij and 0
   respectively, so y·ε_ij = D·ε_ij·[y = D]. Summing gives (3), with P_i = c_ij + c_ik ≥ 0 and
   Q_i = σ_ij + σ_ik. Then Σ_iQ_i = Σ_pairs ε = E₂ − E₁. Correct.
3. If f_i(y) = 0, the subgradient choice σ_ij = −σ_ji (or 0 if both vanish) satisfies the optimality
   relation, and ρ_ic_ij = 0. The identity in step 2 still holds.
4. (4): Cauchy–Schwarz gives A_i = |(ρ_i, a_i)| ≥ ρ_i cos α + a_i sin α and
   B_i = |(ρ_i, a_i − D)| ≥ ρ_i cos β + (D − a_i) sin β, for all angles.
5. The choice of angles.
   - e_ij + e_ik = 2cos δ_i (cos μ_i, sin μ_i), with cos δ_i ≥ 0 because |δ_i| ≤ π/2.
   - With α = ν + μ and β = ν − μ: cos α + cos β = 2cos ν cos μ, sin α − sin β = 2cos ν sin μ, and
     sin β = sin ν cos μ − cos ν sin μ.
   - Setting cos ν = κ cos δ makes these equal κP, κQ and M − κQ/2, with M = cos μ √(1 − κ²cos²δ).
   - ν is well defined because κ cos δ ∈ [0, κ] ⊂ [0,1].
   - The sign of ν matters only through sin ν. Choosing ν ≥ 0 makes M ≥ 0, which is the better choice. The
     identities hold for either sign.
6. The sum. A_i + B_i ≥ κ(ρ_iP_i + a_iQ_i) + D(M_i − κQ_i/2). Summing and inserting (3):
   Σ_S ≥ κ(Σd + DE₂) + D(ΣM − (κ/2)(E₂ − E₁)), hence
   Σ_S − κ(D + Σd) ≥ D(ΣM − κ + (κ/2)(E₁ + E₂)).
   With √10·M = cos μ √(10 − 9cos²δ) = cos μ √(1 + 9 sin²δ) and √10·κ = 3, this is l. 257–260 exactly.
   **All ρ_i and a_i terms cancel**, as claimed.
7. Nothing requires v_i off the spine. No relation between the six angles is used except the sign
   conventions, so Φ ≥ 0 on the whole cube suffices. That is the claim of l. 262.

Numerical test (`prop32_check.py`). 200 000 random books, with about 200 000 pairs of each hub type
(interior / u₁ / u₂). The sample includes ρ = 0, ρ ≈ 10⁻³, v_i = u_k, far points and near-W5 books. Book
distances were computed in closed form (unfolding, then clamping); the first 3000 books were cross-checked
by bounded scalar minimisation and a 20 001-point grid. The sign conventions were asserted for every pair.

- Minimum of [Σ_S − κΣ_T(Z)] − (D/√10)Φ: **+1.5·10⁻⁵**, with no violation.
- Minimum of (D/√10)Φ: 0, at collinear books.
- Minimum of R(book): 0.948687 > κ.
- At W5 (D = 1, ρ_i = 1.5, a_i = ½): ψ = 0 and lhs = rhs = 0.

## 3. Equality cases — confirmed

- At W5(ℓ, ℓ/3), D = 2ℓ/3 and ρ = ℓ = 1.5D, a = D/2. Then ψ = 0, Φ = 0 and Σ_S − κΣ_T = 0.
  R = 6√(ℓ²+h²)/(6ℓ+2h) is minimised at h = ℓ/3 (derivative ∝ 3x − 1), with value 3/√10.
- The six cube corners also give Φ = 0. They are: vertex i, ψ_ij = ψ_ik = −sπ/2, the other four +sπ/2;
  the pair {j,k} carries |ε| = 2. These are collinear books, where the true ratio is R ≥ 1, so the slack is
  (1 − κ)Σ_T > 0. They are not equality cases of the theorem, only of the relaxation.
- My search found no other zeros of Φ (§5). So equality in Theorem 5 forces ψ = 0 plus equality in (2) and
  (4). This supports the uniqueness conjecture (l. 473–474). I have not proved uniqueness.

## 4. The chain to tensors (§2, l. 175–184; §5(i)) — correct; no normalisation mismatch

- **What a price is.** "For every spectral point φ there is a pseudometric d_φ on V with values in [0,1]
  such that φ(⟨q⟩_uv) = q^{d_φ(u,v)}" (l. 216–217; Lemma A.2, l. 1069–1074). "A price on a finite set V is
  a limit of functions c·d_φ" (Def. A.4, l. 1121). So **the price is the exponent d_φ itself**, which is
  linear in log φ(wire).
- **The curvature statement is for that same d.** thm_cn (l. 417): "|zy|² ≤ ½|zx|² + ½|zx′|² − ¼|xx′|²",
  written in |·| = the price. Theorem C.1 (l. 1444–1446) is stated for "points of a price". Prop. C.3 embeds
  the price, not its square root, into a CAT(0) space. N5 = √(rank metric) is consistent with this: its
  squared prices are ranks. R is linear in d, which is exactly the object on which CAT(0) is asserted.
  **No square-root mismatch.**
- **Strassen spectrum ⊂ AN spectral points.** AN Def. A.1 requires φ(s) ≤ Σφ(t_j) whenever s is covered by
  t_1, …, t_r. Let F ∈ 𝒳 and s = Σ_j s_j with s_j = (⊗_v A_v^{(j)}) t_j. Then s is a restriction of ⊕_j t_j,
  using the per-party maps [A_v^{(1)} … A_v^{(r)}] on the block-diagonal sum. So
  F(s) ≤ F(⊕t_j) = ΣF(t_j), and F(1) = 1. AN itself says (l. 1064): "This class is larger than Strassen's
  asymptotic spectrum".
- **Duality.**
  - The five-party tensors over any field k, with ⊕, ⊗ and restriction, form a Strassen preorder: n ≤ m
    in ℕ iff n ≤ m, a ≤ ⟨r⟩ for r = rank, and 1 ≤ b for b ≠ 0. Strassen's spectral theorem applies over
    every field, finite fields included. Strassen 1988 §2 gives the abstract theorem; Christandl–Vrana–
    Zuiddam treat k-tensors over arbitrary fields.
  - F(⟨2⟩_uv) = 2^{d_F(uv)} as in A.2. S ≥ ⟨2⟩_{all five}, because a spanning tree of K₂,₃ gives the unit
    tensor. So "≤ S^{⊗(n+o(n))}" and "≤ S^{⊗n}⊗⟨2^{o(n)}⟩" agree.
  - Hence T^{⊗p} ≲ S^{⊗q} ⇔ pΣ_Td_F ≤ qΣ_Sd_F for all F, and f\* = inf_{F: Σ_T d_F > 0} R(d_F).
    Irrational κ is no issue: take rationals p/q ↑ κ.
  - Alternatively, AN's own Theorem A.6 (l. 1164–1167) gives covers of C^N by 2^{εN} products. A cover is a
    restriction of a direct sum, and ⟨2^{εN}⟩ ≤ S^{⊗εN}. So the AN route works without Strassen as well.
- **Fields.** AN l. 564–567: "the field only supplies the scalars: the crossing identity is between integer
  tensors, the geometry sees only the real numbers φ(t)". So thm_cn, and hence C.3 and C.4(a), hold for
  prices over every field.
- Hence: every F ∈ 𝒳 over k gives an AN price d_F over k. By C.3, d_F is the pull-back of a CAT(0) metric.
  Theorem 5 then gives Σ_S d_F ≥ κΣ_T d_F, and so f\*(K₂,₃; k) ≥ 3/√10. Correct.
- "Inf" versus "min": see §0.3.

## 5. (CL\*) and five-point R: own numerics

`clstar_search.py`:

- 2·10⁷ random points (half pushed to faces): minimum 0.0, at a corner.
- 800 Nelder–Mead + L-BFGS-B starts (uniform, near corners, near 0) and 2 differential-evolution runs:
  **no negative value**. The only zeros are the six corners and the origin. The next-lowest local values
  are 3·10⁻⁵ to 5·10⁻⁴, all at |ψ| ≈ 0.01 next to the origin (quadratic growth).
- Near the corners: min Φ/|dev|₁ = 0.440 over 1.2·10⁶ inward samples at scales 10⁻¹ to 10⁻⁶. That is
  linear growth with slope ≈ ½, as in l. 310–312.
- Near 0: min Φ/|ψ|² = 0.479 (compare the eigenvalue 3/4 of (I) plus the ε gain).
- The slice identity Φ|_{ψji = −ψij} = F(θ) − 3 with θ = (ψ₁₂, −ψ₁₃, ψ₂₃) holds to 4·10⁻¹⁵
  (`slice_check2.py`).

`cat0_R.py`, R on five points of CAT(0) spaces:

- random points of star₃ × star₃ × ℝ^m: minimum 0.9576;
- local minimisation over star₃ × star₃ × ℝ (400 starts): **0.948706 = κ + 2.3·10⁻⁵**, approaching the W5
  value from above;
- hyperbolic plane: random minimum 1.0005, local minimum 1.0000 (curvature −1 does not help);
- ℓ₁ check for §4 item 3 (`cuts.py`): every cut of K₂,₃ separates at least as many S-wires as T-wires, so
  R ≥ 1 on ℓ₁ metrics. Confirmed.

## 6. The certificate glue (coordinator's item; `tools/ivcert/src/problems/clstar.rs`)

**(a) Substitution and pairing — correct and exactly equivalent.**
- σ = sin ψ is a bijection [−π/2, π/2] → [−1, 1] with cos ψ = √(1−σ²) ≥ 0.
- (cos a + cos b)² + 10(sin a − sin b)² = 4cos²μ cos²δ + 40cos²μ sin²δ = 4cos²μ(1 + 9 sin²δ), with
  μ = (a+b)/2 and δ = (a−b)/2. Since cos μ ≥ 0, ½√(…) = cos μ √(1+9 sin²δ). The identity is exact, and so
  is the equivalence of the statements.
- The term (3/2)|sin ψ_ij + sin ψ_ji| = (3/2)|σ_ij + σ_ji| carries over literally.
- Pairing, against the notes' order ψ = (ψ₁₂, ψ₁₃, ψ₂₁, ψ₂₃, ψ₃₁, ψ₃₂) (l. 257):
  - pairs: ε₁₂ = x0+x2, ε₁₃ = x1+x4, ε₂₃ = x3+x5;
  - vertices: 1 ↔ (σ₁₂, σ₁₃) = (x0, x1); 2 ↔ (σ₂₁, σ₂₃) = (x2, x3); 3 ↔ (σ₃₁, σ₃₂) = (x4, x5).
- The code matches: `eval` uses (0,2), (1,4), (3,5); `vertex_terms` uses (0,1), (2,3), (4,5) with
  kp1 = 1 + 9 = 10.
- This is the bookkeeping of Prop. 3.2: each ψ_ij enters the vertex term of i and the pair term of {i,j}.

**(b) Covering — complete. Corner lemma — correct.**
- `clnear`: σ_ij = a+e and σ_ji = e−a, i.e. a = (σ_ij − σ_ji)/2 and e = (σ_ij + σ_ji)/2. In code:
  s = [a12+e12, a13+e13, e12−a12, a23+e23, e13−a13, e23−a23], which matches the coordinate order.
  - A point with |σ|∞ ≤ ½ has |a|, |e| ≤ ½, so it lies in one of the 8 orthant boxes.
  - On an orthant (3/2)|σ_ij+σ_ji| = 3s_k e_k. This is the `gain` term, and it is exact there.
  - Each box maps into [−1,1]⁶ (|a ± e| ≤ 1), so Φ is defined throughout. That the boxes cover more than
    the central cube is harmless.
- `clstar` on [−1,1]⁶ closes every leaf except:
  - X leaves, which are boxes wholly inside [−½,½]⁶ (covered by `clnear`) or wholly inside a corner region
    {sσ_jk ≥ 15/16, sσ_kj ≥ 15/16} (code: lo ≥ 0.9375 or hi ≤ −0.9375 on the pair (p,q));
  - P leaves, which lie wholly outside the fundamental domain.

  Coverage of the tree is structural: the checker rebuilds the boxes. So every point is in a closed leaf,
  in the central cube, in a corner region, or (via a symmetry) in the image of one of these.
- The six corner regions are exactly neighbourhoods of the six zero corners: 3 pairs × 2 signs.
- Corner lemma. Put d₁ = 1 − sσ_jk ∈ [0, 1/16]. Then c_jk = √((1−|σ|)(1+|σ|)) = √(d₁(2−d₁)) ≥ √d₁. All
  c ≥ 0, so V_j ≥ ½c_jk. All vertex terms are ≥ 0, the other two |ε| are ≥ 0, and
  |ε_jk| = 2 − d₁ − d₂. Hence Φ ≥ ½(√d₁ + √d₂) − 3 + (3/2)(2 − d₁ − d₂) = ½(√d₁ + √d₂) − (3/2)(d₁ + d₂).
  This is ≥ 0 because 3d ≤ √d for d ≤ 1/9, and 1/16 < 1/9. **Correct.**
- Rigour notes. 15/16 and ½ are dyadic, so the region tests are exact in floating point. Interval sqrt
  returns INVALID if the argument's lower end is < 0, so 1 − σ² rounding below 0 cannot be silently
  accepted. The checker compares domain and bound bit-for-bit with the problem definition (`cert.rs`
  l. 133–146). I re-ran `ivcheck` on all 10 (CL\*) certificates (8 `clnear`, `clstar`,
  `clstar_nosym`): all VERIFIED, under 1 s each for `clnear`.

**(c) Symmetry — sound (and not load-bearing).**
- Φ in σ-coordinates is invariant under S₃ acting by σ_ij ↦ σ_{π(i)π(j)}. The vertex term V(a,b) is
  symmetric in (a,b), and the pair term is symmetric. So the image of vertex i's term is vertex π(i)'s term,
  and the pairs are permuted. The global flip σ ↦ −σ fixes c, (a−b)² and |a+b|.
- w_i = σ_ij + σ_ik transforms by w ↦ w∘π⁻¹ under S₃, and by w ↦ −w under the flip.
- Every orbit meets {w₁ ≥ w₂ ≥ w₃, Σw ≥ 0}: sort; if the sum is < 0, flip and sort again. So this is a
  fundamental domain in the covering sense, which is all that is needed.
- Pruning uses only strict certain violations (w₀.hi < w₁.lo, …, Σhi < 0), so no point of the closed
  domain is pruned.
- The excluded regions need not be invariant: `clnear` and the corner lemma cover their regions entirely,
  not only their intersection with the fundamental domain.
- The no-symmetry certificate also verifies.

## 7. §4 (P2), briefly

- Item 2: correct except for inf versus min (§0.3). It also needs Theorem 5, now certified.
- Item 3: confirmed (cuts.py).
- Items 1, 4–7: no objection found, but not refereed in depth.

## 8. Corrected final statement and trust base

**Theorem 5 (computer-assisted).** Let u₁, u₂, v₁, v₂, v₃ be points of a CAT(0) space in the sense of AN §C.4
(complete, midpoints satisfying CN). Then
Σ_{k,i} |u_k v_i| ≥ (3/√10)·(|u₁u₂| + |v₁v₂| + |v₂v₃| + |v₁v₃|),
with equality at W5(ℓ, ℓ/3). The same holds for every AN price on five parties over any field k (via C.3).

**Corollary.** For every field k: f\*(K₂,₃; k) = inf over Strassen's asymptotic spectrum of R(d_F), which is
≥ 3/√10. Here f\* is the rate of exact asymptotic restriction T^{⊗⌈fn⌉} ≤ S^{⊗(n+o(n))} with binary wires
and the uniform demand (v₁v₂, v₂v₃, v₁v₃, u₁u₂). This is the "rates up to 3/√10 are attainable" half; it is
non-constructive. Together with §2 and H2: if Contracting(k) fails, f\* = 3/√10 exactly.

**Trust base.**
1. AN Theorem C.1 / thm_cn and Prop. C.3, with Lemma C.4(a) (Lean-backed per the notes). The direction
   used is price ⇒ CAT(0) embedding; C.4(a) is a standard CAT(0) fact.
2. Strassen's spectral theorem for the semiring of 5-party tensors over k (Strassen 1988; or AN Theorem A.6
   with the cover-to-restriction step above).
3. §3.1 and Prop. 3.2: elementary, recomputed here line by line and tested numerically.
4. (CL\*): the 10 certificates checked by `ivcheck`, plus the corner lemma and the covering argument (§6b).
   This trusts the shared Rust code: interval arithmetic with directed rounding, AD, the gain and convexity
   tests, and the problem encoding. I verified the encoding by hand. No independent second implementation
   exists.
5. Not needed: Reshetnyak gluing, Toyoda's theorem, the uniqueness of the minimiser, anything from OA.
