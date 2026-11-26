# Referee report: the hull lemma (hull/notes.md §1, Lemma H, Corollaries H1, H2) and the K_{2,3} bound

Adversarial review, 26 Nov 2026. "AN" = Anthropic, "VP ≠ VNP over every field". Line numbers "l." refer to
`scratchpad/fm/paper.txt`. Lean paths are relative to `scratchpad/fm/repo/vp-vnp`. "notes" =
`research/ports/hull/notes.md`. Computation: `scratchpad/hullranks.py`, which checks the ten ranks in Mat₂ and in
Mat₃ and minimises R over h. No Lean was built.

## Summary

**No fatal gap. The chain from "contracting fails over k" to "f*(K_{2,3};k) ≤ 3/√10" is correct.** It needs three
fixes. None of them changes the bound.

| # | Item | Verdict |
|---|---|---|
| 6 | Price ⇒ rate bound (the notes' "§3") | **Gap in the document, correct in substance.** The notes cite "§3 (three lines)", but notes.md stops at §1.4. The argument is supplied below. The definition of f* covers exact restrictions only. Border protocols (degenerations) are covered over infinite fields by a short extra argument that uses AN's covers. |
| 8 | Field bookkeeping | **Correct with fix.** The statement holds per field k. The 3-SAT consequence holds for any field of characteristic 0, so ℝ or ℂ protocols count. It depends on Theorem A, which is [D] and uses OpenAI's HC 4.2, and on IM 7.1. Those are not reviewed here. |
| 7 | "Contracting fails ⇒ ρ₃ is a price" | **Correct, and better than the notes say.** It is a named Lean theorem: `thm_alt_rank_price` (Alternative.lean:706). Failure of the hypothesis means failure at every μ, so μ = 3 is available. |
| 3 | Flat squares (Step 1) | **Correct.** Both applications of C.4(f) meet its hypotheses exactly. Uniqueness of geodesics gives convexity and the common centre. D.2 Step 8 is not imported; it is redone for one square. |
| 4 | Triangles and gluing (Steps 3–4) | **Correct.** All pairs are covered. Δ_i and ψ_i do not depend on j. |
| 2 | Prop. C.3: is the whole price space's metric a price? | **Correct: yes.** |
| 5 | W5 in the diamond, 3/√10 | **Correct.** The hypothesis ℓ + h ≤ a/√2 in Lemma H is stronger than needed (max(ℓ,h) ≤ a/√2 suffices). This is harmless. |
| 1 | Ranks of N5; Mat₂ ↪ Mat₃ | **Correct** (hand check plus computation). |

---

## 6 (weakest). From "W5 is a price" to the rate bound

**What the notes say.** Table row 5 says "Any AN price d bounds the tensor rate: f*(K_{2,3};k) ≤ R(d). [R] (three lines,
§3)". **The notes contain no §3.** The file ends at line 174, after §1.4. Row 5 therefore has no proof in the document.
Here is the missing proof, with its exact scope.

**Definitions used.**
- AN Def. A.1 (l. 1058–1061): a spectral point φ on I is ≥ 0, φ(1) = 1, multiplicative, and φ(s) ≤ Σ_j φ(t_j)
  whenever s is covered by t_1,…,t_r. "For r = 1 the last condition says that φ is monotone under restriction".
- Cover (l. 1028–1030): "s = s_1 + ⋯ + s_r with every s_j a restriction of t_j".
- Lemma A.2: φ(⟨q⟩_{uv}) = q^{d_φ(u,v)} for all q ≥ 1.
- Def. A.4 (l. 1121–1124): a price on a finite set V is a pointwise limit of c·d_φ with c ≥ 0 and φ a spectral point on V.
  Lean `def_price` (Prices.lean:23) states the same as an ε–δ approximation.
- f* = sup{f : T^{⊗fn} ≤ S^{⊗(n+o(n))}} (ideas-ports.md l. 912), where ≤ is restriction. S and T are products of
  2-dimensional wires.

**Claim (exact restriction).** Let d be a price on the five parties with Σ_T d > 0. If T^{⊗m} is a restriction of S^{⊗n},
then m·Σ_T d ≤ n·Σ_S d.

*Proof.* Take a spectral point φ on the five parties. By monotonicity, multiplicativity and A.2,
2^{m Σ_T d_φ} = φ(T^{⊗m}) ≤ φ(S^{⊗n}) = 2^{n Σ_S d_φ}, so m Σ_T d_φ ≤ n Σ_S d_φ. Multiply by c ≥ 0. The inequality is
linear in the distances and closed, so it survives pointwise limits. ∎

With m = f·n and S^{⊗(n+o(n))}, dividing by n and letting n → ∞ gives f ≤ R(d). Wires of other dimensions also work, since
A.2 holds for every q. A protocol T(r_e) ≤ S(c_e) with dimensions 2^{r_e}, 2^{c_e} gives Σ r_e d(e) ≤ Σ c_e d(e). The
statement "rate f" in the conclusion means **the same rate f on all four demand wires**. Non-uniform demand vectors, such
as the (4,4,4,3) experiment of ideas-ports.md, only test the weighted inequality against W5. Each such vector must be
checked separately, for example over the whole W5(ℓ,h) family.

The notes' description, "monotone and multiplicative so the bound is direct", is right. Cover-subadditivity is not needed
for exact restrictions. Only two facts are needed: prices are limits of non-negative multiples of d_φ, and the bound is
linear.

**Border protocols (degeneration).** The definition of f* does not include them. ideas-ports.md (b) proposes "the border
version (maps polynomial in ε, leading term T)". AN spectral points are not stated to be monotone under degeneration.
Over an **infinite** field (for example ℚ, ℝ or ℂ) the bound still holds, by this argument:

- Suppose (⊗_p A_p(ε))·S^{⊗n} = ε^e·T^{⊗m} + O(ε^{e+1}), with the A_p polynomial in ε of total degree D.
- Then T^{⊗m} is the ε^e coefficient of a polynomial of degree ≤ D, whose value at each ε is a restriction of S^{⊗n}.
- Lagrange interpolation at D+1 distinct field elements writes T^{⊗m} as a linear combination of D+1 such restrictions.
  The scalars can be absorbed into one party's map. So T^{⊗m} is covered by D+1 copies of S^{⊗n}.
- By A.1, 2^{m Σ_T d_φ} ≤ (D+1)·2^{n Σ_S d_φ}.
- Powering a border protocol multiplies D by the power, so D = O(n) and the factor (D+1) is 2^{o(n)}. The rate bound is
  unchanged.

Over a finite field this needs ≥ D+1 elements, so it fails for border protocols of high degree. It is irrelevant over ℚ.

**Verdict.** Gap in the write-up only. Add the proof above as §3 of the notes. State there that "protocol" means
T^{⊗fn} ≤ S^{⊗(n+o(n))} by restriction, with border/approximate protocols included over infinite k by the cover
argument above.

## 8. Field bookkeeping

- "Price over k": spectral points act on tensors over k (Def. D.1: "the field k, on which the notion of a price
  depends"). Corollary H2 and the rate bound use the same k throughout, so the statement is per field: **for every field
  k, if Contracting(k) fails then f*(K_{2,3}; k) ≤ 3/√10.**
- Contrapositive: a protocol over k with rate > 3/√10 implies Contracting(k).
- A protocol over ℚ is also one over ℚ̄, ℝ and ℂ, so each of those fields would satisfy Contracting. A protocol found
  only over ℝ or ℂ, for example by numerical alternating least squares made exact, gives Contracting(ℝ) or
  Contracting(ℂ). That is still a characteristic-0 field.
- Theorem A (ideas-ports.md §2.2) is stated for any k and concludes "ports in char k". So **any characteristic-0 field
  suffices, not only ℚ.** The notes' "over ℚ" is a special case. The step ℚ vs ℚ̄ is not needed; ideas-ports.md says the
  same (l. 266–270).
- Downstream dependencies, unreviewed here:
  - Theorem A is [D]. It uses AN F.6 and OpenAI's HC 4.2 (review-theoremAB.md: "CORRECT … 85%").
  - The 3-SAT conclusion uses IM 7.1 (OpenAI). Alternatively it uses Theorem R (note-contracting-eth.md §3), which uses
    only AN. Its uniform form rests on the uniformity audit (review-uniformity.md).
  - Table row 7 of the notes should name Theorem R as the AN-only alternative and say that it is [D].

## 7. "Contracting fails ⇒ ρ₃ is a price"

- Definition D.1 (l. 1701–1702): "There are an integer μ ≥ 2 and a real number s with 1 ≤ s and s² < μ such that
  D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)." Lean `Contracting` (Alternative.lean:45) is the same ∃μ ∃s statement.
- Its negation is ∀μ ≥ 2 ∀s ∈ [1, √μ): some price has D(μ) > s D(1). So failure gives every μ, in particular μ = 3.
  **Failure "at some μ" is not the right reading; the negation of an existential is universal.**
- The proof (l. 1714: "Suppose that the contracting hypothesis fails, and fix μ ≥ 3") proves, in Steps 1–7 (l. 1717–1778),
  that some price on Mat_μ(F₂) has |a,a′|² = rk(a−a′). Step 5 needs μ ≥ 3 (l. 1760: "As μ ≥ 3, …"). So μ = 2 directly
  is not available. Pulling back along Mat₂ ↪ Mat₃ is the right move.
- **Lean:** `thm_alt_rank_price (hK : ¬ Contracting K) (hμ : 3 ≤ μ) : ∃ w, IsPrice K w ∧ ∀ a a', w a a' ^ 2 =
  (a - a').rank` (Alternative.lean:706–709). Since w ≥ 0, w = √rk.
- The notes' caveat (notes l. 170–172: "not a separately named Lean theorem") is wrong in the conservative direction. It
  should cite this theorem.
- Remark D.3 (l. 1787–1789) says the same in words, as the notes quote.

**Verdict.** Correct. Fix the caveat.

## 3. Flat squares (Lemma H, Step 1)

**C.4(f) as stated** (l. 1658–1660; Lean: last conjunct of `lem_toolkit`, Toolkit.lean:462ff, any real δ, h):

> "Suppose that |xy| = |uv| = δ and |xu| = |yv| = h, that both diagonals of the quadrilateral x, y, v, u have the squared
> length δ² + h², and that a ∈ [x,u] and b ∈ [y,v] have |xa| = sh and |yb| = th. Then |ab|² = δ² + h²(s−t)²."

The hypotheses are only these: two pairs of equal opposite sides and both diagonals Pythagorean. No angle hypothesis
appears and no inequality is used. "The equality case of C.4(b)" is how the notes motivate (f); it is not a hypothesis.

**First application** (x, y, v, u with all sides a and diagonals √2a): δ = h = a, both diagonals 2a² = δ² + h². This
gives (1): |α(s)β(t)|² = a²(1 + (s−t)²).

**Second application** (x′ = α(s), y′ = α(s′), v′ = β(s′), u′ = β(s)). Each hypothesis checks out:

- |x′y′| = a|s−s′|, because both points lie on the geodesic [x,u] of length a.
- |u′v′| = a|s−s′|, likewise on [y,v].
- |x′u′| = |α(s)β(s)| = a and |y′v′| = a, by (1) with t = s.
- The diagonals x′v′ = α(s)β(s′) and y′u′ = α(s′)β(s) both have squared length a²(1 + (s−s′)²) = δ′² + h′², by (1).

So |Φ(s,r)Φ(s′,r′)|² = a²((s−s′)² + (r−r′)²). The case s = s′ holds trivially on one geodesic. The corner values
Φ(0,0) = x, Φ(1,0) = u, Φ(0,1) = y, Φ(1,1) = v are right.

**Convexity and uniqueness.**
- C.4(a) (l. 1642–1644: "exactly one point γ(t) has the distances t|xv| from x and (1−t)|xv| from v") makes geodesics
  unique. So the Φ-image of a straight segment is the geodesic between its ends, and Q is convex.
- The solid square on four given vertices is therefore unique: it is the union of the geodesics [α(s), β(s)], each
  determined by the vertices.
- The three squares Q_ij all contain the same diagonal [n,s], and c = mid(n,s) = mid(t_i,t_j) for every pair. The
  midpoint is unique (l. 1604–1605).

**D.2 Step 8.** It is not needed as a citation. The notes reprove the one-square case from C.4(f) alone. That is exactly
the content of Step 8's "applied with h = 1 to two such segments", made explicit. Nothing in it depends on the context
of Step 8.

**Verdict.** Correct.

## 4. Triangles and gluing (Steps 3–4)

- **Δ_i** = ∪_{p∈[n,s]} [t_i, p] is defined from geodesics alone, so it is the same set whether viewed inside Q_ij or
  Q_ik. Inside Q_ij it is Φ of the closed triangle (0,0), (1,1), (0,1), because geodesics from t_i = Φ(0,1) to
  diagonal points are images of segments.
- **ψ_i does not depend on j.** The parametrisations from Q_ij and from Q_ik are both isometries of Δ̄ onto the same set
  Δ_i, and both are injective because Y is a metric space. They agree on the three non-collinear vertices. So the
  composite of one with the inverse of the other is an isometry of Δ̄ fixing three affinely independent points, hence
  the identity. The notes' wording "a point of Δ̄ is determined by its distances to the three vertices" is the same
  argument. Valid.
- **The hub is well defined:** ψ_i(0,σ) is the unique point at height σ on [n,s], for every i.
- **All pairs are covered.**
  - Same leg: the points lie in the flat convex triangle Δ_i, and the distance is the Euclidean one in Δ̄. This equals the
    planar distance, since Δ̄ is convex, and that equals the distance in 𝕋 × ℝ.
  - Legs i ≠ j: in the flat square Q_ij, Δ_i and Δ_j lie on opposite sides of the diagonal, so the distance is
    √((τ+τ′)² + (σ−σ′)²). This equals the tripod-product distance. The ψ_j coming from Q_jk equals the parametrisation
    of the Δ_j half of Q_ij by the uniqueness just shown.
  - Hub points lie in every Δ_i, so they fall under the first case.

**Verdict.** Correct.

## 2. Prop. C.3: is the whole metric a price?

- The price-space definition (l. 1600–1602): "A metric space is CAT(0) if it is complete and if any two of its points
  have a midpoint that satisfies the CN inequality. A price space is a CAT(0) space whose metric is a price in the sense
  of Definition A.4."
- Prop. C.3 (l. 1608–1609): "Every price on a set V is the pull-back of the metric of a price space."
- Def. A.4 (l. 1123–1124): "A function on the pairs of elements of an arbitrary set Y is a price if all its pull-backs to
  finite sets are prices."
- So the metric of all of Y is a price, and every finite F ⊂ Y, including points outside the image of V, carries a price.
  The proof (l. 1622–1624) confirms this: "This metric is a price, as a limit of prices".
- **Lean** `prop_space` (Curvature.lean:211–213): `∃ X _ (_ : Cat.CN X) (f : V → X), IsPrice K (fun a b : X => dist a b)
  ∧ ∀ a b, dist (f a) (f b) = w a b`. Here `Cat.CN` (Nc/Cat/Core.lean:22) is "CompleteSpace and every two points have a
  CN midpoint".
- The second clause of `def_price` gives the pull-back characterisation for an arbitrary type.

**Verdict.** Correct. This is the load-bearing step, and it holds as used in H1.

## 5. W5 inside the diamond and 3/√10

- Distances in W5: v_j = (leg j, ℓ, 0) and u_± = (o, ±h). So |u v| = √(ℓ²+h²) on the six supply pairs, |v_i v_j| = 2ℓ,
  and |u₊u₋| = 2h.
- R(h) = 6√(ℓ²+h²)/(6ℓ+2h). With ℓ = 1, R′ = 0 ⟺ h(6+2h) = 2(1+h²) ⟺ h = 1/3. Then R = 6(√10/3)/(20/3) = 3/√10.
  Numerically the grid minimum is 0.948683298 at h = 0.3333.
- Membership: (ξ,σ) ∈ D needs |ξo| + |σ| ≤ a/√2 for each point separately. So the v's need ℓ ≤ a/√2 and the u's need
  h ≤ a/√2. The condition ℓ + h ≤ a/√2 in Lemma H is sufficient but not necessary. Scaling (Def. A.4: non-negative
  multiples) gives every (ℓ,h).

**Verdict.** Correct.

## 1. Ranks

- n = 0, s = I, t₁ = e₁₁, t₂ = e₂₁+e₂₂, t₃ = e₁₂+e₂₂. Computed ranks of differences (Mat₂ and, after a ↦ diag(a,0),
  Mat₃):
  - |ns| = 2
  - |n t_i| = 1
  - |s t_i| = 1
  - |t_i t_j| = 2
- So N5 is √(graph metric of K_{2,3}) as claimed.
- diag(a,0) − diag(b,0) = diag(a−b,0) has the rank of a−b, so the pull-back (Def. A.4) of ρ₃ is ρ₂.

**Verdict.** Correct.

---

## Corrected final statement

**Theorem.** Let k be any field. Use these notions:
- price: AN Def. A.4 over k;
- spectral point: AN Def. A.1 over k;
- Contracting(k): AN Def. D.1, Lean `Contracting K`;
- for parties u₁, u₂, v₁, v₂, v₃: S = ⊗_{i,j} ⟨2⟩_{u_i v_j} and T = ⟨2⟩_{v₁v₂}⟨2⟩_{v₂v₃}⟨2⟩_{v₁v₃}⟨2⟩_{u₁u₂};
- a protocol of rate f: restrictions T^{⊗m_n} ≤ S^{⊗n} with m_n/n → f.

(i) [AN D.2 Steps 1–7 = Lean `thm_alt_rank_price` with μ = 3; pull-back along a ↦ diag(a,0)] If Contracting(k) fails,
then N5 ⊂ (Mat₂(F₂), √rk) is a price over k.

(ii) [Lemma H, from AN C.4(a),(f) = `lem_toolkit`; AN Prop. C.3 = `prop_space`; Def. A.4] If N5 is a price over k, then
every finite subset of the diamond D ⊂ tripod × ℝ, in particular W5(ℓ,h) for all ℓ, h ≥ 0, is a price over k on the five
parties.

(iii) [§6 above, from Def. A.1, Lemma A.2, Def. A.4] If W5(ℓ, ℓ/3) is a price over k, then every protocol over k has rate
f ≤ 3/√10. If k is infinite, this also holds for border protocols (polynomial-in-ε maps with leading term T^{⊗m_n}),
by the interpolation/cover argument.

Hence, if any field k admits a protocol of rate > 3/√10, then Contracting(k) holds. If in addition char k = 0, Theorem A
(ideas-ports.md §2.2, [D]) gives ports in characteristic 0. That gives 3-SAT in 2^{O(v^{1−δ})}, via IM 7.1 (OpenAI) or
via Theorem R (AN only, [D]). Parts (i)–(iii) are proved. The consequence beyond "Contracting(k)" inherits the status of
Theorem A and IM 7.1 / Theorem R.

## Requested edits to notes.md

1. Add the missing §3 (the proof in item 6), with the scope of "protocol" and the border-rank extension over infinite k.
2. In H2's caveat (l. 170–172), cite `thm_alt_rank_price` (Alternative.lean:706).
3. In Lemma H, the hypothesis ℓ + h ≤ a/√2 can be relaxed to max(ℓ,h) ≤ a/√2. This is optional.
4. In row 7, replace "over ℚ" with "over any field of characteristic 0". Name Theorem R as the AN-only route, and give the
   [D] status of Theorem A.
5. Remark 3 (the second tripod) is correctly tagged [D]: it uses the flat-triangle lemma [BH99, II.2.9], which is not in
   AN's toolkit. Nothing in H, H1 or H2 depends on it.
