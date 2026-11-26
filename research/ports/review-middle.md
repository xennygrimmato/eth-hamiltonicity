# Review of `middle/notes.md` §2, §4, §5.2 (adversarial)

Scope: the parts of `middle/notes.md` listed in its §10.1:
- Theorem M0, Corollary M0′, §2.2, §2.3 and §2.4;
- Lemma K, Proposition S, 4.2(a)–(e) and §4.4;
- Theorem M2 and Corollaries M2′, M2″;
- the pull-back claim of §1.2.

Sources re-opened:
- AN `scratchpad/fm/paper.txt`: Def. A.4 (l.1121), Prop. C.3 (l.1608), Lemma C.4 (l.1641), Def. D.1
  (l.1698) and D.2 Steps 1–2 (l.1717–1730).
- EG (the OA paper) was not available to me, so the OA-class claims are not checked against their
  source.

Numerics: `scratchpad/midref/m2check.py`. This is my own code, independent of `sl2.py`. A Lean check
is in `lean/PortsLean/RankKernel.lean` (see `lean/NOTES.md` Task 6).

**Overall: no fatal gap. Every [R] statement I checked is correct, with the constants as stated.** The
problems are bookkeeping and wording. Weakest point first:

| # | Item | Verdict |
|---|---|---|
| 1 | Reformulation and class bookkeeping (§0 rows 2 and 7, §2.4) | Logic correct. **Tagging is too strong**: the "⇔" needs Theorem A, which is [D]. The OA half was not checked against EG |
| 2 | 4.2(d) "Reading" | Two loose sentences: the LPS claim follows from (c), not (a); "the cubic window is empty" is not literally true |
| 3 | §0 row 5, "edge ranks ≤ 1" | Correct, but only in Grassmann units. In F₂-rank units the edge ranks are about 2 log₂ n |
| 4 | Theorem M2 and Corollaries M2′, M2″ | Correct. Numerics confirm it (SL₃(F₄) exactly; F₈ to F₆₄ by sampling) |
| 5 | 4.2(a), (b), (c), (e) | Correct; all constants recomputed |
| 6 | Theorem M0 and §2.2 monotonicity | Correct. It is Def. D.1 at this μ |
| 7 | Lemma K and Proposition S | Correct. A slightly stronger version holds (λ = λ₂ signed). It is exactly tight on Cay(Mat_μ, rank 1). Formalised in Lean |

---

## 1. Reformulation "[¬C ∧ AN-ports] ⇒ (GE)" and the class bookkeeping

**Forward direction: correct.**
- Assume ¬C_AN. AN D.2 Steps 2–7 use only the failure of contracting at the given μ ≥ 3. So every
  ρ_μ with μ ≥ 3 is an AN price, and ρ₁, ρ₂ are too, as isometric pull-backs along the block
  embedding into Mat₃.
- Then √D_f is an AN price on V for every placement f, because it is a pull-back.
- So an AN port family with constant γ satisfies E_pairs D_f ≤ γ E_edges D_f for every f. That is
  (GE) for that family, with the same γ.

**Contrapositive use: correct.**
- ¬(GE) applied to a P_X family with its own γ gives one graph G_i and one f with P > γe. Theorem M0
  needs exactly that: one graph and the same γ.
- The cone formulation does not change this. A violating δ in the closed cone can be approximated by
  a single c·D_f, because sums of D_f are again D_f (block sums) and the ratio is quasi-linear.
- If E_edges δ = 0, then δ = 0 on a connected graph, and a P_X family is connected because cuts are
  X-metrics.

**Caveats.**
1. **Tag.** §0 row 2 says "¬(GE) ⇒ (AN-ports ⇔ contracting)" and tags it [R].
   - The direction P ⇒ C is [R]: it is Theorem M0.
   - The direction C ⇒ P is Theorem A, which §2.4 itself tags [D] ("C_AN ⇒ P_AN. [D]").
   - So the row should read "¬(GE) ⇒ (AN-ports ⇒ contracting) [R]; ⇔ given Theorem A [D]". The same
     applies to the OA statement, where C_OA ⇒ P_OA is "[D, OA]".
2. **The literal cell {¬C_AN, P_OA} "equals" {¬C_AN, C_OA} under ¬(GE).**
   - Only the inclusion ⊆ follows from M0. It also needs the OA version of M0, which rests on two
     unchecked facts:
     - OA metrics are closed under pull-back along arbitrary maps V → Mat_μ(F₂) (EG §2.2);
     - the quadrilateral inequality EG (4.5) holds for squared OA metrics.
   - I could not check either against EG. Equality also needs C_OA ⇒ P_OA, which is [D, OA].
   - The qualitative conclusion "under ¬(GE) the literal middle cell lies inside the class gap" needs
     only the inclusion. It is right, conditional on the OA version of M0.
3. **Regular graphs versus bounded-degree ports.** (GE) is stated for d-regular graphs, while ports
   is stated for bounded degree. This is harmless:
   - pad each vertex with loops up to the maximum degree;
   - loops carry w = 0, so E_edges changes by a factor in [d_min/d_max, 1], and γ changes by at most
     d_max/d_min.
   - It would be cleaner to say so once.
4. **Corollary M0′, converse.** "¬C ⇒ β_ρ ≤ β_AN for every graph" is correct by the forward argument.
5. **Dead end 7.8** ("the converse-type statement is equivalent to ¬(GE)"). This is consistent with the
   above, with the same tag caveat.

## 2. 4.2(d): two loose sentences

- **LPS claim.** "For Ramanujan graphs of degree p+1 ≥ 18 … there is no 1-Lipschitz spreading placement
  at all."
  - Consequence (a) with r = 1 needs λ* ≤ 1/4, i.e. 2√p/(p+1) ≤ 1/4, i.e. p ≥ 62.
  - At p = 17 the claim is true, but through (c):
    - λ = 2√17/18 = 0.458 < 1/2, so e ≤ 1 < log₂(1/λ) = 1.127;
    - c = (½ − 0.458)/(1 − 0.458) = 0.0775;
    - the bound is E_pairs D ≤ 2/(c(1−λ)) + 2⌈log₂(1/c)⌉ ≈ 47.6 + 8 ≈ 56.
  - The threshold λ < 1/2 is 4√p < p+1, i.e. p ≥ 14, so p = 17 is the first LPS prime. The claim holds
    with the correct pointer ((c), with constant ≈ 56).
- **"For cubic graphs the window is empty."**
  - λ₂ ≥ 2√2/3 − o(1), so the window is e < log₂(3/(2√2)) ≈ 0.085 (from (c)), and (b) also covers
    e ≤ (1−λ₂)/4.
  - The window is small but not empty. What is true is that no placement with a constant fraction of
    rank-≥1 edges is covered.

## 3. §0 row 5 / Theorem M2: "edge ranks ≤ 1 (after the normalisation)"

- The placement is g ↦ gW, measured by d_J = τ²/2.
- Turning it into an F₂-rank placement (§1.2) goes through F_q with q = 2^s > n = |Γ_p|. This
  multiplies all ranks by 2s ≥ 2 log₂ n. So as a placement into Mat_μ(F₂), the edges have rank about
  2 log₂ n, not ≤ 1.
- The ratio is scale-free, so β_ρ ≥ 6j − 2 is unaffected.
- This is consistent with the threshold of §4: the kernel 2^{−D_f} of the F₂-rank placement is
  essentially 1 on all pairs, so Prop. S says nothing about it.
- M2″ correctly uses the different kernel 2^{−d_J} = |gW∩hW|/|W| = ⟨1_{gW}, 1_{hW}⟩/|W|. That kernel
  is PSD with diagonal 1, so the abstract Prop. S applies (see the Lean `spectral_ineq`).
- Suggest saying "edge Grassmann distance ≤ 1" instead.

## 4. Theorem M2 and Corollaries M2′, M2″: correct

### 4.1 The edge bound (part 1)

- e_ab(t) acts by v_a ↦ v_a + t·v_b. For t = 1 it preserves U³, since U is additive.
- For t = x: if u ∈ U³ and u_b ∈ span(1, …, x^{j−2}), then x·u_b ∈ span(x, …, x^{j−1}) ⊂ U. There is no
  reduction, since j − 1 < k.
- So dim(e_ab(x)W ∩ W) ≥ 3j − 1, i.e. d_J ≤ 1. For j = 1 the subspace is u_b = 0, still of codimension 1.
- E_edges d_J = (6·0 + 6·1)/12 = ½. Numerically each e_ab(x) has d_J exactly 1.

### 4.2 The pair bound (part 2)

- SL₃(F_q) acts F_q-linearly, hence F₂-linearly, on F_q³ = F₂^{3k}, and transitively on F_q³∖0. So for
  w ≠ 0 and uniform g, gw is uniform on F_q³∖0. That is the transitive action used.
- Then E_g|gW ∩ W| = Σ_{w∈W} Pr[gw ∈ W] = 1 + (|W|−1)²/(q³−1).
- This is < 1 + |W|²/q³ = 1 + 2^{6j−3k} ≤ 2, because (a−1)²/(b−1) < a²/b whenever a² ≤ b and a > 1.
- Jensen for 2^X gives E dim(gW∩W) < 1, so E_g d_J > 3j − 1.
- Pairs (g, h) give τ(W, g⁻¹hW), which is uniform in g⁻¹h, with the diagonal included.

### 4.3 The ratio and the comparison with log₂ n

- The ratio is ≥ (3j − 1)/½ = 6j − 2 ≥ 3k − 5.
- |SL₃(F_q)| = q³(q³−1)(q²−1) < 2^{8k}, so 3k > (3/8) log₂ n.
- The final bound (3/8) log₂ n − 5 is correct.
- "log n is the largest possible order": for δ a metric (and the rank cone ⊂ MET), uniform
  multicommodity flow on an expander gives E_pairs δ ≤ O(log n) E_edges δ. So this is right for
  expander families.

### 4.4 Expansion (part 3)

- e_ab(x^{i+1}) = [e_ac(x^i), e_cb(x)], and additivity in t, give generation.
- SL₃(F₂[x]) is a lattice in SL₃(F₂((1/x))) and has (T).
- Reduction mod p is onto, because SL₃ over a field is generated by elementary matrices.
- This is the standard argument ([K]); I did not re-derive (T).

### 4.5 Corollary M2″

- λ₂ ≥ (E_e K − p)/(1 − p), with E_e K = 3/4 and p < 2^{1−3j}.
- Then (3/4 − p)/(1 − p) ≥ 3/4 − p, since the difference is (3p − 4p²)/(4(1−p)) ≥ 0 for p ≤ 3/4.
- So λ₂ ≥ 3/4 − 2^{1−3j}, as claimed.

### 4.6 The pull-back claim (§1.2)

- Common complement.
  - At step t, the bad vectors lie in n subspaces of dimension m + t − 1 ≤ 2m − 1.
  - n·q^{2m−1} < q^{2m} when q > n, so a complement exists.
- Graphs. Γ_a and Γ_b have dim(Γ_a + Γ_b) = m + rk(a−b).
- Scalar extension. Dimensions of sums are preserved by ⊗F_q, and rk_{F₂} = s·rk_{F_q} under the
  regular representation.
- Annihilator. dim((U⊕U⁰)+(V⊕V⁰)) = dim(U+V) + N − dim(U∩V). So τ² = σ_N² on U ↦ U⊕U⁰ ∈ Gr(N, 2N).
- Hence τ = s^{−1/2}·(pull-back of ρ_{Ns}): a scaled pull-back. M2′ follows given `thm_alt_rank_price`.

### 4.7 Numerics [N] (`midref/m2check.py`)

Group elements are enumerated by breadth-first search, or sampled uniformly from SL via GL with the
first row scaled by det⁻¹.

| group | n | E_edges d_J | E_pairs d_J | claim 3j−1 | ratio | λ₂ | 4.2(e) bound | M2″ bound |
|---|---|---|---|---|---|---|---|---|
| SL₃(F₄) (exact) | 60 480 | 0.5 | 2.2917 | 2 | 4.583 | 0.8005 | 0.679 | 0.500 |
| SL₃(F₈) (sample 2·10⁴) | 16 482 816 | 0.5 | 2.907 | 2 | 5.81 | – | – | – |
| SL₃(F₁₆) (sample) | ≈2^{32} | 0.5 | 5.175 | 5 | 10.35 | – | – | – |
| SL₃(F₃₂) (sample) | ≈2^{40} | 0.5 | 5.884 | 5 | 11.77 | – | – | – |
| SL₃(F₆₄) (sample) | ≈2^{48} | 0.5 | 8.162 | 8 | 16.32 | – | – | – |

Further checks:
- SL₃(F₄), exact: the pair distribution is {0: 168, 1: 3528, 2: 35280, 3: 21504}, and
  E_pairs 2^{−d_J} = 0.2222 = (1 + 49/63)/8 exactly, as the transitivity count predicts.
- λ_min = −0.595.
- The notes' SL₂ table (k = 2, 3, 4) is reproduced exactly by independent code: n = 60, 504, 4080;
  E_pairs = 1.500, 1.869, 3.313; λ₂ = 0.731, 0.938, 0.965.
- E_pairs d_J is about 3j − 0.85, so the bound 6j − 2 on the ratio is nearly tight.

## 5. Consequences 4.2(a), (b), (c), (e): correct, constants recomputed

### 5.1 Consequence (a)

Hypotheses: D_f ≤ r on edges, r ≥ 1, λ* ≤ 2^{−r−1}.
1. p ≥ (2^{−r} − λ₂)/(1 − λ₂) ≥ 2^{−r} − λ₂ ≥ 2^{−r−1}. This holds for either sign of λ₂.
2. Take S = {D(u₀,·) ≤ r+2}. Then p ≤ |S|/n + 2^{−r−3}, so |S|/n ≥ 3·2^{−r−3}.
3. Expander mixing with e(S,T) = 0 gives |S||T| ≤ λ*²n², so |T|/n ≤ 2^{−2r−2}/(3·2^{−r−3}) = 2^{1−r}/3 ≤ 1/3.
   This needs the two-sided λ*, as stated.
4. Co-area gives E_pairs|g−g| ≤ (1−λ₂)⁻¹ E_edges|g−g|. Here E_edges|1_S − 1_S| = (2/n)·1_Sᵀ(I−A)1_S
   ≥ 2(1−λ₂)|S||Sᶜ|/n² = (1−λ₂)·E_pairs.
   - g = 0 on a set of density ≥ 2/3, so E_pairs|g−g| ≥ (4/3)E g.
   - λ₂ ≤ 1/4, so E g ≤ (3/4)·(4/3)·r = r.
5. E_pairs D ≤ 2E g + 2(2r+2) ≤ **6r + 4**. ✓

### 5.2 Consequence (b)

- 1 − 2^{−D} ≤ D/2 and 1 − 2^{−D} ≥ ½·1[D≥1] for integers D ≥ 0.
- Prop. S rearranges to E_pairs(1−K) ≤ E_edges(1−K)/(1−λ₂).
- So Pr_pairs[D ≥ 1] ≤ e/(1−λ₂) ≤ 1/4. Hence Σ s_i² ≥ 3/4, and the largest fibre has density ≥ 3/4.
- Then (3/2)E g ≤ e/(1−λ₂), so E_pairs D ≤ 2E g ≤ **(4/3)e/(1−λ₂)**. ✓
- More generally, with largest fibre density σ: E_pairs D ≤ e/(σ(1−λ₂)).

### 5.3 Consequence (c)

- Jensen gives E_edges 2^{−D} ≥ 2^{−e}, so p ≥ c = (2^{−e} − λ₂)/(1 − λ₂).
- The ball of radius R = ⌈log₂(1/c)⌉ has density ≥ c − 2^{−R−1} ≥ c/2.
- So E_pairs D ≤ **2e/(c(1−λ₂)) + 2⌈log₂(1/c)⌉**. ✓

### 5.4 Consequence (e)

This is Prop. S rearranged. It needs p < 1. ✓

### 5.5 §4.4

- **Eigenvalue formula.** Re-derived: Σ_{u,v≠0}(−1)^{uᵀBv} = 2^μ(2^{μ−ρ} − 1) − (2^μ − 1). Checked
  numerically: λ₂ = 1/9 for μ = 2 and 0.3469 for μ = 3, matching the formula.
- **"Proposition S is tight up to O(2^{−μ})."** This undersells it: **it is exactly tight.**
  - 2^{−rk(a)} = E_x 1[ax = 0], and {a : ax = 0} is a subspace whose annihilator is {y xᵀ}. So the
    Fourier transform of the kernel is supported on matrices of rank ≤ 1.
  - All rank-one characters have eigenvalue λ₂, so equality holds.
  - Numerically: 1/9 + (8/9)(0.4375) = 0.5000 for μ = 2, and 0.3469 + 0.6531·0.2344 = 0.5000 for μ = 3.
- **Percolation barrier.**
  - PSD: Pr[u↔v] = E Σ_C 1_C(u)1_C(v), and integer powers follow by Schur products.
  - Upper bound: Σ_{ℓ≥d_G} d(d−1)^{ℓ−1}p^ℓ ≤ 2((d−1)p)^{d_G}/(1−(d−1)p).
  - The factor-2 comparison for p ≤ (d−1)^{−2} follows from (d−1)p ≤ √p. ✓

## 6. Theorem M0 and §2.2: correct

### 6.1 Theorem M0

- **Affine action.** The group 𝔄 = {a ↦ αaα′ + b} is transitive on ordered pairs with rk(a−a′) = j:
  - choose α, α′ with α(a−a′)α′ equal to the target difference;
  - then fix b.
  So for σ uniform in 𝔄, (σa, σa′) is uniform on that orbit.
- **No averaged price is needed.** The proof averages *inequalities*:
  - each w∘σ∘f is a price on V (AN A.4: pull-backs of prices are prices);
  - apply the Poincaré inequality to each one, then average.
  - E_σ w(σa, σa′)² = D(j)² is exactly AN's D(j)²: the mean of |a, a+W|² over all a and all W of rank
    j, with w symmetric.
- **D.2 Step 1 (quote).** "the mean of the second inequality of Lemma C.4(b) over these quadrilaterals
  is D(i+j)² ≤ D(i)² + D(j)²" (paper l.1717–1722).
  - So the **squared** price is subadditive along transversal steps.
  - Step 1 is unconditional:
    - it uses only Prop. C.3 ("Every price on a set V is the pull-back of the metric of a price
      space") and Lemma C.4(b) (Reshetnyak's inequality in CAT(0));
    - neither depends on ¬contracting, even though the D.2 proof opens with "Suppose that the
      contracting hypothesis fails".
  - I re-checked the averaging. a is uniform and independent of (W, W′), so all four sides and both
    diagonals have the stated uniform distributions, and both diagonals have difference W + W′ in
    characteristic 2.
  - Induction gives D(j)² ≤ j·D(1)². Also D(μ)² ≤ D(j)² + D(μ−j)², including j = 0 and j = μ, where
    it is trivial.
- **Normalisation.** π (ordered pairs, diagonal included, weight n⁻²) and ε (weight A_uv/n) are
  probability distributions. So Σπ_j = 1 and Σ_j π_j(μ − j) = μ − P.
- **Result.** D(μ)² − (μ−P)D(1)² ≤ Σπ_j D(j)² ≤ γ Σε_j D(j)² ≤ γe·D(1)². Hence
  **D(μ)² ≤ (μ − (P − γe))·D(1)²**. ✓
- **It is Def. D.1 at this μ.** Take s² = max(1, μ − (P − γe)).
  - s ≥ 1, and s² < μ because P > γe and μ ≥ 2.
  - s does not depend on the price.
  - D(1) = 0 is harmless.
  - The hypothesis μ ≥ 2 is all Def. D.1 asks; Step 1 holds for every μ.

### 6.2 §2.2 monotonicity

- An embedding ι(a) = αaα′ + b, with α of size μ′×μ injective and α′ of size μ×μ′ surjective, is
  rank-isometric.
- For uniform (α, α′, b), the pair (ιa, ι(a+W)) is uniform among the pairs of Mat_μ′ with difference
  rank r:
  - b makes the base point uniform and independent of the rest;
  - the law of αWα′ is GL_μ′ × GL_μ′-invariant, hence uniform on rank r.
- So D_μ′(r)² = E_ι D_ι(r)², and the argument goes through with the same gain η. ✓
- "Contracting at μ ⇔ at all μ′ ≥ μ" is correct, upward.

### 6.3 §2.3

- "Contracting fails at μ ⇔ ρ_μ is a price" (μ ≥ 3): ⇒ is AN Steps 2–7 at that μ; ⇐ holds because ρ_μ
  has D(μ)² = μD(1)². ✓
- Step 2 uses only the failure at that μ.

## 7. Lemma K and Proposition S: correct (and formalised)

- **Lemma K.**
  - 2^{−rk c} = |ker c|/2^μ = Pr_x[cx = 0].
  - K(a,b) = E_x Σ_y 1[ax=y]1[bx=y] is an average of Gram matrices.
  - Powers follow by Schur products (equivalently, independent x's).
  - The remark "only integer k": Schoenberg plus the non-Hilbertian ρ (M5, N5). This is fine as
    stated.
- **Proposition S.** tr(AK) = Σ λ_i φ_iᵀKφ_i, where each φ_iᵀKφ_i ≥ 0 (this is where PSD is used),
  tr K = n (K_vv = 1), and φ₁ = n^{−1/2}·1 (so φ₁ᵀKφ₁ = n·E_pairs K).
  - **Which eigenvalue:** λ₂, the second largest and *signed*. Since Σ_{i≥2} λ_i q_i ≤ λ₂ Σ q_i for
    q_i ≥ 0, the bound holds with λ = λ₂ even when λ₂ < 0. max(λ₂, 0) is a harmless weakening,
    because the right-hand side is increasing in λ when E_pairs K ≤ 1.
  - It is **one-sided**: λ* and |λ_n| are not needed.
  - **Diagonal:** u = v is included in E_pairs. Loops in E_edges are fine.
- **Lean** (`lean/PortsLean/RankKernel.lean`, all `[propext, Classical.choice, Quot.sound]`):
  - `card_ker_mul_two_pow_rank`: #{x | c x = 0}·2^{rank c} = 2^n over ZMod 2.
  - `rankKernel_psd`, `rankKernel_pow_psd`: Σ w_i w_j 2^{−k·rank(a_i−a_j)} ≥ 0 for all k ∈ ℕ.
  - `spectral_ineq`, the abstract Prop. S.
    - Hypotheses: A with row and column sums 1 (no symmetry needed); the quadratic-form hypothesis
      Σ A g g ≤ λΣg² on 1^⊥; a feature-map kernel with K(u,u) = 1.
    - Conclusion: N⁻¹ΣA K ≤ λ + (1−λ)N⁻²ΣK, in exactly the notes' normalisation.
  - `propS_rank`, `propS_rank_pow`: Prop. S for matrix placements over F₂.
  - Courant–Fischer (from λ₂ to the quadratic-form hypothesis) is left as a hypothesis.

## Recommended edits

1. §0 row 2: split the tag into "[R] for ports ⇒ contracting" and "[D] for ⇔ (Theorem A)".
2. §2.4 last bullet / §0 row 7: say that only ⊆ is [R], conditional on the OA analogue of M0 (EG §2.2
   and (4.5) not re-checked), and that equality needs C_OA ⇒ P_OA [D, OA].
3. 4.2(d):
   - the LPS sentence follows from (c), with constant ≈ 56 at p = 17; (a) needs p ≥ 62;
   - replace "the cubic window is empty" with "the window is e < 0.085".
4. §0 row 5 / §5.2: write "Grassmann edge distance ≤ 1". As an F₂-rank placement the edge ranks are
   about 2 log₂ n (scale-free ratio).
5. §4.4: Prop. S is *exactly* tight on Cay(Mat_μ, rank 1) with the identity placement, because the
   Fourier support of 2^{−rk} is rank ≤ 1.
6. Prop. S: λ = λ₂ (signed) suffices.
