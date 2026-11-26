# Referee report: research/sat3/q1-notes.md (26 Nov 2026)

Scope: `q1-notes.md` §§0–6, and its inputs: `sat3/notes.md` §§2–4 and `review-sat3.md`; `ports/c1d1/notes.md` D1.1–D1.3;
`ports/middle/notes.md` §1.2; AN `scratchpad/fm/paper.txt` (Def. A.4, Prop. C.3, Lemma C.4, Thm D.2 Steps 1–8).
Every number below comes from my own code in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refQ1/`, listed at the end. I did not run
`q1_verify.py` or `q1_x4.py`, and none of my code imports them.

Tags: **[R]** checked here in full; **[D]** argument checked, rests on a named unreviewed input; **[N]** my numerics;
**[C]** conjecture; **[X]** false or dead.

## Verdicts, weakest first

| # | claim | verdict |
|---|---|---|
| 6a | Prop. 6.2 (Z₃ has no skew realisation) | **wrong as stated, correct with an added hypothesis** (counterexample below) |
| 4 | Theorem D′, "repairs Theorem S" | **correct for the per-copy class; the "repair" is a narrower class than Theorem S** |
| 3′ | Cor. 3.3, "a non-graph is an extreme point, hence not in the hull" | **gap** (unused anywhere) |
| 2′ | §0 item 2, "on every set of generic edges … which is the cap" | **wording error** (true only for balanced sets) |
| 2″ | Remark 2.3.2, "every entry of the pod column becomes 0.7071" | **correct only after changing the net family per row** |
| 3 | Theorem B (finite subsets of 𝒞_N(2^s) are prices when contracting fails), Cor. 3.2 (hull) | **correct** |
| 5 | E_D: balanced, fully crossing, F_CAT = 1/√2 | **correct** |
| 6b | Lemma 6.1, Remark 3.4, dead values Φ = 9/4 and Φ = 1 | **correct** |
| 2 | Theorem A (placement, value, counts, cap tightness, Cor. 2.2) | **correct** (can be upgraded to [R]) |
| 1 | The space 𝒞_N(q): well defined, Cone(Δ) × ℝ, CAT(0), subspace formula | **correct** |

The unconditional statement that another theorem depends on is "𝒞_N(q) is CAT(0), and Theorem A gives F_CAT(𝒩) ≥
1/√2 − ((q+1)/√2 − 1)/(g+1) for every prime power q". It stands [R].

---

## 6a. Prop. 6.2: wrong as stated [X]; repaired statement [R]

**The step that fails.** The proof writes R₂ ⊂ W₂₀ = C₀ + D₂. That equality needs C₀ ∩ D₂ = 0. The hypotheses
(dim W_rc = 2s and D_{r+c} ⊂ W_rc) do not give it.

**Counterexample** [N] (`t_prop62.py`). Take s = 1 over F₂⁴, with R_r = D_d = ⟨e₁⟩ for all r, d, and C₀, C₁, C₂ =
⟨e₂⟩, ⟨e₃⟩, ⟨e₄⟩. Every W_rc = ⟨e₁, C_c⟩ is 2-dimensional and contains D_{r+c}. The nine spaces span all of F₂⁴,
so dim 4 > 3s. The exhaustive search fixes R₀ = e₁ and C₀ = e₂ (no loss, since GL is transitive on such pairs). It finds 192
configurations that span F₂⁴, and in **every one of them some node has two coincident hubs**.

**Repair.** Add the hypothesis D_{r+c} ∩ R_r = 0 = D_{r+c} ∩ C_c, i.e. the three hub spaces of each node are pairwise
transversal. For point hubs this means the three hubs of a node are distinct points. With it, C₀ + D₂ = W₂₀ and
R₀ + D₁ = W₀₁, and the proof as written is complete. The search finds no counterexample with distinct hubs. The
follow-up claims need the same hypothesis:
- "the sub-net over ⟨d⟩ lies in W_n + W_{n′}" (I re-derived the closure: from R_i, C_j one gets D_{i+j}, from R_i, D_k
  one gets C_{k−i}, and so on, so all indices in ⟨d⟩ are reached);
- "cyclic nets have no realisation of this kind";
- "Δ₃ gets ≤ 1/3 from point hubs on node-lines".

Hubs placed at coincident points are a different kind of realisation, and nothing here bounds them.

## 4. Theorem D′ and the repair of Theorem S

### What I verified [N, R]

- **Partition** (`t_x4.py`, my code). I used Lemma 4.1 of q1 §4.2, which assigns each generic edge to the copy (S = im(a−a′), coset
  a + Hom(F₂², S)).

  | g | generic edges | copies | (planes × cosets) | edges per copy | remainder | 3/(g+1) |
  |---|---|---|---|---|---|---|
  | 4 | 48 | 1 | 1 × 1 | 48 | 0.60000 | 0.60000 |
  | 8 | 1344 | 28 | 7 × 4 | 48 | 0.33333 | 0.33333 |
  | 16 | 26880 | 560 | 35 × 16 | 48 | 0.17647 | 0.17647 |

- **Isomorphism with merge structure.** For every copy I fix the F₂-linear coordinates S ≅ F₂² and map the coset to
  Mat₂(F₂). Two checks hold for every copy at g = 4, 8, 16:
  - The edge set of the copy is exactly the set of generic pairs inside the coset, and it maps onto X₄.
  - For each of the three classes, the big-net groups restricted to the coset are exactly the lines of the small net,
    of the same class. So merges restrict to merges.

  The proof of Lemma 4.1 is also correct [R]. If a coset a″ + Hom(F_q², S′) contains a and a′, then im(a−a′) ⊆ S′,
  so S′ = S. Inside the coset, line membership and rank are computed as in the small net.
- **Balance.**
  - X₄ is balanced [N]. The general X_q(P) is balanced too [R]: with b = uφ_x^T and b′ = u′φ_{x′}^T, b − b′ is invertible
    iff u, u′ are independent. That gives (q²−1)(q²−q) = |GL₂(F_q)| pairs, which is the degree. I checked this
    numerically for q = 3 and all 11 slope sets P with |P| ≥ 2.
  - The whole generic edge set is balanced at g = 4, 8, 16, as it must be, because balance is additive over the copies.
- **Floor of X₄ when contracting fails** = 48λ/√2 per merge. The lower bound is Thm C, which needs only the placement
  and Thm B and does not need balance. The upper bound is Thm 3.2 for each pair of merges, which needs balance and full
  crossing. [D on AN's `thm_alt_rank_price`]

### The proof of D′ against D1 [D]

(i) and (ii) are D1's Lemma D1, Lemma D2 and Theorem D, with 1/√2 in place of 1/√p. They are valid because the class
has a **finite list of fixed configurations, all-crossing, with one identity per configuration and a product term set**.
Under that hypothesis the averaging step "one C recurs with λ → ∞" goes through, and the floor with no rate can be
applied. This is exactly the referee's fix 2 in `review-sat3.md`.

One point to restate. D′(ii) concludes "contracting over k, then items 3–4 of D1.3", but those items need contracting
over k̄. The clean route is direct: an identity over k is also one over k̄, and costs over k̄ are at most costs over k.
So if contracting failed over k̄, Theorem C over k̄ would contradict the engine. Hence the engine forces contracting
over k̄. This is a wording fix, not a gap.

### Is "per-copy pieces" what real engines do?

Anthropic's engine is per-copy: App. B pieces on each crossing, and terms are products. So D1's class contains the one
known engine, and D′ is a genuine theorem about natural engines.

But D′ is weaker than "Theorem S repaired" sounds:
- Theorem S, as stated in `notes.md` §6, allows one identity per level for the whole net level, with 2^{o(λE)} arbitrary
  terms. D′ does not cover that class.
- D′ also does not cover any term set that is not a product over the X_q copies. Examples are pieces on whole
  translation classes E_v of the order-g net, which have g² nodes and so grow with g, and correlated choices across
  copies. These are exactly what a "three merges beat two" engine on nets would most plausibly use (`notes.md` §7.5).
- For the whole-level class, only the per-level form of q1 §4.1 is proved, with λ₀ depending on g.

The authors' own "Scope, honestly" paragraph says this. The headline in §0 item 4 ("This repairs the gap …") should
say "for engines with per-copy pieces on the X_q partition".

### What replaces Theorem S (precise statement)

- **S′(a) [D, tower form].** Let k be a field, q = 2^s, and P ⊆ P¹(F_q) with |P| = p ≥ 2 (q = 2, p = 3 is the 3-net of
  F₂^m). Consider tower engines in the sense of D1.1 such that:
  - every level is the level of some 𝒩(q, m_ℓ, P) with merges into g_ℓ = q^{m_ℓ} groups;
  - the generic edges are partitioned into copies of X_q(P) as in Lemma 4.1, with remainder ξ_ℓ = (q+1)/(g_ℓ+1);
  - the terms are products of pieces, one per copy, taken from one identity Σ_{i∈I} A_i = d·f_{X_q(P)} with
    |I| ≤ 2^{τ(λ)}, τ = o(λ).

  If such an engine has log-exponent α′ > 1/2 along infinitely many n, then contracting holds over k̄, and 3-SAT is
  power-saving (Theorem R in characteristic 0, C1 in characteristic p).
- **S′(b) [D, per-level form, whole-level identities].** For fixed g = 2^m ≥ 4 and η > 0: if for some λ ≥ λ₀(g, η, τ)
  the three-merge level tensor of the F₂^m net has a cover with at most 2^{τ(λ)} terms in which every term has
  min_k c_k ≤ (1/√2 − 1.13/(g+1) − η)Eλ, then contracting holds over k̄. The dependence of λ₀ on g is not controlled,
  so this gives no tower statement.
- **Items 2–3 of the old Theorem S** (thresholds 0.7075 and 0.79 for whole-level classes) stay [C], with the same
  uniformity gap. S′(a) supersedes them for the per-copy class, with the stronger threshold 1/2.

## 3′. Cor. 3.3, "proper subset of the slice": gap [unused]

The notes say a μ-dimensional non-graph U is a vertex of every cube containing it, "hence an extreme point, and is not
in the hull of the others". For the closed convex hull in a CAT(0) space this does not follow. The iterated-geodesic
hull keeps extreme points of the ambient set out only at finite stages; the closure could still contain U as a limit.
Moreover, "extreme points of a closed convex hull lie in the closure of the generating set" is not a known general fact in
CAT(0) spaces.

A proof would need a convex function that is ≤ 0 on graphs and > 0 at U, or a direct argument in the cone. The notes
say this is not needed, and I agree: nothing downstream uses it. Mark it [C].

## 2′, 2″. Wording

- §0 item 2: "on every set of generic edges the placement value is exactly 1/√2 …, which is the cap". The placement
  value is 1/√2 on every set of generic edges [R]. It equals the cap only for **balanced** sets. A single wire is fully
  crossing but unbalanced, and its CAT(0) cap is 1: in a Hilbert space all hub differences can be parallel to the leg
  line. Theorem A itself states this correctly ("for every balanced set C").
- Remark 2.3.2: "The table of `notes.md` §5.4 is superseded: every entry becomes 0.7071."
  - As an F_CAT statement (unconditional), this is right for nets of F_q^m with any q ≥ p − 1.
  - As a price statement when contracting fails, it needs q = 2^s ≥ p − 1. Those are F₄^m nets for p = 4, 5 and F₈^m
    nets for p ≤ 9, not the table's F₃^M nets (p = 4) or F₇ nets (p = 7). For odd q the price statement is open, as
    §0 item 6 says. The row labels must change.

## 3. Theorem B and Cor. 3.2: correct [D on `thm_alt_rank_price`; every other step R]

- **Step 0.** The map s ↦ ½ + εs scales d by ε exactly and sends filtrations to filtrations. Multiples of prices are
  prices (Def. A.4). ✓
- **Step 1.** 𝔉 is a finite set of *subspaces*, not of basis-labelled cube vertices. This is what makes the later gluing
  work: j(V_i) does not depend on which cube V_i is viewed in. ✓
- **Step 2.**
  - (2a) Restriction of scalars from F_q to F₂ preserves + and ∩ and multiplies dimensions by s. ✓
  - (2b) dim((U⊕U⁰)+(U′⊕U′⁰)) − n = dim(U+U′) + n − dim(U∩U′) − n. ✓
  - (2c) This is `ports/middle` §1.2 verbatim. The counting r·Q^{2n−1} < Q^{2n} needs Q > r. Graphs over A = U₁⊗F_Q
    give dim(U_i+U_j) − n = rk(a_i − a_j), and the regular representation multiplies ranks by t. ✓
  - (2d) μ = nt ≥ 3 can always be arranged. Mat_μ embeds in Mat_{μ+1} preserving rank, so pad if needed. ✓
  - [N] `t_step2.py` builds ι explicitly in two cases and finds rk(ιU − ιU′) = t·τ(U,U′)² on all pairs (0 failures):
    - 𝔉 = Sub(F₂²): 5 spaces, Q = 8, μ = 6; 10 pairs.
    - 𝔉 = the coordinate subspaces of two random bases of F₂³: 12 spaces, Q = 16, μ = 12; 66 pairs.
- **Step 3** is Prop. C.3. ✓
- **Step 4.**
  - This is AN Step 8 coordinate by coordinate, i.e. `notes.md` Lemma 4.1 with Z = [0,1]^i × {0,1}^{N−i−1}, h = 1. ✓
  - The vertices satisfy τ² = |SΔS′|. ✓
  - Φ_f does not depend on the order of the coordinates: an isometric embedding of a cube is fixed by its vertex images,
    by Lemma 3.1 applied to each simplex of the standard triangulation.
- **Step 5 (the point to press).**
  - Lemma 3.1 is correct. An isometric image of a segment is a geodesic, and geodesics are unique (C.4(a)); induct on
    the dimension.
  - The barycentric formula x = (1−s₁)·1_∅ + Σ_j (s_j − s_{j+1})·1_{V_j} checks. The coefficients are ≥ 0, sum to 1
    and depend on p only.
  - The chain vertices are affinely independent, with intrinsic mutual distances √(dim V_j − dim V_i).
  - So for two adapted bases f, f′ ∈ ℬ the maps Φ_f and Φ_{f′} agree on the chain simplex of p, because they agree on
    its vertices j(0), j(V₁), …, j(V).
- **Step 6.** The worry "pairs whose geodesic leaves both cubes" does not arise. Φ is only needed on P, and for each pair
  {p, p′} the basis f_{pp′} is adapted to both. By Step 5 both points can be computed in that single cube, where Φ_f is
  an isometry. So |Φ(p)Φ(p′)| = |x − x′| = d(p, p′). No compatibility of whole cubes is used, and none is claimed.
  Pull-backs of prices are prices. ✓
- **Cor. 3.2.**
  - With ℬ = all bases, every point of K_N(q) has a chain simplex, so Φ is well defined everywhere.
  - Any two points share a cube, so Φ is isometric, and the geodesic between two images is the image of the segment in
    their common cube, so the image is convex.
  - The image is compact.
  - Every point of the image is reached from the vertices by iterated geodesics, so it lies in every closed convex set
    containing j(Sub V).

  The "hull = K_N(q)" statement holds in every CAT(0) space that contains an isometric copy of (Sub(V), τ) [R].
- **Is q = 2^s needed or sufficient?**
  - Sufficient: yes. The restriction-of-scalars map 𝒞_N(2^s) → 𝒞_{sN}(2) is √s times an isometry on all filtrations,
    not just on subspaces: the F₂-basis {ω_j f_i} is adapted to both and repeats every level s times. [N]
    `t_metric.py` gives max |d_{F₂} − √2·d_{F₄}| = 9·10⁻¹⁶ on 200 random pairs of filtrations of F₄³. So Theorem B for
    q = 2 already implies it for every 2^s, and Step (2a) is a convenience.
  - Needed: only by the proof. No route is known from F₃-subspace lattices to F₂-rank metrics. Whether 𝒞_N(3) is a
    price when contracting fails is open (q1 §8 open problem 2). It is not refuted, and some subsets, such as pods
    with 4 arms, are prices by `notes.md` Thm 4.3.
- **What is new relative to the product-hull theorem (`notes.md` Thm 4.3).**
  - Thm 4.3 is a special case. 𝒞₂(q) is the (q+1)-pod × ℝ. Filtrations split along V = ⊕V_j form the l₂ product
    ∏𝒞_{N_j}, isometrically, using a split common basis. So finite subsets of ∏ (pod × ℝ) with ≤ q+1 arms are covered.
  - New: (1) one price realises *all* coordinate subspaces of several bases at once, using the whole-Grassmannian
    embedding of `ports/middle` §1.2 rather than block-diagonal matrices. (2) Pieces glue along chain simplices, so the
    cubes overlap in a non-product way. (3) The result includes irreducible pieces with flats of dimension ≥ 3, the
    cones over A_{N−1} buildings, N ≥ 3. By Remark 3.4 these are still not trees with two branch points.

## 5. E_D: correct [R + N]

- **Structure.** D ∈ GL₂(F₂) is nonzero and a + D + D = a, so E_D is a perfect matching (8 wires). It is fully crossing
  because Dx ≠ 0 for every x ≠ 0.
- **Balance [R].** For y = n₀ + uφ_x^T one needs uφ_x(x′) = Dx′. That has exactly one solution, which equals deg = 1.
- **Numerics** (`t_x4.py`, `t_chain.py`), for all six D:
  - all 8 edges are generic, and E_D is balanced;
  - with the placement at T = 10⁶, b_k = 5.656851 for each of the three merges (8/√2 = 5.656854);
  - for D = I and every pair of merges, the Thm 3.2 chain is tight up to the convexity slack 5.7·10⁻⁴ at T = 10⁴, which
    is O(1/T).
- **"Union of four AN crossings for each pair of merges"** (partner a + B, Bx_k = 0, Bx_l = Dx_l). It checks in
  characteristic 2: (a+B+D)x_l = ax_l. Enumeration (`t_misc.py`) finds exactly 4 crossing pairs for each of the three
  merge pairs and each D, i.e. a perfect pairing.
- So F_CAT(E_D) = 1/√2 [R]. When contracting fails, the price floor is 8λ/√2 per merge [D on `thm_alt_rank_price`].

## 6b. Lemma 6.1, Remark 3.4, dead values: correct

- **Lemma 6.1 [R].**
  - Pushing the legs out along the line of their apartment does not decrease any s^k (triangle inequality). Lemmas 1.4
    and 6.1 then apply in that apartment.
  - On a projective line, ν = min_supp d is a valuation: it is constant except at at most one point, where it is
    larger. ν̄ is constant except at at most one point, where it is smaller.
  - I checked the four cases (i ∉ {J, J′}; i = J ≠ J′; i = J′ ≠ J; i = J = J′) line by line. Each gives
    Σ_k s^k ≤ a⁺ − b⁻ = d_j − d_{j′} ≤ √2.
  - [N] `t_chain.py` takes the exact far-leg optimum over all 840 frames of F₂⁴ and all unit d, computed as the min-norm
    point of the convex hull. For a collinear pair it gives Σ_k s^k = 1.414214. For a generic pair it gives 3.000000 =
    pδ/√2, so generic edges cannot exceed the placement's total either.
- **Remark 3.4 [R].**
  - At p the tangent cone is ℝ^k × ∏ Cone(Δ_{n_j}), so the link is S(L) * (spherical building), a spherical join.
  - In a join, cos d = cosθ cosθ′ cos d_S + sinθ sinθ′ cos d_B ≤ cos(θ−θ′). Antipodal directions therefore need
    θ = θ′ and antipodal sphere components, which three directions cannot have pairwise unless θ = π/2.
  - Hence tripod arms are ⊥ L. With b_i ∈ L_i this gives |v|² = ⟨v, b₂⟩ − ⟨v, b₁⟩ = 0.
- **Φ = 9/4 [R].**
  - Generic nodes are at Levi-graph distance 4, so with φ ≥ π/4 the two node rays form a line. Then s^k = 2t cosφ for
    every class, and parallel lines are also at distance 4, so δ = 2t.
  - The value is cos φ = √Φ/3.
  - The net's triangles give 6-cycles, so CAT(1) needs φ ≥ π/3. Hence Φ ≤ 9/4.
- **Φ = 1 [R].**
  - The cone over the PG(2,q) incidence graph with edges π/3 is Cone(Δ(GL₃(F_q))), i.e. 𝒞₃(q) modulo its ℝ-factor.
    Hubs at line vertices are the dual of point hubs.
  - In the projection, a vertex has radius t = √(2/3), so δ = √2 = √3·t, matching the notes.
  - Two dual node-lines meet, so Lemma 6.1, applied after duality, gives Σ_k s^k ≤ δ per edge. Hence value ≤ 1/3 and
    Φ ≤ 1. The described legs attain it.
- §6 items 5–7 (direct sums, tripod³, products) were not asked for. I checked only that they are labelled [X]/[D]
  consistently.

## 2. Theorem A: correct; tag can be [R]

All numbers below are from `t_place.py`. It uses my own filtration arithmetic over F₂, F₃ and F₄, the
second-difference distance formula, and no use of Lemma 1.4. T = 10⁴.

| q, m, p | E | generic / collinear / other rank-1 | generic s^k (all classes) | min_k b_k/E | formula | cap √(g/(2(g+1))) |
|---|---|---|---|---|---|---|
| 2, 2, 3 | 120 | 48 / 72 / 0 | 0.999950 | 0.48279 | 0.48284 | 0.63246 |
| 2, 3, 3 | 2016 | 1344 / 672 / 0 | 0.999950 | 0.58247 | 0.58252 | 0.66667 |
| 2, 4, 3 | 32640 | 26880 / 5760 / 0 | 0.999950 | 0.64111 | 0.64115 | 0.68599 |
| 3, 2, 4 | 3240 | 1944 / 1296 / 0 | 0.999950 | 0.52422 | 0.52426 | 0.67082 |
| 3, 2, 3 | 3240 | 1944 / 972 / 324 | 0.999950 | 0.52422 (one merge 0.62422) | 0.52426 | 0.67082 |
| 4, 2, 5 | 32640 | 23040 / 9600 / 0 | 0.999950 | 0.55791 | 0.55796 | 0.68599 |

For every case in the table:
- all hub–hub distances are √2;
- |x_e y_e| = 2T+1;
- |x_e, h|² − (T² + ½) is at −1.5·10⁻⁸ (that is O(1/T²)) for **every** point h of W;
- s^k = 1 − 1/(2T) exactly;
- for rank-one edges, s^{k₁} → √2 and the other classes → 0, both with error O(1/T).

The edge counts match E_gen = E(g−q)/(g+1), E_coll = Ep/(g+1) and E_other = E(q+1−p)/(g+1) exactly.

**(i) Normalisation.** The quantity is `notes.md` §2's: b_k = (L − H_k)/δ_k, with δ_k the largest hub–hub distance
in merge k (here √2 for all k), legs placed per edge end (any points), and b_kδ_k = Σ_e s^k_e. Cor. 3.4 bounds
(1/p)Σ_k b_k in the same units. So the comparison "value = cap" is like for like. ✓

**(ii) Rank-one edges.**
- The recipe is correct. h, i, h′ are independent, and every other point of W has support {i} or {h, i}.
- Optimality "within these hubs" holds in two ways:
  - from the pair bound s^k + s^l ≤ 2|z(a)z(a′)|, where z(a) = W at level ½, so |z z′| = 1/√2 for W ∩ W′ a point,
    together with s^{k₀} ≤ 0;
  - for any p, from Lemma 6.1.
- Generic edges are also capped at Σ_k s^k ≤ p, by the pair bound with |z(a)z(a′)| = 1, and the frame search agrees.
- With these hubs, the total Σ_k b_k of the placement is therefore maximal. Because the placement is balanced across
  merges, its min_k b_k is optimal for these hubs.
- For p < q+1 the rank-one edges with kernel slope outside P give one merge an extra √2. Row (3, 2, 3) shows this.
  Theorem A ignores it, so the bound stays valid; it is not optimal there.

**(iii) Tightness of the cap proof.** I evaluated each step of `notes.md` Thm 3.2 separately on X₄ (all 48 edges, each
pair of merges, `t_chain.py`):

| step | slack at T = 10², 10⁴, 10⁶ |
|---|---|
| convexity λ₁\|xo¹\| + λ₂\|xo²\| ≥ Λ\|xβ\| | 0.339, 3.4·10⁻³, 3.4·10⁻⁵ (→ 0 like 1/T) |
| triangle \|xy\| − \|xβ\| − \|yβ′\| ≤ \|ββ′\| | 0 (x, z(a), z(a′), y are collinear in one apartment) |
| C.4(a) chain for \|ββ′\|² | 1·10⁻¹⁴ |
| balance (cross terms = subtracted terms) | 0 |
| \|o^k o^k′\| ≤ δ | 0 |
| Cauchy–Schwarz | 0 (\|ββ′\| = 1 on every edge) |

b_k + b_l = 67.8822 against the cap √2·48 = 67.8823 at T = 10⁶. Every step is tight in the limit, so there is no
contradiction between the two results.

One observation the notes do not make: here the balance step cancels *edge by edge*. All hubs are pairwise at √2, so
the per-edge cross terms equal the per-edge subtracted terms (1 = 1). The placement attains the cap without using
balance. Balance is needed only for the upper bound.

**(iv) Counts.** Each node has (g−1)(g−q) generic partners, plus (g−1)(q+1) rank-one partners, and the two numbers sum
to g² − 1. E_gen = 48, 1344, 26880 for q = 2. All match [R, N].

**(v) Cor. 2.2 and scope.**
- The pull-back respects the hubs because π(ab) = π(a) + π(b).
- Hubs with equal images coincide (prices are pseudometrics), so δ_k = √2.
- Edges that are not generic get legs along a dummy direction orthogonal to all hubs, so s → 0 for them by Lemma 1.4.
  One dummy coordinate would also do.
- The fraction count |Γ|²|ker|²(g′−1)(g′−q)/2 over |Γ|²(|Γ|²−1)/2 ≥ (1−1/g′)(1−q/g′) checks.
- Z_n^m → F_p^m (p | n), Z_p × Z_p → F_p² and Z₄^m → F₂^m are all fine.
- Scope "any prime power q, m ≥ 2, 2 ≤ p ≤ q+1 slopes in P¹(F_q)": correct for the CAT(0) statement. Nothing in
  §§1–2 uses the characteristic.
- The price versions (Thm C, per-level form, Cor. 2.2's last sentence) need q = 2^s.

**F_CAT(𝒩(q,m,P)) ∈ [1/√2 − ((q+1)/√2 − 1)/(g+1), √(g/(2(g+1)))]**, and F_CAT(C) = 1/√2 for every balanced set of generic
edges [R].

## 1. The space 𝒞_N(q): correct [R + N]

- **Well defined [R].** Lemma 1.1(b): F_s ∩ F′_{s′} is a coordinate subspace of any common adapted basis, so the joint
  level multiset is determined by the numbers dim(F_s ∩ F′_{s′}). Its second differences are the multiplicities m(j,l).
  - [N] `t_metric.py` compares the formula with explicit adapted bases built with randomised choices (two different
    bases per pair). The difference is exactly 0 in all cases: q = 2 (N = 3, 4, 5), q = 3 (N = 3, 4), q = 4 (N = 3).
  - The point at t on the geodesic, built from different adapted bases, is the same filtration in every trial.
- **Cone × line [R, standard].**
  - Filtrations with level vector x in basis f are the points x of the apartment ℝ^N.
  - The S_N walls x_i = x_j cut 1^⊥ into the Coxeter complex of type A_{N−1}, and the cone coordinate is the
    1^⊥-component. The ℝ-factor is (mean level)·√N, an orthogonal split.
  - Two filtrations lie in a common apartment (Lemma 1.1(a)). The chart transition between two apartments containing
    both is the identity on the level multiset (Lemma 1.1(b)), so apartment distances agree.
  - The cone metric over the spherical building Δ restricts to the Euclidean metric on each apartment, because Δ's
    metric restricts to the round metric on apartments (B–H II.10A.4 and its proof) and the cone formula is
    Euclidean in each 2-plane.
  - Hence d is the Cone(Δ) × ℝ metric.
  - Δ is finite for finite q, so it is complete. CAT(1) is B–H II.10A.4, the cone being CAT(0) is II.3.14, and the
    product is CAT(0). So CAT(0) follows from the cited theorems and not only from tests.
- **Subspace formula [R].** U, U′ are coordinate subspaces 1_S, 1_{S′} in a common basis, so d² = |SΔS′| =
  dim(U+U′) − dim(U∩U′). [N] error ≤ 9·10⁻¹⁶.
- **Independent CAT(0) tests [N].** The tests use explicit geodesic points. Each triple and quadruple was classified by
  enumerating all frames of the space (28, 234, 840 and 1120 frames for (q, N) = (2,3), (3,3), (2,4), (4,3)).

  | q, N | trials | triples not in a common apartment | C.4(a)/CN max excess | Reshetnyak max excess | 4-point (B–H II.1.11) max excess |
  |---|---|---|---|---|---|
  | 2, 3 | 400 | 139 | 4·10⁻¹² / 3·10⁻¹⁵ | 9·10⁻¹⁶ | 4·10⁻¹⁶ |
  | 3, 3 | 300 | 162 | 3·10⁻¹² / 3·10⁻¹⁵ | 0 | 0 |
  | 2, 4 | 300 | 193 | 4·10⁻¹² / 4·10⁻¹⁵ | < 0 | < 0 |
  | 4, 3 | 150 | 94 | 3·10⁻¹² / 4·10⁻¹⁵ | < 0 | 0 |
  | 3, 4 / 2, 5 | 60 each | not enumerated | ≤ 3·10⁻¹² | < 0 | < 0 |

  The excess 4·10⁻¹² is rounding, since levels are stored to 12 digits.

  A note for anyone repeating this: a naive 4-point test that fixes the comparison diagonal at d(x₁,x₂) reports false
  "violations" of size ~1 when the comparison quadrilateral is not convex. The test must maximise over D ≥ d(x₁,x₂),
  which my final version does.

## Minor

- Lemma 1.4 is correct. The replacement of f_{i*} keeps the filtration x_T, and T + ⟨c,d⟩ − min_A d_i + O(1/T) follows.
  In the statement, i* minimises c_i + Td_i, so for large T it minimises d_i with ties broken by c.
- §2.2, "For a collinear edge … successor": `q1_verify.py` alternates between the two other classes by edge parity
  instead. That is harmless for the totals but is not the rule stated in the notes. My code uses the stated rule.
- The finite-g deficit window [0.354, 1.121]/(g+1) for q = 2 is correct: 1/(2√2) = 0.3536 and 3/√2 − 1 = 1.1213.
- Lemma 6.1 implicitly assumes W ≠ W′. Distinct nodes of 𝒩(q,m,P) always have distinct planes, so this is fine.

## Scripts

All in `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refQ1/`:
- `ff.py`: fields F_q for q = 2, 3, 4, 8, 16, 32; subspaces; filtrations; both distance computations; geodesic points.
- `t_metric.py`: item 1 (output in `metric_out.txt`).
- `t_place.py`: item 2 placement and counts (`place_out.txt`, `place_full.txt`).
- `t_chain.py`: Thm 3.2 tightness on X₄ and E_D, b_k of the six E_D, far-leg optimum over all frames (`chain_out.txt`).
- `t_x4.py`: partition with merge structure, balance (`x4_out.txt`).
- `t_misc.py`: E_D crossing pairings, balance of X₃(P) (`misc_out.txt`).
- `t_step2.py`: explicit ι of Theorem B Step 2 (`step2_out.txt`).
- `t_prop62.py`: counterexample to Prop. 6.2 as stated (`prop62_out.txt`).
