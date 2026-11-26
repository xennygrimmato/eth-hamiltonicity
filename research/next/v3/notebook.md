# v3 notebook: the contracting hypothesis, ports, and ω (26 Nov 2026)

Tags: **[L]** machine-checked in Lean (`lean/EthFollowup/Spectral/`, standard axioms, no `sorry`; exploratory files,
not imported by the root module, not claimed results). **[R]** proved here on paper, unreviewed. **[N]** computed;
script and output in this folder. **[K]** quoted from a named source; the 2026 sources are unrefereed preprints.
**[C]** conjecture or open.

Sources. A = Anthropic, "VP ≠ VNP over every field" (23 Nov 2026). G = OpenAI, "Euclidean geometry in the asymptotic
spectrum of tensors". P = OpenAI, "Circuit lower bounds for Hamiltonian cycle and the permanent". M = OpenAI, "The
matrix multiplication exponent" (all 24 Nov 2026). c1 = `research/vpvnp/c1/notebook.md`.

## 0. Summary

| # | Statement | Tag |
|---|---|---|
| A | Anthropic's contracting hypothesis implies that the field admits OpenAI's ports. | R, from K |
| B | If the contracting hypothesis fails, then ω ≥ 2e^{z²/2} = 2.1944, z = Φ⁻¹(2/3). Already "the rank metric on Mat₂(F₂) is a price" gives ω ≥ 3/√2 = 2.1213. | R, from K; two steps L; numbers N |
| B′ | So ω < 2.1944 implies the contracting hypothesis, and ω < 2.1213 implies it at μ = 2. If ω = 2, both the contracting hypothesis and ports hold. With OpenAI's claimed ω = 9/4 the test is passed by a margin of 2.5%. | R |
| C | At μ = 2 the dichotomy is one finite question: the contracting hypothesis holds at μ = 2 iff the rank metric ρ₂ on the 16 matrices is not a price. (c1 had this for μ ≥ 3.) | R + N |
| D | ρ₂ is {0} ∪ [3]×[3] ∪ S₃ with an explicit table. Around each rank-two pair there are six flat pages; three of them form a book (tripod × segment). | L + R |
| E | tripod × line a price geometry ⇒ ω ≥ 3/√2. tripod × ℓ₂ ⇒ ω ≥ 2.1944. So price geometries are closed under products with a line only if ω > 2.12. | R, from K |
| F | Correction to v2 and to my earlier claim: the eight points 0, I, hexagon do not force a cone of angle 3π. They also sit in tripod × tripod × line. Only the six flat sectors are forced. | L + N |

Chain (Figure `fig_book.png`, panel c):

    no ports  ⇒  contracting fails  ⇒  ρ_μ is a price for every μ  ⇒  books × cubes are price geometries  ⇒  ω ≥ 2.1944.

Nothing here decides the contracting hypothesis. What is new is that it is tied to ports on one side and to the
value of ω on the other.

## 1. Definitions [K]

- Price: a limit of positive multiples of the wire pseudometric d_φ(u,v) = log₂ φ(⟨2⟩_uv) of spectral points φ
  (A, App. A). Every price is the pull-back of a complete CAT(0) space whose metric is a price (A, Prop. C.3;
  G, Thm "geometry"). Spectral spaces are closed under rescaling, closed convex subspaces, pointed ultralimits (P §2).
- Contracting hypothesis (A, Def. D.1): some μ ≥ 2 and s² < μ with D(μ) ≤ s·D(1) for all prices on Mat_μ(F₂);
  D(r)² = mean squared distance over pairs whose difference has rank r.
- Rank metric ρ_μ(a,b) = √rk(a−b). The hypothesis fails ⇒ ρ_μ is a price for every μ ≥ 3 (A, proof of Thm D.2,
  Steps 1–7; c1 Prop. 1), hence for μ = 2 by pull-back along a ↦ diag(a, 0).
- Ports (P §2; G Def. "ports"): regular multigraphs of one degree and unbounded order with V(x) ≤ γ·E_G(x) for every
  placement in every Hadamard spectral space.
- Shared-label rate δ(S): price per bit of Δ_S(2). Monotone; submodular on intersecting sets (G, Prop. "Copying a
  common label"); equal to the mean width on every finite-dimensional convex Euclidean patch (P, proof of Lemma
  "Diagonal price in a ball", first step).
- For three sites, perimeter ≤ ω·δ, because three binary wires on a triangle are the 2×2 matrix multiplication
  tensor, of asymptotic rank 2^ω (M, introduction).

## 2. Theorem A: contracting ⇒ ports [R from K]

G builds its port graphs (Prop. "refresh-graph", appendix "Construction of the port graphs") from one input:

> Grassmann gap at m: there is η > 0 with B_m ≤ (m − η)·B_1 for every map of the m-dimensional subspaces of F₂^{2m}
> into a complete CAT(0) spectral space; B_r = mean squared distance over pairs with dim(U+V) = m + r.

The rest of that construction (sparse matrices, Cesàro averages, the replacement product) uses only barycentres in
CAT(0) spaces. G obtains the gap from "no (k+1)-cube"; it can be obtained from the contracting hypothesis instead.

*Proof.* Suppose the hypothesis holds at μ₀, and let m > μ₀ be a power of two. If the gap failed at m, G's own
equality argument (rescale to B_1 = 1, B_m → m, pass to a limit) gives a spectral space in which
d(U,V)² = dim(U+V) − m for all pairs with dim(U+V) < 2m. Pull back along a ↦ graph(diag(a,0)), a ∈ Mat_{μ₀}(F₂).
By `finrank_graph_sup_graph` [L], dim(graph a + graph b) − m = rk(a−b) ≤ μ₀ < m. So ρ_{μ₀} is a price, with
D(μ₀)² = μ₀·D(1)², against the hypothesis. Hence the gap holds at m, and G's construction gives ports. ∎

Lean: `GraphRank.lean`, `finrank_graph_sup_graph`: dim(graph f + graph g) = dim V + rank(f − g), any field.

Consequences. (i) "No ports" implies that the contracting hypothesis fails, so that every ρ_μ is a price.
(ii) Anthropic's contracting case is contained in OpenAI's ports case. (iii) The converse, ports ⇒ contracting, is
open. A counting argument suggests the finite spaces ρ_μ alone do not defeat bounded-degree random graphs (a ball of
rank radius εμ has only N^{2ε} of the N points), so a proof would need the hulls.

Not checked: I read G's appendix once. The claim that nothing but the gap is used should be re-read by a second
person, or checked against OpenAI's Lean.

## 3. Proposition C: the case μ = 2 [R + N]

A's Steps 4–7 need μ ≥ 3. For μ = 2, Steps 1–3 still give: if the hypothesis fails at μ = 2 there is a price on
Mat₂(F₂) with D(1) = 1, D(2)² = 2, and every quadrilateral a, a+W, a+W+W′, a+W′ (W, W′ of rank one, W+W′ invertible)
is a flat parallelogram. Write n_a(X) = |a, a+X|².

1. n_a(W) does not depend on a for W of rank one: (D.1) gives invariance under the four rank-one matrices
   transversal to W, and these span Mat₂(F₂).
2. Fix an invertible V and its three splittings V = W_j + W_{j+3}. The parallelogram law gives
   n_a(V) + n_{a+W_j}(V) = 2n(W_j) + 2n(W_{j+3}) =: 2s_j. Two neighbouring W_j, W_{j+1} add up to a matrix U of rank
   one, and n_{a+U}(V) = n_a(V) + 2(s_{j+1} − s_j); as 2U = 0, s₁ = s₂ = s₃.
3. These equal-sum conditions for all six V have only the constant solutions (`rank2.py`: 12 equations, rank 8, on
   9 unknowns) [N]. So n ≡ 1 on rank one, and n_a(V) = 2 + τ_V·χ_V(a) with χ_V(a) = (−1)^{tr(V⁻¹a)}.
4. The three parallelograms on the diagonal [a, a+V] share its midpoint m, and |a+W_j, m|² = (2 − τ_Vχ_V(a))/4.
   For W_j, W_{j+2} (difference V′ of rank two): 2 + τ_{V′}χ_{V′}(a+W_j) ≤ 2 − τ_Vχ_V(a). Summed over a both sides
   are equal, so equality holds for every a; distinct characters are independent, so τ = 0. (`rank2.py` confirms by
   a linear programme: largest |τ| is 0.) ∎

So: **the contracting hypothesis holds at μ = 2 ⇔ ρ₂ is not a price**, and it holds at all ⇐ ρ₂ is not a price.

## 4. The shape of ρ₂ [L + R]

`RankTwo.lean` [L], all by exhaustion:
- 9 matrices of rank one, 6 invertible; rank of a difference is a metric (`rk_add_le`).
- The rank-one matrices are x_i y_jᵀ, a 3×3 grid; rk(W − W′) = [i ≠ i′] + [j ≠ j′] (`cell_rk`).
- For invertible V, the rank-one W with rk(V − W) = 1 are six, each has two neighbours at rank-distance one among
  them, there is no triangle, and the opposite of W is V − W (`hex_card`, `hex_two_neighbours`, `hex_no_triangle`,
  `hex_opposite`). For V = I they are the off-diagonal cells (`cell_one`).
- `rank2.py` [N]: invertible g ↔ permutation σ of the three vectors; rk(g − x_i y_jᵀ) = 2 iff i = σ(j);
  rk(g − h) = 1 iff the parities differ.

Forced flat pieces in any CAT(0) space containing ρ₂ [R]. Let m be the midpoint of 0 and I and E₁,…,E₆ the hexagon
in cyclic order. Each E_j is at distance 1 from 0 and I, so at most 1/√2 from m; non-neighbours are √2 apart, so
all are exactly 1/√2 from m and m is the midpoint of every non-neighbouring pair. Hence:
- the half-squares H_j = conv(0, I, E_j) are flat; H_j ∪ H_k is a flat unit square when j, k are not neighbours;
- neighbours span a flat right-angled sector at m;
- H₁ ∪ H₃ ∪ H₅ is a convex subset isometric to a piece of tripod × segment: a **book** with spine [0, I] and three
  pages. Its tips E₁, E₃, E₅ are pairwise √2 apart and 1/√2 from the spine.

Where the pieces live (`RankTwo.lean` `apex_embeds`, `H8_embeds`, `diag_cells_misplaced` [L]; `embed.py` [N]):
- 0 and the nine rank-one matrices embed isometrically in tripod × tripod × line: cell (i,j) ↦ (leg i at ½, leg j at
  ½, 0), 0 ↦ (centre, centre, −1/√2).
- H₈ = {0, I, E₁..E₆} embeds there too, with I ↦ (centre, centre, +1/√2). H₈ is not Euclidean (Gram eigenvalue −¼).
- The embedding does not extend to all of ρ₂. ρ₂ lies in the building of GL₄(F₂((t))) (c1 §2), not in this product.

**Correction.** I said earlier that H₈ forces a cone of total angle 3π at m, times a line. That is one model. The
product model above is another, and there the bisectors of opposite sectors are at angle π/2, not π. Only the six
flat sectors and the pairwise angles of the six rays are forced. The v2 notebook's row 3 stands; the reduction
"contracting at μ = 2 ⇐ no price geometry has a 3π cone point" is withdrawn and replaced by Proposition C.

## 5. Theorem B: failure of the contracting hypothesis forces ω ≥ 2.19 [R from K]

**Book bound** (`Book.lean`, `book_bound` [L]): for sites p, q, r and a finite set s,
δ{p,q,r} ≤ δ({p,q} ∪ s) + δ({q,r} ∪ s) − δ({q} ∪ s). Only monotonicity and submodularity are used.

*Proof of B for μ = 2.* Let ρ₂ be a price, X a Hadamard spectral space containing it, and take the book of §4.
Tips p, q, r = E₁, E₃, E₅; s = two points u, d of the spine at distance ¼ from m, that is 1/√8 in units of the
arm 1/√2. The sets {p,q,u,d}, {q,r,u,d}, {q,u,d} lie in flat squares, so their rates are half-perimeters: in units
of the arm, 3√2/2, 3√2/2 and √2. The book bound gives δ(tips) ≤ 2√2 arms = 2 (`book_two_spine_sites` [L]). The
perimeter is 3√2 = 6 arms, and perimeter ≤ ω·δ, so ω ≥ 3/√2 (`omega_sq_ge_of_book` [L]: ω² ≥ 9/2). ∎

*Proof of B in general.* If the hypothesis fails, ρ_{n+2} is a price for every n. Block matrices diag(a, D), a ∈
Mat₂(F₂), D diagonal, give ρ₂ × {0,1}ⁿ inside ρ_{n+2} with the ℓ₂ product metric. For non-neighbouring j, k the points
{0, E_j, I, E_k} × {0,1}ⁿ are the corners of a unit cube, which fills to a flat solid cube (A, Step 8; G §"crossing").
So X contains book × [0,1]ⁿ, and each page × cube is a convex Euclidean patch. Take the tips at the centre of the
cube and s a fine net of a small sphere in the n + 1 spine directions. By the book bound and the flat law,

    δ(tips)/arm ≤ √(2π)·E[2·max(|g₀|, M) − max(g₀, M)],   M = max over s.

For a sphere of radius ρ in R^k, M = ρ·|g′|; as k → ∞ with ρ√k → m this tends to √(2π)(m + 3·E(G − m)₊), minimal at
m = z = Φ⁻¹(2/3), with value 3e^{−z²/2} = 2.7342. (This is P's ball lemma for n = 3.) With perimeter 6 arms, ω ≥ 6/2.7342. ∎

`bookbound.py` [N]:

| spine dimension k (matrices of size k+1) | 1 | 2 | 3 | 5 | 10 | 30 | 100 | ∞ |
|---|---|---|---|---|---|---|---|---|
| bound on δ(tips)/arm | 2.8284 | 2.7894 | 2.7730 | 2.7584 | 2.7466 | 2.7384 | 2.7355 | 2.7342 |
| ω ≥ | 2.1213 | 2.1510 | 2.1637 | 2.1752 | 2.1845 | 2.1910 | 2.1934 | 2.1944 |

Reading.
- Contrapositive: ω < 2.1944 ⇒ contracting hypothesis ⇒ ports (Theorem A). ω < 3/√2 ⇒ it holds with μ = 2.
  A has no value for μ; this gives one under an assumption on ω.
- Before October the known range was 2 ≤ ω ≤ 2.3713, and ω = 2 was the common conjecture. Under it both dichotomies
  are decided. A proof that the contracting hypothesis fails would be a proof that ω > 2.19.
- OpenAI claim ω = 9/4 (M). Then δ(tips) ≥ 8/3 for every unit tripod (M, "Tripod principle"), and the book bound
  2.7342 is 2.5% above it. No contradiction. `tripod_scan.py` [N]: for unequal arms the book bound stays above
  M's lower bound D*(a) = Σa_i − 1/Σ(1/a_i) everywhere on the grid; the ratio is 1.0253 at equal arms and tends to 1
  only when an arm degenerates.

Checks that failed to improve the bound [N]: the six-page structure with sites at the tips and on the spine gives the
same optimum as three pages (`hexbook.py`, linear programme over all axioms); in tripod × line the linear programme
with up to 12 sites gives [8/3, 2√2] for the tips under ω = 9/4 and is feasible (`book.py`).

## 6. Corollary E: products [R from K]

Tripods are price geometries (quantum functionals over ℂ; `review-link.md` over every field) and so are Hilbert
spaces (G). Their product need not be: the argument of §5 uses only the patch [centre, tip] × Euclidean space, so

- tripod × line carries spectral prices ⇒ ω ≥ 3/√2;
- tripod × ℓ₂ carries spectral prices ⇒ ω ≥ 2.1944.

P proves closure under products only for a subclass and only when there are no ports (Thm "Product theorem"). The
above shows why that is hard: closure of all price geometries under products with a line would prove ω > 2.12.

The smallest undecided table has four sites: m, P₁, P₃, P₄ with |mP_i| = 1, |P₁P₃| = |P₁P₄| = 2,
|P₃P₄| = 2 sin(θ/2), 0 < θ < π. It is neither Euclidean nor a tree metric, it embeds in tripod × line (`embed.py`),
and A's random-point extension (Prop. A.8) cannot produce it from its three outer sites.

## 7. What would decide it [C]

1. **A better upper bound on δ(tips) in the hull of ρ_μ.** Below 8/3 per arm it contradicts M's tripod principle and
   proves the contracting hypothesis in OpenAI's world; below 2.530 it does so against the pre-October bound
   ω < 2.3713. The hull has far more flat pieces than the book (cubes of every frame; 2^k + 1 pairwise opposite tips
   in Mat_{2k} from projections over F_{2^k}). One-step chains cannot beat 2.7342 (the optimum over spine sets is
   attained by a constant). Multi-step chains through neighbouring pages, or sites off the pages, are untested
   because distances between such sites are not forced by the metric of ρ_μ alone.
2. **Ports ⇒ contracting?** Would make the two dichotomies equal.
3. **Is ρ₂ a price?** Sixteen parties. By c1's cover characterisation this asks whether the complete network on
   Mat₂(F₂) has an asymptotically cheaper cover in ρ₂-weighted bond length.

My estimate: the margin 2.19 against 2.25 is thin enough that route 1 is worth a serious attempt, and if ω = 9/4 is
right the two numbers may be related. I do not have a guess which way it goes.

## 8. Files

`rank2.py` (model, μ = 2 equality case, graph identity), `embed.py` (embeddings), `book.py` and `hexbook.py` (linear
programmes; need `../v2/cone.py`), `bookbound.py` (table of §5), `tripod_scan.py`, `figures.py`, `fig_book.png`,
outputs `*.out`. Lean: `RankTwo.lean`, `Book.lean`, `GraphRank.lean`; build with
`cd lean && lake build EthFollowup.Spectral.RankTwo EthFollowup.Spectral.Book EthFollowup.Spectral.GraphRank`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` or fewer.
