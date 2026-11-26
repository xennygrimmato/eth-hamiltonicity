# sat3: can an engine with more merges per level beat 2^{O(n/√log n)} for (#)3-SAT?

Theory notes, 26 Nov 2026. Nothing here is committed, machine-checked or refereed.

Tags: **[R]** proved here in full from the cited inputs; **[D]** derived here, proof written but unreviewed (or
resting on an unreviewed input, named); **[N]** numerical (script named); **[K]** quoted (K-AN = Anthropic's
VP ≠ VNP paper, `scratchpad/fm/paper.txt`; K-OA = OpenAI's release); **[C]** conjecture; **[X]** dead, with reason.

Inputs: K-AN Lemma A.2/A.3, Thm A.6, Prop. B.3, Prop. C.3, Lemma C.4(a),(c),(f), Thm D.2 with the Lean statement
`thm_alt_rank_price` (¬contracting ⇒ √rank on Mat_μ(F₂) is a price, μ ≥ 3); our `vpvnp/b2` (price method (★), flat
floor), `next/review-link.md` (refereed win-win), `ports/c1d1/notes.md` D1, `ports/note-k23-rate.md` §2 (Lemma P,
Lemma H_m, refereed), `next/z1`, `next/w1`.

Scripts in this folder: `podprod.py` (far-leg optimiser in products of pods), `onetree.py` (one-tree ratio Γ),
`limitnet.py`, `limit_refine.py` (large-g limit problem), `check_nodepods.py`, `verify_d3_finite.py` (two
independent checks of the Δ₃ configuration). The executor's parallel notebook is `s3-experiments.md`, data in `data/`.

---

> **Status update, 27 Nov (later the same day). Parts of this file are superseded.** See `q1-notes.md` (the
> three-merge floor on nets of F_q^m, m ≥ 2, equals the cap 1/√2, in the space of real filtrations; replaces the
> 0.6124 floor of §5.4, the table and §5.5 for those nets; proposes a repair of Theorem S via the fixed
> configuration X₄), `attain-notes.md` (Theorem W: every cover generated from the crossing identity by nesting
> is bounded below by every CAT(0) placement), `q2-notes.md` (conditional on OpenAI's hub-compression theorem:
> any algebraic clique engine beating exponent 1/2 gives ports), and the referee reports `review-sat3.md`,
> `review-thmW.md`, `review-q1.md` (the last two in progress). The floors below remain correct as stated and
> remain the best known for cyclic groups, Δ₃ and K₄.

## 0. Answer in brief

1. **No algorithm.** I have no construction and no exponent above 1/2.
2. **The route is not dead by counting [R].** Designs with more merges than the node growth pays for exist: every
   p-net (p parallel classes of AG(2,g), or any p−2 mutually orthogonal Latin squares) has node growth β = 2 for
   every p. Product designs always give exactly 1/2.
3. **Two merges are closed without any hypothesis [R].** A new CAT(0) inequality (two bimedians, §3) shows that no
   price whatsoever proves more than E/√2 on a balanced two-merge configuration. For K₄ with three matchings the
   floor over all prices is exactly the flat one.
4. **Three merges: the flat floor is not the true floor when contracting fails [R + D].** If contracting fails,
   every finite subset of a product of pods and lines is a price (§4, [D]). In such products:
   - Δ₃ (rows, columns, diagonals): floor ≥ 6λ per merge, ρ ≥ 2/3, against the flat 3√3λ (ρ = 0.577). Attained by
     a product of nine tripods ([R] for the value; two independent checks). The supremum over all tree products is
     exactly 6 by search ([N]; executor: 32/32 chains over general trees) and equals (1/3)√(9·Γ) with Γ a one-tree
     ratio (§5.2, [R]).
   - 3-nets of F₂^M (or F₄^M) with g = 2^M → ∞: ρ → ½√(3/2) = 0.6124, against flat 1/√3 = 0.5774 ([R] in the
     limit model and for the transfer, refereed, `review-sat3.md`). The exact finite-g values increase to the
     limit (0.541, 0.573, 0.591 at g = 4, 8, 16; 0.6120 at g = 1024) and are below the flat value for g ≤ 8.
     The construction needs GL-mixing: for cyclic Z_g it gives only 0.5857. 4-nets of F₃^M: ρ → 1/√3 against
     flat 1/2.
   - Every price, under any hypothesis, gives at most 1/√2 on a p-net ([R]).
   So when contracting fails the three-merge window for the level value is ρ ∈ [0.6124, 0.7071) in the limit
   g → ∞. The translation into exponent thresholds (α′ ≤ 0.7075 for three merges, ≤ 0.79 for four) has a gap
   found by the referee: it needs a floor uniform in g, which is not proved (§6).
5. **Barrier (P4): not proved.** "No net engine beats 1/2 unless contracting" would follow from a price with value
   E/√2 on 3-nets. Tree products do not seem to reach it; §5.5 says what geometry would be needed.
6. **Attainment (P3): duality does not help.** AN Thm A.6 characterises attainment by a condition on spectral
   points evaluated on non-wire tensors; the price method is a relaxation of it (§7; whether the relaxation
   can be strict is not shown, see the correction in §7 item 2).
   Any sphere-law three-merge identity on a net would itself prove contracting.

---

## 1. P1: what a piece must provide, the exponent, the designs

### 1.1 The level and the recursion [K + D]

Notation as in `c1d1` D1.1. A level on K′ nodes has p merges (partitions of the nodes into at most K groups), the
edges of the K′-clique carry λ bits each, and the level tensor f = Π_{edges} ⟨2^λ⟩_e is written as Σ_i A_i (with
2^{o(λ·#edges)} terms; in Anthropic's level the terms are products of pieces over small configurations). A piece A has,
for each merge k, a cost c_k(A) = the smallest total log bond dimension of a network on the groups of merge k that
represents A. The level pays, per term, the cheapest merge. By von Neumann the level value is

    V = min over families of  max_μ min_k Σ_i μ_i c_k(A_i) = min over families of min_{q ∈ Δ_p} max_i ⟨q, c(A_i)⟩,

and ρ := V/(λ·#edges). One level maps the cost exponent e_K to e_{K′} = ρ·e_K + (lower-order terms), and
K′ = K^β. Hence e_K = (log K)^{−α′} with

    α′ = log_β(1/ρ*),   ρ* = lim of the level values.        (1.1)

D1's formula α′ = log_β(1/ρ) is this. Its bound α′ ≤ ½ log_β p uses the flat floor ρ ≥ 1/√p, which is the flat value
only for **balanced** configurations (Definition 2.1). For unbalanced designs the flat floor is higher (item (c)
below), and for balanced ones it need not be the true floor (§5).

### 1.2 Designs [R unless marked]

| design | merges p | node growth β | balanced | flat floor | ½·log_β p or exponent at the flat floor |
|---|---|---|---|---|---|
| (a) g×g grid, rows and columns (Anthropic) | 2 | 2 | yes | 1/√2, attained (App. B) | 1/2 |
| (b) d-dimensional grid, d coordinate-hyperplane merges | d | d | yes | 1/√d | 1/2 |
| (c) d-dimensional grid, d line merges | d | d/(d−1) | **no** | ≥ √((d−1)/d) [D] | 1/2 [D] |
| (d) p-net: AG(2,g) with p of its g+1 parallel classes | 3 ≤ p ≤ g+1 | 2 | yes | → 1/√p (g → ∞) | ½ log₂ p: 0.79, 1, 1.16, … |
| (e) AG(d,g) with p hyperplane classes | ≤ (g^d−1)/(g−1) | d | yes | → 1/√p | ½ log_d p |
| (f) triangle-free geometries (generalised quadrangles with spreads) | t+1 | → 2 | no | not computed | — |

- (c): line merge i is the partition by the other d−1 coordinates; with hubs in a product of simplices the best
  direction has cosine √((d−1)/d) with each merge, and log_{d/(d−1)} √(d/(d−1)) = 1/2. I did not prove that this is
  the Euclidean maximum.
- (d): smallest instances: K₄ with its three perfect matchings (g = 2, p = 3); Δ₃ = the nine edges of the fourth
  class of AG(2,3) with rows, columns, diagonals (three triangles); the full AG(2,3) level with p = 3 or 4.
  For a group G the 3-net is the Latin square of G: nodes (r,c) ∈ G², classes r, c, r−c.
- Any design with β = 2 and groups meeting in at most one node has K groups of size K per merge; then lines of
  different classes always meet, i.e. it is a net. A tower cannot be built from a fixed small design: K₄ maps 4
  nodes to 2 and has no iterate; products "K₄ × inner nodes" lose balance (the edges with different inner
  coordinates see the three merges aligned).
- So **"p ≤ β for every natural design" is false**; the question is only the true floor ρ* of nets.

---

## 2. The price method and the Euclidean value

**Price method (b2 (★), refereed).** Let d be a price on legs and hubs (one hub o^k_G per group G of merge k). For
every family Σ_i A_i = d·f with 2^{o(λ)} terms some piece has, for all k at once,

    c_k(A_i) ≥ λ·b_k − o(λ),   b_k = (L − H_k)/δ_k,

L = Σ_e |e⁺e⁻|, H_k = Σ_legs |ℓ, o^k(ℓ)|, δ_k = largest hub–hub distance in merge k. Mixing prices and their images
under the symmetries of the configuration, V/λ ≥ sup over prices of (1/p) Σ_k b_k when the symmetry group is
transitive on the merges.

Write s^k_e = |e⁺e⁻| − |e⁺, o^k(e⁺)| − |e⁻, o^k(e⁻)| (the saving of edge e under merge k), so b_k δ_k = Σ_e s^k_e.

**Definition 2.1 (balance).** A configuration (nodes, edges, merges) is *balanced* if for all groups G, G′ of two
different merges

    #{(y,z) : {y,z} an edge, y ∈ G, z ∈ G′} = Σ_{n ∈ G∩G′} deg(n).

For fully crossing configurations this says: #edges from G∩G′ to the outside of G∪G′ = #edges between G∖G′ and
G′∖G. Examples: the rectangle crossing; Δ₃ (the sum over (r,c) factorises and each factor telescopes around Z₃);
every full p-net level (both sides equal g²−1). A single wire, or the d-dimensional grid with line merges, is not.

**Proposition 2.2 (Euclidean value) [R].** For hubs h^k_G in a Hilbert space and any leg positions,
Σ_k b_k ≤ √(E·Σ_k E_k), where E_k is the number of edges crossing merge k. If the configuration is fully crossing
this is E√p, so min_k b_k ≤ E/√p, with equality for the orthogonal-simplex configuration of b2.

*Proof.* With u_e the unit vector from e⁺ to e⁻: |e⁺ o| ≥ ⟨u_e, o − e⁺⟩ and |e⁻ o′| ≥ ⟨u_e, e⁻ − o′⟩, so
s^k_e ≤ ⟨u_e, Δ^k_e⟩ with Δ^k_e = h^k(e⁻) − h^k(e⁺), |Δ^k_e| ≤ δ_k. Put Δ̃ = Δ/δ_k. Then
Σ_k b_k ≤ Σ_e |Σ_k Δ̃^k_e| ≤ √E·(Σ_e |Σ_k Δ̃^k_e|²)^{1/2}. The cross terms are
Σ_e ⟨Δ̃^k_e, Δ̃^l_e⟩ = Σ_{G,G′} ⟨h_G, h_{G′}⟩/(δ_kδ_l)·[Σ_{n∈G∩G′} deg(n) − #{(y,z)}] = 0 by balance. ∎

This turns b2's numerical statement "the Euclidean optimum on Δ₃ is 9√p" into a theorem, without the far-leg
ansatz.

---

## 3. What CAT(0) alone gives

All prices embed in CAT(0) price spaces (K-AN C.3), so an inequality valid in every CAT(0) space bounds what the
price method can ever prove.

**Proposition 3.1 (two bimedians) [R].** In a CAT(0) space let γ_t(a,b) be the point at t on [a,b]. For points
o, o′, w, w′ and t ∈ [0,1]:

    |γ_t(o,w), γ_t(o′,w′)|² + |γ_t(o,w′), γ_t(o′,w)|² ≤ 2(1−t)² |oo′|² + 2t² |ww′|².

For t = ½: the squared bimedians of the quadrilateral o, w, o′, w′ add up to at most half the squared diagonals.

*Proof.* C.4(a) twice: |γ_t(o,w), γ_t(o′,w′)|² ≤ (1−t)|γ_t(o,w), o′|² + t|γ_t(o,w), w′|² − t(1−t)|o′w′|²
≤ (1−t)²|oo′|² + t²|ww′|² + t(1−t)[|wo′|² + |ow′|² − |ow|² − |o′w′|²]. The same for the other pair gives
(1−t)²|oo′|² + t²|ww′|² + t(1−t)[|w′o′|² + |ow|² − |ow′|² − |o′w|²]. The brackets cancel. ∎

**Theorem 3.2 (two-merge cap in every CAT(0) space) [R].** Let a configuration with two merges be balanced. For
every placement of legs and hubs in a CAT(0) space, b_1 + b_2 ≤ √(E·(E_1+E_2)), where E_k is the number of edges
crossing merge k; for fully crossing configurations b_1 + b_2 ≤ √2·E and min(b_1,b_2) ≤ E/√2.
Hence no price, over any field, proves more than E/√2 for a balanced two-merge configuration.

*Proof.* Put λ_k = 1/δ_k, Λ = λ_1+λ_2, t = λ_2/Λ and β(n) = γ_t(o¹(n), o²(n)). For an edge e = (x,y) at nodes
(n,n′), convexity of the distance (C.4(a)) gives λ_1|x o¹(n)| + λ_2|x o²(n)| ≥ Λ|x β(n)|, so
Σ_k λ_k s^k_e ≤ Λ(|xy| − |xβ(n)| − |yβ(n′)|) ≤ Λ|β(n)β(n′)|. As in Prop. 3.1,
|β(n)β(n′)|² ≤ Σ_{k,l} μ_kμ_l |o^k(n) o^l(n′)|² − t(1−t)(|o¹(n)o²(n)|² + |o¹(n′)o²(n′)|²), μ = (1−t, t).
Summing over the edges, the terms with k ≠ l are Σ_{G,G′} μ_1μ_2 |o_G o_{G′}|²·#{(y,z)} and the subtracted terms
are Σ_{G,G′} μ_1μ_2 |o_Go_{G′}|²·Σ_{n∈G∩G′} deg(n); they cancel by balance. So
Σ_e |ββ′|² ≤ Σ_k μ_k² Σ_e |o^k(e⁺)o^k(e⁻)|² ≤ Σ_k μ_k² E_k δ_k² = (E_1+E_2)/Λ², and
b_1+b_2 = Σ_e Σ_k λ_k s^k_e ≤ Λ Σ_e|ββ′| ≤ √(E(E_1+E_2)). ∎

Consequences.
- The crossing bound 2√(δ_R²+δ_C²) follows from CAT(0) alone (no App. B needed), in agreement with
  `ports/protocol` ("the crossing identity reaches exactly the four-point bound").
- **Δ₃ with two merges:** every price gives at most 9/√2; under FH this is the floor (b2). New.
- **Corollary 3.3 (K₄) [R].** K₄ = X₁ ⊗ X₂ ⊗ X₃, X_j the crossing formed by the two edges of matching j, which
  crosses the two other merges and is internal to merge j (saving ≤ 0 there). Theorem 3.2 on each X_j gives
  Σ_k b_k ≤ 3·2√2, so min_k b_k ≤ 2√2 in every CAT(0) space. With the flat value 2√2 (z1): **the price floor of K₄
  with three matchings is exactly 2√2λ (ρ = √2/3) under FH and nothing more under any hypothesis.** K₄ is a pure
  attainment question (z1's three-rank object). The executor's runs agree (2.828427 in every tree product tried).
- **Corollary 3.4 (p-nets, pairwise cap) [R].** The full level of a p-net is balanced for every pair of merges
  (internal edges included), so Theorem 3.2 gives b_k + b_l ≤ √(2E·E_×), E_× = E − g·C(g,2) the number of edges
  crossing one merge. Summing over the pairs: (1/p)Σ_k b_k ≤ √(E·E_×/2) ≤ E/√2. So **every price gives at most
  1/√2 on a p-net**, and the true price floor of a 3-net lies in [1/√3, 1/√2] (lower end under FH).
- Δ₃ alone is not a union of rectangles for any pair of merges (the partners of class-4 edges are diagonal-class
  edges), but Theorem 3.2 applies to it directly for each pair: b_k + b_l ≤ 9√2, so min_k b_k ≤ 9/√2.

**Proposition 3.5 (the three-merge chain and its excess) [R].** For p merges, weights μ_k = λ_k/Λ, let β(n) be the
barycentre of Σ_k μ_k δ_{o^k(n)} (C.4(c)), Var(n) = Σ_k μ_k|β(n)o^k(n)|², W(n) = ½Σ_{k,l} μ_kμ_l|o^k(n)o^l(n)|²,
X(n) = W(n) − Var(n) ≥ 0. For a balanced configuration

    Σ_k b_k ≤ Λ Σ_e |β(e⁺)β(e⁻)|,    Σ_e |β(e⁺)β(e⁻)|² ≤ Σ_k μ_k² Σ_e |o^k(e⁺)o^k(e⁻)|² + Σ_n deg(n)·X(n).

*Proof.* Jensen for barycentres, then the variance inequality C.4(c) twice, then balance as above. ∎

X(n) = 0 when the hubs of n lie on one geodesic (always for p = 2) and in flats; X(n) > 0 when they span a tripod.
So **a price can beat the flat value on a balanced configuration only by making the p hubs of a node non-flat.**
The chain is tight for the Δ₃ optimum of §5.3 (ΣX = 1, bound 6) but is not a usable upper bound in general: with all
rows at one point P₁, all columns at P₂, all diagonals at P₃ of a tripod, X = 1/3 at every node while all
same-merge distances and all savings vanish. The loss is in the Jensen step.

---

## 4. Which non-Euclidean sets are prices when contracting fails

**Lemma 4.1 (segment filling) [R, from C.4(a),(f)].** Let Z be a metric space, Y a CAT(0) space, h > 0, and
F: Z × {0,1} → Y isometric for d² = d_Z² + h²[ε ≠ ε′]. Let F̃(z,t) be the point at t/h on [F(z,0), F(z,1)]. Then
F̃: Z × [0,h] → Y is isometric for the l2 product metric.

*Proof.* For z, z′ apply C.4(f) to x = F(z,0), u = F(z,1), y = F(z′,0), v = F(z′,1): |xy| = |uv| = d_Z(z,z′),
|xu| = |yv| = h, both diagonals have squared length d_Z² + h². ∎ (This is K-AN's Step 8 with Z arbitrary.)

**Lemma 4.2 (pod × anything) [D].** Let S_m = {n, s, t_1, …, t_m} with |ns| = |t_it_j| = √2·a, |nt_i| = |st_i| = a
(the square root of the graph metric of K_{2,m}, scaled), and let D_m = {(ξ,σ) ∈ (m-pod) × ℝ : |ξo| + |σ| ≤ a/√2}
be the diamond of `note-k23-rate` §2.2. Let Z be a metric space and F: S_m × Z → Y an isometric embedding into a
CAT(0) space (l2 product metric). Then F extends to an isometric embedding D_m × Z → Y.

*Proof.* For i ≠ j the four points n, t_i, t_j, s are the vertices {0,a}² of a square (n = (0,0), t_i = (a,0),
t_j = (0,a), s = (a,a)). Lemma 4.1 with Z₁ = {0,a} × Z, then with Z₂ = [0,a] × Z, gives an isometric
Φ_ij: Q_ij × Z → Y on the solid square Q_ij. For fixed z the maps Φ_ij(·,z) and Φ_ik(·,z) agree on the triangle
Δ_i = conv(n,s,t_i): they agree at its vertices, and geodesics in Y are unique (C.4(a)). So Ψ(ξ,z) := Φ_ij(ξ,z)
is well defined on D_m = ∪Q_ij. Isometry is a condition on pairs, and any two points of D_m lie in one square. ∎

**Theorem 4.3 [D].** If the contracting hypothesis fails over k, every finite subset of every finite l2-product
∏_j (𝕋_{m_j} × ℝ), 𝕋_m the m-pod with infinite arms, is a price over k.

*Proof.* Choose r with 2^r + 1 ≥ max m_j. By Lemma P of `note-k23-rate` the matrices 0, I, ι₂(t_p) ∈ Mat_{2r}(F₂)
carry √r times the metric of S_m (a = √r). Block-diagonal matrices have additive rank, so on
∏_j S_{m_j} ⊂ Mat_{2rJ}(F₂) the metric √rk is the l2 product. By `thm_alt_rank_price` it is a price; by C.3 it sits
in a price space Y. Apply Lemma 4.2 to one factor after another (Z = the product of the diamonds already built and
the S's not yet treated). Y then contains ∏_j D_{m_j}, and a finite subset of ∏(𝕋_{m_j} × ℝ) fits into it after
one scaling. ∎

Status: the proof is complete as written but unreviewed; inputs are K-AN's Lean statement and our refereed Lemma P.
It contains tripod², tripod⁹, tripod × ℝ^k. **Not covered:** trees with two branch points; cones over other links
(§5.5). In the contracting world none of this is available (and 3-SAT is power-saving by Theorem R).

---

## 5. Tree products raise the three-merge floor

### 5.1 The far-leg value in a product of trees [R]

Let X = ∏_j T_j (trees, l2 product). For an edge e with legs x, y and unit weights w_{e,j} ∝ d_j(x_j,y_j):
|x o| ≥ Σ_j w_{e,j} d_j(x_j,o_j), so

    s^k_e ≤ Σ_j w_{e,j} σ^k_{e,j},   σ^k_{e,j} = d_j(x_j,y_j) − d_j(x_j, o^k(e⁺)_j) − d_j(y_j, o^k(e⁻)_j),

with equality in the limit of far legs. In a tree, with F_n(g) = Σ_k λ_k d(g, o^k(n)) and Λ = Σλ_k,

    c_e(T) := sup over x, y of Σ_k λ_k σ^k_e = max over points g, g′ of [Λ d(g,g′) − F_n(g) − F_{n′}(g′)]   (5.1)

(g, g′ are the gates of x, y). For a pod with hubs at (arm, radius): each leg picks an arm, a hub counts +radius
if it is on that arm and −radius otherwise, the two arms must differ.

### 5.2 One-tree reduction [R]

**Theorem 5.1.** For every finite l2-product of trees and every placement,
Σ_k b_k ≤ √(E·Γ*), where

    Γ* = sup over λ and over ONE tree T with hubs of  S_λ(T)/D_λ(T),
    S_λ(T) = Σ_e (c_e(T))₊²,   D_λ(T) = (1/p) Σ_k λ_k² · mean over pairs of hubs of merge k of d_T².

For λ ≡ 1, if the automorphism group of the configuration is transitive on edges and on same-merge hub pairs,
the bound √(E·Γ) (Γ the supremum at λ ≡ 1) is attained by the product of the images of an optimal tree.

*Proof.* Σ_k b_k = Σ_e Σ_k λ_k s^k_e ≤ Σ_e ‖(c_e(T_j))₊‖₂ ≤ √(E Σ_j S_λ(T_j)) ≤ √(E Γ* Σ_j D_λ(T_j)), and
Σ_j D_λ(T_j) = (1/p)Σ_k λ_k²·mean_pairs Σ_j d_j² ≤ (1/p)Σ_k λ_k² δ_k² = 1. For the product over an orbit all
inequalities are equalities. ∎

So no search over products is needed. (Whether sup_λ exceeds the value at λ ≡ 1 is not proved; the product
searches of the executor and mine, with free radii, never exceeded it. [N])

### 5.3 Δ₃ [R for ≥, N for =]

**Theorem 5.2.** Take one tripod; put the three hubs R_r, C_c, D_{r−c} of one node n₀ on its three arms at radius
1 and all other hubs at the centre. Then S = 24, D̄ = 2/3, Γ ≥ 36, and the product of the nine such tripods has
b = (6, 6, 6). Hence, if contracting fails (Theorem 4.3), every family of pieces for Δ₃ with 2^{o(λ)} terms has a
piece with c_k ≥ 6λ − o(λ) for all three merges: **ρ_Δ₃ ≥ 2/3**. Under every hypothesis ρ_Δ₃ from prices ≤ 1/√2.

*Proof.* Let e = (n,n′) and n″ the third point of its class-4 line. A point n₀ off that line is joined to n, n′, n″
by lines of three different classes among R, C, D (they are the three such lines through n₀). So in the factor n₀
the leg at n has exactly one hub on an arm (class k₁), the leg at n′ exactly one (class k₂ ≠ k₁): c = 2, a gain in
two merges at once. In the factors n₀ ∈ {n, n′} the node has its three hubs on three arms (c ≤ 0), and for n₀ = n″
nothing. So ‖c_e‖² = 6·4, δ² = 6 (two parallel lines differ in six factors by 1), Σ_k b_k = 9·√24/√6 = 18. ∎

Checks: `check_nodepods.py` (far-leg evaluator: b = (6,6,6), δ = √6); `verify_d3_finite.py` (explicit points, legs
at distance M: 5.9136, 5.99914, 5.999991 for M = 10², 10⁴, 10⁶); the executor's independent check and Rust unit test.
`onetree.py` (150 restarts over pods) and the executor's search over general trees (32/32 chains) give Γ = 36 and
nothing larger. The executor's earlier values 2+2√3 (tripod²) and 5.4798 (tripod × ℝ⁴) are local optima.

**Conjecture 5.3 [C].** Γ_trees(Δ₃) = 36: in tree products the Δ₃ floor is exactly 2/3.
Proved cases [R]: one cut (a line price) gives 27; for the three-arm family with radii x ≥ y ≥ z,
S − 36D̄ = −2[(x−y)²+(y−z)²+(x−z)²] + 2(x−y−z)₊² ≤ 0, with equality iff x = y = z. A proof is a finite family of
copositivity statements (tree topologies on nine hubs × gate choices in (5.1)); the diagonal part has slack exactly
1/3 because single cuts obey the Euclidean balance identity. Two relaxations fail and should not be retried: the
chain of Prop. 3.5 (unbounded excess) and the per-cut relaxation c_e ≤ Σ_cuts len·|a_c(n) − a_c(n′)| (gives 42).

Remark. 2/3 is the value that w1's conjectural single-tensor inequality c₁ ≤ c₂ + c₃ would give on Δ₃.

### 5.4 Large nets: the gap does not close [R; refereed; transfer valid for F₂^M, F₃^M, F₄^M only]

The node-tripod family on a p-net of order g gives per merge √((g+p−2)/(gp)) of the edge bits (2/3 at g = p = 3),
which tends to 1/√p. A better family keeps a gap.

**Limit model.** Let G be a vector space over F₂ (or F₄), nodes G², merges r, c, r−c, and pull a pod labelling
back from a quotient Q. For generic pairs of nodes the two images in Q² are independent and uniform; with the whole
orbit under translations and GL(G) all generic edges have the same norm, so the level value tends to √Φ/3 with

    Φ = E_{n,n′}[c(n,n′)₊²] / D̄,   D̄ = (1/3)Σ_k E_{q,q′} d(pos_k(q), pos_k(q′))².

Flat: Φ = 3. Cap (Cor. 3.4): Φ ≤ 9/2.

**Theorem 5.4.** Let A ≤ G have index 1/θ. One tripod: all rows r ∈ A at one point of arm 1, all columns c ∈ A at
one point of arm 2, all diagonals d ∈ A at one point of arm 3 (radius 1), all other hubs at the centre. Then
Φ = 3(1−θ)(1+2θ); at θ = 1/4, **Φ = 27/8 and the level value is ½√(3/2) = 0.6124.**

*Proof.* r, c ∈ A ⟹ r−c ∈ A, so a node has x = 0, 1 or 3 active lines, with probabilities (1−θ)(1−2θ), 3θ(1−θ),
θ². A node with x = 1 gains 1 on its arm; x = 3 gives −1; x = 0 gives 0. A pair gains 2 if both have x = 1 in
different classes, 1 for (x=1, x=0), 0 or less otherwise (two legs cannot share an arm). So
E[c₊²] = 4·(2/3)(3θ(1−θ))² + 2·3θ(1−θ)·(1−θ)(1−2θ) = 6θ(1−θ)²(1+2θ), and D̄ = 2θ(1−θ). ∎

Checked by `limitnet.py` (Q = Z₂, …, Z₆: 3, 10/3, 27/8, 3.36, 10/3; Z₈ with A = {0,4}: 27/8). My random searches
over pods on Z₅, Z₆, Z₈, Z₂³ are too weak to count as evidence for optimality.

**Proposition 5.5 (p merges) [D].** For p classes such that two lines in A force all p (slopes 0, ∞, 1 for any
subgroup; 0, ∞, 1, −1 for odd index; in general p pairwise transversal points of P¹(Z_d)), the same p-pod gives
Φ_p = p(1−θ)(1+(p−1)θ). At θ = (p−2)/(2(p−1)): value ½√(p/(p−1)) (p = 4, index 3: 1/√3 against flat 1/2). The
transversality condition forces θ ≤ 1/(p−1), where the value is √(2(p−2)/(p(p−1))) ≈ √2 × flat for large p
(p = 5: 0.548 with F₄; p = 6: 0.516 with F₅; p = 7: 0.477 with F₇).

| p | flat floor | pod floor (¬contracting) | cap (all prices) | exponent window when contracting fails |
|---|---|---|---|---|
| 2 | 0.7071 | 0.7071 | 0.7071 | {1/2} (closed) |
| 3 | 0.5774 | 0.6124 (Δ₃ alone: 0.6667) | 0.7071 | (1/2, 0.7075] |
| 4 | 0.5000 | 0.5774 | 0.7071 | (1/2, 0.79] |
| 5 | 0.4472 | 0.5477 | 0.7071 | (1/2, 0.87] |
| 7 | 0.3780 | 0.4768 (F₇, θ = 1/7) | 0.7071 | (1/2, 1.07] |

The pod column is a lower bound on the floor, from one family; nothing says it is optimal for p ≥ 3.

### 5.5 What would close the window [D, partly C]

Equality in Corollary 3.4 needs, for every pair of merges and every edge (n,n′): the leg directions affine on
[o^k(n), o^l(n)] and the line of the edge through the midpoints m_kl(n), m_kl(n′), with |m_kl(n) m_kl(n′)| = δ/√2.
For three merges the three side-midpoints of the hub triangle of n must then lie on the line of every edge at n.
With distinct collinear hubs this forces full savings (no trade), so the hub triangle must be a symmetric tripod
with the edge directions perpendicular to its three arms. I checked that this cannot be arranged in a tree, in a
Euclidean space, or in pod × ℝ^M with all nodes' tripod centres over one tree point [D, ansatz only]. It would need
a CAT(0) space whose links contain three pairwise antipodal directions with a perpendicular family of rank ≥ 2.
[C] Candidates are the hulls of Mat_μ(F₂), μ ≥ 3, transversally to the diagonal [0, I] (the cubes of all frames
share that diagonal); I have not determined these hulls. So:

**Open question Q1.** Is sup over prices (contracting failing) of the 3-net value equal to 1/√2? If yes: no net
engine with three merges beats exponent 1/2 unless contracting holds. If the supremum is < 1/√2, the window is
real and the question is attainment.

---

## 6. Consequences for engines (sharpening D1) [D]

**Correction (referee, `review-sat3.md` item 5).** Items 2 and 3 below are NOT proved as stated. D1's
averaging argument needs a finite list of fixed configurations in which every edge crosses every merge, so that
one configuration recurs with λ → ∞ and a floor that is only a liminf in λ (no rate) can be applied. Net levels
of order g → ∞ are a different configuration at every level and contain edges internal to merges; the level that
dips can be a different configuration for every n. What IS proved is the per-level statement: for a fixed g, a
family of covers of the order-g level tensor (λ → ∞) with value below the pod floor of that g by a constant
proves contracting. The tower thresholds 0.7075 and 0.79 need either a floor uniform in g (a rate in λ for the
statement "this finite set is a price") or a decomposition of net levels into fixed configurations; neither is
available. Item 1 is also not literally D1 for configurations that are balanced but not all-crossing. The
arithmetic of the thresholds is right. Status of items 2, 3: [C] with a named gap.

**Theorem S (items 2, 3 conditional on a uniform floor).** Let k be a field and consider tower engines whose levels are p-net levels over k (class of D1.1
with one configuration per level, 2^{o(λ·E)} terms).
1. p = 2 (rectangle levels), or any level whose configurations are balanced for two merges: certified exponent
   α′ ≤ 1/2 unless FH fails (D1), and no price argument can ever give a smaller bound than 1/2 (Thm 3.2).
2. p = 3, nets of F₂^M or F₄^M: if α′ > log₂(3/√(27/8)) = 0.7075 along infinitely many n, then
   some level has ρ below the pod floor by a constant, so some finite subset of a product of pods is not a price,
   so contracting holds over k (Thm 4.3), and 3-SAT is power-saving (Theorem R in characteristic 0, C1 in
   characteristic p). D1 had 0.79 here.
3. p = 4 (nets of F₃^M, slopes 0, ∞, ±1): the same with threshold log₂√3 = 0.79 instead of 1.
(Δ₃ itself, with floor 2/3, is a single instance at g = 3 and not a level of a tower.)

The proof is D1's averaging argument with the pod floor in place of the flat floor (the floor statement is
"liminf as λ → ∞ at fixed configuration", with the same absence of a rate as in D1.4).

What is **not** proved: the threshold 1/2 for p ≥ 3 (Q1).

---

## 7. P3: attainment and duality

1. **What duality gives [D from K-AN A.6].** Fix a unit size D₀ and let 𝒫 be the set of tensors on the legs of the
   unit configuration whose cost profile is in a prescribed set (closed under restriction). A.6 (its proof works
   for a compact family in place of a finite list) gives: f^N is covered by 2^{εN} products of members of 𝒫 for
   all ε > 0 iff every spectral point φ has φ(f) ≤ sup_{A∈𝒫} φ(A).
2. **Why this is not the price method.** For A ∈ 𝒫, φ(A) ≤ min_k φ(N_k(c_k)), N_k the hub network of merge k, and
   the price method only uses this bound. The set of tensors below several networks is not the set of restrictions
   of one tensor, and the minimum is not attained in general: on three parties, with N_1 = ⟨N⟩₁₂ and N_2 = ⟨N⟩₂₃,
   every common restriction is a product state (φ = 1), while the flattening rank at {2}|{1,3} is N on both. **Correction
   (referee):** this shows slack for a single functional only, not a gap between floor and attainment: a target
   that passes the price test for every functional is forced by the flattenings at parties 1 and 3 to be
   u⊗f₂⊗v, which is itself a piece. So no example here separates "price floor" from "pieces exist"; whether
   they can differ is open. Attainment is a statement about spectral points on
   non-wire tensors. In our setting the same gap shows on K₄: no price sees the cost of a crossing piece across the
   merge that contains both its edges (z1), and on Δ₃ in characteristic 0, where w1's rank inequality forces the
   star piece off the sphere.
3. **Uniformity is not the obstacle.** If the spectral condition held, the cover of f^N is generated by one finite
   certificate per ε (K-AN's proof of A.6), found by search in time depending on ε only; letting ε → 0 slowly gives
   a uniform algorithm with ρ + o(1).
4. **Filter for candidates [R given §5].** When contracting fails there is no sphere-law family on a net (it would
   have ρ = 1/√3 < 0.6124) and no family on Δ₃ with ρ < 2/3. So an A₂-graded three-way crossing identity with
   Σ_k c_k² ≤ (Eλ)² would itself prove contracting. A three-way identity compatible with non-contracting must have
   balanced value in [0.6124, 0.7071).
5. **What a three-way identity must be.** The smallest balanced sub-configurations of a net of a group are the
   translation classes E_v = {n → n+v : n ∈ G²} (v = (a,b) with a, b, a−b ≠ 0): g²/ord(v) cycles of length
   ord(v); Δ₃ is E_{(1,−1)} in Z₃². They are not unions of rectangles: the rectangle partner of an edge for a
   pair of merges has another slope (t ↦ −t, 2−t, t/(2t−1)), possibly a merge slope. So a three-way identity is a
   family Ψ_ν with Σ_ν Ψ_ν = d·f_{E_v}, an object on cycles through all g² nodes, not on four parties; it needs
   2^{o(λ)} terms per class and, for each merge, a network on the g groups with costs c_k(ν) such that
   min_q max_ν ⟨q, c(ν)⟩ ≤ ρ·|E_v|·λ with ρ < 1/√2.
6. **Candidates.** None live.
   - Littlewood–Richardson / hives: recoupling data of U(n); the pieces would be isotypic projectors on finite
     shells, the type that died for SU(2) and su(1,1) recoupling (w1 §3: Racah-polynomial uncertainty). [C: dead
     for the same reason; not proved for U(n).]
   - Two-variable determinants with X·Y·Z = 1 (w1 §4): a sphere law, excluded by item 4 unless contracting.
   - The catalogue's surviving requirement (group-element-like pieces, infinite ladder, pole of order ≥ 2) is
     unchanged; I have nothing to add to it.

---

## 8. P4: the barrier, as far as it goes

Proved and refereed: Theorem 3.2 with its corollaries (unconditional statements about what prices can prove),
Theorem 4.3 (product hulls, now [R]), Theorems 5.2 and 5.4 (floors, for nets of F₂^M, F₃^M, F₄^M), and the
per-level form of Theorem S. Not proved: the tower thresholds of Theorem S items 2, 3 (uniformity gap, §6).

Not proved: "no rewriting engine beats 2^{n/(log n)^{1/2+o(1)}} unless contracting holds". The class for which it
is proved is p ≤ β (D1). For nets it is equivalent to Q1 as far as price arguments go.

Outside the class of Theorem S: non-product term sets (correlated decompositions, barrier note §4.4), levels with
growing lists of configurations, cut hierarchies that are not merges, instance-adaptive algorithms, and anything
in the contracting world.

---

## 9. P5: other routes

- **K₄'s three-rank object.** The one place where the price floor is settled and below the two-merge value at the
  same g (0.471 against 0.569): decide whether crossing pieces exist with sphere-law costs in two directions and
  2^{o(λ)} operator-Schmidt rank in the third. It gives no tower by itself, but a positive answer would be the first
  three-merge trade and a negative one (a rank inequality beyond Song et al.) would be the first non-price floor.
- **Deciding contracting.** Every positive result here is conditional on non-contracting; if contracting holds,
  3-SAT is power-saving. The geometric question of §5.5 (what the hull of Mat_μ(F₂) is) bears on both.
- Nothing else. Adaptive compression (ideas-3sat Route 3) is untested and I have no argument for it.

---

## 10. Specs for executors

**E1 (limit problem, 2 h).** Maximise Φ of `limitnet.py` over pods and over general trees for Q = Z₄, Z₂², Z₈, Z₂³,
Z₄², with a serious optimiser (annealing over arms, exact line search over radii; cluster moves that shift a whole
coset). Start from the subgroup tripod (27/8). Report any Φ > 27/8; cap 9/2.

**E2 (full levels at small g, running).** Γ for the full 3-net level on AG(2,g), g = 3, 4, 5, 7, 8, all edges; report
the Cauchy–Schwarz bound (1/3)√(EΓ)/E and the value of the symmetrised product against ρ_orth(3,g) and 1/√2. For
g = 4, 8 include the subgroup tripod.

**E3 (proof of Conjecture 5.3, optional, 3 h).** Enumerate X-trees on the nine hubs of Δ₃ modulo the symmetry group
(order 108); for each tree and each gate assignment in (5.1) certify S − 36D̄ ≤ 0 on the positive orthant.

**E4 (referee, 1 h).** Lemma 4.1–Theorem 4.3 (product hull); Proposition 3.1 and Theorem 3.2 (ten lines each).

**E5 (geometry, open-ended).** In Mat₃(F₂) with √rk: the points 0, I, the 28 rank-one and 28 rank-two idempotents.
Compute the comparison angles at the midpoint of [0, I] and test whether the transversal link is forced to be the
incidence graph with edges π/3 (flat hexagons for frames). If forced, evaluate the 3-net value in cone × ℝ.

---

## 11. Dead ends and corrections

- [X] c1d1 spec S3 as written (placements in Mat_μ(F₂), μ ≤ 3): the vertex set has no far legs (the executor's
  argument: √rk is a square root of a metric); the relevant prices are the hulls.
- [X] "K₄ is the better design": its 0.471 is ρ_orth(3,2), a small-g value; no iterate.
- [X] Proving Γ ≤ 36 by the barycentre chain or by per-cut maxima (§5.3).
- [X] Random active sets of lines in the limit problem: Φ = 3 − O(θ²) < 3. The gain needs the subgroup property.
- Correction to my interim note 3: "impossible in pod × ℝ^M" is checked only for the ansatz of §5.5, and the
  description of the hull of Mat₃(F₂) as a cone over an A₂-type graph is a guess [C], not a computation.
