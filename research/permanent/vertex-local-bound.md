# Vertex-local networks for the permanent: beyond the single cut

Target: Conjecture 6.5 of `barrier.md` — in Model V(s) (Definition 5.2 there: every node's data
depends on A ∈ {0,1}^{n×n} only through the rows *and* columns of one cluster of ≤ s vertices of
[n] ⊔ [n]′, skeleton independent of A), every network family with value(N(A)) = per(A) has
U ≥ (1 − o(1))·n·log(n/s).

Conventions as in `barrier.md`: log = log₂, ranks over ℚ, U = Σ_a Σ_{b≠a} c_{a,b} (ordered pairs),
w(L,R) = Σ_{a∈L,b∈R} c_{a,b} (crossing bits once), so U = 2·Σ_{unordered pairs} c_{a,b}. We refer to
Lemmas 3.1–3.4, Proposition 3.5 and Theorems 6.1, 6.2 of `barrier.md` by those numbers, prefixed
"B-" (B-Lemma 3.1 etc.). Scripts: `scripts/vlb_*.py` (exact arithmetic unless stated).

---------------------------------------------------------------------------------------------------

## 0. Summary

**The conjecture remains open.** What is proved here, in decreasing order of relevance:

* **Theorem 2.1 (an obstruction that is not a cut width).** In Model V(1) with the clusters
  {i, i′} (row i and column i), no network whose skeleton is a star (one routing centre, one
  shared bit per leaf, U = 2n) computes per(A), for any n ≥ 3; more generally no skeleton may
  contain a routing node with three one-bit leaves. For n = 3 **every** cut of this skeleton
  passes the rank test of B-Lemma 3.1 (Proposition 2.2), so this is the first statement about
  Model V that the single-cut method cannot deliver; for n ≥ 4 the two-leaf cut already excludes
  the one-bit star, and the content is the *method*: the diagonal entries are private variables,
  the network identity becomes a family of tensor identities Π(s) = (M₁(s₁) ⊗ ⋯ ⊗ Mₙ(sₙ))·G with
  *local* 2×2 matrices M_i (Lemma 1.3), and two configurations are separated by Cayley's
  hyperdeterminant (GHZ-orbit vs W-orbit). The smallest skeleton on which every cut passes for
  every n is the star with **two** bits per leaf (U = 4n); excluding it is Problem 5.2 and is where
  the method has to be pushed (Remark 2.3).
* **Theorem 3.1 (tree skeletons).** If the skeleton is a tree, U ≥ 2·Σ_{edges e} log C(k_e + k′_e, k_e)
  with (k_e, k′_e) the row/column counts on the smaller side of e. For the clusters {i,i′} and a
  tree all of whose nodes have degree ≤ Δ this gives U ≥ 4·n·log_{Δ−1} n − O(n log log n)
  (Corollary 3.2): **Conjecture 6.5 holds, with constant 4/log(Δ−1) instead of 1, for
  bounded-degree tree skeletons.** The bound degenerates exactly at high-degree routing nodes
  (the star: U ≥ 2n only) — the case Theorem 2.1 addresses.
* **Proposition 4.1 (separation Model V ≻ Model R; the one-1-per-row family is useless).** The
  function f(A) = [A is a permutation matrix] has a Model V(1) network with U = 0, while every
  Model R(s) network for it has U ≥ n·log(n/s). Consequently the test family 𝓕₁ (exactly one 1 per
  row), which carries the whole of B-Theorem 6.1, cannot give *any* lower bound in Model V:
  intermediate goal (i) of the task is false as stated, and a hard family for Model V must have at
  least two 1s in (most) rows and columns.
* **Proposition 4.2 (the natural hard family and its single-cut rank).** On 𝓒 = {I + P_σ} (σ a
  derangement) the value is 2^{c(σ)} (c = number of cycles). For a vertex cut with b crossing arcs
  in each direction the rank of the private-vs-private matrix is the Catalan number
  C_b = C(2b,b)/(b+1) (Schur–Weyl: 2^{c(π)} = Σ_{ℓ(λ)≤2} s_λ(1,1) χ_λ(π)), i.e. again ≤ 2 bits per
  crossing arc — the "cycle-counting" view confirms B-Proposition 3.5 from a different angle and
  identifies the obstacle as a *pointer-chasing / permutation-routing* obstacle on a fixed skeleton.
* **§5: what a proof of Conjecture 6.5 has to do.** We show (Remark 5.1) that for skeletons that
  separate all row clusters from all column clusters every cut has rank **1** — the single-cut
  method certifies nothing at all there, not even B-Theorem 6.2's 2n (which needs the balanced
  grouping of its Step 1). The right formulation of the conjecture is a lower bound on the
  *tensor-network* representation of the tensor family Π(s) (Lemma 1.2) with s-local node
  tensors; we state the precise open problems (5.2–5.4) and the reduction of the star case to a
  "simultaneous-messages with linear combining" problem.

Proved: Lemmas 1.1–1.3, Theorem 2.1, Proposition 2.2, Theorem 3.1 with Corollary 3.2, Propositions
4.1, 4.2. Numerically checked: `vlb_star_hyperdet.py` (Theorem 2.1, n = 3, 4), `vlb_cycle_rank.py`
(Proposition 4.2, b ≤ 5). Heuristic only: `vlb_star_als.py` (alternating least squares for the
star; it does *not* find known solutions reliably and is not used as evidence).

Not proved: Conjecture 6.5 itself; any bound beyond 2n for skeletons with a routing node of
degree ≥ 3 and bond dimension ≥ 3 (Problem 5.2); any bound for the row-subtree/column-subtree
skeleton of Remark 5.1 (Problem 5.3); intermediate goal (ii) of the task (grid skeletons) beyond
what Theorem 3.1 gives for their spanning trees (Remark 3.3).

---------------------------------------------------------------------------------------------------

## 1. Reformulation: tensor networks with private diagonal legs

**Lemma 1.1 (tensor-network form).** For every network N (Definition 2 of [A], as pinned in
`barrier.md` §1) with shared-bit counts c_{a,b},

```
value(N) = Σ_{θ ∈ Θ} Π_a F_a(θ_{∂a}),   Θ = Π_{a<b} {0,1}^{c_{a,b}},   θ_{∂a} = (θ_{a,b})_{b≠a},
F_a(θ_{∂a}) = Σ_{z_a ∈ S_a} W_a(z_a) Π_{b≠a} f_{a,b}(z_a, θ_{a,b}),
```

and F_a depends only on the data (S_a, W_a, f_{a,·}) of node a. In particular, in Model V, F_a
depends on A only through the rows and columns of a's cluster.

*Proof.* Replace every Ψ_{a,b}(z_a,z_b) by Σ_θ f_{a,b}(z_a,θ) f_{b,a}(z_b,θ) (`fact`), and exchange
the sums over z and θ. ∎

So a network *is* a tensor network: node a carries a tensor F_a with one leg of dimension
D_{a,b} := 2^{c_{a,b}} towards each neighbour b, and value = full contraction. U = 2 Σ_{a<b} log D_{a,b}.
B-Lemma 3.1 is the single-edge-cut rank bound for tensor networks; it is well known to be tight
for *tree* tensor networks of a fixed tensor, which is why one cannot expect more from it on a
single cut.

**Lemma 1.2 (private diagonal legs).** Consider Model V with clusters each containing a row i and
the column i′ (e.g. s = 2, clusters {i,i′}; or any clusters V_j ⊇ {i, i′} for all i ∈ V_j ∩ [n]).
Write A = diag(x) + s with x ∈ {0,1}^n the diagonal and s the off-diagonal part (zero diagonal).
Then x_i is seen by the node(s) of cluster(i) only, and for every node a and every θ,

```
F_a(x, s, θ_{∂a}) = F_a^0(s_a, θ_{∂a}) + Σ_{∅≠T⊆X_a} (Π_{i∈T} x_i) F_a^T(s_a, θ_{∂a}),
```

X_a the set of diagonal entries in a's cluster, s_a the off-diagonal entries in a's rows and
columns. Hence, with Π(s) ∈ (ℚ²)^{⊗n} denoting the coefficient tensor of the multilinear
polynomial x ↦ per(diag(x) + s) (coefficient of x^S is D_S(s) := Σ_{σ : Fix(σ) = S} Π_{i∉S} s_{iσ(i)},
the "derangement permanent" of s[S^c]):

```
Π(s) = contraction of the same skeleton in which node a carries the tensor
       F̂_a(s_a) ∈ (ℚ²)^{⊗X_a} ⊗ ⊗_b ℚ^{D_{a,b}},   F̂_a(s_a)[T, θ_{∂a}] = F_a^T(s_a, θ_{∂a}),
```

i.e. a tensor network for the whole *family* {Π(s)}_s in which the node tensors depend on s
*locally* (node a on s_a only).

*Proof.* A function of a 0/1 variable is affine in it; expand each F_a multilinearly in the x_i it
sees (Lemma 1.1 gives that only cluster(i)'s nodes see x_i). Equality of the two multilinear
polynomials per(diag x + s) and Σ_θ Π_a F_a(x,s,θ) on {0,1}^n gives equality of coefficients. ∎

**Lemma 1.3 (star criterion).** Let the skeleton be a star: leaves 1..n (cluster {i,i′}) joined
to one routing centre by c_i bits, D_i = 2^{c_i}. Then the network computes per iff there are a
tensor G ∈ ⊗_i ℚ^{D_i} and, for every node i and every view s_i, a 2×D_i matrix M_i(s_i) with

```
Π(s) = (M_1(s_1) ⊗ ⋯ ⊗ M_n(s_n)) · G      for all zero-diagonal s ∈ {0,1}^{n×n}.        (1.1)
```

Equivalently: for every S ⊆ [n], D_S(s) = G(w_1, …, w_n) with w_i = u_i(s_i) (row 1 of M_i, the
coefficient of x_i) if i ∈ S and w_i = v_i(s_i) (row 0 of M_i) if i ∉ S.

*Proof.* Lemma 1.2 with F̂_centre = G and F̂_i(s_i) = M_i(s_i) (a 2 × D_i tensor). ∎

(1.1) says that every Π(s) is a *restriction* of the single tensor G, with the restriction maps
constrained to be local in s. Dropping locality, (1.1) is satisfiable with D_i = 2 for every
single s (Π(s) is a 2×⋯×2 tensor), which is the tensor-network form of B-Proposition 3.5; the
content of Conjecture 6.5 for the star is that locality forces D_i ≥ n^{1−o(1)}.

---------------------------------------------------------------------------------------------------

## 2. The star with one bit per leaf: an obstruction that is not a cut width

Throughout this section: Model V(1) with clusters {i,i′}; skeleton = star with a routing centre
and c_{i,centre} = 1 for every leaf i, so U = 2n (B-Theorem 6.2 gives U ≥ 2n − o(n), so this star
sits exactly at the single-cut threshold).

**Proposition 2.2 (which cuts pass).** Let I be a set of leaves, 1 ≤ |I| = k ≤ n/2, and cut
L = I, R = the rest (centre included). Then w(L,R) = k, and for the fixing of B-Lemma 3.4 the
matrix (A[I,I], A[I^c,I^c]) ↦ per(A) has rank exactly C(2k,k). Hence the cut passes the rank test
of B-Lemma 3.1 iff k = 1. The cut isolating the centre passes trivially (one row). Consequently:

* for n ≥ 4 the single-cut method already excludes the one-bit star (k = 2: C(4,2) = 6 > 2²);
* for **n = 3 every cut passes** (all proper cuts have a single leaf on one side, or the centre
  alone), so no single-cut argument can exclude the one-bit star for n = 3;
* for the star with **two** bits per leaf (U = 4n) every cut passes for every n, because
  w = 2k ≥ log C(2k,k) — this is the smallest "all cuts pass" skeleton in Model V(1), and the
  real target of the method below (Problem 5.2).

*Proof.* B-Lemma 3.4 with I_L = J_L = I, I_R = J_R = I^c (possible since 2k ≤ n) and B-Lemma 3.1. ∎

**Theorem 2.1.** For every n ≥ 3, no network in Model V(1) with clusters {i,i′} and a star
skeleton with c_{i,centre} = 1 for all i computes per on {0,1}^{n×n}. More generally, no network
computes per if its skeleton contains a routing node r adjacent to three cluster nodes 1, 2, 3
with c_{i,r} = 1 and no other edges at 1, 2, 3 (the rest of the skeleton arbitrary).

For n = 3 this is the first statement in Model V that the single-cut method cannot deliver
(Proposition 2.2); for n ≥ 4 its content is the *method*, which never looks at a cut width and is
the template for Problem 5.2.

*Proof.* By Lemma 1.3, a star network gives G ∈ (ℚ²)^{⊗n} and local 2×2 matrices M_i(s_i) with
Π(s) = (⊗_i M_i(s_i)) G for all zero-diagonal s. Consider two configurations supported on nodes
1, 2, 3 (all other entries 0):

* s^{cyc}: s_{12} = s_{23} = s_{31} = 1. Then per(diag x + s^{cyc}) = x_4⋯x_n · (x_1x_2x_3 + 1).
* s^{path}: s_{12} = s_{21} = s_{23} = s_{32} = 1. Then per(diag x + s^{path}) = x_4⋯x_n · (x_1x_2x_3 + x_1 + x_3).

(Rows/columns ≥ 4 must use their diagonal entry; on {1,2,3} a permutation either fixes all three
or runs around the 3-cycle, resp. fixes all three, or uses (12) and fixes 3, or uses (23) and
fixes 1. Checked by `vlb_star_hyperdet.py` for n = 3, 4.)

For j ≥ 4 the view s_j is the zero view in both configurations, so M_j(0) is the same matrix in
both. Contract legs 4..n of (1.1) with e_1^* (coefficient of x_j = 1); both sides are multilinear:

```
f^{cyc}  := x_1x_2x_3 + 1          = (M_1(s^{cyc}_1)  ⊗ M_2(s^{cyc}_2)  ⊗ M_3(s^{cyc}_3))  G′,
f^{path} := x_1x_2x_3 + x_1 + x_3  = (M_1(s^{path}_1) ⊗ M_2(s^{path}_2) ⊗ M_3(s^{path}_3)) G′,
```

with the same G′ := (id⊗id⊗id ⊗ e_1^*M_4(0) ⊗ ⋯ ⊗ e_1^*M_n(0)) G ∈ ℚ^{2×2×2}. Both f^{cyc} and
f^{path} have all three one-leg flattenings of rank 2 (f^{cyc}: slices {1, x_2x_3}; f^{path}:
{x_3, x_2x_3 + 1}, {x_1 + x_3, x_1x_3}, {x_1, x_1x_2 + 1}). The i-th flattening of
(M_1⊗M_2⊗M_3)G′ has rank ≤ rank M_i, so all six matrices M_i(·) are invertible. Hence f^{cyc}
and f^{path} lie in the GL₂^{×3}-orbit of G′, so in the same orbit. But Cayley's hyperdeterminant
is a relative invariant, Det((M_1⊗M_2⊗M_3)T) = (det M_1 det M_2 det M_3)² Det(T), and
Det(f^{cyc}) = 1 ≠ 0 = Det(f^{path}): f^{cyc} = e_1e_1e_1 + e_0e_0e_0 is the GHZ tensor,
f^{path} = e_1e_1e_1 + e_1e_0e_0 + e_0e_0e_1 is in the W-orbit (all flattenings of rank 2,
hyperdeterminant 0). Contradiction.

"More generally": with 1, 2, 3 leaves of a routing node r and all other nodes arbitrary, Lemma
1.2 gives Π(s) = (M_1(s_1) ⊗ M_2(s_2) ⊗ M_3(s_3) ⊗ E(s_{rest})) · G_r, where G_r ∈ (ℚ²)^{⊗3} ⊗ ℚ^{D}
is r's tensor (legs to 1, 2, 3 of dimension 2 each; its other legs bundled, D = Π_{b≠1,2,3} D_{r,b})
and E(s_{rest}) is the contraction of all other node tensors — a linear map ℚ^{D} → (ℚ²)^{⊗(n−3)}
depending only on the views of nodes ≠ 1, 2, 3, hence the same for s^{cyc} and s^{path}.
Contracting legs 4..n with e_1^* makes E a fixed functional and G_r a fixed G′ ∈ ℚ^{2×2×2}; the
rest is unchanged. ∎

**Remark 2.3 (what the proof uses).** (a) The diagonal entries are private legs (Lemma 1.2);
(b) two inputs with identical views at all but three nodes are two restrictions, by the *same*
environment, of one fixed 2×2×2 tensor; (c) an orbit invariant separates them. The template for
legs of dimension D = 2^{c} and a set Q of q leaves of one routing node: all Π-tensors
f_s ∈ (ℚ²)^{⊗q} of configurations s supported on Q are restrictions (⊗_{i∈Q} M_i(s_i)) G_Q of one
tensor G_Q ∈ (ℚ^{D})^{⊗q} with M_i(s_i) ∈ ℚ^{2×D} depending on node i's view only. For q = 3 and
D ≥ 3 no invariant can work: every 2×2×2 tensor has rank ≤ 3, so all f_s are restrictions of the
unit tensor ⟨3⟩ (but *not* with local M_i — the locality is what has to be used). So already for
the two-bit star (Proposition 2.2, third bullet) one needs q ≥ 4 nodes and an argument that uses
the locality of the M_i, see Problem 5.2.

---------------------------------------------------------------------------------------------------

## 3. Tree skeletons: n log n with constant 4, up to the degree of the routing nodes

The single-cut bound of B-Theorem 6.2 is summed over a *partition* of the clusters into groups,
because U charges each pair of nodes once and different cuts must not share crossing pairs. In a
tree skeleton every edge is a cut and the cuts are pairwise disjoint as sets of crossing pairs, so
the sum over *all* edges — a laminar, not a partition, family of cuts — is available.

**Theorem 3.1 (tree skeletons).** Let A ↦ N(A) be a network family for per in Model V(s) whose
skeleton (g, c_{a,b}) is a tree T (routing nodes allowed anywhere). For an edge e of T let
(k_e, k′_e) be the numbers of rows and of columns in the clusters of the nodes on the side of e
with fewer vertices (so k_e + k′_e ≤ n). Then

```
U ≥ 2 · Σ_{e ∈ E(T)} log C(k_e + k′_e, k_e).
```

*Proof.* Fix e and let (L, R) be the two sides; w(L,R) = c_e since e is the only skeleton edge
between L and R. The data of L depends on A only through rows I_L (|I_L| = k_e) and columns J_L
(|J_L| = k′_e), that of R through I_R = I_L^c and J_R = J_L^c. Fix the shared blocks I_L × J_R and
I_R × J_L as in B-Theorem 6.2, Step 2: an injection β : I_L → J_R (exists as k_e ≤ n − k′_e), an
injection γ : J_L → I_R (k′_e ≤ n − k_e), zeros elsewhere. Then, exactly as there,
per(A) = Σ_{I⊆I_L, J⊆J_L, |I|=|J|} per(X[I,J])·per(Y[I_R ∖ γ(J_L∖J), J_R ∖ β(I_L∖I)]) with both
families independent (B-Lemma 3.3), so the matrix (X, Y) ↦ per(A) has rank
Σ_i C(k_e,i)C(k′_e,i) = C(k_e + k′_e, k_e) (Vandermonde), and B-Lemma 3.1 gives
2^{c_e} ≥ C(k_e + k′_e, k_e). Sum over the edges: U = 2 Σ_e c_e. ∎

**Corollary 3.2 (bounded-degree trees, clusters {i,i′}).** Let the clusters be {i, i′} (i ∈ [n])
and let the skeleton be a tree all of whose nodes have degree ≤ Δ, Δ ≥ 3. Then

```
U ≥ 4·n·log_{Δ−1} n − O(n·log log n)  =  (4/log(Δ−1) − o(1)) · n log n.
```

In particular U ≥ (4 − o(1)) n log n for binary routing trees. (Conjecture 6.5 asks for
(1 − o(1)) n log(n/2) here.)

*Proof.* Root T at a centroid for the weight "number of clusters": a node v such that every
component of T − v contains ≤ n/2 clusters (exists: move from any node towards a component with
> n/2 clusters until none is left). For an edge e let m_e be the number of clusters below e; then
the side below e has 2m_e ≤ n vertices and (k_e,k′_e) = (m_e,m_e), so Theorem 3.1 gives
U ≥ 2 Σ_e log C(2m_e, m_e) ≥ 2 Σ_e (2m_e − log(2m_e+1)) using C(2m,m) ≥ 4^m/(2m+1) (and 0 for
m_e = 0). Edges with m_e = 0 contribute nothing; along a path of degree-2 routing nodes all edges
have the same m_e, so keeping one edge per such path only lowers the bound; after that the tree
has n cluster nodes and routing nodes of degree ≥ 3, hence E ≤ 2n − 2 edges with m_e ≥ 1. Put
M := Σ_e m_e = Σ_{clusters} depth. By concavity Σ_e log(2m_e+1) ≤ E·log(2M/E + 1) ≤ 2n·log(M/n + 1).
Since at most 1 + Δ Σ_{j<d}(Δ−1)^j ≤ 3(Δ−1)^d nodes have depth ≤ d, the n clusters satisfy
M ≥ Σ_{t=1}^{n} log_{Δ−1}(t/3) ≥ n log_{Δ−1}(n/3) − n/ln(Δ−1) ≥ n log_{Δ−1} n − O(n). Then
U ≥ 4M − 4n log(M/n+1) and, as M/n ≥ log_{Δ−1} n − O(1) → ∞, 4n log(M/n + 1) = O(n log log n). ∎

**Remark 3.3 (what Theorem 3.1 does and does not cover).**

(a) *Where the bound degenerates.* For a routing node of degree n (the star) M = n and
Theorem 3.1 gives only U ≥ 2n·log C(2,1) = 2n, i.e. B-Theorem 6.2 (one bit per leaf). Conjecture 6.5 for
trees is therefore exactly the question of high-degree routing nodes, which is where Theorem 2.1
and Problem 5.2 live. Note also that for *general* clusters the per-edge term can vanish: if one
side of e contains only row clusters, C(k_e + 0, k_e) = 1 (Remark 5.1). Corollary 3.2 needs the
clusters to be balanced; for clusters with k_j rows and k′_j columns and |k_j − k′_j| ≤ d the same
proof gives U ≥ 4M(1 − O(d²/…)) − O(n log log n) along the lines of B-Theorem 6.2, Step 2.

(b) *Model R comparison.* In Model R(1) the same tree argument gives U ≥ 2 Σ_e log C(n, m_e)
(B-Lemma 3.2), which for a binary tree is ≈ Σ_d 2^d (n/2^d) d ≈ n log² n, strictly more than
B-Theorem 6.1's n log n; so for trees the row-local model is provably more expensive than the
vertex-local one by a factor ≈ log n /4 — consistent with the separation of §4.

(c) *Grids and cliques (intermediate goal (ii)).* For a non-tree skeleton, the cuts induced by a
spanning tree T′ are not disjoint: a skeleton edge (a,b) is counted in dist_{T′}(a,b) of them, so
U ≥ 2 Σ_{e∈T′} log C(…) / max_{(a,b)} dist_{T′}(a,b). Every spanning tree of a √n × √n grid has an
adjacent pair at tree distance Ω(√n), and for the clique skeleton the hierarchical family has
multiplicity log n, so the cut-packing bound returns to Θ(n) in both cases. Goal (ii) is **not**
achieved here; for grid-like skeletons (Anthropic's Lemma 8 groupings, our HC network) the only
route we see is the orbit method of §2 applied to a routing node together with all its
neighbours' tensors as "environment" (Theorem 2.1, "more generally").

---------------------------------------------------------------------------------------------------

## 4. Model V is strictly more powerful than Model R; the right hard family

**Proposition 4.1 (separation; intermediate goal (iii)).** Let f(A) := [A is a permutation
matrix] on {0,1}^{n×n}.

(a) f has a network in Model V(1) (clusters {i,i′}) with g = n nodes, U = 0, P = 0, one setting per
node: W_i := [row i has exactly one 1]·[column i has exactly one 1], Ψ ≡ 1.

(b) Every network family for f in Model R(s) has U ≥ Σ_j log C(n,|V_j|) ≥ n log(n/s).

(c) Consequently B-Theorem 6.1's test family 𝓕₁ = {A : exactly one 1 per row} gives no lower
bound at all in Model V: on 𝓕₁, per = f, and (a) is correct on 𝓕₁ with U = 0. Any lower-bound
family for Model V must contain matrices with ≥ 2 ones in rows *and* columns that the column
(row) nodes cannot check locally.

*Proof.* (a) A 0/1 matrix is a permutation matrix iff every row and every column has exactly one
1; the product of the W_i is this indicator; value = Π_i W_i since Ψ ≡ 1 and each S_i has one
element. (b) B-Theorem 6.1's proof uses only matrices in 𝓕₁, on which per = f: the cut around
cluster V_j gives the matrix M_{V_j}[X,Y] = f(A) of rank C(n,|V_j|) by B-Lemma 3.2's proof (the
evaluation points are matching matrices, which lie in 𝓕₁). (c) is (a)+(b). ∎

So intermediate goal (i) of the task ("one 1 per row plus allowed columns forces log n per row
in Model V") is false; the engine's networks for per would have to be excluded on a richer family.
Proposition 4.1 also explains *why* Conjecture 6.5 is harder than B-Theorem 6.1: the bijection
check that costs log n per row in Model R is free in Model V, and what remains hard is only the
*global* consistency of several 1s per row and column — a counting/cycle-structure problem.

**Proposition 4.2 (the cycle-counting family and its single-cut rank).** Let 𝓒 := {I + P_σ : σ a
derangement of [n]} (two 1s in every row and column; I denotes the identity matrix). Then
per(I + P_σ) = 2^{c(σ)}, c(σ) = number of cycles, and in Model V(1) with clusters {i,i′} node i
sees exactly (σ(i), σ^{−1}(i)). Let Q ⊆ [n] be a set of clusters (cut L = Q), and fix the crossing
arcs of σ: b arcs leaving Q and b arcs entering Q, b ≤ |Q|. The private data of L is the bijection
φ_L : in-arcs → out-arcs induced by σ inside Q together with the cycles of σ inside Q; similarly
φ_R for R; and

```
per(A) = 2^{c_L + c_R} · 2^{c(φ_R ∘ φ_L)},    rank_{(φ_L, φ_R)} [2^{c(φ_R φ_L)}] = Σ_{λ ⊢ b, ℓ(λ) ≤ 2} (dim λ)² = Catalan(b) = C(2b,b)/(b+1).
```

Hence a cut around Q of width w needs 2^{w} ≥ Catalan(b) ≈ 4^b/b^{3/2}: again at most ≈ 2 bits
per crossing arc, i.e. ≤ 2 bits per vertex of Q, consistent with B-Proposition 3.5. (Checked for
b ≤ 5 in `vlb_cycle_rank.py`, together with the q^{c} version, rank = #{π ∈ S_b with no decreasing
subsequence of length q+1}.)

*Proof.* A perfect matching of I + P_σ chooses on each cycle of σ either all diagonal entries or
all arcs: 2^{c(σ)}. The cycles of σ are the cycles inside Q, the cycles inside Q^c, and the
cycles formed by alternately following φ_L and φ_R, whose number is c(φ_R φ_L) as a permutation of
the b out-arcs. The matrix M[π,ρ] := 2^{c(ρπ)} on S_b is the matrix of right-convolution by the
class function h(π) = 2^{c(π)} on ℚ[S_b]; its rank is Σ_λ (dim λ)² over the irreducible λ with
ĥ(λ) ≠ 0. By Frobenius' formula, p_μ(y) = Σ_λ χ_λ(μ) s_λ(y) for the power-sum symmetric function of
cycle type μ, and p_μ(1,1,0,0,…) = 2^{ℓ(μ)} = 2^{c(π)}, so h = Σ_λ s_λ(1,1) χ_λ and s_λ(1,1) ≠ 0 iff
λ has at most two rows. Σ_{ℓ(λ)≤2} (dim λ)² counts the permutations whose RSK shape has ≤ 2 rows,
i.e. (Schensted) with no decreasing subsequence of length 3, which is the Catalan number. ∎

**Remark 4.3 (what 𝓒 is good for).** On 𝓒 the problem is: node i holds the two pointers
(σ(i), σ^{−1}(i)), the skeleton is fixed and independent of σ, and the network must output
2^{c(σ)}. This is pointer chasing / cycle counting with a *fixed communication topology*, i.e. a
permutation-routing problem: to follow a cycle, information about i must reach σ(i), whose
position in the skeleton is unrelated to i's. Shannon's lower bound for rearrangeable switching
networks (log n! ≈ n log n switch states) is the classical statement that routing all
permutations through a fixed network costs n log n; Conjecture 6.5 is its "linear-algebraic"
analogue — the tensor contraction is allowed to superpose exponentially many routings. The gap
between the two is exactly what Proposition 4.2 quantifies: a single cut sees only the Catalan
number, because superposition lets the two sides exchange *paired* in/out arcs rather than
addresses. On 𝓒 the diagonal legs of Lemma 1.2 are all x_i = 1; the richer family
{diag(x) + P_σ} with Π(P_σ) = ⊗_{cycles c} (e_1^{⊗c} + e_0^{⊗c}) is the one the orbit method of §2
uses, and it is the family we recommend for Problem 5.2.

---------------------------------------------------------------------------------------------------

## 5. What a proof of Conjecture 6.5 has to do

**Remark 5.1 (cuts can certify nothing at all in Model V).** Take Model V(1) with 2n singleton
clusters ({i} and {i′} separately) and a skeleton consisting of a tree on the n row nodes, a tree
on the n column nodes, and one edge between them. For *every* cut (L,R): if L contains all row
nodes, both sides see all of A; if L contains a proper subset of the row nodes and no column
node, R sees all of A (through the column nodes); and symmetrically. So every cut has rank 1 and
the single-cut test is passed with c ≡ 0 — and U = 0 is of course impossible (the value would be a
product of local terms). B-Theorem 6.2 only avoids this because its Step 1 *groups* row and
column clusters into balanced groups before cutting. Thus "2 bits per vertex" (B-Prop. 3.5) is
the single-cut truth for balanced groups and 0 bits for unbalanced ones; neither is the truth about
networks. Lower bounds for this skeleton (Problem 5.3) need to use that the row subtree computes a
*vector* F(A) ∈ ℚ^{2^{w}} by a Model R network, the column subtree a vector G(A) by a transposed
Model R network, and per(A) = ⟨F(A), G(A)⟩ — a "row/column factorisation" of the permanent with
both factors of low cut rank in their own variable order; B-Theorem 6.1's method bounds each
factor's cut ranks but says nothing about their inner product.

**Problem 5.2 (two-bit star; the first all-cuts-pass case).** Show that no Model V(1) network with
clusters {i,i′}, a routing centre and c_{i,centre} = 2 computes per for large n. Equivalent
tensor formulation (Lemma 1.3): there are no G ∈ (ℚ⁴)^{⊗n} and local M_i(s_i) ∈ ℚ^{2×4} with
Π(s) = (⊗_i M_i(s_i)) G for all zero-diagonal s. Restricted to configurations supported on a
q-set Q (other views zero), this says that the tensors f_s = per_Q(diag x_Q + s_Q) ∈ (ℚ²)^{⊗q},
s_Q ranging over the 2^{q(q−1)} zero-diagonal 0/1 matrices on Q, are all restrictions of one
tensor G_Q ∈ (ℚ⁴)^{⊗q} by maps M_i depending only on row i and column i of s_Q. A proof has to
use the locality of the M_i (Remark 2.3), and probably the sub-family {diag(x) + P_σ} of Remark 4.3,
on which f_σ = ⊗_{cycles} GHZ_c and M_i depends only on (σ(i), σ^{−1}(i)). The orbit argument of
Theorem 2.1 is the q = 3, D = 2 case. A positive answer with D = n^{Ω(1)} legs needed would give
U = Ω(n log n) for stars and, through the "more generally" clause of Theorem 2.1, for every skeleton
with a high-degree routing node; combined with Theorem 3.1 this would prove Conjecture 6.5 (with
a worse constant) for all tree skeletons.

**Problem 5.3 (row/column factorisation).** In the setting of Remark 5.1 with w bits on the
connecting edge and U_R, U_C bits inside the two subtrees: show U_R + U_C + 2w ≥ (1−o(1)) n log n.
Even the special case w = 0 — per(A) = F(A)·G(A) with F computed by a Model R network of total
shared bits o(n log n) and G by a column-local one — is open. On 𝓕₁ it is trivial (F ≡ 1,
G = Π_j [column j has one 1]), so again a richer family is needed.

**Problem 5.4 (the right potential function).** The sum-over-cuts of B-Theorem 6.1 is a special
case of the following: a function Φ on networks with (i) Φ(N) ≤ U(N) and (ii) Φ(N) ≥ n log(n/s)
whenever value(N) = per. In Model R, Φ = Σ_j log rank(cut_j) works because row cuts are disjoint
and each has rank C(n,k_j). In Model V the candidates are: (a) Σ over a laminar family of
cuts of log rank, divided by the multiplicity — gives Theorem 3.1 for trees and only Θ(n) for
expanders, grids and cliques (Remark 3.3(c)); (b) an entropy/Shearer bound on the shared bits
θ — but the network value is a signed sum, not a probability, so Shearer's lemma does not apply to
it directly; its natural linear-algebraic substitute is the *tensor-network rank* (minimal bond
dimensions over all networks of a given shape), for which no technique beyond flattening ranks
is known even for a fixed tensor (this is the tensor-network analogue of the HWY obstacle quoted
in B-§6.5); (c) orbit/invariant arguments as in §2, which are the only ones here that certify
something flattenings cannot. We regard (c), developed for the family {diag(x) + P_σ}, as the
most promising route; it is however an algebraic-geometry question (which GL-orbits of
⊗_c GHZ_c-type tensors can be restrictions of one tensor of format D^{×q} with *local*
restriction maps) that we have not been able to settle beyond D = 2.

---------------------------------------------------------------------------------------------------

## 6. Relation to the literature

* **Nisan 1991 / B-Theorem 6.1.** The row-cut rank C(n,k) is Nisan's partial-derivative-matrix
  rank for the noncommutative permanent; Theorem 3.1 is its tree-shaped sum in Model V. The
  vertex-cut rank C(k+k′,k) (B-Lemma 3.4) and the Catalan rank of Proposition 4.2 are the
  "unknown partition" analogues discussed for any-order ROABPs by
  [Bhargava–Tengse](https://arxiv.org/html/2407.10143v1); the permanent is *not* hard under the
  row/column-overlapping partitions that Model V induces, which is the whole difficulty.
* **Tensor networks as an arithmetic model.** Austrin, Kaski and Kubjas,
  [*Tensor network complexity of multilinear maps*](https://mirror.theoryofcomputing.org/articles/v018a016/)
  (Theory of Computing 2022), study exactly the model of Lemma 1.1 (a tensor network whose
  contraction equals a multilinear map, cost = largest intermediate tensor) and note that it
  captures the O*(2^n) algorithms for the permanent; their lower-bound technique is the
  flattening (cut) rank, and they state that no technique beyond flattenings is available for
  network-shape lower bounds — the same wall as B-Proposition 3.5. Lemma 1.2 turns Model V into
  a tensor network for the *family* Π(s) with s-local tensors, which is the structure a lower
  bound has to exploit (Problem 5.4).
* **Orbit classification of 2×2×2 tensors.** The GHZ/W dichotomy (Dür–Vidal–Cirac 2000),
  Cayley's hyperdeterminant as the relative invariant separating them
  ([Miyake, quant-ph/0206111](https://ar5iv.arxiv.org/html/quant-ph/0206111);
  [Bremner–Bickis–Soltanifar](https://arxiv.org/pdf/1106.5068): it generates the invariant ring),
  and "Det ≠ 0 is closed under restriction/degeneration" are what Theorem 2.1 uses. The tensor
  f^{path} = x_1x_2x_3 + x_1 + x_3 is a W-type tensor (rank 3, border rank 2); f^{cyc} = GHZ.
  Maximal ranks of 2×⋯×2 tensors ([arXiv 1306.0708](https://ar5iv.labs.arxiv.org/html/1306.0708))
  bound how many nodes the orbit method needs for larger bond dimension (Remark 2.3).
* **HWY 2011.** [Hrubeš–Wigderson–Yehudayoff](https://www.doi.org/10.1090/S0894-0347-2011-00694-2)
  reduce noncommutative *circuit* lower bounds for the permanent to the sum-of-squares problem;
  the obstacle there (no single cut separates the variables) is the one B-§6.5 compares Model V
  to. Our Lemma 1.2 shows the obstacle in Model V is milder: the diagonal legs are genuinely
  separated, only the off-diagonal entries are shared, and the shared part is "two-party per
  entry". No analogue of the sum-of-squares reduction is used here.
* **Number-on-forehead.** The cut around one cluster {i,i′} hides only A_{ii} from the rest, a
  NOF-type situation. Known NOF lower bounds (Babai–Nisan–Szegedy;
  [Rao–Yehudayoff](https://eccc.weizmann.ac.il/report/2014/060/revision/1/download) Ω(n/4^k)
  deterministic disjointness; [Lee–Shraibman](https://ar5iv.arxiv.org/html/0712.4279)) are for k
  players each missing a block and degrade exponentially in k; here there are n "players", so the
  NOF literature gives nothing directly, and the overlap structure (every entry seen by exactly
  two nodes, overlap graph K_{n,n}) is closer to edge-input distributed models (CONGEST-type
  lower bounds for cycle/matching detection) — but those measure rounds along input edges, not
  bits along a fixed skeleton, and we found no transferable statement.
* **Switching networks.** Shannon's bound log n! ≈ n log n for rearrangeable networks is the
  combinatorial shadow of Conjecture 6.5 on the family 𝓒 (Remark 4.3); Proposition 4.2 shows
  that linear superposition reduces what a single cut can see to a Catalan number, so the
  classical counting argument does not transfer.
* **Symmetric functions.** Frobenius' formula p_μ = Σ_λ χ_λ(μ) s_λ and the Schensted/RSK
  correspondence (Stanley, EC2, Ch. 7) give the Catalan rank in Proposition 4.2; the matrix
  2^{c(ρπ)} is the Gram matrix of the Brauer/Temperley–Lieb-type loop model at loop weight 2.

---------------------------------------------------------------------------------------------------

## 7. Checklist and scripts

Proved here: Lemma 1.1 (tensor-network form), Lemma 1.2 (private diagonal legs), Lemma 1.3
(star criterion), Proposition 2.2 (which cuts pass for the one-bit star), Theorem 2.1 (no
routing node with three one-bit leaves; in particular no one-bit star), Theorem 3.1 (tree
skeletons), Corollary 3.2 (bounded-degree trees: (4/log(Δ−1) − o(1)) n log n), Proposition 4.1
(Model V ≻ Model R; 𝓕₁ useless in Model V), Proposition 4.2 (cycle family, Catalan rank).
Inputs taken from `barrier.md`: Lemmas 3.1–3.4, Theorem 6.2 Step 2, Theorem 6.1's proof.

Open: Conjecture 6.5 (all skeletons); Problem 5.2 (two-bit star, the smallest all-cuts-pass
skeleton); Problem 5.3 (row/column factorisation); grid/clique skeletons (Remark 3.3(c)); the
input-dependent-skeleton and sums-of-networks gaps A, B of `barrier.md` are untouched.

Scripts (`research/permanent/scripts/`):

* `vlb_star_hyperdet.py` — exact: the tensors Π(s) for the 3-cycle and path configurations
  (n = 3, 4), their one-leg flattening ranks (all 2) and Cayley hyperdeterminants (1 vs 0).
  Output in `vlb_star_hyperdet.out`.
* `vlb_cycle_rank.py` — exact: rank of [2^{c(ρπ)}]_{π,ρ∈S_b} = Catalan(b) for b ≤ 5, and the
  q = 3 version. Output in `vlb_cycle_rank.out`.
* `vlb_star_als.py` — heuristic (floating point, alternating least squares) fit of a star
  network with bond dimension D to per on all 2^{n²} matrices. It did not recover the known
  D = 3 solution for n = 3 (local minima), so its non-zero residuals for D = 2 are **not** used as
  evidence; Theorem 2.1 is the proof. Kept as a starting point for Problem 5.2 experiments
  (D = 4, n = 4 is feasible).
