# Extensions of the fermionic matrix-tree blob network

27 Oct 2026. This extends `exact-count-lowrank.md` (the identity n·#HC = Σ_{2-factors} τ, plus its
blob network). Tags: **[Computed]** means checked exactly by `research/scripts/ext_*.py`.
**[Mine]** means a derivation that has not been machine-checked. **[Paper]** means the Anthropic
manuscript. Every algorithmic consequence below is conditional on the paper's Lemma 1/Lemma 8 and
Theorem A(b) for *general* networks (Def. 2), exactly as the HC result is. Nothing here changes
that dependency.

Scripts (all exact int/Fraction, brute-force ground truth):

* `ext_engine.py` is a generic engine. A problem is given by local states, local constraints and
  even Grassmann factors. The engine builds the blob network by an exact rank factorisation of
  each crossing edge's factor, and it computes the reordering sign directly.
* `ext_problems.py [seed] [trials]` checks 13 problem families three ways: brute-force combinatorial
  count = the identity evaluated by explicit determinants = the blob network on random partitions
  with K = 2, 3, 4.
* `ext_hubs.py` covers the bit-budget questions: the ghost/root vertex, colour cost, hub splitting
  and degree-2 compression.

Status: `ext_problems.py` with seeds 1, 2, 3 (2 + 4 + 4 random instances per family, each on 1–4
random blob partitions) and `ext_hubs.py` both print ALL OK.

## 0. The general template

```
Z = Σ_{s,σ} Π_v C_v(s_v, σ|δ(v)) · ∫dψ̄dψ  Π_v M_v(s_v) · Π_e F_e(s_u, s_v, σ_e)
```

* `s_v` is a vertex state: membership y_v, a colour, or a domination flag.
* `σ_e` is an edge state that the constraints can read (x_e for degree tests).
* `C_v` is an arbitrary local integer table.
* `M_v` is an even element. Examples: the mass term `1 + w ψ̄_vψ_v`, or `ψ̄_vψ_v` to delete a vertex
  outside S.
* `F_e` is an even element in the generators of u and v. It may contain any *pairwise* scalar,
  such as [y_u ∨ y_v], [colour_u = colour_v] or z^{w_e}.
* A root vertex simply has no generators.

**Network.** For a crossing edge e = (i ∈ lower blob, j ∈ higher blob), and for each σ and parity
p, take the matrix (s_i, monomial of i) × (s_j, monomial of j) and factor it exactly as
Σ_t α_t ⊗ β_t. A label is (σ, p, t), and the edge costs log₂(#labels) bits. The sign is that of the
permutation of the odd pieces from edge order into blob order. Each edge's two pieces have equal
parity because F_e is even, so the sign rule of `exact-count-lowrank.md` §2 applies unchanged:
`ε = local · (−1)^{Σ interleaving P_ab P_cd}`, which costs O(g³) parity bits. In all the cases
tested, the tables came out integral. In general, scaling α_t by the lcm of each edge's denominators
keeps W integral, at a cost of O(|E|) extra bits of B.

**Global counting constraints** include |X| = n−1, |S| = k, the degree of a universal vertex, and
"coefficient of w¹". Each one is handled by a generating variable, folded into one integer by
Kronecker substitution Y = 2^b and decoded with balanced digits, because intermediate coefficients
can be negative. This changes only B, which stays poly(n), and B enters the Theorem A(b) cost only
as (λ+B)^{C0K²} = 2^{O(K² log n)}. Evaluating at poly(n) integer points and interpolating is the
alternative.

## 1. Results table

| # | Problem | Identity (local constraints × one det) | Labels / crossing edge (bits) | Status |
|---|---|---|---|---|
| 0 | #HC (baseline) | n#HC = Σ_{2-factors X} det L_X^{(r)} | 5 (2.32) | [Computed] |
| 1 | #directed HC | #DHC = Σ_{cycle covers X} det (D_out−A)_X^{(r)} | **3 (1.58)** | [Computed] |
| 2 | TSP / ATSP, integer w ≤ W = poly | n Σ_H z^{w(H)} = Σ_X z^{w(X)} τ(X); min = lowest power, #optimal = coeff / n | 5 / 3 (weights live in the tables) | [Computed] |
| 3a | Ham s–t paths | #HP_{st} = Σ_{X: deg s = deg t = 1, else 2} det L_X^{(s)} | 5 | [Computed] |
| 3a′ | all Ham paths | Σ_{X: deg ≤ 2} z^{\|X\|} τ(X) = #HP·z^{n−1} + n#HC·z^n | 5 | [Computed] |
| 3b | directed s→t Ham paths | Σ_{X: out/in = (1,0) at s, (0,1) at t, (1,1) else} det L_out^{(t)} | 3 | [Computed] |
| 4a | spanning trees with local degree constraints (leaf count, max leaf, degree bound) | [z^{n−1}] Σ_X z^{\|X\|} Π_v c_v(deg_X v) τ(X), because \|X\| = n−1 makes τ(X) = [X is a tree] | 5 | [Computed] (leaf distribution) |
| 4b | Steiner tree: count and min weight, #optimal | Σ_{S⊇T} det L_w(G[S])^{(t₀)} = Σ_{subtrees ⊇ T} z^{w} | 5 | [Computed] |
| 4c | connected vertex cover | [w¹t^k] Σ_{S VC} t^{\|S\|} det(L_S + wI) = k Σ_{\|S\|=k} τ(G[S]) | 4 (2.0) | [Computed]: decision and min size are exact; counts are τ-weighted |
| 4c′ | connected dominating set (so also max-leaf = n − γ_c) | same, with domination by inclusion–exclusion: [v dominated] = Σ_{d_v}(−1)^{d_v}[d_v ⇒ v and its neighbours ∉ S], which is pairwise | 5 | [Computed]: same caveat |
| 4d | induced forests: **exact #min FVS** | [forest] = 2^{\|E(S)\|−\|S\|} [z^{\|S\|−\|E(S)\|}] det(L_S + z·diag(2 − deg_S)) | 5 | [Computed] |
| 4d′ | all forests, T_G(2,1), by #edges | same identity with S = V and free edges | 4 | [Computed] |
| 4e | Steiner forest with p pairs: count, min weight | Σ_{partitions of pairs} Σ_{colourings} Π_{colours} det (one root per block) | 4c+1 for c colours | [Computed] for p = 2 |
| 4f | #k-paths, #k-cycles (longest path/cycle) | [w¹ z^{n−1} t^k] = k·#P_k and [w¹ z^n t^k] = k²·#C_k, with deg ∈ {1,2} on S and 0 off S | 5 | [Computed] |
| 5 | exact #connected VC / CDS / connected subgraphs, T_G(1,2) | no τ-free connectivity indicator | — | **fails** (only τ-weighted counts) |

Consequence [Mine, conditional on Paper]: each problem in rows 0–4f is solvable deterministically in
time 2^{δn} for every δ > 0 on graphs with |E| = O(n), and the counting is exact in the sense
stated in the table. The cost is U ≈ (bits/edge)·2|E| + O(g⁴) and P ≈ U/g + g², the same
bookkeeping as for HC. A lower bits/edge improves only constants, since e* → 0.

## 2. Notes on the identities

**Directed.** With L = D_out − A, arc i→j contributes exp(ψ̄_i(ψ_i−ψ_j)) = 1 + ψ̄_iψ_i − ψ̄_iψ_j. By the
directed matrix-tree theorem, det L^{(r)} counts arborescences oriented towards r. In a cycle cover,
this count is 1 when the cover is a single cycle (drop r's out-arc) and 0 otherwise, because a cycle
avoiding r gives a singular block with zero row sums. No factor n appears. The factor's Schmidt rank
is only 2: (1+ψ̄_iψ_i)⊗1 − ψ̄_i⊗ψ_j, in either blob order. So an arc costs log₂3 bits, while an
undirected edge costs log₂5.

**Paths, without gadgets.** Requiring degree 1 at s and t forces |X| = n−1, so τ(X) = [X is the s–t
path]. For "any path", requiring deg ≤ 2 leaves only paths and Ham cycles as connected spanning
X. The z^{|X|} weight (a local scalar) separates the two. The universal-vertex reduction also works:
make the universal vertex the root, so its edges are local. Its "degree = 2" test, however, is
global and has to be done by z-marking, which is what row 3a′ does directly.

**Trees with local constraints (4a).** This is the general principle. Fix |X| through a generating
variable. A spanning X with n−1 edges has τ(X) ∈ {0, 1}, and τ(X) = 1 exactly when X is a tree, so
*any* per-vertex constraint on the tree's own degrees becomes exact. That covers the leaf
distribution (and so exact #max-leaf spanning trees), degree-≤d spanning trees, and weighted
versions. Subtrees work the same way, with z^{|X|−|S|} bookkeeping.

**Forest indicator (4d).** This is new here and [Computed]. By the matrix-forest theorem,
det(L_H + diag(d)) = Σ_{rooted spanning forests} Π_roots d_root, where H is on vertex set S.
Rooted spanning forests have at least c(H) trees, and |S| − |E(H)| ≤ c(H), with equality iff H is a
forest. When H is a forest, H itself is the only spanning forest with c(H) trees. Choosing
d_v = z(2 − deg_H v) then gives each tree T the factor Σ_{v∈T}(2 − deg_T v) = 2. In Grassmann form,
`−z deg_S(v)ψ̄_vψ_v` is spread over the edges, so every factor stays local or pairwise. Corollaries:
exact counts of induced forests by size (and so of minimum feedback vertex sets), and of
forests by edge count (T_G(2,1), #P-hard). No ghost vertex is needed.

**Connectivity versus counting (4c).** τ(G[S]) > 0 iff G[S] is connected. That gives decision and
optimisation (lowest t-power), and exact counts of (S, spanning tree) pairs. It does not give
#{connected S}. Steiner *trees* are fine because the object being counted *is* the tree.

## 3. Bit budget and the per-node bound of Lemma 8

Lemma 8(i), with g = 3K⁸, costs 2^{e(U+gP/K) + 2gP/K}, where P is the **maximum over blobs** of
the bits a blob shares. So total bits are not enough: every blob's boundary has to be close to the
average. With bounded maximum degree Δ, a balanced partition gives P ≈ 2.32·Δn/g + g², and
gP/K ≈ 2.32Δn/K. A vertex of degree Θ(n) would give P = Θ(n) and gP/K = Θ(K⁷n), which breaks the
bound. There are three ways round this:

1. **Ghost / root vertex: free.** The root has no generators, so an edge (v, root) whose x is not
   read at the root has Schmidt rank 1 and costs 0 bits. [Computed] in `ext_hubs.py` §1:
   det(L+I) = τ(G+ghost), with 1 label on every ghost edge. A universal ghost therefore costs
   nothing. A ghost *with a degree test* has a global constraint, which is moved into a
   generating variable.
2. **Hubs under degree ≤ 2 (HC, paths, cycle covers): compress.** Only 1 + 4d + 16·C(d,2)
   labelings of the hub's d edges into one blob are realisable, which is O(log d) bits per pair
   instead of 2.32d. So P_hub = O(g log n). One extra code is reserved for infeasible
   configurations on the other side. ([Mine]; the counts are printed in `ext_hubs.py` §4.)
3. **Hubs in tree/forest/subset problems: split.** Replace h by a path of copies joined by *forced*
   edges (factor q_e, copies sharing y; for CDS they also share d). This preserves #subtrees ⊇ T
   and #induced forests, and gives n' ≤ n + 2|E| = O(n) with Δ ≤ 3. [Computed] (`ext_hubs.py` §3,
   Steiner through the network, induced forests by brute force). A degree constraint at the hub
   (4a leaf tests) has to be carried along the copy path by a saturating counter, which costs O(1)
   bits [Mine].

Other caveats:

* **Dense graphs.** U = Θ(|E|), so the bound is 2^{δ|E|}, which is useless once |E| = ω(n).
* **Weights.** W must be poly(n). B ≈ nW·b with b = O(n log n). Exponential weights make B
  exponential, so this gives exactness only for small weights; scaling gives approximations.
* **Steiner forest.** The cost is log₂(4c+1) bits per edge, plus Bell(p) networks. That is fine for
  p = O(1). As p grows, U/n ~ log p grows, and 2^{δn} for *every* δ is lost; the bound degrades
  to 2^{O(δ n log p)}.
