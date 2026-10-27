# A meta-theorem for connectivity CSPs on sparse structures

27 Oct 2026. This follows `exact-count-lowrank.md` and `exact-extensions.md`. Tags: **[Computed]**
means checked exactly by `research/scripts/meta_*.py` (or `ext_*.py` where cited). **[Mine]**
means a derivation that has not been machine-checked. **[Paper]** means the Anthropic manuscript.
This is a research exploration. **Every algorithmic statement below is conditional on (A1) and
(A2).** Nothing here removes either assumption.

Scripts (exact int/Fraction arithmetic, brute-force ground truth):

* `meta_engine.py` extends `ext_engine.py` from one Grassmann field to p independent fields: a
  vertex v carries the pairs (ψ̄_v^f, ψ_v^f), f < p, and a field may be absent at a vertex (that
  field's root). It reuses `ext_engine`'s exact rank factorisation of crossing edges and its sign
  contraction unchanged.
* `meta_problems.py [seed] [trials] [subset]` covers nine new problem families P1–P9 (§4). Each is
  checked three ways: brute force = identity by explicit determinants = blob network on random
  partitions, with K = 2, 3 (and 4 where the crossing budget allows).
* `meta_ablate.py` removes the reordering sign, or merges two fields into one, to show that both
  ingredients are needed.

---

## 0. Assumptions

**(A1) Network evaluation [Paper: Def. 2, Lemma 1, Lemma 8, Theorem A(b)].** Take a network in the
sense of Def. 2 on g nodes. Its node tables W_a are arbitrary integers of at most B = poly bits,
each computable within τ_cost operations. Its pairwise equality-test edges have c_ab shared bits,
total U = 2Σc_ab and per-node maximum P. Its value Z = Σ_z Π_a W_a(z_a) Π Ψ_ab can be computed
deterministically within

  2^{e(U + gP/K) + 2gP/K} · (P+B)^{C} · τ_cost  operations.

Here (K, e, g) run along the sequence of Theorem A, and e = e_ℓ → 0 and K_ℓ → ∞ as ℓ → ∞.
This is used for *general* networks with arbitrary integer W, not only for the clique networks
that come from k-SAT. That is the same dependency as in `exact-count-lowrank.md` §4–5.

**(A2) Grassmann blob construction [`exact-count-lowrank.md` §2, `exact-extensions.md` §0, §3].**
Consider a sum

  Z = Σ_{s,σ} Π_v C_v(s_v, σ|δ(v)) · ∫ Π_v M_v(s_v) Π_e F_e(s_u, s_v, σ_e).

Here C_v is an integer local table, M_v is even in v's generators, and F_e is even in the
generators of u and v. Such a sum is the value of a network of this kind on any partition of V
into g blobs, as follows:

* Each crossing edge carries log₂(#labels) bits, where #labels is the exact Schmidt rank of F_e
  per (σ, parity).
* The fermionic reordering sign costs one parity bit per blob pair, copied along interleaving
  chords, which is O(g³) bits in all.
* Blob tables are integers (after clearing denominators edge by edge) and can be evaluated in
  2^{O(n/g)} · poly.
* Global counting markers go in through one Kronecker variable Y = 2^b with B = poly(n).
* Hubs are handled as in `exact-extensions.md` §3.

(A2) was stated there for one field. §2 extends it to p fields; that extension is [Computed] here
and is not a new assumption.

---

## 1. The class CONN-CSP

**Structure.** The input is a graph or digraph G = (V, E) with n = |V| and |E| ≤ c·n. A
bounded-arity hypergraph or CSP is first replaced by its incidence graph, with one auxiliary
vertex per constraint, which keeps the size linear.

**Labels.** Each vertex gets a label s_v ∈ Σ_V and each edge a label σ_e ∈ Σ_E, with |Σ_V|, |Σ_E| = O(1).

**Local part.** Integer tables of poly(n) bits each:
* vertex tables C_v(s_v, σ|δ(v)), which may read the labels of all incident edges (degree
  constraints);
* edge tables Ψ_e(s_u, s_v, σ_e).

The weight of a configuration is w(s,σ) = Π_v C_v · Π_e Ψ_e. Auxiliary labels with signed
weights are allowed (for example the inclusion–exclusion for domination). In that case
"configuration" means its *primary* part, and w is the sum over the auxiliary labels.

**Objective.** ω(s,σ) = Σ_v a_v(s_v, σ|δ(v)) + Σ_e b_e(s_u, s_v, σ_e), with integer values in
[0, W] and W = poly(n).

**Global predicates.** There are p = O(1) of them. Predicate j has a *selector*: a vertex set
S_j = {v : s_v ∈ A_j} and an edge set X_j = {e : (s_u, s_v, σ_e) ∈ B_j}. The selector must satisfy
X_j ⊆ E(S_j), which is a pairwise condition, so configurations violating it get weight 0. Write
H_j = (S_j, X_j). Its *type* is one of:

| type | meaning | certificate D(H) | value of D | exact? |
|---|---|---|---|---|
| CONN_r | H connected, fixed r ∈ S | det L_H^{(r)} | τ(H) | no |
| CONN | H connected (rootless, S ≠ ∅) | [w¹] det(L_H + w I_S) | \|S\| τ(H) | no |
| TREE | H is a spanning tree of S | CONN + marker on \|X\| − \|S\| | [tree] | **yes** |
| PATH | H is a path | TREE + local deg ≤ 2 on S | [path] | **yes** |
| CYCLE | H is one cycle | local deg = 2 on S + [w¹] det(L_H + wI) | \|S\|² [cycle] | **yes** (\|S\| tracked) |
| FOREST | H is acyclic | 2^{\|X\|−\|S\|}[z^{\|S\|−\|X\|}] det(L_H + z diag(2 − deg_H)) | [forest] | **yes** |
| MINCOMP | objective = c(H), minimised | lowest w-power of det(L_H + wI) | Σ_F w^{#trees} | min only |
| OUT-BRANCH_r | out-arborescence of S from r | local indeg 1 on S∖r, 0 at r; det L_in^{(r)} | [branching] | **yes** |
| IN-BRANCH_r | in-arborescence to r | local outdeg 1 on S∖r, 0 at r; det L_out^{(r)} | [branching] | **yes** |
| REACH_r | every v ∈ S reachable from r (or reaching r) | det L_in^{(r)} (or det L_out^{(r)}) | #arborescences | no |
| STRONG_r | H strongly connected, r ∈ S | det L_out^{(r)} · det L_in^{(r)} (2 fields) | #in-arb · #out-arb | no |
| DCYCLE | H is one directed cycle | local in = out = 1 on S; [w¹] det(L_out + wI) | \|S\| [cycle] | **yes** |
| DPATH | H is one directed path | local in, out ≤ 1, ≥ 1 arc; [w¹ z^{\|S\|−1}] det(L_out + wI) | [path] | **yes** |

Notation: L_H is the Laplacian of H on S; L^{(r)} deletes row and column r; L_out = D_out − A;
L_in = D_in − Aᵀ; τ is the number of spanning trees. "Rootless" types can also be given a root
*label*: exactly one vertex of S is marked as root (via [t¹] of a marker), and the mass w ψ̄ψ is
placed only at the marked vertex.

**Problems.** The input is (G, tables, selectors, types, k). The problem is one of:
* **Decision:** is there (s,σ) with w(s,σ) ≠ 0, all predicates true and ω = k (or ≤ k)?
* **Optimisation:** find min or max ω over the solutions.
* **Counting:** compute N_k = Σ_{(s,σ): all predicates true, ω = k} w(s,σ). When w ∈ {0,1} this
  is the number of solutions of value k.

---

## 2. Certificates and the fermionic product

**Lemma 1 (certificates).** For every type in the table, D(H) ≥ 0, D(H) > 0 iff the predicate
holds (given the stated local constraints), and D(H) has the stated value. **Proof.**

* *CONN_r, CONN.* By the matrix-tree theorem, det L^{(r)} = τ(H), which is > 0 iff H is connected.
  By the matrix-forest theorem, det(L + wI) = Σ_{rooted spanning forests F} w^{#trees(F)}. Its w¹
  coefficient counts rooted spanning trees, which is |S|τ(H). In general the lowest w-power with a
  non-zero coefficient is exactly c(H), and that coefficient is Π_C |C|τ(C) > 0. This gives
  MINCOMP, because all coefficients are ≥ 0, so nothing cancels.
* *TREE.* A connected H with |X| = |S| − 1 is a tree, and then τ(H) = 1. Since |X| − |S| is a sum
  of local terms, it is fixed by a marker: weight z on each selected edge and z on each vertex
  outside S, then take [z^{n−1}].
* *PATH* is the same, with a local degree constraint.
* *CYCLE.* With deg = 2 on S, H is a disjoint union of cycles, and [w¹] picks single-component H.
  A cycle of length ℓ has τ = ℓ, so the value is |S|². Here |S| is tracked by t^{|S|}, so dividing
  by k² is exact.
* *FOREST.* See `exact-extensions.md` §2 [Computed there]. Rooted spanning forests of H have at
  least c(H) ≥ |S| − |X| trees, with equality iff H is a forest. In that case the only such forest
  is H itself, and each tree T contributes Σ_{v∈T}(2 − deg_T v) = 2.
* *Directed types.* By the directed matrix-tree theorem, det L_in^{(r)} counts out-arborescences
  rooted at r, and det L_out^{(r)} counts in-arborescences towards r. If in-degree is exactly 1 on
  S∖r and 0 at r, then X is an out-arborescence iff X is acyclic, so the count is 0 or 1.
  STRONG_r holds iff both counts are > 0, and both are needed, as the example a→b shows.
  DCYCLE: a directed cycle of length ℓ gives det(L_out + wI) = (1+w)^ℓ − 1, whose lowest
  coefficient is ℓ. DPATH: a directed path gives w(1+w)^{ℓ−1}, whose lowest coefficient is 1.
  The power of w is the number of components, so [w¹] selects single paths and cycles, and the
  marker z^{|X|} separates the two (|X| = ℓ−1 or ℓ). ∎

**Lemma 2 (Grassmann form and independent fields).** For one predicate, write
q_e = (ψ̄_u − ψ̄_v)(ψ_u − ψ_v) for an undirected edge, ψ̄_u(ψ_u − ψ_v) for an arc u→v in L_out,
and ψ̄_v(ψ_v − ψ_u) for an arc in L_in. Then

  det(L_H^{(R)} + diag(d)) = ∫ Π_{v∈S∖R} (1 + d_v ψ̄_vψ_v) · Π_{v∉S} ψ̄_vψ_v · Π_{e∈X} (1 + q_e),

where root generators are omitted and ∫ takes the top coefficient. The factor ψ̄_vψ_v deletes v,
because no other term can then use v's generators. Since X ⊆ E(S), no selected edge touches such
a v. The −z·deg_H part of the 2-deg mass is spread over the edges as exp(q_e − z(ψ̄_uψ_u + ψ̄_vψ_v)).
Membership e ∈ X_j and v ∈ S_j depend only on (s_u, s_v, σ_e) and s_v respectively. So every factor
is a pairwise F_e(s_u, s_v, σ_e) or a local M_v(s_v), which is the form required by (A2).

For p predicates, give each its own pairs (ψ̄^f, ψ^f). Even elements in disjoint generator sets
commute, and the top monomial is a product of even pairs. Therefore

  ∫ Π_f A_f(ψ^f) = Π_f ∫ A_f(ψ^f),

and the integrand Π_v Π_f M_v^f · Π_e Π_f F_e^f computes Π_j D_j(H_j) **[Computed: P1, P8, P9]**.
The fields must be *independent*. Sharing one field computes det(L_{X_1} + L_{X_2}) instead of the
product (`meta_ablate.py` B).

**Bits per crossing edge.** The crossing matrix of F_e for fixed σ_e is indexed by (s_i, monomial
of i) × (s_j, monomial of j). Its rank is therefore at most |Σ_V|·4^p for each parity, so an edge
costs β ≤ log₂(2|Σ_E||Σ_V|4^p) = O(1) bits. The sign still needs only the total parity of each
piece, because every F_e is even, so its cost stays O(g³) whatever p is. The measured label counts
per crossing edge (maximum, §4) were:

| CFVS | COCT | k-leaf outbranching | degree trees | directed paths | metric TSP | cycle cover (u/d) | 2 trees | strong |
|---|---|---|---|---|---|---|---|---|
| 8 | 6 | 3 | 5 | 3 | 9 | 5 / 3 | 9 | 5 |

---

## 3. The meta-theorem

**Theorem (conditional on A1, A2).** Fix c, |Σ_V|, |Σ_E|, p and the types. Let 𝒫 be a problem in
CONN-CSP whose instances satisfy:

* (S) |E| ≤ c n;
* (D) maximum degree Δ = O(1), or the hub condition (D′) below;
* (W) the objective values and the bit sizes of the tables are poly(n);
* (P) *positivity*: w(s,σ) ≥ 0 for every primary configuration. This is needed for parts (a) and
  (b) only.

Then for every δ > 0 there is a deterministic algorithm running in time 2^{δn} (for n ≥ n₀(δ)) that
does the following:

* **(a) decision.** It decides 𝒫, and finds a witness by self-reduction: pin labels one at a time
  with unary tables, using n|Σ| calls.
* **(b) optimisation.** It computes min ω and max ω over the solutions.
* **(c) certificate-weighted counting.** For every k it computes
  N_k^D = Σ_{sol, ω=k} w · Π_j D_j(H_j).
* **(d) exact counting.** Suppose every predicate is *tree-like*, meaning that on true instances
  D_j(H_j) = κ_j(m_j) for a known function κ_j of quantities m_j that are sums of local terms and
  tracked by markers. The types marked "yes" in §1 qualify: κ ∈ {1, |S|, |S|²}. A CONN predicate
  also qualifies if the constraints force |X_j| = |S_j| − 1. Then it computes N_k exactly, which is
  the exact number of solutions of value k when w ∈ {0,1}.

**Proof.**

1. *Identity.* Introduce markers: one variable y for ω, and one per tracked quantity (w for the
   mass, z for |X| − |S| and the 2-deg trick, t for |S|). Their degrees are poly(n). By Lemmas 1
   and 2,

   Z(y, markers) = Σ_{s,σ} w(s,σ) y^{ω} Π(markers) Π_j D̂_j,

   where D̂_j is the determinant before coefficient extraction. The coefficient extraction in
   Lemma 1 is linear, so each target quantity is one coefficient of Z. Substituting Y = 2^b for the
   markers, with b = O(n log n) for the bound on |coefficients|, makes Z a single integer. Since
   intermediate coefficients can be negative (the 2-deg trick), decode with balanced digits. The
   values then stay below 2^{B} with B = poly(n).

2. *Network.* (A2) with p fields (§2). Take a balanced partition into g blobs. Then
   * P ≤ βΔn/g + O(g²);
   * U ≤ 2β|E| + O(g³) ≤ 2βcn + O(g³);
   * the table cost τ_cost is 2^{O((Δ + p) n/g)}·poly. A blob table sums over at most
     |Σ_V|^{n/g}|Σ_E|^{Δn/g} internal configurations, each with a Grassmann product in 4^{p·n/g}
     monomials.

   With bounded degree, a balanced partition with every blob boundary at most Δn/g exists
   trivially. The equality-test structure of Def. 2 comes from the exact rank factorisation
   (`ext_engine.decompose_edge`).

3. *Evaluate.* Apply (A1) at level ℓ. The exponent is at most

   n · [ e_ℓ(2βc + βΔ/K_ℓ) + 2βΔ/K_ℓ + O((Δ + p)/g_ℓ) ] + O(g_ℓ⁴ + log n).

   Choose ℓ = ℓ(δ) so that the bracket is < δ/2. Then n ≥ n₀ absorbs the constants and the
   poly(P + B).

4. *Extract.*
   * (c) is a coefficient of Z.
   * (a), (b): the coefficient of y^k in N^D equals Σ_{sol, ω=k} w · Π D_j. Under (P) every term is
     ≥ 0, and terms with a false predicate vanish (Lemma 1), so the coefficient is non-zero iff a
     solution of value k exists. min/max ω is the lowest/highest non-zero y-power. For MINCOMP the
     objective is the w-power itself, and the lowest non-zero power is the minimum because all
     matrix-forest coefficients are ≥ 0.
   * (d): on solutions Π_j D_j = Π_j κ_j(m_j), and the m_j are tracked by the markers, so divide
     coefficient by coefficient. ∎

**(D′) hubs [Mine; partly Computed in `ext_hubs.py`].** Degree Θ(n) breaks the per-node bound P.
Without bounded degree, (S) still suffices if each vertex h of degree > Δ₀ satisfies two
conditions:

* (i) C_h reads its incident edge labels only through a commutative finite automaton with O(1)
  states, such as min(deg, d₀), deg mod q, "all edges selected", or the exact count needed for
  in-degree 1;
* (ii) every predicate type that selects h is CONN/TREE/FOREST/STRONG-like rather than
  degree-2-like.

Then h can be split into a path of copies of degree ≤ 3. The copies share s_h by pairwise equality
tables. They carry the automaton state on the path edges, which costs O(1) bits. In every field the
path edges are *forced*: the factor is q_e rather than 1 + q_e, which contracts the path back to h,
so τ, [tree] and [forest] are unchanged. In `ext_hubs.py` the splitting was [Computed] for Steiner
trees through the network, and for induced forests by brute force. For degree-2 types (CYCLE, PATH,
2-factors) use the label compression of `exact-extensions.md` §3.2 instead. Directed hubs are
unchecked.

**Corollary (combination).** Predicates combine freely: products of certificates of independent
fields, with labels coupling them only through local tables. The costs multiply only in the
constant β (factor 4 in the rank per extra field), and since e_ℓ → 0 this changes nothing
asymptotically. Exactness holds iff *each* factor is tree-like.

**What the class cannot express (as far as this construction goes).**

1. Exact counts of connected but non-tree objects, such as #connected vertex covers,
   #connected subgraphs or T_G(1,2). D = τ is not constant on solutions, and no τ-free
   connectivity indicator is known (`exact-extensions.md` row 5).
2. *Maximising* the number of components (cycle packing, max cycle cover, maximally disconnected
   dominating set). The matrix-forest polynomial exposes c(H) only as its lowest power. For
   forests, c = |S| − |X| is local, so forest-type component objectives work in both directions.
3. Acyclicity of digraphs (directed FVS). There is no determinant certificate that is ≥ 0 and
   > 0 iff acyclic.
4. Non-local global quantities such as diameter, distances, flow values and cut values. Statistics
   that are sums of local terms, such as leaf counts, degrees, |S| and weights, are fine even for
   non-spanning structures.

---

## 4. Coverage

Status: **D** decision, **O** optimisation, **#** exact count, **#τ** certificate-weighted count
only. "ext" means verified in `exact-extensions.md`; P1–P9 means verified here.

### Cut&Count list (Cygan et al., arXiv 1103.0534, Theorem 1.2, plus §5)

| # | Problem | Encoding in CONN-CSP | Status | Verified |
|---|---|---|---|---|
| 1 | Steiner Tree | y_v (S ⊇ T), TREE_r on G[S] (det counts the tree edges) | D O # (also #min-weight) | ext 4b |
| 2 | Feedback Vertex Set | FOREST on G[V∖Y] | D O # | ext 4d |
| 3 | Connected Vertex Cover | local VC + CONN(G[S]) | D O #τ | ext 4c |
| 4 | Connected Dominating Set | signed auxiliary domination labels (w ≥ 0 after summing) + CONN | D O #τ | ext 4c′ |
| 5 | Connected FVS | CONN(G[Y]) × FOREST(G[V∖Y]), two fields | D O #τ | **P1** |
| 6 | Connected OCT | 3 states (X / colour A / colour B), local properness + CONN(G[X]) | D O #τ (weight τ·2^{c(V∖X)}) | **P2** |
| 7 | Min Cycle Cover (undirected / directed) | local 2-factor / cycle cover + MINCOMP | D O; coefficient = Σ Π ℓ_i² (resp. Π ℓ_i) | **P7** |
| 8 | Longest Path (undirected / directed) | y_v; deg ∈ {1,2} (in, out ≤ 1) on S; CONN/DPATH + markers | D O # (#P_k for all k) | ext 4f; **P5** |
| 9 | Longest Cycle (undirected / directed) | CYCLE / DCYCLE + t^{\|S\|} | D O # | ext 4f; **P5** |
| 10 | Exact k-Leaf Spanning Tree (min / max leaf) | TREE + local u^{[deg=1]} | D O # | ext 4a; **P4** (internal = n − leaves) |
| 11 | Exact k-Leaf Out-branching (min / max leaf) | OUT-BRANCH_r + u^{[outdeg=0]}; root free: ×n roots | D O # | **P3** |
| 12 | Max (Exact) Full Degree Spanning Tree | TREE + a^{[deg_X = deg_G]} | D O # | **P4** |
| 13 | Graph-metric TSP (closed walk ≤ k) | σ_e ∈ {0,1,2}, local even degree, CONN_r(support), z^{x_e·len_e} | D O #τ; also poly-weight walks | **P6** |
| – | Hamiltonian path / cycle (undirected, directed) | special cases of 8 and 9 | D O # | ext 0, 1, 3a, 3b |
| – | Cycle Packing, Max Cycle Cover | would need *max* #components | **not covered** (fixed ℓ: ℓ CYCLE colour fields, but fixed ℓ is already polynomial; ℓ = ω(1) costs β ~ log ℓ, so 2^{O(δ n log ℓ)}) | – |
| – | Maximally Disconnected DS | maximises components | **not covered** | – |

The constant-ℓ remark uses separate colours. One field per colour costs 4^ℓ in the worst case,
but for colour-diagonal factors the rank is about 4ℓ + 1, as in Steiner forest.

### Other connectivity problems

| Problem | Encoding | Status | Verified |
|---|---|---|---|
| Max Internal Spanning Tree | TREE + b^{[deg ≥ 2]} | D O # | **P4** |
| Min-degree spanning tree (spanning tree with max degree ≤ d; minimise d) | TREE + [deg ≤ d]; scan d | D O # | **P4** |
| Exact k-path / k-cycle counting (#P-hard) | as rows 8, 9 | # | ext 4f, **P5** |
| Steiner Forest, p pairs | partitions of pairs × colourings × product of TREE dets | D O # for p = O(1); degrades as log p | ext 4e |
| Directed Steiner tree (Steiner arborescence) | y_v ⊇ T, OUT-BRANCH_r on D[S] via det L_in^{(r)} (D[S]) = #arborescences spanning S | D O # [Mine] | – |
| k vertex-disjoint s_i–t_i paths, counting (k = O(1)) | k colours, PATH per colour | # [Mine] | – |
| Two (or q = O(1)) edge-disjoint spanning trees, counting | σ_e ∈ {0..q}, q TREE fields | # | **P8** |
| Min Strongly Connected Spanning Subgraph | STRONG_r, 2 fields, minimise \|X\| | D O #τ | **P9** |
| TSP / ATSP with poly weights | ext 2 | D O # | ext 2 |
| Connected Max-Cut-type ("one side connected") | CONN on side 1 + local cut weights | D O #τ [Mine] | – |
| Directed FVS / DAG-ness | no certificate | **not covered** | – |
| Exact #connected induced subgraphs, #CVC, #CDS | τ-weighted only | **not covered** (exactly) | – |
| Dense graphs, \|E\| = ω(n) | U = Θ(\|E\|) | only 2^{δ\|E\|} | – |
| Exponential weights | B exponential | **not covered** exactly | – |

---

## 5. Verification [Computed]

`meta_problems.py` was run with seeds 1, 2, 3 and 3 instances per family for P1–P7, with
P8: seeds 3 (3 instances) and 1 (2 instances), P9: seeds 1–4 (3 instances each). P7 was also run
separately with seeds 1–4 × 4, using the planted generator that forces ≥ 2 cycles on odd trials,
which gives instances with min 2 and 3 cycles. Every family prints
**OK**: brute force = identity = network on every partition. Instances have n = 4–7. Each
instance's network is evaluated on 2 random partitions for each K ∈ {2, 3} (P2 also K = 4), with up
to 7 crossing edges.

| | Problem | Identity checked | Highlights |
|---|---|---|---|
| P1 | connected FVS | [w¹ Z^n t^k]/2^n = k Σ τ(G[Y]) | min CFVS ∈ {1, 2}; two fields (connectivity × 2-deg forest) |
| P2 | connected OCT | [w¹ t^k] = k Σ τ(G[X]) 2^{c(V∖X)}; lowest k = brute-force optimum | min COCT = 2 |
| P3 | exact k-leaf out-branching | Σ_X u^{#leaves} det L_in^{(r)} = exact leaf distribution | e.g. [2, 22, 24, 2] |
| P4 | spanning trees: full degree, internal, max degree ≤ d (d = 2, 3, n) | [z^{n−1}] joint distribution of (#full-degree, #internal) | exact for each d |
| P5 | directed k-paths / k-cycles | [w¹t^k z^{k−1}] = #P_k, [w¹t^k z^k] = k#C_k (2-cycles included) | exact for all k |
| P6 | graph-metric TSP; weights 1..3 | lowest z-power = metric-closure TSP by permutations | independent truth |
| P7 | min cycle cover, undirected / directed | lowest w-power = min #cycles; coefficient = Σ Π ℓ² / Σ Π ℓ | minimum 1, 2, 3 seen |
| P8 | ordered pairs of edge-disjoint spanning trees | [z₁^{n−1} z₂^{n−1}] Σ τ(X₁)τ(X₂) = brute force | exact; two TREE fields |
| P9 | min strongly connected spanning subgraph | assert det_out·det_in ≠ 0 ⟺ strong on every X; lowest power = MSCS | MSCS = n+1 on non-Hamiltonian instances (e.g. n=5: 6, n=4: 5) |

Ablations (`meta_ablate.py`):
* (A) Dropping the reordering sign changes the network value in 11 of 12 (CFVS, MSCS, K = 2, 3)
  cases, so the sign remains necessary with several fields.
* (B) Replacing two independent fields by one shared field changes the two-tree value in every
  case.

---

## 6. Caveats

1. **Conditional.** Everything rests on (A1) for *general* networks with arbitrary integer tables,
   which is the paper's internal Lemma 1/8 together with Theorem A(b). It is not the Lean Main
   Theorem. As `exact-count-lowrank.md` §4 explains, the construction does not go through k-SAT.
2. **Sparse only.** U = Θ(|E|), so the bound is 2^{δ|E|}. Bounded degree, or the hub condition
   (D′), is needed for the per-node P of Lemma 8. (D′) is [Mine] beyond the Steiner and forest
   checks, and unchecked for directed hubs and for counters on degree-constrained hubs.
3. **Positivity.** Decision and optimisation need w ≥ 0 after summing the auxiliary labels;
   otherwise solutions can cancel. The certificates are ≥ 0 by construction.
4. **Exactness.** Exact counting requires every predicate to be tree-like (τ ∈ {0,1}, or a known
   function of tracked local sums). CONN, REACH, STRONG, MINCOMP and graph-metric TSP give only
   certificate-weighted counts.
5. **Weights** must be poly(n) for exact optimisation. Exponential weights blow up B.
6. **Constants.** "2^{δn} for every δ" hides n₀(δ) and constants of tower type that come from
   Theorem A's level sequence. β = log₂(2|Σ_E||Σ_V|4^p) affects only constants, because e_ℓ → 0.
   It does, however, force p, |Σ| = O(1). Growing p (Steiner forest with many pairs, cycle packing
   with ℓ = ω(1)) gives 2^{O(δ n log p)}.
7. The checks are small (n ≤ 7, K ≤ 4, at most 7 crossing edges). They test the identities and
   the multi-field network algebra, sign included, not the asymptotic bit bookkeeping.
