# The open door, stated as finite problems: hyperedge configurations under three merges and under constant-size groups

5 Nov 2026. Sources read for this note: Anthropic, *A 2^{o(n)} time algorithm for 3-SAT* (§2, §3–5, App. A/B/H; local
text `scratchpad/anth-paper.txt`); Majdoddin, *Lowered crossover points of Anthropic's subexponential 3-SAT algorithm*,
arXiv 2610.41622 (§2, §4, §5; local text `scratchpad/hx/axpdf/2610.41622.txt`; his scripts
`calc/r123_idsearch.py`, `r123_idcut.py`, `r123_escapes_cut.py`, `r123_laser_threecut_lb.py`); our
`engine2-decorrelated.md` §7–8, `engine2-algebraic.md` M7/§9, `engine2-probabilistic.md` §7, `pieces.md`,
`permanent/clique-evaluation.md` §4, `permanent/rate.md` §3, `permanent/barrier.md`, `ambitious-targets.md` §0, and the
parallel `engine3-search.md` (the search agent's results on C, cited as [S]).
Scratch computations for this note (all in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/opendoor/`): `flatcert.py`, `flatcert2.py`,
`flatcert3.py`, `flatcert4.py` (flattening certificates and core floors), `prism_als.py`, `rect_als_control.py` (N = 2
identity search); outputs `*.out`. Tags as in our notes: **[R]** proved here, **[K]** known (source named), **[N]** exact or
numerical computation (script named), **[C]** heuristic/conjecture, **[M-argued]** stated by Majdoddin as "argued", not proved
there, **[S]** from `engine3-search.md`.

## 0. Verdict

* **The three-merge candidate C of Majdoddin §4.7–4.8 (two lines of AG(2,3)) is closed: ρ_C ≥ 1/2 − o(1) for every identity,
  hyperedge pieces included [R, Theorem 2.3 and Remark 2.4].** Two proofs. (a) The **core floor** (§2.3): fix the b-legs; the
  a-triangle remains, every merge puts a_0, a_1, a_2 in distinct groups, the uniform quantum functional of ⟨N,N,N⟩ is N², a
  network of cost c has functional ≤ 2^{2c/3}, so some piece costs ≥ 3m under *every* merge (this is Majdoddin's §4.8 "halves"
  argument made rigorous; found independently by the search agent [S]). It proves the two-lines configuration of AG(2,q) closed
  for **all q** (one line is an agreeing core with half the edges). (b) My transfer proof (Remark 2.4) gives in addition that the
  piece full under the heaviest merge has c_{k′} + c_{k″} ≥ 6m. Flattenings alone certify only 1/3 on C [N], so the functional is
  necessary, as in his Lemma 4.11. His `r123_idsearch.py` searched only merge-local *product* terms (Prop. 4.23 territory); the
  search agent's explicit non-local identity P⊗F⊗F + B⊗F⊗F reaches 5/6 at N = 2, 3 and, asymptotically with App. B crossing
  pieces, ρ_C ≤ 0.957 [S]. Window on C: **[1/2, 0.957]**, and the lower end is final.
* **The AG(2,4) instances he names as the next door are closed at 1/2 too, by flattenings alone, once the hyperedge cost is
  defined [N, `flatcert.out`, `flatcert2.out`]:** the translation matching with three (or all four) slopes as merges certifies
  exactly 4 of 8, the two-parallel-lines configuration (q = 4 analogue of C) 6 of 12 (and its core floor is 1/2 as well). On every
  small three-merge instance proposed, three orthogonal merges buy nothing beyond two; the "floor 1/3" of §4.8 is not approached.
* **The core floor as a design principle (§2.5, coordinator's request).** For any configuration and any set of merges, fixing the
  legs outside a node set H leaves the graph tensor of H on the parts of the *join* of the restricted merges; the uniform
  functional gives max_i min_k c_k(π_i) ≥ |E_cross(H)|·m − o(m), hence **ρ ≥ max_H |E_cross(H)|/E** [R]. A configuration can have
  ρ < 1/2 only if no core carries half its edges. Two-lines configurations fail (one line = half). Configurations that pass, with
  their proved floors (core / flattening): the three transversal triangles Δ_3 of the 3×3 grid (1/3 / **4/9**), the 3×3 level
  (2/9 / 4/9), full parallel classes Δ_q of AG(2,q) (1/q / unknown), the prism (4/9 / 2/3), the incidence 8-cycle (0.45 / ≥ 0.65).
  **Δ_3 (9 nodes, 9 edges, 18 strings, two merges) is now the smallest open instance for ρ < 1/2**, half the size of the 3×3 level,
  and it is simultaneously the cleanest test of Majdoddin's rectangle-content conjecture (§4.4), which predicts no trade at all
  on it (every edge is the lone diagonal of its rectangle).
* **Arithmetic of success (§2.6).** Theorem A gives e(K) = Θ((log K)^{−α′}), α′ = log₂(1/ρ) exactly [K, Thm A(a)]. A configuration
  family with ρ_C < 1/2 placed in a squaring level (the AG(2,q) levels with three parallel classes as merges and Δ_q classes as
  configurations do plug in, §2.7) gives α′ > 1, hence e = o(1/log K), which is all the dense wall needs (e·U = o(n) at
  U = n log n). Majdoddin's "a lever on ρ, i.e. on α′, not a change of the type of decay" is also correct: the decay stays
  polylogarithmic and the crossover lower bound log₂ m* ≥ q(C/bar)^{1/α′} stays exponential in a power of 1/bar (it would drop
  from ≈ 6.2·10³ to ≈ 3.2·10² at α′ = log₂ 3 in his main-term model, from ≈ 10⁹ to ≈ 10⁵ with the actual constants). Different
  questions, both right. **For our programme, ρ < 1/2 on a squaring-compatible configuration is success**, and the open
  instances for it are Δ_3, the 3×3 level and the Δ_q classes.
* **Polynomial decay is a different door, now sharply located [R, Propositions 1.9–1.10].** K_{ℓ+1} = gK_ℓ needs groups of
  constant size g. Then (i) at most C(p,2)·g²·K edges are in three- or four-cell position for any pair of the p merges, so the
  known (rectangle) trades cover a vanishing fraction; (ii) by the core floor, edges between different components of a
  configuration's *incidence subgraph* pay in full under every merge, and a node pair at incidence distance D needs a
  configuration of ≥ D nodes; in a degree-g incidence graph on 2K/g vertices almost all pairs are at distance Ω(log_g K). Hence
  **configurations of size Ω(log K/log g) are forced: this is the precise content of Majdoddin's "pieces of growing arity"**
  (coordinator's item (iv): confirmed, with core floor + counting as the mechanism; his own stated reason is Prop. 4.9 + Lemma
  4.11 + §4.6). The smallest probe of a non-rectangle trade is the prism (6 nodes, two orthogonal perfect matchings as merges):
  flattenings certify ρ_P ≥ 2/3 [N]; a two-piece identity at N = 2 with bonds 2 or 4 does not exist even approximately (ALS
  residuals 0.988, 0.927 against 10⁻¹¹ for the exact bond-8 control and 10⁻¹⁷ on the rectangle control) [N]. The smallest instance
  with two-cell edges is the incidence 8-cycle (flattenings ≥ 13 of 20 by search).
* What this leaves (§6): Δ_3 / Conjecture 8.1 for α′ > 1; two-cell trades in growing configurations for polynomial decay;
  Majdoddin's Open Problem 1 (the rectangle window ρ ∈ [1/2, 1/√2]) as the only lever inside RM_2.

---------------------------------------------------------------------------------------------------

## 1. Exact definitions

### 1.1 The clique sum and the exponent per edge bit [K]

Fix K ≥ 3, λ ≥ 1, N = 2^λ. Every edge {u,v} of K_K carries a string z_{uv} ∈ {0,1}^λ; node v holds an arbitrary table
W_v of its K − 1 strings. The (K,λ)-clique sum is

  Z_K(N) = Σ_{(z_{uv})} Π_{v∈[K]} W_v(z_v)      (Majdoddin (1); Anthropic Def. 3 writes it with two copies per edge and the
  equality test Ψ_{w,w′}(z_w, z_{w′}) = [z_w(w′) = z_{w′}(w)] on every edge).

S = C(K,2)·λ is the number of edge bits; an algorithm has **exponent per edge bit** e if it runs in time 2^{(e+ε)S} for all
tables and large λ (Majdoddin §2.1; Anthropic Def. 4 uses C·2^{eK²λ}(B+λ)^C with S ≈ K²λ/2, so Anthropic's e is half of
Majdoddin's at the same K; we use Majdoddin's). e(K) is the infimum over a class of algorithms. Brute force: e = 1. **Input
floor** e ≥ 2/K (Prop. 2.4(a): every table entry has nonzero coefficient, K·N^{K−1} entries). **Flattening floor** for
rank-one methods (border/asymptotic rank included): e ≥ ⌊K²/4⌋/C(K,2) → 1/2 (Prop. 2.4(b): the graph tensor T_K has flattening
rank N^{|A|(K−|A|)}). **Width bound** for contraction trees: e ≥ c(K−c)/C(K,2) → 4/9, c = ⌈K/3⌉ (Prop. 2.4(c); our
`clique-evaluation.md` §4.2).

### 1.2 Signed Network Sums as a model [K, Majdoddin Def. 2.3; Anthropic §2.2, Def. 1–2]

A Signed Network Sum writes Z = Σ_q c_q Z_q with fixed scalars c_q, each Z_q the value of a tensor network whose tensors are
computed from the input tables (re-indexing, merging nodes, multiplying by fixed tensors), each term contracted along its own
contraction tree; the cost is at least the total number of entries of all tensors materialised. *A term* is one choice of a
piece for every (configuration, block) pair of the level's identity (Def. 4.2 (L2)). *It costs* the size of the merged tables it
builds plus the cost of the merged instance it hands to the recursion ((L5)). *A merge* is a partition P of the nodes into
groups; a term is evaluated under one merge; a group becomes one node whose table is the product of its members' tables and of
the pieces internal to it; a piece between two groups G, G′ is written by a fixed rank decomposition across (V(C)∩G | V(C)∩G′),
its index becomes part of the merged edge, and its **cost** c(π) = log₂(rank across the split) is the number of bits the merged
edge carries for it ((L4); Anthropic Def. 1: "F costs c bits if F(z,z′) = Σ_{θ∈{0,1}^c} f(z,θ)f′(z′,θ)", least such c ≥ log₂
rank). On three tables the model collapses to rank-one methods (Thm 2.5); at K = 4 it beats every rank-one method and every
contraction tree if ω = 2 (Thm 2.7, N^{23/6}); Tables 2–3 give the one-level values at K = 4, 6, 9, 16.

### 1.3 The class RM_p and its axioms [K, Majdoddin Def. 4.2]

(L1) the edges are partitioned into configurations C, f_C = ⊗_{e∈E(C)} I_e; (L2) strings are cut into blocks of m bits, m → ∞
or m = λ, and for each (C, block) there is an exact identity f_C|_block = Σ_{i∈I_C} π_{C,i} (up to a nonzero scalar) with
|I_C| ≤ 2^{o(m)}; the level's identity is the product over all (configuration, block) pairs and **every** choice is a term;
(L3) merges P_1, …, P_p; **merge k is usable only if every configuration meets at most two groups of P_k**; (L4) the cost above;
(L5) size charge. Balanced = equal group sizes, 2 to K/2 groups; homogeneous = every pair of groups of P_k carries the same
multiset of configuration types, each in → ∞ incidences. Anthropic's level is an RM_2^{bh} level (Remark 4.3): g×g grid,
configurations = rectangles (the two diagonals of a 2×2 subgrid) and straight edges, merges = rows and columns. (L3) is the axiom
the open door violates (Remark 4.5: such a configuration "would become a hyperedge of the merged instance").

### 1.4 What one Anthropic level does, exactly [K]

Grid g×g, K_ℓ = g², g = 3K⁸ in the main text (Lemma 1, Chebyshev) and g = 2^{3ℓ+x₀}K in Theorem A (Lemma 8(ii), Hoeffding).
Every edge whose endpoints differ in row and column is a diagonal of exactly one rectangle; straight edges are a 2/(g+1)
fraction. For a rectangle with strings x, y (top row) and u, v (bottom), the crossing [x = v][y = u] has rank N² row-wise
(xy | uv) and column-wise (xu | yv). Lemma 2: t = ⌈λ/3⌉ blocks of 3 bits, eight-square identity 2[x_s=v_s][y_s=u_s] = R_s + C_s
per block (R_s = [x_s⊕y_s⊕u_s⊕v_s = 0]σ(x_s,y_s)σ(v_s,u_s) factors through 3 bits row-wise, 6 column-wise; C_s the reverse);
pieces A_i = Σ_{|Q|=i} Π_{s∉Q}R_s Π_{s∈Q}C_s with Σ_i A_i = 2^t[x=v][y=u] and c_i^{row} + c_i^{col} ≤ 11t ≤ 4ρλ + 8, ρ = 11/12,
the "+1+1" being the t naming bits of Q in each direction. Prop. 3: per term merge rows or columns, whichever total is smaller;
(K, e) achievable ⇒ (g², (ρ + 2/K)e + 2/K) achievable. Theorem A with pieces (ρ, c) (Def. 7: Σ_i A_i = d[x=v][y=u],
c_i^{row} + c_i^{col} ≤ 4ρλ + c log(2λ), |I| ≤ (2λ)^c): K_{ℓ+1} = g_ℓ², e_{ℓ+1} = (ρ + 3ζ_ℓ)e_ℓ + 3/K_ℓ, ζ_ℓ = 2^{−ℓ−5}; (a): ½ρ^ℓ ≤
e_ℓ ≤ 0.85ρ^ℓ and log K_ℓ = (3x₀+6)2^ℓ − 6ℓ − 2x₀ − 6, so ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α′} with **α′ = log₂(1/ρ)**: 11/12 → 0.125,
App. B's 1/√2 → 1/2.

### 1.5 Why ideal ρ = 1/2 gives exactly 1/log K [K]

Two merges; some piece is full across each split (pigeonhole, Prop. 4.6); the adversary mixes the two full pieces half-half
(Prop. 4.8; our `clique-evaluation.md` §4.3): every two-merge identity on a configuration meeting two groups per merge has
ρ ≥ 1/2. Pieces reaching it ("ideal", costs (2,0) and (0,2) per bit; open, Majdoddin Open Problem 1, Remark 2.9) would give
α′ = 1; Theorem 4.13 proves 1/e(K) ≤ log₂ K for every grid algorithm with any pieces, tight exactly for ideal pieces (Rem. 4.14).

### 1.6 Cost of a piece on a configuration meeting r ≥ 3 groups: the definition Majdoddin leaves open [R]

Let C meet the groups G_1, …, G_r of merge k and let π be a piece (a tensor on the strings of C, grouped into r legs). Majdoddin
§4.8: "a hyperedge over four blocks of the third merge, whose cost the model does not yet define". Two definitions are
natural; both reduce to (L4) when r = 2.

**(D1) network cost.** c_k(π) := min Σ_{i<j} log₂ d_{ij} over exact representations π = Σ_θ Π_i f_i(ℓ_i; (θ_{ij})_{j≠i}) with bond
dimensions d_{ij} (a K_r tensor network on the groups). The index θ_{ij} becomes part of the merged edge (G_i,G_j) exactly as in
(L4), the merged instance is again a weighted clique sum, and Anthropic's recursion (Def. 2 has only pairwise Ψ_{a,b}) applies
verbatim. **Cut bound [R]:** rank(π; ∪_{i∈S}G_i | rest) ≤ Π_{i∈S, j∉S} d_{ij}; hence c_k(π) ≥ max_S log₂ rk_S(π) and c_k(π) ≥
½Σ_i log₂ rk(π; G_i | rest). Coarsening the groups to unions can only lower the network cost (bonds inside a union become
internal). For f_C and r = 3, c_k(f_C) = (number of crossing edges)·m exactly.

**(D2) hyperedge cost.** c_k(π) := log₂ R(π), the tensor rank of π as an r-party tensor (one index shared by all r groups; the
"hyperedge with values in H" of Thm 2.5's remark). Not a cost the recursion as written can pay. **Relation [R, uses K]:**
D2 ≤ D1, and for r = 3, D1 ≤ (3/2)·D2 + O(1): the diagonal tensor [θ_1=θ_2=θ_3] on 2^c values is a restriction of the triangle
network with bonds d,d,d (which is ⟨d,d,d⟩) as soon as the subrank Q(⟨d,d,d⟩) ≥ 2^c, and Strassen proved Q(⟨d,d,d⟩) ≥ ⌈3d²/4⌉
[K, Strassen, *Relative bilinear complexity and matrix multiplication*, 1987, to my recollection; the asymptotic subrank is d²],
so d = 2^{c/2}(4/3)^{1/2} suffices, cost 1.5c + O(1), and 1.5c is a lower bound by the cut bound. For r groups the path
simulation costs (r−1)c and the cut bound gives ≥ rc/2.

**Choice.** D1 throughout: the only cost the recursion can pay, equal to (L4) when r = 2, within a constant factor of D2. Every
lower bound below uses only the cut bound and coarsening, so it holds for every cost ≥ D1's cut bound.

### 1.7 The mixing criterion and the finite (fixed-N₀) criterion [R, formalising Prop. 4.8 and Lemma 2]

Let C be a configuration all of whose E edges cross every one of p merges (true for every instance below), so the raw cost of C
is E·m under every merge. For a block identity f_C|_block = Σ_{i∈I} π_i with cost vectors c(i) = (c_1(π_i), …, c_p(π_i)), the
adversary chooses fractions x ∈ Δ(I) of the (configuration, block) incidences, the algorithm the merge; the level pays on C

  V(C) := max_{x∈Δ(I)} min_k Σ_i x_i c_k(i) = min_{q∈Δ_p} max_{i∈I} ⟨q, c(i)⟩   (von Neumann),    ρ_C := V(C)/(E·m).

So **ρ_C ≥ 1/2 iff for every weighting q of the merges some piece has ⟨q, c(i)⟩ ≥ E·m/2** (the piece may depend on q), and
**ρ_C < 1/2 iff some q has ⟨q, c(i)⟩ < E·m/2 for every piece.** For p = 2 and uniform q: ρ_C < 1/2 iff every piece has
c_1 + c_2 < E·m, i.e. the sum of a piece's two costs is below the raw cost of *one* merge (eight-square on a 3-bit rectangle:
3 + 6 = 9 against E·m = 6: ρ = 3/4 before naming bits; ideal: 0 + 6 = 6: exactly 1/2). The pigeonhole gives, for each k, a piece
with c_k ≥ E·m − o(m) (§2.3 makes this precise with the quantum functional), so at uniform q that piece needs Σ_{k′≠k} c_{k′} <
(p/2 − 1)E·m: impossible for p = 2 (Prop. 4.8), and for p = 3 it asks for c_{k′} + c_{k″} < E·m/2.

*Fixed alphabet.* A block identity at a fixed alphabet N₀ = 2^{m₀} with T pieces does not satisfy (L2) by itself (T^{#blocks}
terms); Anthropic's grouping by type (Lemma 2, eq. (20), the t naming bits) turns it into poly(λ) pieces at the price of
log₂ T bits per block in **every** direction. The exact finite criterion, in bits per block of m₀ bits, is

  min_q max_i ⟨q, c(i)⟩ + log₂ T  <  E·m₀/2   (for ρ < 1/2),   resp.  < E·m₀  (for any trade, ρ < 1),

with c the D1 costs at alphabet N₀. Sufficient, not necessary (App. H: "the count is not tight"). Check: eight-square, N₀ = 8,
T = 2, costs (3,6), (6,3): 4.5 + 1 = 5.5 of 6, ρ = 11/12. At N₀ = 2 the rectangle has the ideal two-piece identity [x=v][y=u] =
[x=u][y=v] − [x≠y](−1)^x[u≠v](−1)^u (App. H) with costs (0,2),(2,0): 1 + 1 = 2 of 2, no gain: the naming bits are why small
alphabets never show a gain, and why a fixed-N₀ identity is informative only through its cost vectors.

### 1.8 Why polynomial decay needs constant growth of K [K, Majdoddin Prop. 4.1, §4.1]

With e_{ℓ+1} = ρe_ℓ and K_{ℓ+1} = K_ℓ^β, e(K) = Θ((log K)^{−log(1/ρ)/log β}): polylogarithmic for every β > 1. Polynomial decay
e(K) = Θ(K^{−γ}) needs log K_{ℓ+1} − log K_ℓ = O(1), i.e. K_{ℓ+1} = gK_ℓ, γ = log(1/ρ)/log g, so the merge used has K/g groups of
average size g. Thresholds (Prop. 4.1): polylog gives log₂ m* ≥ q(C/bar)^{1/α′}, polynomial gives log₂ m* ≤ (q/γ)log₂(C/bar) + q.

### 1.9 What constant growth forces, I: the known trades die [R, counting]

Fix p merges with groups of size ≤ g. For an edge (u,v) and merges (k,k′) let G,G′ be the k-groups and H,H′ the k′-groups of
u, v. The edge is **four-cell** if G∩H′ ≠ ∅ ≠ G′∩H, **three-cell** if exactly one is nonempty, **two-cell** otherwise. For fixed u
and (k,k′), H′ ranges over the ≤ g groups meeting G and v over their ≤ g² nodes (and symmetrically), so

  #(edges that are three- or four-cell for some pair of merges) ≤ C(p,2)·g²·K,   a fraction ≤ p²g²/K of all edges.

Prop. 4.9 is the four-cell part. Every known identity trades on four-cell edges: the rectangle is the four-cell configuration,
App. B's pieces live on it, and in the grid or in AG(2,q) with three parallel classes *every* edge is four-cell for every pair of
merges. Lemma 4.11 proves that configurations with ≤ 3 cells meeting ≤ 2 groups per merge cannot trade at all. So with constant g
the known mechanism covers a p²g²/K fraction, and polynomial decay needs trades on **two-cell edges**. Many merges do not help:
a term is evaluated under one merge k; rectangle pieces are cheap only under their own two merges, and the adversary's full
pieces (all node ranks full) pay E·m under every third merge in which the configuration's nodes lie in distinct groups (cut
bound: ½Σ_v deg(v)m), which fails for at most O(gK) rectangles per merge; so the cheap edges under k are a ≤ 1/p + O(pg²/K)
fraction and ρ ≥ 1 − 1/p − o(1).

### 1.10 What constant growth forces, II: growing arity [R, core floor + counting; see §2.3 for the core floor]

Let I(C) be the **incidence subgraph** of a configuration C: vertices = the groups (of all merges) meeting C, one hyperedge per
node of C joining its groups (for p = 2 a bipartite graph with one edge per node). Its connected components are the parts of the
join of the restricted merges, so by the core floor with H = V(C): **edges of C between different components of I(C) pay m under
every merge in some piece of every identity, and the adversary can take that piece in every block: they never trade.** A pair
(u,v) at distance D in the full incidence graph I of the level (degree ≤ pg, 2K/g vertices for p = 2) can therefore trade only
inside a configuration whose incidence subgraph connects G_u to H_v; a configuration of s nodes has incidence diameter
≤ (p−1)s (each node makes its p groups mutually adjacent). The number of v within incidence distance D of u is ≤ g·(pg)^{D}, so
the edges that bounded-size configurations can connect number at most K·g(pg)^{(p−1)s}/2 and cover a constant fraction ε of the
≈ K²/2 edges only if (pg)^{(p−1)s} ≥ εK/g, i.e. **s ≥ log(εK/g)/((p−1) log(pg)) = Ω(log K/log g)** for constant p. Configurations (and hence pieces) of
unbounded arity are forced for constant-growth levels. This confirms Majdoddin's "pieces of growing arity" (§4.8) and gives its
mechanism; his own route to it is Prop. 4.9 + Lemma 4.11 + the §4.6 reduction of size arguments to four-leg pieces, which shows
that bounded (four-leg) pieces square K, not that bounded arity is impossible with constant g. The two-cell edges of §1.9 are the
distance-≥ 3 pairs; §1.10 says most pairs are at distance Θ(log K).

---------------------------------------------------------------------------------------------------

## 2. The open door at the smallest instances

### 2.1 Configuration C of AG(2,3) [K, Majdoddin §4.7; made explicit here]

Points of AG(2,3) = Z_3²; parallel classes: columns (x = const), rows (y = const), diagonals (x − y = const), anti-diagonals
(x + y = const). Take the two anti-diagonal lines a_i = (i, −i), b_i = (i, 1−i), i ∈ Z_3. a_i and b_j share a column iff j = i, a
row iff j = i+1, a diagonal iff j = i+2. With merges k = 0 (columns), 1 (rows), 2 (diagonals):

  G_i^k = {a_i, b_{i+k}},  i ∈ Z_3;   the nine groups are the nine pairs {a_i, b_j}.

C has the six edges inside the two lines: a_i a_j and b_i b_j. Strings X_{ij} (a_i's copy on a_i a_j), Y_{ij} (b_i's copy on
b_i b_j): twelve strings of m bits, two per node. f_C = Π_{i<j}[X_{ij} = X_{ji}][Y_{ij} = Y_{ji}] = T_A ⊗ T_B, two copies of the
triangle graph tensor ⟨N,N,N⟩. Under merge k the pair (G_i^k, G_j^k) carries the **bundle** {a_i a_j, b_{i+k} b_{j+k}} (2m bits);
raw cost 6m under every merge; as a 3-party tensor on any merge's groups f_C ≅ ⟨N²,N²,N²⟩. This is `r123_idsearch.py::
config('z3')`. *k-local pieces* (Prop. 4.23): tensor products of one factor per bundle, charged Σ log₂ rank(M_{ij}; G_i | G_j) —
D1 with the three bundle factors as the network. *Hyperedge pieces*: any other tensor; its D1 cost under k is its best triangle
network on G_0^k, G_1^k, G_2^k. Prop. 4.23 [K]: across Q = {forward strings X_{i,i+1}, Y_{i,i+1} | backward}, rank f_C = N⁶ and
every k-local piece has log₂ rank_Q = c_k(π), so identities of k-local pieces have ρ = 1 (`r123_idcut.py`: e(Q) = 6, p_k(Q) = 0;
his least-squares search `r123_idsearch.py` searched only merge-local products of 2×2 factors, residuals 0.98, 0.95).
*Non-local pieces beat this* [S]: f_C = P⊗F⊗F + B⊗F⊗F with P = [x=u][y=v] and B = F − P on one merge-1 crossing, costs 5 and 4
bits at N = 2 (P⊗F⊗F has rank N⁶ across Q but costs 5λ by routing one leg into a neighbouring group), ρ = 5/6; with crossing pieces
of parameter ρ_x on the three merge-1 crossings, ρ_C ≤ ρ_x + 1/4 (0.957 with App. B). The lower bound is the next theorem.

### 2.2 The target on C, exactly

By §1.7 with E = 6: ρ_C < 1/2 iff there are an identity Σ_i π_i = d·f_C|_block, |I| = 2^{o(m)}, and q ∈ Δ_3 with ⟨q, c(i)⟩ < 3m − o(m)
for every piece. The "floor 1/3" of §4.8 would need cost vectors (6m,0,0) and permutations, impossible: a piece free under two
merges is a product over the atoms of the two partitions, which are the single nodes (`engine2-algebraic.md` Lemma 7.2), hence
free under all three. A product over the groups of merge 2 has cost vector (R, R, 0), R = Σ_j log₂ rank(h_j) (both other merges
see the same three ranks), so product pieces give ρ_C ≥ 2/3, worse than the rectangle; only non-product pieces could do better.

### 2.3 The core floor [R; uses K: CVZ quantum functionals]

**Setting.** Configuration C with E edges, merges P_1, …, P_p (partitions of V(C)), block of m bits. For H ⊆ V(C) let Q_H be the
**join** of the restricted partitions P_k|_H (the finest partition of H coarser than every P_k|_H; its parts are the connected
components of the incidence subgraph of H), g_H = |Q_H|, and E_cross(H) = the number of edges of C with both ends in H and in
different parts of Q_H.

**Theorem 2.3 (core floor).** For every identity Σ_{i∈I} π_i = d·f_C|_block (d ≠ 0) and every cost ≥ the D1 cut bound,

  max_i min_k c_k(π_i) ≥ E_cross(H)·m − (g_H/2)·log₂|I|   for every H ⊆ V(C);   hence   ρ_C ≥ max_H E_cross(H)/E − o(1).

*Proof.* Fix the legs of V(C)∖H to arbitrary values. f_C becomes the graph tensor of the subgraph of C induced on H (edges to fixed
nodes become vectors), a tensor on the parties Q_H; with the uniform CVZ functional F (θ = 1/g_H on each part) [K: monotone
under restriction, additive on ⊕, hence subadditive, F(T) ≤ Π_x rk_x(T)^{θ_x}, F of a graph tensor = N^{Σ_edges(θ_u+θ_v)},
F(vector) = 1, scale invariant], F(f_C|_H) = N^{2E_cross(H)/g_H}: this is φ(H) in the coordinator's notation, φ(H) = 2E_cross/g_H =
the average "crossing degree"; single edge 1, K_3 2, P_3 4/3, C_4 2, K_4 3, K_r r−1 (all nodes singletons). A piece π restricted the
same way is, under merge k, a network on P_k|_H with bonds ≤ those of π (the fixed-group tensors contract into the bonds), cost ≤
c_k(π); coarsened to Q_H its cost is still ≤ c_k(π), and each part's flattening rank is ≤ the product of the bonds at the part, so
F(π|_H) ≤ 2^{(1/g_H)Σ_parts log rk} ≤ 2^{2c_k(π)/g_H}. This holds for **every** k, so F(π|_H) ≤ 2^{(2/g_H)min_k c_k(π)}.
Subadditivity: N^{2E_cross/g_H} ≤ Σ_i F(π_i|_H) ≤ |I|·2^{(2/g_H)max_i min_k c_k(π_i)}. Rearranging gives the bound; the adversary
takes that piece in every block, and then every term costs ≥ E_cross(H)·m − o(m) under every merge. ∎

*Checks.* (i) Uniform θ is optimal: with general θ the same argument gives Σ_e(θ_u+θ_v)·m / max_{parts P,P′}(θ_P+θ_{P′}) ≤
E_cross·m. (ii) g_H = 2 is the common-cut contraction of `engine2-decorrelated.md` Theorem 1 / §7.5(a); g_H ≥ 3 with all
merges separating H is its Theorem 2 (diagonal labellings) — the core floor is these two theorems for arbitrary merges, with the
join making precise what "all merges agree on H" means. (iii) The derivation the coordinator relayed — F(GT(H)) = N^{φ(H)}, a
network of cost c has F ≤ 2^{2c/g_active}, so max cost ≥ (g_active/2)φ(H)λ and ρ ≥ max_H g_active φ(H)/(2E) — is correct and is
the same bound: (g_H/2)φ(H) = E_cross(H).

**Corollary 2.3.1 (C and all two-lines configurations are closed).** On C take H = {a_0,a_1,a_2}: every merge separates them,
E_cross = 3 of 6, so some piece costs ≥ 3m − 1.5 log₂|I| under every merge and **ρ_C ≥ 1/2 − o(1)**. For two parallel lines L, L′
of AG(2,q) with any three (or more) other parallel classes as merges, H = L is an agreeing core (a line meets each merge line
once) with C(q,2) of 2C(q,2) edges: **ρ ≥ 1/2 for all q**, which is Majdoddin's §4.8 "halves" claim [M-argued] proved.
*Core floors computed [N, `flatcert4.out`]:* C 3/6; two lines of AG(2,4) 6/12; T4 2/8 (a vertical line); Δ_3 3/9 (one
triangle); 3×3 level 4/18 (H = {(1,1),(1,2),(2,3),(3,3)}, join {(1,1),(1,2)} | {(2,3),(3,3)}); prism 4/9 (same H); 8-cycle 9/20.

### 2.4 Remark: the transfer proof and what it adds [R; uses K: three-party rank inequality]

An independent proof of Corollary 2.3.1 on C that bounds a whole cost vector. Write R_{ij} = log₂ rank(π; {a_i,b_j} | rest) ≤ 4m.
(i) Uniform functional on the merge-0 groups: F(f_C) = N^{6·2/3} = 2^{4m}, F(π) ≤ 2^{(R_{00}+R_{11}+R_{22})/3}, so some π* has
R_{00}+R_{11}+R_{22} ≥ 12m − 3 log|I|, all three ≥ 4m − 3 log|I|, c_0(π*) ≥ 6m − 1.5 log|I|. (ii) For the partition {a_l,b_l},
{a_i,b_j}, {a_j,b_i} (one group of each merge) the three-party inequality rk_C ≤ rk_A·rk_B [K] gives R_{ll} ≤ R_{ij} + R_{ji};
summing over l, Σ_{i≠j}R_{ij} ≥ 12m − 9 log|I|, and the six cross pairs are exactly the groups of merges 1 and 2, so
**c_1(π*) + c_2(π*) ≥ 6m − 4.5 log|I|**: the piece full under one merge pays at least the full cost under the other two together.
(iii) For q with q_0 maximal, ⟨q,c(π*)⟩ ≥ 6m(q_max + q_min) − 4.5 log|I| ≥ 3m − 4.5 log|I|, since q_max + q_min = 1 − q_mid ≥
max(q_max, 1 − q_max) ≥ 1/2. The transfer step needs every complement of a group to be a union of groups of the other merges,
which holds for q = 3 and fails for q ≥ 4; the core floor needs nothing of the kind. Flattenings alone certify 2 of 6 on C
[N, `flatcert.out`, exhaustive over 3⁶ orientations with the §8.2 reduction generalised to three merges]: both proofs need the
functional, as Majdoddin's Example 4.10 predicts.

### 2.5 The design principle, and the configurations that pass it [R + N]

**Necessary condition for ρ_C < 1/2: no core carries half the edges, max_H E_cross(H) < E/2.** Since every single edge e = (u,v)
with u, v separated by all merges is a core with E_cross = 1, configurations must be large; since a set of nodes pairwise
separated by all merges is a core with all its internal edges, **the configuration must not contain a "transversal" sub-
configuration with half the edges**. For designs (point set, several parallel classes as merges, the edges of the other classes
as configurations), a line of a configuration class is always a core (two points determine their line), so a configuration made
of r lines of one class has core floor ≥ 1/r: **r = 2 is closed (two-lines, all q), r ≥ 3 passes.** The join over ≥ 2 merges of two
lines is connected (cross edges 0), so for r ≥ 3 the core floor is exactly 1/r.

Candidates for a second-round search, with floors (core / flattening world / known upper bound), all with the merges separating
every configuration edge:

| configuration | nodes / edges / strings | merges | core | flattening | upper | remarks |
|---|---|---|---|---|---|---|
| **Δ_3**: the three anti-diagonal triangles of the 3×3 grid (one line class of AG(2,3)) | 9 / 9 / 18 | rows, cols (+ diagonals) | 1/3 | **4/9** [N exhaustive, both with 2 and with 3 merges, `flatcert4.out`] | 1 | every edge is the lone diagonal of its rectangle; the rectangle-content conjecture (§4.4) predicts no trade; smallest open instance for ρ < 1/2 |
| 3×3 level K_3×K_3 = Δ_3^{anti} ∪ Δ_3^{diag} | 9 / 18 / 36 | rows, cols | 2/9 | 4/9 (exact ILP, §8.2) | 11/12 (eight-square) | Conjecture 8.1; hub profile §8.6 |
| Δ_q: one full class of AG(2,q), q ≥ 4 | q² / qC(q,2) / q²(q−1) | 3 (or more) other classes | 1/q | not computed (needs the ILP of §8.2 with q groups and 3 merges) | 1 | plugs into squaring, ρ_level → ρ_Δ (§2.7) |
| prism (6-cycle incidence) | 6 / 9 / 18 | two matchings | 4/9 | **2/3** [N] | 1 | constant-growth probe, all edges three-cell |
| incidence 8-cycle | 8 / 20 / 40 | two matchings of pairs | 9/20 | ≥ 13/20 [N search] | 1 | 12 two-cell edges |

Closed (core ≥ 1/2 or flattening ≥ 1/2): C [R], two lines of AG(2,q) [R], T4 [N], every configuration meeting ≤ 2 groups per
merge [K], 3×2 grid and all rectangle-sub-configurations of the 3×3 grid [L].

### 2.6 What ρ_C < 1/2 would give the recursion — the arithmetic [R, checked against Thm A(a) and Lemma 2]

*Per level.* In Theorem A the per-level factor is Def. 7(b), c_i^{row} + c_i^{col} ≤ 4ρλ + c log(2λ) per rectangle, the o(λ) term
containing the naming bits; (41) gives U ≤ N(ρ + 1/g) + 4cg⁴log(2λ), balancing adds 3ζ_ℓ, so e_{ℓ+1} = (ρ + o(1))e_ℓ + 3/K_ℓ with
K_{ℓ+1} = K_ℓ²·2^{6ℓ+2x₀}; the additive 3/K_ℓ is negligible (Thm A(a): e_ℓ ≤ 0.85ρ^ℓ). Hence

  e(K) = Θ((log K)^{−α′}), α′ = log₂(1/ρ):   1/√2 → (log K)^{−1/2};  1/2 → 1/log K;  ρ < 1/2 → (log K)^{−1−ε}, ε = log₂(1/(2ρ)).

A configuration family with ρ_C < 1/2 helps exactly if it sits in a level whose merged instance has K^{1/2+o(1)} nodes (β = 2,
α′ = log₂(1/ρ_level), ρ_level → ρ_C when the raw-edge fraction → 0); the AG(2,q) levels do (§2.7). Then e(K) = o(1/log K),
which is what the dense wall needs: `permanent/barrier.md` Lemma 2.1 and `permanent-attack.md` (P) give time 2^{e_K U + 2gP/K}
with U = Θ(n log n) for dense permutation witnesses and admissible node load P = o(n/K⁷) (K up to n^{1/7−ε}); with e_K =
C(log K)^{−α′} and log K = Θ(log n) the main term is C′n(log n)^{1−α′} = o(n) iff α′ > 1 (Θ(n) with constant ≥ 7C at α′ = 1, not
below Ryser; ≫ n at α′ = 1/2: `ambitious-targets.md` T3).

*Majdoddin's caveat, reconciled.* "Even a success here would be a lever on ρ, i.e. on α′, not a change of the type of decay"
(§4.8, three-or-more-merges paragraph) refers to Prop. 4.1: ρ_C < 1/2 changes α′, the decay stays polylogarithmic, the crossover
lower bound log₂ m* ≥ q(C/bar)^{1/α′} stays exponential in a power of 1/bar; his "open door" paragraph then says *polynomial*
decay needs hyperedge configurations for the different reason of §1.8–1.10, not because of ρ < 1/2. Both are right; neither
contradicts the coordinator's statement, which is about dense-problem asymptotics, where α′ > 1 is the whole game. Numbers: main-
term model with C = 1, q = 2, bar = 3.2·10⁻⁴: log₂ m* ≥ 2·3125^{1/α′} = 6250 (α′ = 1), 320 (α′ = log₂ 3), 112 (α′ = 2); with Theorem
A(a)'s constants (e_ℓ ≤ 0.85((3x₀+6)/log K_ℓ)^{α′}, x₀ ≥ 18, log m ≥ 9 log K) the general-3-SAT estimate moves from ≈ 1.4·10⁶
(α′ = 1) to ≈ 8·10⁴ (α′ = log₂ 3), against ≈ 4·10⁹ at α′ = 1/2 (his 8.6·10⁹ with sharper constants): four orders of magnitude in
the exponent, still astronomical. That is "lever, not type".

### 2.7 Three-merge levels plug into squaring; the AG(2,4) instances are closed by flattenings [R + N]

*The level.* AG(2,q), K = q², q+1 parallel classes of q lines, every edge in exactly one line; three classes as merges (q groups
of size q, pairwise orthogonal), the lines of the other q − 2 classes as configurations — in pairs of parallel lines (closed by
Corollary 2.3.1), as whole classes Δ_q (open), or for q = 4 as translation matchings (closed, below). Under merge k the qC(q,2)
edges of class k are internal, the 2qC(q,2) edges of the other merge classes are raw: ρ_level = 2/(q+1) + ρ_C(q−2)/(q+1) → ρ_C.
The merged instance has q = √K nodes and is homogeneous (two lines of class k are joined by q edges of every other class); with
q = K·polylog(K) and Lemma 8(ii) grouping this is a Theorem A level with ρ_level in place of ρ: **β = 2, α′ = log₂(1/ρ_level)**;
squaring is forced ("orthogonality again forces squaring") and the input floor 2/g of §4.7 does not arise. With rows and columns
only (two merges) and the q − 1 other classes as Δ_q configurations the same holds (for q prime the classes are x + cy = const),
so Δ_q with two merges plugs in as well; the 3×3 level is the case q = 3 with both classes as one configuration.

*T4, the AG(2,4) translation matching* (Majdoddin §4.8). F_4 = {0,1,ω,ω²}; edges {(x,c),(x,c+1)}, x ∈ F_4, c ∈ {0,ω}: 8 edges,
16 nodes, one string each; merges = slopes 0,1,ω (groups y − sx = c); under every merge the edge joins groups c − sx and
c − sx + 1, so C is two bundles of 4 edges on the group pairs {0,1}, {ω,ω²}, and a non-product piece is a K_4-network on the four
groups. Flattening certificate (§8.2 generalised: a term under merge k passes a contraction M iff Σ_{G∈S} n_G ≤ e(S|S^c) for all
S ⊆ P_k, cheapest passing term by LP, certified value max_M min_k d_k(M); for 4 groups the pair cuts enter), exhaustive over 3⁸
orientations [N, `flatcert.out`]: **D = 4 of 8 with three merges and with all four non-vertical slopes: ρ_{T4} ≥ 1/2 for all
pieces** (orientation: all c = 0 edges one way, the c = ω edge of x = 3 reversed: n = (2,−2,2,−2) under every slope, LP value 4).
Majdoddin argued ρ ≥ 1/2 only for products over pairs of strings; with the cost defined, flattenings close it for all pieces.
Core floor there is only 2/8, so this closure is not a core phenomenon.

*Two parallel lines of AG(2,4)*: 8 nodes, 12 edges, merges slopes 0,1,ω; exhaustive over 3¹² orientations with LP caching
[N, `flatcert2.out`]: D = 6 of 12; the core floor gives 1/2 as well (Corollary 2.3.1). For q = 3 flattenings give only 2 of 6.

*Consequence.* On every three-merge configuration with ≤ 16 nodes that has been proposed, three orthogonal merges give exactly
the two-merge floor 1/2. The route "ρ < 1/2 by a third merge" has only the full-class configurations Δ_q left, and they sit in
squaring levels, so it is a lever on α′ only.

---------------------------------------------------------------------------------------------------

## 3. The two-merge instances: the 3×3 level, Δ_3, the prism, the 8-cycle

### 3.1 The 3×3 level and Conjecture 8.1 versus C [R]

Our 3×3 level (`engine2-decorrelated.md` §8) is K_3 × K_3: 9 nodes (r,c), 18 crossing edges, merges rows and columns. A
"row-network of cost c" is exactly a D1 triangle network on the rows, and Conjecture 8.1 (Σ_t 2^{c_t} ≥ N⁹) is ρ ≥ 1/2 on this
configuration (§1.7). It meets three groups of each merge, so it violates (L3): **a hyperedge configuration in Majdoddin's sense,
under two merges** — his open door with p = 2, the terms being non-product groupings across the nine rectangles (Remark 4.5). It
is not C and not a special case of it: C is 6 nodes, 12 strings, 3 merges, ⟨N,N,N⟩^{⊗2}; the level is 9 nodes, 36 strings, 2
merges, ⟨N⁶,N⁶,N⁶⟩ under either merge. Proved there: S ≥ N⁸ (Lean), and 8 is the limit of every flattening argument (§8.2 ILP)
and of every m-party CVZ argument with straddlers (§8.3). Why C closes and the level does not: in C every complement of a group
is a union of other merges' groups and the a-triangle is an agreeing core with half the edges; in the level the largest core has
4 of 18 edges, every column functional on a row-full piece meets straddling legs (§8.3), and the hub profile of §8.6 passes every
test. A proof of Conjecture 8.1 must use that a row network's three cuts come from one bond triple (§8.7).

### 3.2 Δ_3: half of the 3×3 level, and the smallest open instance [R + N]

Each 2×2 subgrid of Z_3² has exactly one anti-diagonal-class edge (r+c = r′+c′) and one diagonal-class edge, so the 18 crossing
edges split as Δ_3^{anti} ∪ Δ_3^{diag}, each a parallel class of AG(2,3) = three disjoint triangles meeting all three rows and all
three columns. Δ_3 (either half): 9 nodes, 9 edges, 18 strings, raw cost 9m under rows and under columns; under either merge it is
⊗ of three ⟨N,N,N⟩'s on the same three groups with the three "alignments" (bijections line → groups). Floors: core 1/3 (one
triangle); flattening world **4 of 9 = 4/9**, exhaustive over 3⁹ orientations with 3 groups per merge (closed form d_k = max_G
|n_G|), the same with the diagonals as a third merge [N, `flatcert4.out`]. Upper bound: raw. The §7.6 exhaustive check of
`engine2-decorrelated.md` covered unions of rectangles (both diagonals), not Δ_3, which takes one diagonal from each rectangle;
so Δ_3 was not among the configurations shown to reach ρ ≥ 1/2. Three things make it the right next target:
(i) **Size:** 18 strings; at N₀ = 2 a piece is a 2¹⁸ tensor, the size of the prism search below (ALS feasible).
(ii) **It plugs in:** the 3×3 level is Δ^{anti} ∪ Δ^{diag}; a piece family on Δ_3 with ρ_Δ < 1/2 gives, by tensoring the two halves,
ρ < 1/2 on the level, and Δ_q classes with two merges tile the AG(2,q) grid level (§2.7), so this is a route to α′ > 1.
(iii) **It is the rectangle-content test:** Majdoddin's conjecture (§4.4, "only min(d,a) bits of a four-cell configuration can be
traded") predicts, extended to hyperedge configurations, no trade at all on Δ_3 (d = 1, a = 0 for every rectangle). Any identity
with ρ_Δ < 1 refutes that extension; the proved floor is 4/9, so the window [4/9, 1] is wide open.
*Finite problem.* ρ_Δ < 1/2 ⟺ pieces with c_row + c_col < 9 log₂ N₀ (uniform q), e.g. (3, 5) bits at N₀ = 2 — note that the
generic cost of a tensor on Δ_3 under the other merge is 2·6 log N₀ = 12 log N₀ > 9 log N₀, so a piece must be *simultaneously*
a cheap row network and a below-raw column network. Search: f_Δ = R + C with R a row network of bonds (2,2,2) whose column
flattening ranks are ≤ 16, 16, 4 (bonds (4,4,2)), and C its image under the transpose (r,c) ↦ (c,r), which maps Δ^{anti} to itself
and rows to columns; alternating least squares with rank projections, N₀ = 2. Any trade at all (ρ_Δ < 1) needs only c_row +
c_col < 18 log₂ N₀: f_Δ = R + C with R row bonds (2,2,2) and C column bonds (2,2,2) (then (3 + 12)/2 + 1 = 8.5 < 9) — the direct
analogue of the prism search of §3.3, not yet run on Δ_3.

### 3.3 The prism: the smallest instance of the constant-growth door [R + N]

Two partitions of six nodes into pairs with no common pair have a 6-cycle as incidence graph and the crossing edges form the prism
K_3 × K_2: nodes A=(1,1), B=(1,2), C=(2,2), D=(2,3), E=(3,3), F=(3,1), edges = different row and column (AC, AD, AE, BD, BE, BF,
CE, CF, DF), rows {AB, CD, EF}, columns {AF, BC, DE}. Every edge is three-cell for (rows, columns); under each merge f_P is a
triangle of 3-edge bundles, ⟨N³,N³,N³⟩, raw 9m. It is the unique minimal level K = 6 → 3 with groups of size 2, so **ρ_P < 1 is the
smallest finite test of a non-rectangle trade**, with the caveat of §1.10 that even a trade here covers only O(gK) edges of a
level. Proved: flattening D_P = 6 of 9, **ρ_P ≥ 2/3** for every identity [N, exhaustive, `flatcert.out`; `flatcert3.py`'s local
search reproduces 6]; core floor 4/9; single edges as configurations give ρ = 1. Searched [N, `prism_als.py`, outputs
`als_d{2,4,8}.out`]: f_P = R + C with R a row network and C a column network, both with bonds (d,d,d), alternating least squares,
validated on the rectangle (finds the App. H identity exactly, 48 of 50 restarts, `rect_als_control.py`) and on the prism itself
at d = 8 (= N³, where R alone represents f_P: residual 7·10⁻¹¹ at the first restart). Results: **d = 2: 40 restarts × 60 sweeps,
minimal relative residual 0.988 (all 40 at 0.99); d = 4: 20 restarts, minimal 0.927 (18 at 0.93, 2 at 0.94).** A solution at
d = 2 would have given per-block cost (3 + 12)/2 + 1 = 8.5 < 9 and a constant-growth trade; R + C captures 1–7% of f_P. Weak
evidence (ALS, N = 2, one bond pattern) for ρ_P = 1, consistent with the rectangle-content picture.

### 3.4 The incidence 8-cycle: the smallest instance with two-cell edges [R + N]

G_1={n₁,n₂}, H_1={n₂,n₃}, G_2={n₃,n₄}, H_2={n₄,n₅}, G_3={n₅,n₆}, H_3={n₆,n₇}, G_4={n₇,n₈}, H_4={n₈,n₁}; crossing edges = the 20
non-consecutive pairs; the 8 at cyclic distance 2 are three-cell, the 12 at distance 3 or 4 are **two-cell**. Under each merge: 4
groups, K_4 networks, raw 20m. Core floor 9/20 (H = {1,2,3,5,6,7}). Flattening certificate by local search [N, `flatcert3.out`,
lower bounds]: ≥ 13 of 20 (ρ ≥ 0.65); two-cell edges alone ≥ 9 of 12; three-cell edges alone ≥ 4 of 8. So flattenings do not
forbid a two-cell trade here (they would need 12 of 12 on the two-cell sub-configuration). By §1.10 this is the first non-trivial
"routing" instance: a trade on n₁n₄ must be routed through n₂, n₃ (or n₅…n₈).

---------------------------------------------------------------------------------------------------

## 4. What is proved impossible, what is not

| statement | status | source |
|---|---|---|
| Two-merge identities on a configuration meeting ≤ 2 groups per merge: ρ ≥ 1/2 | proved | Anthropic App. H; Majdoddin Prop. 4.6 + 4.8; `clique-evaluation.md` §4.3 |
| Configurations with ≤ 3 cells of two merges (≤ 2 groups each) cannot trade at all | proved (quantum functionals) | Lemma 4.11; flattenings insufficient: Example 4.10 |
| Grid algorithms, any pieces: 1/e(K) ≤ log₂ K; the recursion as written: (1 − 8.5·10⁻²²)/log₂ K | proved | Thm 4.13, 4.18, Cor. 4.19 |
| Balanced homogeneous two-merge: 1/e(K) ≤ (log₂ K)³ | proved | Thm 4.12 |
| Four-cell edges ≤ K(c₁c₂+c₁+c₂)/2; three-/four-cell for some pair of p merges ≤ C(p,2)g²K | proved | Prop. 4.9; §1.9 [R] |
| **Core floor: ρ_C ≥ max_H E_cross(H)/E for all pieces, any merges, any cost ≥ D1 cut bound** | proved | Theorem 2.3 [R]; the C case also [S] and [M-argued] |
| **Constant-growth levels need configurations of Ω(log K/log g) nodes** | proved | Prop. 1.10 [R] |
| k-local pieces on C: ρ = 1; pair-factor identities need ≥ N⁶ pieces | proved | Prop. 4.23; `r123_idcut.py`, `r123_escapes_cut.py` |
| **All pieces on C: ρ_C ≥ 1/2**; two lines of AG(2,q), all q: ρ ≥ 1/2 | proved | Cor. 2.3.1 [R], Remark 2.4 [R] |
| Non-local pieces on C beat ρ = 1: 5/6 at N = 2, 3; ρ_C ≤ ρ_x + 1/4 with crossing pieces (0.957 with App. B) | proved construction | [S] `engine3-search.md` §3 |
| **T4 (three or four slope merges), two lines of AG(2,4): ρ ≥ 1/2 for all pieces** | exact computation of a proved certificate | §2.7 [N]; method §8.2 [R] |
| Correlated two-merge decompositions: two rectangles, 3×2 grid (Lean), full levels ρ ≥ 3/8, 3×3 level S ≥ N⁸ (Lean) | proved | `engine2-decorrelated.md` Thm 1, 4, 5, §8.4 |
| No flattening argument certifies > 8 on the 3×3 level; no m-party CVZ argument with straddlers either | proved + exact ILP | §8.2, §8.3 |
| Δ_3: flattening world certifies exactly 4 of 9 (2 or 3 merges); prism exactly 6 of 9; 8-cycle ≥ 13 of 20 | exact / search | §3.2–3.4 [N] |
| Prism: no R + C identity with bonds ≤ 4 at N = 2 | ALS evidence only | §3.3 [N][C] |
| Many/random/adaptive grouping families on a grid level: ρ ≥ 1/2 − O(√(log g)/g) (product pieces) | proved | `engine2-probabilistic.md` Thm A |
| Any number of groupings with product gadget pieces: α′ ≤ 1 | proved under homogeneity/regularity | `engine2-algebraic.md` Thm 7.1, 7.3 |
| App. B shape: ρ_B ≥ 2/3 (concave profile), ≥ 1/√2 (power profiles) | proved / argued | Prop. 4.24; `pieces.md` §3 |
| Three-cut size game at K = 4 never below N³ | computed on a parameter grid, conditional on rk(BC\|AD) ≤ rk(AB\|CD)·rk(AC\|BD) [8, Thm 9] as read by Majdoddin; `r123_laser_threecut_lb.py` assumes the rank triangle inequality explicitly; [S] checked it holds for every four-leg piece used | Prop. 4.22 + §4.6 |
| Rectangle-content conjecture (only min(d,a) bits trade), K4 minus a diagonal, 4-cycle with over-full pieces | open | §4.4, §4.8, Open Problem 3 |

**Not ruled out.** (1) ρ < 1/2 on Δ_3 (window [4/9, 1]), on the 3×3 level ([4/9, 11/12]) and on the Δ_q classes (core 1/q). (2) Any
trade on three-cell edges in configurations meeting ≥ 3 groups (prism, window [2/3, 1]). (3) Any trade on two-cell edges (8-cycle,
[0.65, 1] by search). (4) The rectangle window ρ ∈ [1/2, 1/√2] (Open Problem 1). (5) Anything outside Signed Network Sums.

---------------------------------------------------------------------------------------------------

## 5. Candidate constructions, with success criteria and what to compute

Ordering after §2–3: (5.1)–(5.3) aim at α′ > 1 and must be aimed at Δ_3, the 3×3 level or Δ_q (C and the AG(2,4) instances are
closed); (5.4)–(5.5) at the constant-growth door. "Success" always means the finite criterion of §1.7 at some N₀.

### 5.1 Composition algebras beyond octonions; Hurwitz–Radon across groupings [C]

The eight-square identity is L_v^⊤L_x + L_x^⊤L_v = 2[x=v]·Id for the octonion left-multiplications (App. H): a multiple of
[x=v]·Id as a combination of the two orders of a product, each passing through a space of dimension 8 = N. *Pfister / 16
squares:* Pfister's 2ⁿ-square identities have c_k **rational**, not bilinear, in (a,b) for 2ⁿ ≥ 16 (Hurwitz: bilinear only for
1,2,4,8). Non-bilinearity is fatal for pieces: App. H's (71)⇔(72) equates coefficients of a_x a_v b_y b_u, which needs bilinear
z_k; a rational identity gives no tensor decomposition of the crossing. Bilinear [N,N,s] formulas with s = N^{1+o(1)} would be
ideal pieces (`pieces.md` (2.2)); App. B already gives s = N^{√2+o(1)} < Hrubeš's N^{1.62}, so pieces are ahead of the sum-of-
squares literature. *Three groupings:* on C a "three-order" identity cannot beat 1/2 (Cor. 2.3.1); on Δ_3 or Δ_q the analogue
of (74) is a sum of networks cheap under rows plus networks cheap under columns, and §3.2 states the exact finite target. A
structural observation that constrains all symmetric two-piece ansätze [R]: with R a row network of cost a and the generic
other-direction cost 2L log N₀ (L strings per group), the type-grouped count is (a + 2L log N₀)/2 + 1 < E log N₀/2 ⟺ a <
(E − 2L) log N₀ − 2, and E ≤ 2L on every configuration here (rectangle: E = 2, L = 2; Δ_3: 9, 6; 3×3 level: 18, 9; prism: 9, 6), so
**a two-piece identity shows ρ < 1/2 by the simple count only if the pieces are below raw in the other direction too**; the gain
must come from double-cheap pieces or from App. B-type many-piece families with correlated types.

### 5.2 Clifford / Jordan algebras, group algebras [C]

F = SWAP on ℂ^N⊗ℂ^N; a piece T has c_row = log rank T, c_col = log OSR T (`pieces.md` §1). Candidates: left/right regular
representations L_g, R_h of a nonabelian group G (Q₈, S₃, S₄) on ℂ[G], which commute — the structure App. H exploits ("directions
are orders"). Compute: the exact optimum of the span{L_g⊗R_h} ∪ span{R_g⊗L_h} class by the generic-flag/quantile method of
`pieces.md` §4 (needs the relative position of two flags of ℂ[G], feasible for |G| ≤ 24). Success: ρ < 1/√2 on the rectangle
(Open Problem 1, a lever inside RM_2). Known failure modes: commutative classes stay ≥ 0.80. On Δ_3 the Z_3-shifts are the three
alignments; a Z_3×Z_3-equivariant ansatz for Δ_3's pieces reduces the search space by a factor 9 and is the natural first
structured search.

### 5.3 Border / degeneration identities with interpolation [R on the barrier side]

A border identity Σ_i π_i(ε) = d·f_C + ε·(junk), recovered by interpolation over poly(degree) values of ε, is admissible in (L2) if
the degree is poly(λ). All lower bounds here survive it: flattening ranks are lower semicontinuous (border rank ≥ flattening
rank), the §8.2 certificates are flattening ranks of node-locally processed tensors, the core floor uses CVZ functionals, which
are defined on the asymptotic spectrum and monotone under degeneration [K], and the D1 cut bound is a flattening. **Degeneration
opens nothing at the barriers**; it can only help a construction reach a cost the barriers allow (e.g. a border hub ansatz on
Δ_3 or the 3×3 level).

### 5.4 Randomised / probabilistic groupings, and the prism search [R + N]

`engine2-probabilistic.md` Theorem A (covering bound) shows random or adaptive choice among partitions does not move the
product-piece floor; the core floor is likewise a statement about the identity, not about the choice of merge, and holds for
every merge simultaneously, so randomisation gives no escape at the configuration level. The prism search of §3.3 is the
computational content of this item: negative at N = 2 for bonds 2 and 4.

### 5.5 The two-cell instance: what to compute on the 8-cycle [R formulation]

(a) The exact flattening certificate D₈ (the search gives ≥ 13 of 20): generalise `diff.py` to two merges with 4 groups (3²⁰
orientations are too many for brute force; a MILP over orientations with the 4-group LP's dual vertices as a disjunction). If
D₈ = 20, flattenings would prove "no two-cell trade" on this instance, the first non-counting obstruction to polynomial decay.
(b) An identity search on the 12 two-cell edges alone (24 strings, 2²⁴ entries at N = 2, ALS with bonds 2): success = any
identity with min_q max_i⟨q,c(i)⟩ + log₂ T < 12 — the first trade not routed through a rectangle. (c) The conceptual step: a
Lemma 4.11-type theorem "an edge whose four groups are pairwise non-incident pays m under both merges in every identity"; with
§1.9–1.10 it would close the polynomial-decay door for rewrite-and-merge with constant-size groups. §8.3 shows what such a proof
cannot be (node-locally processed flattenings, m-party functionals with straddlers).

### 5.6 Computations done for this note [N]

| instance | nodes / edges / strings | merges | flattening certificate D (of E) | core floor | other |
|---|---|---|---|---|---|
| rectangle (sanity) | 4 / 2 / 4 | 2 | 1 of 2 | 1/2 | |
| C = two lines of AG(2,3) | 6 / 6 / 12 | 3 | 2 of 6 (exhaustive 3⁶) | **3 of 6** | ρ ≥ 1/2 by Cor. 2.3.1 / Rem. 2.4 |
| two lines of AG(2,4) | 8 / 12 / 24 | 3 | 6 of 12 (exhaustive 3¹²) | 6 of 12 | |
| T4 translation matching | 16 / 8 / 16 | 3 and 4 | 4 of 8 (exhaustive 3⁸) | 2 of 8 | |
| Δ_3 (three transversal triangles) | 9 / 9 / 18 | 2 and 3 | **4 of 9** (exhaustive 3⁹) | 3 of 9 | smallest open instance |
| prism | 6 / 9 / 18 | 2 | 6 of 9 (exhaustive 3⁹) | 4 of 9 | ALS N = 2: d = 2 residual 0.988 (40 restarts), d = 4 0.927 (20), d = 8 exact |
| incidence 8-cycle | 8 / 20 / 40 | 2 | ≥ 13 of 20 (search) | 9 of 20 | two-cell edges only ≥ 9 of 12; three-cell only ≥ 4 of 8 |
| 3×3 level (comparison) | 9 / 18 / 36 | 2 | 8 of 18 (exact ILP, §8.2) | 4 of 18 | Conjecture 8.1 |

All certificates: §8.2 method, single contraction M (oriented edge-disjoint paths), per-term best labelling, LP for the cheapest
term passing all cut inequalities of M; exact where exhaustive, lower bounds where searched. Core floors: exhaustive over all node
subsets H with the join computed by union-find (`flatcert4.py`).

---------------------------------------------------------------------------------------------------

## 6. Where this leaves the programme

1. **For α′ > 1 (the dense wall):** the open configurations are Δ_3 (window [4/9, 1], 18 strings), the 3×3 level ([4/9, 11/12])
   and the Δ_q classes (core 1/q); C, T4 and all two-lines configurations are closed at 1/2. Three merges did not help on any
   small instance. The finite problem is the Δ_3 search of §3.2 (any trade at all refutes the hyperedge rectangle-content
   conjecture; c_row + c_col < 9 log N₀ gives α′ > 1 through the AG(2,q) levels), and a proof must use bond-triple information.
2. **For polynomial decay:** configurations of Ω(log K/log g) nodes are forced (Prop. 1.10) and the trade must be on two-cell
   edges routed along the incidence graph; the smallest instance is the 8-cycle (§3.4, §5.5); the prism (three-cell) shows no
   identity at N = 2 and is certified at 2/3.
3. **Inside RM_2:** the rectangle window ρ ∈ [1/2, 1/√2] (Open Problem 1), worth α′ from 1/2 to 1 at most.
4. Majdoddin's named door is shut at its small instances: Corollary 2.3.1 and §2.7 answer his Open Problem 4 (three or more
   merges on orthogonal designs) and the non-product part of Open Problem 5 for C, T4 and all two-lines configurations; his
   "halves" claim is a theorem (the core floor); his Open Problem 1 and our Conjecture 8.1 remain, joined by Δ_3.
