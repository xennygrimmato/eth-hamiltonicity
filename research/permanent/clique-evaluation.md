# The K-clique network evaluation problem: direct attacks on e_K

29 Oct 2026. Companion to `rate.md` (where the 1/√log comes from), `pieces.md` (the pieces as a
rank problem) and `permanent-attack.md` §6 (why the dense permanent needs e_K·log K → 0).
Scripts: `scripts/clique_bounds.py` (exact fractions; outputs in `clique_bounds.out`) and
`scripts/clique_fmm_terms.py` (exact integer check of the FMM-inside-a-level identity). Tags
**[R]** rigorous, **[N]** numerical, **[C]** heuristic.

## 0. Summary

* **Normalisation.** A (K,λ)-clique costs 2^{e_K·K²λ}. Brute force over the 2^{λK(K−1)/2} labellings is
  e = (K−1)/(2K) → **1/2** (Anthropic's e_0 = 1/2 is brute force; "2^U" in the brief is 2^{U/2}, U counts both
  ends). Query lower bound e_K ≥ (K−1)/K².
* **Direct methods are stuck at a constant.** Every algorithm that stores intermediate tensors (any
  contraction order, any algorithm per contraction, FMM included) has e_K ≥ 2/9 − 1/K [R, §4.2]; FMM reaches
  e_K ≤ ω/9 + O(1/K) ≈ 0.264 for every K ≥ 3, and e_3 = ω/9 exactly (it *is* matrix multiplication). Fourier /
  Walsh / polynomial-method rewritings map the problem to itself (the equality tensor is GL(D)-invariant),
  §4.4. Anthropic's recursion is the only known thing with e_K → 0, and at practical K it loses to FMM: its
  e_ℓ drops below ω/9 only at level 3 (lg K ≈ 420).
* **Coordinator's hunch (MM as the per-level engine): no, and the reason is exact [R, §3].** A level of
  Theorem A is "Σ over ι of a g-node network with ρ·N bits"; its cost is (#ι)·2^{e·ρN}, and #ι = |I|^{|R|}
  with |R| = N/(4λ) rectangles, so a decomposition with |I| = 2^{tλ} terms per rectangle gives
  e' = ρe + t/4 and the fixed point e* = t/(4(1−ρ)). Pieces are the regime t = O(log λ/λ) (poly many terms,
  each with row-rank·column-rank 2^{4ρλ}); FMM is the opposite regime t = Θ(1) (rank-one terms, i.e. ρ = 0,
  but 2^{ωλ'} of them). Driving a level by FMM gives e_{3g} ≤ (ω + e_g)/9 (verified identity, §3.2), fixed
  point ω/8 ≈ 0.30, worse than using FMM once (ω/9). The step of Theorem A that breaks is the count of ι in
  display (44) of the paper (`GeneralPieces.Rec.Chain`, `|I| ≤ (2λ)^c` in Definition 7(c)): the term count
  enters additively, the bit saving multiplicatively, and only the latter compounds. What the pieces
  provide and FMM does not: *few* terms each cheap across *two different* groupings of the same nodes
  (row cut and column cut); a triangle has one grouping and FMM has 2^{Ω(λ)} terms. The ω/3 "saving" of
  FMM at K = 3 is a saving in total work with zero bits left over, not a reduction of shared bits.
* **Lower bounds [R].** (i) Query: (K−1)/K², tight for query count. (ii) Contraction trees: 2/9 − 1/K.
  (iii) Sum-of-products-of-linear-forms (tensor rank, the Christandl–Vrana–Zuiddam setting): 1/4, from the
  flattening rank 2^{K²λ/4}; general circuits beat it (Anthropic), so asymptotic rank of the clique graph tensor
  is not e_K. (iv) Any Anthropic-type recursion (two groupings, min over them, 2^{o(λ)} pieces per rectangle):
  ρ ≥ 1/2 − o(1) (the mixed-ι argument, §4.3), hence α' ≤ 1 and **e_K ≥ c/log K**, so e_K log K → 0 is impossible
  in the framework *even with subexponentially many pieces*; with 2^{Ω(λ)} pieces the fixed point is positive.
* **Conditional barriers [R].** The dual hypergraph H_K (K relations of arity K−1, every two sharing one
  variable) has submodular width Θ(K) (§4.5); Marx's theorem then says ETH ⇒ e_K ≥ Ω(subw^{1/4}/K) = Ω(K^{−3/4}),
  and a direct CNF embedding says ETH ⇒ inf_K e_K > 0. Both are vacuous here: e_K → 0 is Anthropic's theorem,
  and it refutes ETH exactly through the second implication. No standard fine-grained hypothesis (ETH, SETH,
  #ETH, k-clique, OV, APSP, 3SUM, ω > 2) says anything about the *rate* at which e_K → 0: every reduction into
  a (K,λ)-clique pays the table size 2^{(K−1)λ}, which already exceeds the solution space of any fixed-arity
  hypothesis problem, and the rate question lives inside "subexponential", where no hypothesis exists.
* **Verdict.** e_K·log K → 0 is not excluded by anything, but (a) the only known mechanism for e_K → 0 is
  capped at e_K = Θ(1/log K) at best (needs ρ → 1/2, itself open and SOS-hard, `pieces.md` (2.2)), and
  Θ(1/log K) is *exactly* the boundary the dense permanent needs to cross (e_K log K → 0, not O(1)); (b) direct
  methods are stuck at constants; (c) no conditional evidence either way exists or can exist from standard
  hypotheses. I rate e_K = o(1/log K) as implausible with current ideas, and the dense permanent through this
  route as closed unless a non-vertex-algebra "two-order" structure appears (rate.md §3.1).

## 1. Problem and reformulations [R]

**Problem C(K,λ).** Nodes a ∈ [K]; every unordered pair {a,b} carries a label x_{ab} ∈ {0,1}^λ; node a has an
integer table T_a : ({0,1}^λ)^{K−1} → ℤ (|T_a| < 2^B), given by query access. Compute
Z = Σ_{x ∈ ({0,1}^λ)^{E}} Π_a T_a(x|_{δ(a)}), E = K(K−1)/2. U = K(K−1)λ (both ends), cost written 2^{e_K K²λ}·poly.
In Anthropic's Definition 4 the admissible operations are poly-time steps plus unit-cost table queries.
Non-uniform u_{ab} reduce to the uniform case by Lemma 8 (regrouping), losslessly in U.

Equivalent forms (all exact, D = 2^λ):

1. **Holant on K_K.** Edge variables over domain D, vertex signatures T_a of arity K−1 (asymmetric). The
   holographic transformations M ⊗ M^{−T} on each edge (M ∈ GL(D)) leave Z invariant.
2. **Sum over symmetric matrices.** Z = Σ_{X ∈ [D]^{K×K}, X = X^T, zero diagonal} Π_a T_a(X_{a·}). For λ = 1: a sum
   over all graphs on [K] of a product of arbitrary functions of the neighbourhoods, Σ_H Π_a T_a(N_H(a)).
   (Anthropic: 2^{O(K²/√log K)} for this; brute force 2^{K²/2}; degree-sequence counting, T_a = [|N(a)| = d_a],
   is 2^{O(K log K)} by the obvious DP — symmetric tables are much easier than general ones.)
3. **Multilinear form of the clique graph tensor.** Z = ⟨⊗_a T_a, 𝒯_K⟩ with 𝒯_K = ⊗_{e∈E} I_D regrouped as a
   K-party tensor, party a holding its K−1 bond legs. This is the complete-graph tensor T(K_K) of
   Christandl–Vrana–Zuiddam (CCC 2016 / Comput. Complexity 2019) with bond dimension D; for K = 3 it is ⟨D,D,D⟩,
   the matrix multiplication tensor. e_K is the *arithmetic circuit* exponent of this multilinear form, not its
   tensor rank exponent (§4.2).
4. **CSP(H_K).** Variables = E, domain D; constraints = K relations of arity K−1 (one per node, given as
   tables of size D^{K−1}); constraint hypergraph H_K = {δ(a)}: any two hyperedges meet in exactly one
   variable. Counting weighted solutions of CSP(H_K) with input size ‖I‖ = K·D^{K−1}, in time ‖I‖^{e_K K²/(K−1)}.
5. **K-partite clique counting** on parts V_a = [D]^{K−1} with the "agree on the shared label" graph. Parts
   have N = D^{K−1} vertices, Nešetřil–Poljak gives N^{ωK/3} = 2^{(ω/3)(K−1)Kλ}, e ≈ ω/3 > 1/2: worse than brute
   force. The clique structure is far too special for generic clique algorithms.

## 2. Upper bounds by method [R unless marked]

Units: e_K, i.e. exponent / (K²λ). Exact values in `clique_bounds.out`.

| method | e_K | notes |
|---|---|---|
| brute force | (K−1)/(2K) → 1/2 | Anthropic's base case e_0 = 1/2 |
| query lower bound | (K−1)/K² → 1/K | every entry influences Z (set all others to 1) |
| sequential contraction (treewidth) | max_j [(j+1)(K−j−1)+j]/K² = 1/4 + 1/(2K) − 1/K² | intermediate after j nodes has j(K−j) open edges |
| 3 groups + FMM (trace of three 2^{s²λ}-dim matrices) | max(2/9 + 1/(3K), ω/9) → **ω/9 ≈ 0.2635** | forming a group tensor costs ≤ 2K²/9 + K/3 by sequential contraction inside the group; K ≡ 0 mod 3 is exact, other K: see table in `.out`; for K = 3: e_3 = ω/9 exactly (trace(T_1T_2T_3) *is* ⟨D,D,D⟩, and MM ⇔ its trilinear form up to constants) |
| K = 4, rectangular MM | ω(1,1,½)/8 ≈ 0.256 (1/4 if ω = 2) | T_{12}(ac,ad,bc,bd) = Σ_{ab}T_1T_2 is a (D²×D)(D×D²) product; then an inner product of two D⁴-vectors; query LB 3/16 |
| grouping monotonicity | e_K ≤ e_{K'} + O(1/K) for K' ≤ K | Lemma 1 is lossless in U; forming group tensors costs ≤ (K'−1)/K'² + O(1/K) ≤ e_{K'} |
| any contraction tree, any per-step algorithm | ≥ 2/9 − 1/K (lower bound, §4.2) | so ω/9 is optimal in this class iff ω = 2 |
| Anthropic Theorem A (ρ = 1/√2, x₀ = 18) | 0.5, 0.400, 0.302, 0.221, 0.159, 0.113 at lg K = 18, 72, 186, 420, 894, 1848 | e_ℓ ≈ 0.85((3x₀+6)/lg K)^{1/2}; below ω/9 only from level 3 (lg K ≈ 420) |
| hybrid: Theorem A with base e_0 = ω/9 (§5) | 0.527 × the above at every level | constant factor; α' unchanged |
| Fourier / Walsh / character sums / polynomial method | = brute force | self-dual, §4.4 |
| K-partite clique counting | ω(K−1)/(3K) ≈ 0.79 | worse than brute force |

Side remark [R]: the "Christandl–Vrana–Zuiddam exponent per edge" of T(K_k) (asymptotic tensor rank) is
≥ k/(2(k−1)) → 1/2 by flattening, is 0.79 for k = 3 (= ω/3) and ≤ 0.77 for k ≥ 4, and they ask whether it can go
below 2/3. In our units exponent-per-edge p corresponds to e = p(K−1)/(2K), so their lower bound is e ≥ 1/4 and
their question is "e < 1/3". Circuits already give e ≤ ω/9 ≈ 0.264 < 1/3 for all K, and Anthropic gives e → 0:
tensor rank and circuit complexity of this multilinear form are genuinely different (a rank-1 term is a
product of K linear forms; a circuit may multiply, sum, and multiply again, as in forming T_{12} then
contracting). So CVZ bounds neither upper- nor lower-bound e_K.

## 3. Matrix multiplication versus the pieces (the coordinator's question) [R]

### 3.1 What one level of Theorem A is, as accounting

A (g²,λ)-clique has N = g⁴λ bits (both ends); |R| ≈ g⁴/4 = N/(4λ) rectangles (pairs of crossing edges), each
carrying the 4-leg tensor F(x,y,u,v) = [x=v][y=u] (4λ bits, both ends). Write F = Σ_{s∈I} A_s. Expanding
Π_q Σ_s A_s gives |I|^{|R|} terms ι; term ι is a g-node network two ways (rows / columns) with
U_row(ι) = 2Σ_q c^row_{ι(q)} + O(N/g), U_col(ι) = 2Σ_q c^col_{ι(q)} + O(N/g); the cheaper is evaluated recursively:

    cost ≈ |I|^{|R|} · max_ι 2^{e · min(U_row(ι), U_col(ι))} ⇒ e' ≤ ρ e + log₂|I|/(4λ) + O(1/g),   ρ := max_ι min(...)/N.

If every piece has c^row_s + c^col_s ≤ 4ρλ then min ≤ average gives this ρ. The two summands behave
differently under iteration: the first is multiplicative (compounds to ρ^ℓ), the second additive. Fixed point
of e' = ρe + t/4 (|I| = 2^{tλ}) is **e* = t/(4(1−ρ))** (`clique_bounds.out` (4)). Hence:

* e → 0 requires t_ℓ → 0 along the levels: |I| = 2^{o(λ)} pieces per rectangle. (Polynomially many is what
  Definition 7(c) demands; rate.md §3.1 shows 2^{λ^{1−δ}} would also do since λ grows along the levels.)
* With |I| = 2^{o(λ)} the rate is α' = log₂(1/ρ) and ρ ≥ 1/2 − o(1) (§4.3). So α' ≤ 1 for every recursion of
  this shape, regardless of the algebra used to build the pieces.

### 3.2 What FMM gives when inserted into a level

Take K = 3g nodes in three groups G_1,G_2,G_3 and D' = D^{g²}. Z = trace(M_1M_2M_3) with M_1[p,q] =
Σ_{internal G_1} Π_{a∈G_1} T_a, p = labels on G_1–G_3 edges, q = labels on G_1–G_2 edges, etc. A rank
decomposition ⟨D',D',D'⟩ = Σ_{r≤R'} ℓ_r ⊗ m_r ⊗ n_r gives Z = Σ_r ℓ_r(M_1) m_r(M_2) n_r(M_3). To evaluate ℓ_r(M_1)
*without forming M_1* (forming costs 2^{2g²λ·...} = e ≥ 2/9 by itself) the functional must respect the network:
use ⟨D',D',D'⟩ = ⟨D,D,D⟩^{⊗g²} with the g² tensor factors indexed by the triangles (a, b, L(a,b)) of a Latin
square L on [g] (these triangles partition the 3g² cross edges). A rank-R decomposition of ⟨D,D,D⟩ then gives

    Z = Σ_{r ∈ [R]^{g×g}} Z_1(r) · Z_2(r) · Z_3(r),

where Z_1(r) is the value of the (g,λ)-clique on G_1 whose node a has its table modified by row a of r
(T'_a = Σ_{cross labels} T_a Π_b ℓ_{r_{ab}}(x_{a,L(a,b)}, x_{ab})), Z_2(r) uses column b of r at node b, Z_3(r)
uses the fibre L^{−1}(c) at node c. `clique_fmm_terms.py` checks this identity exactly (g = 2, D = 2, random
integer tables, trivial rank-D³ decomposition; PASS). Reading it as a level:

* number of terms R^{g²} = 2^{ω g²λ} — exponential in the bits, *this is the whole cost of FMM*;
* each term: three (g,λ)-cliques with zero bits between groups — ρ = 1/3 on the cross bits, zero on nothing
  else; the node count drops by 3, not to √K.

So e_{3g}·9g²λ ≤ ωg²λ + 3·e_g·g²λ, i.e. **e_{3g} ≤ (ω + e_g)/9**, fixed point ω/8 ≈ 0.296, worse than forming the
M_i explicitly and multiplying once (ω/9). Repeating with K → K/3 adds a geometric series of ω/9 terms. In the
accounting of §3.1 this is the point (t, ρ) = (Θ(1), 0): maximal additive term, no compounding.

The same holds for the rectangle itself: F = [x=v][y=u] has row flattening rank D², so any decomposition into
terms of row-rank ≤ 2^{c} needs ≥ 2^{2λ−c} terms; rank-one (FMM-style) terms need 2^{2λ}, i.e. t = 2, e* = 1/2:
brute force. F is not a matrix-multiplication tensor, so there is no "ω" to gain on it anyway: the MM tensor is
the *triangle*, and the level structure of Theorem A has no triangles, only rectangles (two crossing edges of a
2×2 block of the grid).

### 3.3 What the pieces provide that FMM does not

The pieces are a decomposition of F into poly(λ) terms A_s such that *each* term is cheap across *two* cuts
simultaneously — rank(A_s) (row cut (xy|uv)) times operator-Schmidt rank (column cut (xu|yv)) is ≤ 2^{4ρλ}
with ρ = 1/√2 instead of F's own 2^{4λ} (`pieces.md` §1). The algorithmic use is not "split a node's table
across a cut" (a single table is never split; FMM's bilinear rank is also not used to split tables) but:
choose, per term ι, *which of two groupings* of the g² nodes into g supernodes to use, so that the expensive
side of every piece is averaged away. Three ingredients are needed and FMM supplies none of them:

1. few terms (|I| = 2^{o(λ)}): FMM has 2^{Ω(λ)};
2. two different groupings of the same node set in which every cross pair is crossing in both (the g×g
   grid; §3.4 of rate.md shows this forces K' ≥ K²): a 3-group/triangle structure has one grouping;
3. per-term cost below the identity's on *both* cuts at once with sum < 4λ: the bilinear-rank structure of
   FMM is about a *third* cut (the partial transpose (xv|yu), where F has rank 1 and which plays no role).

So (a): no — an MM-style saving cannot replace or supplement the pieces as a per-level engine; FMM enters only
as a base case or at the bottom (constant factors, §5). (b): the step that breaks is the term count,
display (44) of the paper / `GeneralPieces.Rec.Chain.total_eq_min` summed over ι with |I| ≤ (2λ)^c
(`PiecesCounted.Data.Is.card`): with |I| = 2^{Ω(λ)} the sum over ι is 2^{Ω(N)} by itself. Even granting ω = 2,
"2/3 per level" is not a ρ: FMM at ω = 2 is (t, ρ) = (2, 0) on the triangle, fixed point 2/9, which is the
contraction-tree bound of §4.2 and not zero.

## 4. Lower bounds and barriers

### 4.1 Query bound [R]
Z depends on every table entry (fix all other entries to 1: ∂Z/∂T_a(y) = D^{E−(K−1)} ≠ 0), so every algorithm
reads K·2^{(K−1)λ} entries: e_K ≥ (K−1)/K². Tight for query complexity (read everything, compute for free). Any
better unconditional bound must count operations, i.e. is an arithmetic-circuit lower bound for the
degree-K set-multilinear form of §1.3 with K·D^{K−1} inputs and D^E monomials — beyond current techniques in
general models (cf. the K = 3 case, where it is the MM exponent).

### 4.2 Contraction trees [R]
An algorithm that follows a contraction tree (each internal node S ⊂ [K] materialises the tensor T_S with
|S|(K−|S|) open legs, by any algorithm) needs 2^{λ max_S |S|(K−|S|)} space. Every binary tree on K leaves has an
internal node with |S| ∈ [K/3, 2K/3] (descend into the larger child while its leaf count exceeds 2K/3), and
s(K−s) ≥ 2K²/9 − O(K) there, so **e ≥ 2/9 − 1/K** (DP check for K < 60 in `clique_bounds.out`). The 3-group
FMM algorithm attains ω/9 + O(1/K), so in this class the exponent is 2/9 iff ω = 2. Anthropic's recursion is not
of this form: it never materialises a tensor with Θ(K²) open legs; it materialises exponentially many
smaller networks instead.

### 4.3 Any "min over two groupings" recursion has ρ ≥ 1/2, hence α' ≤ 1 [R]
Let F = Σ_{s∈I} A_s with |I| = 2^{o(λ)}, c^row_s = log₂ rank_{(xy|uv)}A_s, c^col_s = log₂ rank_{(xu|yv)}A_s.
Subadditivity: 2^{2λ} = rank_row F ≤ Σ_s 2^{c^row_s}, so some s_r has c^row_{s_r} ≥ 2λ − o(λ); likewise some s_c has
c^col_{s_c} ≥ 2λ − o(λ). Take ι using s_r on half the rectangles and s_c on the other half:
U_row(ι) ≥ |R|(2λ + c^row_{s_c}) − o, U_col(ι) ≥ |R|(c^col_{s_r} + 2λ) − o, so min(U_row,U_col) ≥ 2λ|R| − o(λ|R|) =
(1/2 − o(1))N. Since the cost is dominated by the worst ι (the term count being 2^{o(N)}), ρ ≥ 1/2 − o(1) for
the level and e_{ℓ+1} ≥ (1/2 − o(1))e_ℓ. With K_{ℓ+1} ≥ K_ℓ² (forced, rate.md §3.4) this is e_K ≥ c/log K for
the recursion, for any pieces, any algebra, and any subexponential term count. (`pieces.md` (2.1) is the
same bound in rank·OSR language; this version shows it is the *schedule*, not the pieces, that is capped.)
Consequence: **e_K log K → 0 is unreachable by any recursion of Theorem A's shape**; the dense permanent
needs a different algorithm altogether, not better pieces.

### 4.4 Transform-invariance [R]
For any invertible M_e per edge, replacing T_a by its partial transform with M_e on leg e and T_b with M_e^{−T}
on the same leg leaves Z unchanged (I = M^T M^{−T}); the Walsh–Hadamard transform on all legs sends
Σ_{X sym} Π T_a(X_a) to D^{−E}Σ_{Ξ sym} Π T̂_a(Ξ_a) (the symmetric-matrix constraint is self-dual). The polynomial
expansion of [X=X^T] over F_D (Π(1 − (X_ab − X_ba)^{D−1})) likewise yields a clique network over alphabet D+1 in
the moments of the T_a. Low-degree *approximation* of the equality is unusable (exact sum of 2^{Ω(U)} signed terms,
identity matrix has full rank over every field; rate.md §3.5). No transform changes e_K.

### 4.5 Conditional barriers: what ETH would say, and why it says nothing here [R]
*Submodular width of H_K.* H_K has vertex set E and hyperedges δ(a). Upper: fhw(H_K) ≤ K/2 (path decomposition
with bags B_j = {ab : a ≤ j ≤ b}, covered by stars 1..j). Lower: the modular function f(X) = |X|/(K−1) is
edge-dominated, so subw(H_K) ≥ (tw(L(K_K)) + 1)/(K−1) where L(K_K) is the line graph. A balanced separator S'
of L(K_K) with |S'| ≤ E/10 would leave two groups of components with disjoint vertex supports V_A, V_B of sizes
≥ 0.47K and 0.42K, and every V_A–V_B edge lies in S', giving |S'| ≥ 0.19K² > E/10; so tw(L(K_K)) ≥ K²/20 − 1 and
**subw(H_K) = Θ(K)**. Marx (JACM 2013, Thm 1.4 quantitative form): ETH ⇒ no f(H)·‖I‖^{o(subw(H)^{1/4})}
algorithm for CSP(H), i.e. ETH ⇒ e_K ≥ Ω(K^{1/4}/K) = Ω(K^{−3/4}). (The log-loss version ‖I‖^{o(tw/log tw)} is for
binary CSPs and does not apply.)
*Direct embedding.* A 3-CNF with n variables and bounded occurrence embeds in a (K,λ)-clique with U = O(n)
and P = O(n/K) (this is Anthropic's Lemma 1 route), so ETH ⇒ inf_K e_K > 0. Since e_K → 0 is a theorem, ETH is
false and both statements are empty; #ETH and SETH fall with it. The remaining standard hypotheses (ω > 2,
k-clique, hyperclique, OV, APSP, 3SUM) cannot bound e_K: any reduction into C(K,λ) must build tables of size
2^{(K−1)λ} = ‖I‖/K, which is already at least the brute-force cost of every fixed-arity hypothesis problem with
≤ (K−1)λ bits of witness (clique, hyperclique, OV encodings all land at e ≥ 1/K, the query bound). So **no
standard hypothesis can speak to the rate** 1/√log K vs 1/log K vs o(1/log K); a hypothesis that could would
have to be of the form "problem X needs 2^{Ω(n/log n)}", which does not exist in the literature.
Conversely, e_K = o(1/log K) gives (via `permanent-attack.md` §3) the dense permanent, dense #HC and ATSP in
2^{o(n)}; none of these is believed impossible in a post-ETH world, so no barrier in that direction either.

## 5. Hybrid: Theorem A with an FMM base case [N]
Replacing e_0 = 1/2 by e_0 = ω/9 = 0.2635 at K_0 = 2^{18} and running the actual recurrence
e_{ℓ+1} = (ρ + 3·2^{−ℓ−5})e_ℓ + 3/K_ℓ (`clique_bounds.out` (3)) multiplies e_ℓ by 0.527 at every level (the +3/K_ℓ
terms are negligible); α' = 1/2 is unchanged. For the dense permanent (Laplace network, exponent
≈ 16·e_K·n·lg K): e_ℓ·lg K_ℓ increases with ℓ in both versions (9.0, 28.8, 56.2, … vs 4.7, 15.2, 29.6, …), so the
best level is level 0 and the exponent improves from ≈ 147n to ≈ 76n — still far above Ryser's n. Starting
the recursion at a later level with e = ω/9 gains less (the recursion's own e_1 = 0.354 is already close).
The base case only ever matters by a constant.

## 6. Verdict on e_K·log K → 0
Not plausible with any known or sketched mechanism. (1) Direct methods (contraction, FMM, transforms) are
constant-bounded (≥ 2/9 for everything that stores intermediates). (2) The only mechanism with e_K → 0, the
two-grouping recursion, is capped at α' ≤ 1 by the schedule (§4.3), so it can at best reach e_K = Θ(1/log K)
— which gives e_K log K → const, not 0, and even that needs ρ → 1/2, equivalent to near-linear
sum-of-squares formulas (`pieces.md`). (3) Matrix multiplication cannot be substituted for the pieces (§3). (4) No
standard hypothesis bears on the rate (§4.5). What would change the picture: a per-level step with
K_{ℓ+1} = K_ℓ^{β}, β < 2, at bit saving ρ_β < 1/β (rate.md §3.3–3.4 rule this out for grid-type steps), or a
genuinely new exact identity for the symmetric-matrix sum of §1.2.
