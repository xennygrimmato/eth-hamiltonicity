# The engine rate, algebraic side: eight mechanisms, one new cap, one meta-barrier

4 Nov 2026. Builds on `permanent/clique-evaluation.md` (problem C(K,λ), §4.3 cap), `permanent/rate.md`,
`permanent/rho-lower-bound.md`, `permanent/sparse-fock.md`, `permanent/parity-barrier.md`, `anthropic-api.md`,
`tutte-plane.md` (the ceiling) and `permanent/permanent-attack.md` §3/§6. Scripts: `scripts/engine2_*.py`, with
outputs in `scripts/engine2_*.out`. All checks use exact integers or Fractions; every script prints PASS or FAIL.
Tags: **[R]** proved here, **[K]** known, **[N]** exact numerical check, **[C]** heuristic.

Normalisation, as in clique-evaluation.md: cost 2^{e_K·K²λ}; N = K(K−1)λ is the number of shared bits, counted at
both ends; a recursion level maps a K'-clique to K-node networks with K' = K^β and multiplies e by ρ, so
e_K ≍ (log K)^{−α'} with **α' = ln(1/ρ)/ln β**. The target e_K = o(1/log K) is the statement α' > 1.

## 0. Verdict first

| # | mechanism | outcome | type |
|---|---|---|---|
| M1 | asymptotic tensor rank / laser / structured tables | dead. A rank-based algorithm has e ≥ 1/4. Low CP-rank tables are cheap, but grouped-CNF tables only lose a constant factor of rank, so this compresses U and leaves the rate alone | [R]+[N] |
| M2 | representation theory: GL(D) per edge, node-local transforms, Schur–Weyl, holographic/matchgates | dead. Every rank-based cost is invariant under node-local invertible maps; Schur–Weyl needs symmetric tables | [R]+[N] |
| M3 | characteristic p, CRT, Beigel–Tarui amplification on the tables | dead. By CRT, e_K over ℤ is the max over primes of e_K over F_p, and all ranks are the same for every p | [R]+[N] |
| M4 | Fourier/Hadamard pieces; transforms between levels | dead. Monomial pieces in **any** product basis have rank_row = rank_col = \|S\|, so **ρ → 1, not 1/2**. Transforms between levels are covered by M2 | [R]+[N] |
| M5 | FMM, exact dependence on ω | **e_tree(ω) = min(ω/9, 1/4) + O(1/K)** for the best contraction tree (≥ 2/9 for every ω). Today 1/4 beats ω/9, a small correction to clique-evaluation.md §5. Any ω gives only a constant | [R]+[N] |
| M6 | conditional and meta barriers | **New meta-barrier [R]:** proving that oblivious algorithms need e_K ≥ φ(K)/K with φ → ∞, which includes c/log K, would prove **VP ≠ VNP** (arithmetic) or **EXP ⊄ P/poly** (Boolean). Conditional cap: "#3-SAT needs 2^{Ω(n/log n)}" ⇒ e_K = Ω(1/log K). That hypothesis is non-standard | [R] |
| M7 | **multi-grouping recursions** (m ≫ 2 groupings, β ≠ m), the main "differently recursive" candidate | **New cap [R]:** for 2-group-good gadget recursions, ρ ≥ E[1/d_γ] (mixing over d distinct cuts) **and** K' ≥ K^{d−o(1)} (entropy product lemma, robust). So α' ≤ 1 still holds. Residue: heterogeneous cut families and gadgets spread over ≥ 3 groups | [R]+[N] |
| M8 | recursion on λ (bit splitting) | dead in one line (the cost is 2^{Eλ₁} copies) | [R] |

**Ranking (most promising first):** (1) correlated (non-product) term decompositions, the one place where neither
§4.3 nor Theorem 7.3 applies (§9); (2) the residue of M7: multi-group gadgets; (3) M5 constants for base cases.
Everything else is closed. **The single most promising next step:** decide the smallest instance of the
"two-flattening rigidity" problem (§9.2). Can F⊗F, two rectangles, be written as 2^{o(λ)} terms, each with
cost below 2·(cost of F) in rows **or** in columns, without the mixed-ι structure? This is where the
§4.3 argument stops, and it is a finite tensor problem.

On the lower-bound branch of the mandate, M6 shows that an *unconditional* proof that oblivious algorithms cannot
beat c/log K is out of reach: it would separate VP from VNP. Only *structured* classes can be capped, and
§4.3 + Theorem 7.3 now cap every product-structured recursion with two-group-good gadgets, for any number of
groupings.

---------------------------------------------------------------------------------------------------

## M1. Asymptotic rank, laser method, structured tables

**Idea.** Z = ⟨⊗_a T_a, 𝒯_K⟩ with 𝒯_K the complete-graph tensor of bond dimension D (Christandl–Vrana–Zuiddam).
Use a rank or border-rank decomposition of 𝒯_K^{⊗n} (laser method), or exploit structure in the tables.

**Accounting [R].** A rank-R decomposition 𝒯_K = Σ_{r≤R} ⊗_a ℓ_{r,a} gives Z = Σ_r Π_a ℓ_{r,a}(T_a), at cost R·K·D^{K−1}.
Flattening along a balanced bipartition of the nodes gives R ≥ D^{K²/4}, so e ≥ 1/4 (clique-evaluation.md §2). Border
rank and asymptotic rank obey the same flattening bound, and the laser method only produces such decompositions. So
every algorithm in this class has e ≥ 1/4, a constant. This is the reason CVZ exponents are irrelevant to e_K.

**Structured tables [R+N].** If each table has CP rank r over its legs, T_a = Σ_{i<r} Π_b f_{a,b,i}(y_b), then

  Z = Σ_{i∈[r]^K} Π_{a<b} ⟨f_{a,b,i_a}, f_{b,a,i_b}⟩,  cost r^K·K²D,

which is polynomial for r = O(1). Checked exactly for (K,D,r) ∈ {(3,3,2),(4,2,2),(4,3,2),(5,2,2)}
(`engine2_tables.out` (a), PASS). Do the tables the engine actually sees have such structure?
`engine2_tables.out` (b) groups random 3-CNFs (K = 3, λ = 2, 3; 3λ private variables per node). At clause density 1.5
the mean log₂(rank)/λ is 0.99 and 0.93; at density 3.0 it is 0.60 and 0.69. So **grouped tables are rank-deficient
by a constant factor**, which was a surprise to me (my first "full rank" PASS criterion failed and I reported the
measured ranks instead). Exact consequence (b′): an edge whose interaction has rank r can be relabelled with a
log₂ r-bit alphabet. Write T_a = Σ_k c_{x,k} B_k with B a row basis, and push the coefficients into T_b; Z is
unchanged (3 instances, D = 4 → r ∈ {2,3}, PASS). This is a reduction of **U** by a constant factor (a
preprocessing gain). It does not touch e_K: e_K is a statement about arbitrary tables, and inside the
recursion the tables are the piece-modified ones, which are generic.

**Verdict.** Dead for the rate. Rank-type algorithms have e ≥ 1/4. Table structure gives U-compression only,
and an arbitrary table can be realised as a #CNF count over private variables, so the engine cannot assume
structure.

## M2. Representation theory: invariance groups, Schur–Weyl, holographic algorithms

**Idea.** The equality on each block is invariant under M ⊗ M^{−T} (M ∈ GL(D)). One could look for a basis in
which the contraction is sparse, or decompose a node's (ℂ^D)^{⊗(K−1)} under S_{K−1} × GL(D).

**Obstruction [R].** (i) The contraction tensor ⊗_e I_e is *fixed* by Π_e GL(D). Its support has D^E monomials in
every basis of this form, so no edge-local basis sparsifies it. (ii) A *node-local* invertible transform (one map
acting jointly on all K−1 legs of node a, possibly entangling legs that belong to different edges or gadgets)
replaces the identities by a non-product tensor. However, for **every** set W of nodes, the flattening rank of
any tensor across (legs at W | rest) is invariant under ⊗_a M_a, because each M_a acts inside one side. Every
lower bound in the project is a function of such node-cut ranks: §4.2, §4.3, pieces.md (2.1), Theorem 7.1 below.
So these transforms are invisible to all of them, and they cannot create savings that those costs do not
already allow. `engine2_fourier.out` (ii) checks this exactly. Two rectangles on four common nodes get a random
unimodular map on node 0's two legs, and all six node-cut ranks are unchanged (4, 16, 16, 1, 4, 1). (iii)
Schur–Weyl needs the tables to commute with S_{K−1}. For symmetric tables, Z is a sum over symmetric matrices
with prescribed row multisets, and there are DPs for that (2^{O(K log K)} for λ = 1, clique-evaluation.md §1.2).
General tables have no symmetry, and symmetrising changes Z. (iv) Holographic/matchgate algorithms need
every T_a to be a matchgate signature after a common basis change. Such signatures form a variety of dimension
poly(K)·D^{O(1)} inside the D^{K−1}-dimensional table space, so a generic table is not one. Also K_K is not
planar.

**Verdict.** Dead. (ii) is the useful statement: node-local transforms, *between levels as well*, cannot change
any of the capped costs.

## M3. Characteristic p, CRT, modulus amplification

**Idea.** The tables are small integers, so one could compute Z mod p for many p and interpolate, maybe with
Beigel–Tarui amplification applied to the tables.

**Accounting [R].** |Z| ≤ 2^{KB + Eλ}, so O(KB + Eλ) primes of size O(log(KB+Eλ)) are enough, and CRT is
polynomial. Hence e_K(ℤ) ≤ max_p e_K(F_p). Conversely, an algorithm over ℤ on lifted tables gives every F_p.
So the rate is the same in every characteristic, up to polynomial factors. Every obstruction is
field-independent: the rectangle F = [x=v][y=u] has rank D² across both cuts over F_2, F_3 and F_5
(`engine2_tables.out` (c)), and CRT reconstruction is checked on a K = 4 instance (PASS). Modulus amplification
(Beigel–Tarui, Chan–Williams) turns a *low-degree approximation* into an exact count. Here there is nothing to
amplify: the equality has full rank, so it has no low-degree approximation of the needed kind. Note that
per mod 2^k is easy (Valiant), but the bijection network of permanent-attack.md §3 does not see that structure.
In the vertex-algebra pieces the normalisation h! vanishes for p ≤ h, so they do not even exist in small
characteristic.

**Verdict.** Dead (exact equivalence plus field-independent ranks).

## M4. Fourier/Hadamard pieces and transforms between levels

**Idea (from the brief).** Walsh pieces might give ρ = 1/2, or a transform applied *between* levels might
compound savings, for example ρ² per level.

**Theorem 4.1 [R].** Let M be any invertible D×D matrix and m_α, m̃_α its columns and the rows of its inverse, so
that [x=v][y=u] = Σ_{α,β} m_α(x)m̃_α(v)m_β(y)m̃_β(u). For any S ⊆ [D]², the monomial piece
A_S = Σ_{(α,β)∈S} m_α(x)m̃_α(v)m_β(y)m̃_β(u) has rank exactly |S| across the row cut (xy|uv) **and** across the
column cut (xu|yv). *Proof:* the families {m_α⊗m_β}, {m̃_β⊗m̃_α}, {m_α⊗m̃_β} and {m_β⊗m̃_α} are each linearly
independent. ∎ So c_row + c_col = 2 log|S| and Σ_s |S_s| = D². With |I| pieces, some piece has
|S| ≥ D²/|I|, and therefore **ρ ≥ 1 − log₂|I|/(2λ) → 1**. Fourier pieces are the *worst* possible, not
1/2: they diagonalise the identity in one product basis and gain nothing on either cut. The theorem is checked
exactly for λ = 2, 3 in the Walsh basis and in random unimodular bases, 6 random S each
(`engine2_fourier.out`, all PASS).

**Transforms between levels [R].** The networks at level ℓ+1 have edges labelled by piece factorisation indices,
and their rectangles are again identities. An edge-local transform fixes them (M2 (i)). A node-local transform
leaves every node-cut rank unchanged (M2 (ii)), so the ρ of level ℓ+1 is the ρ of the identity, whatever
happened at level ℓ. Compounding to "ρ² per level" would need ρ_β < 1/β² with K' = K^β. That is below the
mixing bound ρ ≥ 1/2 at β = 2, and for other shapes see M7.

**Verdict.** Dead. Theorem 4.1 is the precise reason transform invariance (clique-evaluation.md §4.4) holds for
pieces as well.

## M5. Fast matrix multiplication: the exact dependence on ω

**Model.** Contraction trees with the best known algorithm at each merge. Because K_K is symmetric, only sizes
matter. Merging S₁, S₂ (sizes s₁, s₂, with r = K − s₁ − s₂ outside) is the product
(D^{s₁r} × D^{s₁s₂})·(D^{s₁s₂} × D^{s₂r}), at cost D^{ω(s₁r, s₁s₂, s₂r)}. A DP over sizes (`engine2_tree_omega.py`,
exact Fractions) evaluates three bounds:
* UB: ω(a,b,c) ≤ a+b+c − (3−ω)·min(a,b,c) (square blocking);
* LB: ω(a,b,c) ≥ max(a+b, b+c, a+c, ω(a+b+c)/3). The last term follows from symmetrisation:
  ⟨a,b,c⟩⊗⟨b,c,a⟩⊗⟨c,a,b⟩ is square;
* current rectangular constants: ω = 2.371339, α = 0.321334, ω(1,1,2) = 3.250035 (Alman–Duan–Vassilevska
  Williams–Xu–Xu–Zhou 2024), with ω(1,1,k) convex and ω(a,b,c) ≤ |a−b| + min(a,b)·ω(1,1,c/min(a,b)).

**Results [N], K = 240 (all K in the `.out`):**

| ω | e_tree UB | e_tree LB | ω/9 | 1/4+1/(2K) |
|---|---|---|---|---|
| 2 | 0.2222 | 0.2222 | 0.2222 | 0.2521 |
| 2.2 | 0.2444 | 0.2380 | 0.2444 | 0.2521 |
| 2.25 | 0.2500 | 0.2400 | 0.2500 | 0.2521 |
| 2.3713 | 0.2508 (rect. MM: 0.2505) | 0.2444 | 0.2635 | 0.2521 |
| 3 | 0.2521 | 0.2521 | 0.3333 | 0.2521 |

**Statement [R+N].** e_tree(ω) = min(ω/9, 1/4) + O(1/K) is achievable. At ω = 2 the upper and lower bounds coincide
at **2/9**, and the 2/9 − 1/K floor (§4.2) holds for every ω (PASS). Two consequences:
(a) **Correction:** for ω > 9/4, which includes today's value, plain sequential contraction (1/4) beats the
3-group FMM algorithm (ω/9 = 0.2635). The best "direct" constant is 1/4 + O(1/K). Rectangular MM only shrinks the
O(1/K) term. The hybrid of clique-evaluation.md §5 should use e₀ = 1/4, which multiplies all of its levels by
0.50 instead of 0.527, still a constant factor. (b) Inside a level, FMM enters additively
(clique-evaluation.md §3: e' = ρe + t/4 with t = Θ(1)). With ω = 2 the fixed point is 2/9, not 0. **The best
achievable e_K depends on ω only through base-case constants; the rate α' does not depend on ω or on
rectangular exponents at all.**

**Verdict.** Settled: constant-level only.

## M6. Conditional ceilings and a meta-barrier

**6.1 Meta-barrier for the lower-bound branch [R].** Let N_in = K·D^{K−1} be the number of table entries, and
P_K(T) = Σ_X Π_a T_a(X_a), a set-multilinear polynomial of degree K in N_in variables with 0/1 coefficients.
Time 2^{e_K K²λ} equals (N_in/K)^{e_K K²/(K−1)}. Take λ = K, so that K ≈ √log N_in.
* *Arithmetic.* An oblivious algebraic algorithm (a straight-line program over the table entries) computes P_K, and
  the family (P_K) lies in VNP: its degree is ≤ poly, and its coefficient function is 0/1 and computable in
  polynomial time. A lower bound e_K ≥ φ(K)/K with φ → ∞ would give circuit size ≥ (N_in/K)^{φ(K)},
  superpolynomial in N_in, so **P_K ∉ VP, i.e. VP ≠ VNP**. With φ = cK/log K, this covers "no oblivious
  algorithm beats c/log K".
* *Boolean.* Z is computable in time N_in^{K/2+o(1)} = 2^{O(log^{3/2} N_in)}, i.e. quasi-polynomial time. A lower
  bound e_K ≥ φ(K)/K for circuits would put a QP-time function outside P/poly, hence **EXP ⊄ P/poly**. Against *uniform* algorithms, as in Anthropic's
  Definition 4, the statement is weaker but still out of reach. It would be a superpolynomial time lower bound
  for an explicit natural problem in QP, and only diagonal functions are known to have such bounds (time
  hierarchy).

So the query bound (K−1)/K² is the only unconditional lower bound possible without a flagship breakthrough, even
up to factors growing arbitrarily slowly. Barriers have to be proved for *restricted* classes: contraction trees
(2/9), two-grouping recursions (§4.3), and multi-grouping gadget recursions (M7 below).

**6.2 A conditional cap [R].** (Corrected 5 Nov 2026: the first version used Lemma 1 with g = Θ(n) nodes,
P = O(1) and K = n^{1/3}; but Lemma 1 and Lemma 8(i) of Anthropic need g = 3K⁸ nodes, and the overhead
2^{2gP/K} is 2^{O(n/K)} only when gP = O(n), i.e. g ≤ m. With K = n^{1/3}, g = 3n^{8/3} > m and
gP/K = Θ(n^{7/3}).) Use Lemma 8(i) with the accounting of the proof of Anthropic's Theorem A(c): for a
bounded-occurrence 3-CNF with n variables and m = O(n) clauses take g = 3K⁸ ≤ m clusters, so P = 2k⌈m/g⌉,
gP ≤ 2k(m + g) = O(n), U < 2km = O(n), and the (K, L)-clique has K²L ≤ U + gP/K + K² = O(n). The overhead is
K^g · 2^{2gP/K} = 2^{O(K⁸ log K + n/K)}. With K = Θ(n^{1/9}) (any K = n^c, 0 < c ≤ 1/9, works) the overhead
is 2^{O(n^{8/9} log n)} = 2^{o(n/log n)} and log K = Θ(log n), so the running time is
2^{e_K·O(n) + O(n^{8/9} log n)}. Hence

  e_K = o(1/log K)  ⇒  #3-SAT (bounded occurrence) in 2^{o(n/log n)},

and contrapositively **H_log: "bounded-occurrence #3-SAT needs 2^{Ω(n/log n)}" ⇒ e_K = Ω(1/log K), which is exactly the §4.3 cap**,
now for *all* algorithms. H_log is consistent with everything known (Anthropic gives 2^{O(n/√log n)}), but it
is not a standard hypothesis. It is the only *kind* of hypothesis that can speak to the rate, as
clique-evaluation.md §4.5 notes, and here it is made explicit and quantitative. The converse fails: the tables are
arbitrary, so e_K is not reducible to #SAT. ETH-based statements (Marx; the binary-CSP form on K_K with domain
D^{K−1}, whose "n^{o(tw/log tw)}" would read exactly e_K = o(1/log K)) are void, because ETH is false in this world.
That reading also needs arbitrary binary relations, of rank n, whereas the clique has rank-D interactions.

**Verdict.** No falsity barrier exists. Unconditional optimality of c/log K is VP-vs-VNP-hard. The cap is
conditionally tight under H_log.

## M7. Multi-grouping recursions: the cap survives any number of groupings

**Idea.** The §4.3 cap uses two groupings and β = 2, which gives ρ ≥ 1/2, β = 2 and α' ≤ 1. With m groupings the
mixing argument only gives ρ ≥ 1/m. If one could have **m ≫ β** (many groupings, while the node count drops only
polynomially, for example line classes of F_q^d with β = d/(d−1)), α' could exceed 1. The d-dimensional box of
rate.md §3.3 has m = β = d. This is the natural "differently recursive" scheme.

**Setting (multi-grouping gadget level).** K' nodes; groupings P_1..P_m, each into K balanced classes. The crossing
edges are partitioned into gadgets γ, with F_γ = ⊗_{e∈γ} I_e = Σ_{s∈I_γ} A_{γ,s} and |I_γ| = 2^{o(λ)}. Every
ι ∈ Π_γ I_γ is evaluated as a K-node network in the grouping of its choice, and its cost there is at least
L_j(ι) = Σ_γ Σ_{G∈P_j} log₂ rk_G(A_{γ,ι(γ)}), using node-cut ranks as in M2. A gadget is **2-group-good** in P_j if
its nodes meet exactly two classes and each of its edges crosses between them. Identify a node u with its tuple
(G_1(u), …, G_m(u)) ∈ [K]^m. A good gadget containing the edge (u,v) then consists of **mix nodes**
w = (u_S, v_{S^c}) (S = {j : w_j = u_j}), and its distinct cuts correspond to the atoms of the Boolean algebra
generated by these sets S. Write d_γ for their number. (Grid rectangles: m = d = 2.)

**Theorem 7.1 (mixing) [R].** If every gadget is 2-group-good in every grouping, the level satisfies
ρ ≥ (1−o(1))·E_bits[1/d_γ] + (fraction of crossing bits outside gadgets).
*Proof.* For each of γ's d_γ cuts π, subadditivity of rank gives a piece s_π with
log rk_π A_{γ,s_π} ≥ log rk_π F_γ − log|I_γ|. Pick ι with ι(γ) = s_π for π uniform, independently over the
gadgets. In every grouping j, E[L_j(ι)] ≥ Σ_γ L_j(F_γ)/d_γ − o(N). L_j is a sum of independent bounded terms over
≫ log m gadgets, so with positive probability every grouping is simultaneously within o(N) of its mean. ∎

**Lemma 7.2 (exact product lemma) [R+N].** If X ⊆ [K]^m is a product across a cut S and across a cut T, then it is a
product over the four atoms. *Proof:* for u, v ∈ X, z := (u_T, v_{T^c}) ∈ X has z_S = (u_{S∩T}, v_{S∖T}), so
X_S ⊇ X_{S∩T} × X_{S∖T}; induct. ∎ Brute-force check on [3]³: 20000 sets that are products across {0} and {1};
every one is a full product (`engine2_multigroup.out` (a)).

**Theorem 7.3 (robust entropy product lemma) [R+N].** Assume *homogeneity* and *regularity*:
* homogeneity: for all but a δ-fraction of ordered pairs (u,v), the gadget of (u,v) contains the mix nodes for a
  fixed cut family 𝒮 whose algebra has d atoms;
* regularity: on a set J of d coordinates (one per atom), the cells of ∧_{j∈J} P_j have equal size.

If δ < 1/(d−1), then **log K' ≥ d·log K − O(1/(1−(d−1)δ))**, i.e. β ≥ d − o(1).
*Proof.* Let u, v be iid uniform and let A be the J-tuple of u. Regularity gives H(A) = log|π_J X|, and balance gives
H(A_j) = log K. For S ∈ 𝒮, Y = (A_{S∩J}, B_{J∖S}) has H(Y) = H(A_{S∩J}) + H(A_{J∖S}) and lands in π_J X with
probability ≥ 1−δ. So I_S := I(A_{S∩J}; A_{J∖S}) ≤ h(δ) + δ(d log K − log|π_J X|). By data processing
(I(A_{P∩S}; A_{P∖S}) ≤ I_S for every P), refining J into singletons in d−1 steps gives
log|π_J X| ≥ Σ_{j∈J} H(A_j) − (d−1)·max_S I_S. Substitute and solve for log|π_J X| ≤ log K'. ∎
Checked on 15 random designs (products minus a δ-fraction, unions of two sub-products; K ∈ {4,5,6},
d ∈ {2,3,4}). Both the chain inequality and the bound on I_S hold (`engine2_multigroup.out` (b), PASS).

**Linear designs (no regularity or homogeneity assumption) [R+N].** Let X = C ⊆ F_q^m be a linear code of
dimension b (K = q, β = b), with groupings by coordinate. The mix node for an edge w exists iff w|_S ∈ C. The
codewords w with w|_S ∈ C form the subspace (C∩F^S) ⊕ (C∩F^{S^c}), which is proper unless S is a union of
matroid components. So outside a set of density ≤ 2^m/q, every edge's cuts are unions of components, and
**d ≤ #components ≤ b = β**. Numerically, connected [4,3] codes do have edges with 4 > 3 cuts, but on a density
of 0.29, 0.15, 0.088 for q = 5, 17, 31 (≈ 3/q, below 2^m/q; `engine2_multigroup.out` (c), PASS). These exceptional
edges vanish as q → ∞.

**Corollary 7.4 (the cap extends) [R].** Under 7.1 + 7.3, ρ ≥ (1−δ)/d − o(1) and β ≥ d − o(1). So
α' = ln(1/ρ)/ln β ≤ ln(d/(1−δ))/ln(d − o(1)) = 1 + O(δ/ln d), and e_K ≥ c/log K whenever δ → 0 along the levels.
**Many groupings buy nothing: each additional distinct cut costs exactly one factor K in the node count.** The
line-class idea (m ≫ β) fails at the gadget level. In F_q^2 with all q+1 directions, a set of nodes lying on two
parallel lines in three directions has at most 4 points, so every gadget has d ≤ 2 (3 in characteristic 2, where
the third cut makes both edges internal). It is good in only 2 of the q+1 groupings and pays full price in the
others.

**Residue (not covered) [C].** (L1) *heterogeneous* families, where different gadgets use different cut
families: the entropy argument needs one family on a (1−δ)-fraction of pairs. I see no gain, because in each
grouping only the gadgets that are good there are cheap, but I have no proof. (L2) gadgets meeting ≥ 3 classes in
some grouping: mixing then gives only ρ ≥ 1/M_γ, where M_γ is the number of distinct node-cut bipartitions, and
the product lemma does not apply because the third "base" node is not independent of the edge. The Latin-square
(rows/columns/symbols) design is an example. It gives 2λ instead of 4λ only on the 1/g fraction of rectangles of
special shape, so it is useless, but the general case is open. (L3) Decompositions that are not products over
gadgets, see §9.

## M8. Recursion on λ instead of K [R]

Split each block into λ = λ₁ + λ₂ bits. Tables do not factor over the split, so the only identity is
Z = Σ_{x′ ∈ [2^{λ₁}]^E} Z_{λ₂}(T|_{x′}): 2^{Eλ₁} instances at cost 2^{e K²λ₂}, i.e. e_new = λ₁/(2λ) + e·λ₂/λ ≥ e.
Lemma 8 regrouping is lossless in U and only reshapes. Dead.

## 9. What remains, and the next step

### 9.1 Where every proved cap stops

All the caps (§4.2 trees, §4.3 two groupings, Theorem 7.1/7.3 many groupings, Theorem 4.1 transforms) share one of
two hypotheses: the algorithm stores Θ(K²)-leg intermediates, or the term set is a **full product** Π_γ I_γ, which is
what lets the mixed ι exist. A recursion whose admissible terms form a *correlated* set 𝒞 ⊊ Π_γ I_γ (equivalently, a
decomposition I_{K'} = Σ_{t∈𝒞} T_t of the global identity into 2^{o(N)} terms, each a ρN-bit network in *one*
grouping) is not touched by any of them. The rank sums alone (Σ_t rk_row T_t ≥ D^{N_row}) give nothing: column-cheap
terms may carry the full row rank. By M6 this is also the only place where an algorithm with α' > 1 could live
inside the "evaluate terms as smaller cliques" paradigm.

### 9.2 The concrete next step

**Two-flattening rigidity, smallest case.** For F = [x=v][y=u] on D = 2^λ, and for F⊗F (two rectangles of one
grid level), determine

  r₂(λ) := min over decompositions F⊗F = Σ_{t≤T} T_t, T = 2^{o(λ)}, of max_t min(c_row(T_t), c_col(T_t)),

where c_row and c_col are now the costs of the 2-rectangle term in the row and column groupings. The product
(mixed) decompositions give r₂ ≥ 2·(2λ) − o(λ) by §4.3, i.e. ρ ≥ 1/2. **A correlated decomposition with
r₂ < 4λ − Ω(λ) would be the first evidence that ρ < 1/2 is possible at all**, and hence α' > 1 at β = 2. Conversely,
a proof that r_k(λ) ≥ (1/2 − o(1))·4kλ for all k would close the "smaller cliques" paradigm completely. This is a
finite tensor problem, and it is computable for λ ≤ 2 by alternating rank-constrained projections (floating point
first, then an exact certificate). It is the cheapest experiment that could change the picture.

## Files

* `scripts/engine2_lib.py`: exact rank (Bareiss), brute-force Z.
* `scripts/engine2_tables.py/.out`: M1 (CP-rank identity, grouped-CNF ranks, edge compression) and M3 (CRT, ranks mod p).
* `scripts/engine2_fourier.py/.out`: M4 Theorem 4.1 (Walsh and unimodular bases) and M2 (ii) node-local invariance.
* `scripts/engine2_tree_omega.py/.out`: M5 DP over contraction trees as a function of ω, including rectangular MM.
* `scripts/engine2_multigroup.py/.out`: M7 Lemma 7.2 (brute force), Theorem 7.3 (entropy chain), linear designs.
