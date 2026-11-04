# Decorrelated decompositions: §9.2 of engine2-algebraic.md settled for two rectangles

4 Nov 2026. Follows `engine2-algebraic.md` §9 (the open step: correlated, non-product term sets) and
`permanent/rate.md`, `permanent/rho-lower-bound.md` (pieces formalism, R1–R3). Scripts:
`scripts/engine2d_lib.py`, `scripts/engine2d_sat.py` (GF(2) SAT, exhaustive at λ = 1), `scripts/engine2d_bound.py`
(exact ℚ checks); outputs `scripts/engine2d_*.out`. Lean: `lean/EthFollowup/Scratch/Decorrelated/{Basic,Product}.lean`.
Tags: **[R]** proved here, **[L]** Lean-proved, **[K]** known, **[N]** exact computation, **[C]** heuristic.

## 0. Verdict

* **The §9.2 question has a negative answer [R][L].** For two rectangles, every decomposition
  F⊗F = Σ_{t≤T} T_t, with each term a row-network or a column-network (arbitrary local tensors, so a term
  may correlate the two rectangles), satisfies
  **Σ_t 2^{cost_t} ≥ N² = 2^{2λ}**, hence **max_t cost_t ≥ 2λ − log₂T**, i.e. r₂(λ) ≥ 2·(2λ) − 2log₂T in the
  both-ends units of §9.2. This is exactly the product bound of §4.3: **correlation buys nothing, ρ ≥ 1/2 − o(1).**
  It holds for every relative position of the two rectangles, every field, every λ.
* The proof is two lines and was hiding in plain sight: the R3 contraction of `rho-lower-bound.md` Prop. 2.1
  (set y = u = 0) gives one matrix that is simultaneously a submatrix of the row flattening and of the column
  flattening. So it bounds the *minimum* of the two costs, and the mixed-term/min-over-groupings issue that
  the §4.3 argument needed never arises. §9.1's remark "rank sums alone give nothing" applies to the row and
  column rank sums separately. It does not apply to this diagonal one.
* **Generalisation [R].** Theorem 2: the same bound, Σ_t 2^{(2/m)·cost_t} ≥ N^{2Q/m}, so max cost ≥ Qλ − (m/2)log T, holds
  for every configuration of Q rectangles that has a *diagonal labelling* (§3). This covers all two-rectangle
  configurations, the triangle, and every "bipartite" level. The proof uses the Christandl–Vrana–Zuiddam quantum
  functionals [K] for m ≥ 3 parties and plain rank for m = 2.
* **Where it stops.** A full grid level is *not* diagonal. The best diagonal sub-configuration contains 1/4 of
  the rectangles, so unconditionally only **ρ ≥ 1/8** follows for arbitrary correlated network decompositions
  of a whole level (Theorem 3), and then α' ≤ 3 instead of α' ≤ 1. The smallest non-diagonal configuration is the
  **3×2 grid** (three rectangles on one column pair). It is the new minimal open instance. λ = 1 SAT search on
  it: §5.
* **Cap verdict.** Decorrelated decompositions **cannot** beat the c/log K cap through any diagonal
  configuration, and in particular not through pairs of rectangles. A loophole survives only in correlations
  that use non-diagonal configurations (three or more rectangles sharing a row or column pair, routed
  through third rows), and there the proved cap is weaker (ρ ≥ 1/8). Small-λ data cannot decide ρ, because
  the o(λ) terms dominate at λ ≤ 2 (§5). The next step is a lower bound for the 3×2 grid, or a construction on it
  (§6).

## 1. The finite problem, exactly

**Rectangles.** A rectangle q on rows a<b and columns j<j' of the grid has legs x@(a,j), y@(a,j'), u@(b,j),
v@(b,j') ∈ [D], D = N = 2^λ, and F_q = [x=v][y=u]: the two crossing equalities (a,j)–(b,j') and (a,j')–(b,j).
A *configuration* is a set R of Q rectangles. Rectangles may share rows, columns, or both (fat cells).

**Terms.** In the row grouping the classes are the rows. A *row-network* is a tensor
T(legs) = Σ_θ Π_rows W_r(legs of row r; θ_{r,·}) with bond dimensions d_{rs} on row pairs and *arbitrary* local
tensors W_r. W_r may couple all legs of row r, including legs of different rectangles. Column-networks are
defined the same way. A product of per-rectangle pieces (the §4.3 model) is a special case.

**Cost.** cost(T) = Σ_{r<s} log₂ d_{rs} (shared bits, counted once). This is what the recursion pays when it
evaluates the term as a network in its grouping. The level's ratio is

  ρ(𝒟) = max_t cost_t / (2λQ),   for decompositions 𝒟 = {T_t}_{t≤T} with  Σ_t T_t = ⊗_{q∈R} F_q,  log₂T = o(λQ),

where 2λQ is the trivial cost (each rectangle has rank N² across both cuts). The finite proxy used in the searches is
the **rank sum** S(𝒟) = Σ_t 2^{cost_t}. Then max_t cost_t ≥ log₂S − log₂T, so S ≥ 2^{λQ} for all λ gives ρ ≥ 1/2 − o(1).
A correlated decomposition with ρ(𝒟) < 1/2 − ε on every pair of rectangles would give ρ < 1/2 for a level tiled
by such pairs, hence α' > 1. **§9.2's r₂(λ)** is 2·min_𝒟 max_t cost_t over two rectangles, in both-ends units.

**What a cost bounds [R].** For a row-network and any set S of rows, the flattening across (legs in rows S | rest)
has rank ≤ 2^{Σ_{r∈S, s∉S} c_rs} ≤ 2^{cost}. This holds because W_r is local to its row, and contracting a bond
of dimension d costs a factor d. This is the *only* property used below (`rho-lower-bound.md` Lemma 1.1).

## 2. Theorem 1 (two rectangles) [R][L]

**Theorem 1.** For any two rectangles and any decomposition F⊗F = Σ_t T_t into row- and column-networks,
over any field: Σ_t 2^{cost_t} ≥ Σ_t min(rk_row T_t, rk_col T_t) ≥ N².

*Proof.* Choose 2-colourings χ of the rows and ψ of the columns that split both rectangles (a graph with two
edges is bipartite). For each rectangle keep the crossing edge whose ends lie in χ⁻¹(0)×ψ⁻¹(0) and in
χ⁻¹(1)×ψ⁻¹(1) (one of the two crossing edges always qualifies). Fix every other leg to a value o. The
contraction C_t is then a matrix (kept left ends | kept right ends). It is a submatrix of the flattening of T_t
across rows χ⁻¹(0), so rank C_t ≤ 2^{cost} for a row-network, and a submatrix of the flattening across columns
ψ⁻¹(0), so rank C_t ≤ 2^{cost} for a column-network. Also Σ_t C_t = I_{N²}, since F with y = u = o is
[x=v]. By subadditivity, N² ≤ Σ_t rank C_t. ∎

Corollary: some term has min(rk_row, rk_col) ≥ N²/T, i.e. cost ≥ 2λ − log₂T, against the trivial 4λ: **ρ ≥ 1/2 − log₂T/(4λ)**.

*Lean* (`Decorrelated/Basic.lean`, general alphabet α, any field K, arbitrary finite family of arbitrary
tensors; axioms [propext, Classical.choice, Quot.sound]):

    theorem Decorrelated.rankSum_ge [Nonempty α] {ι} (s : Finset ι) (T : ι → Tensor2 K α)
        (hsum : ∑ t ∈ s, T t = FF) :
        Fintype.card α ^ 2 ≤ ∑ t ∈ s, min (rowFlat (T t)).rank (colFlat (T t)).rank
    theorem Decorrelated.exists_expensive ... :
        ∃ t ∈ s, Fintype.card α ^ 2 ≤ s.card * min (rowFlat (T t)).rank (colFlat (T t)).rank

`rowFlat`/`colFlat` are the cuts (x1y1x2y2 | u1v1u2v2) and (x1u1x2u2 | y1v1y2v2). These are the 2-class cuts for
configurations A (fat cell), B (shared row pair) and C (disjoint). The chain configurations D, E reduce to them by
the symmetry (x,y,u,v) ↦ (v,u,y,x) of F (not separately formalised). Since rank ≤ 2^{cost}, the Lean statement implies
Theorem 1 for those configurations.

## 3. Theorem 2 (diagonal configurations) [R, uses K]

A **diagonal labelling** of R with m labels is a pair f: rows → [m], h: columns → [m] such that every rectangle
(a<b, j<j') has f(a) ≠ f(b) and {f(a), f(b)} = {h(j), h(j')}. Party i consists of the grid nodes (r,c) with
f(r) = h(c) = i. Every rectangle then has one crossing edge between two different parties, and its other two legs lie
off the diagonal.

**Theorem 2.** If R has a diagonal labelling, every decomposition satisfies max_t cost_t ≥ λQ − (m/2)·log₂T.

*Proof.* Fix all off-diagonal legs. The target becomes the graph tensor G (one EPR pair of dimension N per
rectangle, between its two parties). A row-network becomes a restriction, by maps local to the m parties, of the graph
tensor with bonds d_{ik} = Π_{f(r)=i, f(s)=k} d_{rs}. This works because all surviving legs of row r lie in party f(r), so
W_r is local. The same holds for column-networks. Let F^θ be a CVZ quantum functional with uniform θ (Christandl–Vrana–
Zuiddam, *Universal points in the asymptotic spectrum of tensors*, STOC'18 / JAMS 2023) [K]. It is monotone under
restriction and additive under ⊕. A sum is a restriction of the direct sum, so F^θ(Σ T_t) ≤ Σ_t F^θ(T_t). Also F^θ(T) ≤ Π_i rk_i(T)^{1/m},
with equality for graph tensors. Hence N^{2Q/m} = F^θ(G) ≤ Σ_t 2^{(2/m)cost_t} ≤ T·2^{(2/m)max cost}. ∎

For m = 2, F^θ is the flattening rank and Theorem 2 is Theorem 1. The triangle (rows ab, bc, ca on columns jk,
kl, jl) needs m = 3: the 2-party bound only gives ρ ≥ 1/3 there, and Theorem 2 gives 1/2.

## 4. Theorem 3 (a full grid level: what survives) [R]

The full g×g level has |R| = C(g,2)² rectangles. A rectangle is diagonal for (f,h) only if its row pair and its column pair
carry the same two labels. With label densities p_i, the diagonal fraction is Σ_{i≠k} 2p_i²p_k² ≤ 1/4 (maximum at
m = 2, balanced). Exact brute force gives 4/9 for g = 3 and 16/36 for g = 4, tending to 1/4
(`engine2d_bound.out` (b)). Restricting to one balanced diagonal sub-configuration and bounding its cut cost by the
term's whole cost gives

**Theorem 3.** For every decomposition of a grid level into row- and column-networks with log T = o(λ|R|),
max_t cost_t ≥ (1/4 − o(1))·λ|R|, i.e. **ρ ≥ 1/8** and α' ≤ 3 at β = 2.

The factor-4 gap to the product bound comes from two losses: only 1/4 of the rectangles survive the contraction, and
a cut sees only part of a term's cost. A term whose bits sit on a single bipartite cut (χ,ψ), with rows on the same side
talking only through rows on the other side, is the only kind that can exploit this gap. No argument of the Theorem-2 type
excludes it, because a functional local to the grid nodes is not bounded on row-networks (W_r couples a whole row).

## 5. Exhaustive search at λ = 1 (GF(2), SAT) [N]

`engine2d_sat.py` encodes "⊗F_q = Σ_t T_t over GF(2) with the given bond profile" for CaDiCaL/Glucose. It uses arbitrary local
tensors, one variable per entry of every W_r, and XOR constraints, and enumerates every profile of total weight S.
In a 2-class grouping ranks add, so one term per such grouping suffices. Every solution found is re-verified
entrywise. GF(2) makes the search space finite and genuinely exhaustive. Theorem 1 holds over every field, and the
product baseline below has the same ranks over GF(2) and ℚ.

RESULTS_TABLE

Product baseline, the pieces F = I + (F−I) with I = [x=u][y=v] (row rank 4, column rank 1) and F−I (row rank 1,
column rank 4): terms I⊗I, I⊗A, A⊗I, A⊗A with min-ranks 1, 4, 4, 1, **rank sum 10, max cost 2 bits = Qλ**.
*Lean* (`Decorrelated/Product.lean`, by explicit integer computation and cast to ℚ):
`product_sum : ∑ s, term s = FF`, `product_costs` (the four minima are 1, 4, 4, 1) and `product_rank_sum = 10`.

Reading. (i) At λ = 1 the product decomposition already meets max cost = Qλ, because log T is not o(λ). Small λ
cannot separate ρ = 1/2 from anything, as the task anticipated: the λ-asymptotics are carried by Theorem 1 alone, for
every λ. (ii) The rank-sum minima lie strictly between the bound 2^Q and the product value 10. Correlated decompositions
beat products *in rank sum* at λ = 1 (e.g. A: 7 via F = I + (I+F) on the fat cell, which treats F⊗F as a
single rectangle). They never get below Theorem 1. That is the expected picture: correlation can repack constants, but
the diagonal contraction forbids an exponential gain. (iii) 3×2 grid: see the table. A decomposition with S < N³ = 8 would
show that the diagonal law S ≥ N^Q fails off-diagonal, at least at λ = 1.

## 6. What remains

1. **The 3×2 grid.** Three rectangles between rows ab, ac, bc on one column pair. Column-networks are single cuts and
   row-networks are triangles. Proved: S ≥ N² (2 of the 3 rectangles are diagonal). Wanted: S ≥ N^{3−o(1)}, or a family with
   max cost ≤ (3 − ε)λ. A proof for it, with the same proof for the K_{g}-shaped row-pair graph, would lift Theorem 3 to ρ ≥ 1/2,
   and the cap c/log K would then hold for all correlated network decompositions of grid levels.
2. Lean: Theorem 1 is formalised for configurations A/B/C. Theorem 2 (m ≥ 3) needs the CVZ functionals, which are not in
   Mathlib. Theorem 3 is not formalised.

## Files

* `scripts/engine2d_lib.py`: configurations, GF(2) network encoding, GF(2) cut ranks.
* `scripts/engine2d_sat.py` / `.out`: exhaustive λ = 1 search (`two`: single rectangle and configurations A–E; `3x2`).
* `scripts/engine2d_bound.py` / `.out`: exact ℚ check of Theorem 1 on random decompositions (λ = 1, 2), diagonal labellings.
* `lean/EthFollowup/Scratch/Decorrelated/Basic.lean`: Theorem 1 (general α, any field). `Product.lean`: the product
  decomposition at λ = 1 and its costs.
