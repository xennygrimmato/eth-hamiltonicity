# Decorrelated decompositions: §9.2 of engine2-algebraic.md settled for two rectangles

4 Nov 2026. Follows `engine2-algebraic.md` §9 (the open step: correlated, non-product term sets) and
`permanent/rate.md`, `permanent/rho-lower-bound.md` (pieces formalism, R1–R3). Scripts:
`scripts/engine2d_lib.py`, `scripts/engine2d_sat.py` (GF(2) SAT, exhaustive at λ = 1), `scripts/engine2d_bound.py`
(exact ℚ checks); outputs `scripts/engine2d_*.out`. Lean: Theorem 1 is in `lean/EthFollowup/Barriers/DecorrelatedRank.lean` (committed, standard axioms); the λ = 1 product check is in the local scratch file `Decorrelated/Product.lean` (not committed).
Tags: **[R]** proved here, **[L]** Lean-proved, **[K]** known, **[N]** exact computation, **[C]** heuristic.

## 0. Verdict

* **Update (§7, same day).** The 3×2 grid is closed: Σ_t min(rk_{b|ac}, rk_col) ≥ N³ for every decomposition
  (Theorem 4, [R][L], any field, any alphabet), so **ρ ≥ 1/2 on the minimal non-diagonal instance**. The tool is a
  *lossy* diagonal contraction: one leg may sit on the wrong side of the row cut and one on the wrong side of the column
  cut, at a factor N each. The same lemma lifts Theorem 3 from ρ ≥ 1/8 to **ρ ≥ 3/8 for full grid levels** (Theorem 5,
  α' ≤ log₂(8/3) ≈ 1.415 instead of 3), and 3/8 is the most this 2-party method can give (Proposition 7.6). The new
  minimal open instance is the full 3×3 level (proved S ≥ N⁸, wanted N⁹). No correlated decomposition beating ρ = 1/2
  exists on any configuration where the method reaches Q (§7.5). The bullets below are the state before §7.

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

| configuration (λ = 1) | Q | Thm 1 bound N^Q | product rank sum | SAT: S proven impossible (exact) | S tried, timeouts (10 s) | smallest S found (profile) |
|---|---|---|---|---|---|---|
| single rectangle | 1 | 2 | 2 | – | – | **2** = bound (row[1] + col[1]: F = I + (I+F)) |
| A fat cell (same row and column pair) | 2 | 4 | 10 | 4 | 5 (4 t/o), 6 (7 t/o) | **7** (row rank 1 + col rank 6) |
| B same row pair, disjoint columns | 2 | 4 | 10 | 4 | 5 (1 t/o), 6 (10 t/o) | **7** (col[1,1] + row rank 6) |
| B′ same row pair, shared column | 2 | 4 | 10 | 4 | 5 (1 t/o), 6 (15 t/o) | **7** (col[1,1] + row rank 6) |
| C disjoint | 2 | 4 | 10 | 4, 5 | 6 (7 t/o); S = 7 run stopped at the 50-min budget | ≤ 10 (product) |
| D, E chains | 2 | 4 | 10 | not run (budget) | – | ≤ 10 (product) |
| **3×2 grid (non-diagonal)** | 3 | (only N² = 4 proved; diagonal law would be N³ = 8) | 26 | 4 | 5 (5 t/o), 6 (23 t/o), 7 (100 t/o at 5 s); profiles failing Thm-1 cut inequalities skipped | **none with S ≤ 7 found** |

(`scripts/engine2d_sat_two.out`, `scripts/engine2d_sat_3x2.out`; every reported solution re-verified entrywise, PASS.
"Exact" = every profile of that weight returned UNSAT.)

Product baseline, the pieces F = I + (F−I) with I = [x=u][y=v] (row rank 4, column rank 1) and F−I (row rank 1,
column rank 4): terms I⊗I, I⊗A, A⊗I, A⊗A with min-ranks 1, 4, 4, 1, **rank sum 10, max cost 2 bits = Qλ**.
*Lean* (`Decorrelated/Product.lean`, by explicit integer computation and cast to ℚ):
`product_sum : ∑ s, term s = FF`, `product_costs` (the four minima are 1, 4, 4, 1) and `product_rank_sum = 10`.

Reading. (i) At λ = 1 the product decomposition already meets max cost = Qλ, because log T is not o(λ). Small λ
cannot separate ρ = 1/2 from anything, as the task anticipated: the λ-asymptotics are carried by Theorem 1 alone, for
every λ. (ii) The rank-sum minima lie strictly between the bound 2^Q and the product value 10. Correlated decompositions
beat products *in rank sum* at λ = 1 (e.g. A: 7 via F = I + (I+F) on the fat cell, which treats F⊗F as a
single rectangle). They never get below Theorem 1. That is the expected picture: correlation can repack constants, but
the diagonal contraction forbids an exponential gain. (iii) 3×2 grid: no decomposition with S < N³ = 8 was found. S = 4 is excluded exactly, and S = 5–7 had many
timeouts, so this is weak evidence [C] that the diagonal law S ≥ N^Q also holds off-diagonal. A solution
would have shown the law fails there, at least at λ = 1. The product rank sum is 26 = 1+1+6·4.

## 6. What remains

*(Item 1 is settled by §7: S ≥ N³, Theorem 4.)*

1. **The 3×2 grid.** Three rectangles between rows ab, ac, bc on one column pair. Column-networks are single cuts and
   row-networks are triangles. Proved: S ≥ N² (2 of the 3 rectangles are diagonal). Wanted: S ≥ N^{3−o(1)}, or a family with
   max cost ≤ (3 − ε)λ. A proof for it, with the same proof for the K_{g}-shaped row-pair graph, would lift Theorem 3 to ρ ≥ 1/2,
   and the cap c/log K would then hold for all correlated network decompositions of grid levels.
2. Lean: Theorem 1 is formalised for configurations A/B/C. Theorem 2 (m ≥ 3) needs the CVZ functionals, which are not in
   Mathlib. Theorem 3 is not formalised.

## Lean status per claim

| claim | status |
|---|---|
| Theorem 1, configurations A/B/C (Σ_t min(rk_row, rk_col) ≥ D², any field, any D, arbitrary terms) | **Lean-proved (general)**: `Decorrelated.rankSum_ge`, `exists_expensive` |
| Theorem 1, chains D/E | by the symmetry of F (not yet formalised) |
| product decomposition at λ = 1: identity, min-ranks (1,4,4,1), rank sum 10, max 4 | **Lean-checked on the instance**: `DecorrelatedProduct.product_sum`, `product_costs`, `product_rank_sum` |
| a correlated decomposition beating the product bound | none exists asymptotically (Theorem 1). The λ = 1 rank-sum improvements (7 < 10) are GF(2) SAT outputs, not formalised |
| Theorem 2 (m ≥ 3, CVZ functionals), Theorem 3 (ρ ≥ 1/8) | not yet formalised (CVZ is not in Mathlib) |
| 3×2: S ≥ 4 proved, S < 8 not found | superseded by §7: S ≥ N³ is **Lean-proved (general)** (`Grid32.rankSum_ge`) |

All Lean theorems print `[propext, Classical.choice, Quot.sound]` under `#print axioms`. No sorry, no native_decide.

## Files

* `scripts/engine2d_lib.py`: configurations, GF(2) network encoding, GF(2) cut ranks.
* `scripts/engine2d_sat.py` / `.out`: exhaustive λ = 1 search (`two`: single rectangle and configurations A–E; `3x2`).
* `scripts/engine2d_bound.py` / `.out`: exact ℚ check of Theorem 1 on random decompositions (λ = 1, 2), diagonal labellings.
* `lean/EthFollowup/Scratch/Decorrelated/Basic.lean`: Theorem 1 (general α, any field). `Product.lean`: the product
  decomposition at λ = 1 and its costs. `Grid32.lean`: Theorem 4 (3×2 grid) and the relabelling no-go of §7.5(b).
* `scripts/engine2d_lossy.py` / `.out`: §7 numeric check of Theorem 4, level counts (Theorem 5), sub-configurations.
* `scripts/engine2d_grid32/` and `scripts/engine2d_grid32.out`: §7.5, §7.7 (min-cut model, λ = 1 matching MILPs).

---------------------------------------------------------------------------------------------------

## 7. Lossy diagonal contractions: the 3×2 grid is closed, full levels have ρ ≥ 3/8

Follows §6 item 1. Lean: `lean/EthFollowup/Scratch/Decorrelated/Grid32.lean` (scratch, sorry-free, standard axioms).
Scripts: `scripts/engine2d_lossy.py` / `.out` (numeric check of Theorem 4, level counts),
`scripts/engine2d_grid32/` and `scripts/engine2d_grid32.out` (λ = 1 searches, min-cut model).

### 7.0 Verdict

* **3×2 grid: correlation buys nothing [R][L].** Every decomposition H = Σ_t T_t of the three rectangles into
  row-networks and column-networks, over any field, satisfies Σ_t min(rk_{b|ac} T_t, rk_col T_t) ≥ N³. Hence
  Σ_t 2^{cost_t} ≥ N³, max_t cost_t ≥ 3λ − log₂T, **ρ ≥ 1/2 − log₂T/(6λ)**. This is exactly the product bound.
  No decomposition of the kind asked for in the task can beat ρ = 1/2 there, at any λ, over any field.
* **Mechanism.** The diagonal contractions of Theorems 1–3 put every kept leg on its "own" side of a cut that is
  both a row cut and a column cut. On the 3×2 grid such cuts see at most two edges (§7.5(a)). Theorem 4 lets **one leg
  straddle the row cut and one leg straddle the column cut**. Each costs a factor N, but only in its own grouping:
  a row-network pays for the row-straddler and a column-network for the column-straddler, never both. The target gains
  N² (rank N⁴ instead of N²), so the net gain is N.
* **Full grid levels [R].** The same lemma (§7.3) with balanced 2-labellings gives, for the g×g level with g = 2h,
  Σ_t 2^{cost_t} ≥ N^{3h⁴−2h³}, i.e. **ρ ≥ h(3h−2)/(2(2h−1)²) − o(1) → 3/8** (4/9 at g = 3, 4; 21/50 at g = 5, 6).
  This replaces Theorem 3's ρ ≥ 1/8. The cap becomes **α' ≤ log₂(8/3) ≈ 1.415** (it was 3). The target α' ≤ 1 still
  needs ρ ≥ 1/2.
* **Limit of the method [R].** No 2-party lossy contraction (any 2-labellings, any kept, fixed or paired legs) gives
  more than (3/4 + O(1/g))Q on the full level (Proposition 7.6). Exhaustive check [N]: every proper sub-configuration of
  the 3×3 grid, every configuration on a 4×2 grid, and every configuration with ≤ 7 rectangles on a 5×2 grid reaches the
  full exponent Q, so ρ ≥ 1/2 holds for all of them. The full 3×3 level (Q = 9) gets 8. **It is the new minimal open
  instance** (S ≥ N⁸ proved, N⁹ wanted).
* **Search for a beating decomposition.** None can exist on the 3×2 grid (Theorem 4). The λ = 1 data are consistent
  with this (§7.7): SL₂-invariant (matching) decompositions need rank sum ≥ 17 > 8 = N³, and the best found is 22.

### 7.1 The 3×2 grid as a hexagon

Rows a, b, c; columns j, j'; rectangles ab, ac, bc on (j, j'). Write the six nodes in the cyclic order
1 = (a,j), 2 = (b,j'), 3 = (c,j), 4 = (a,j'), 5 = (b,j), 6 = (c,j'). The six crossing equalities are then the edges of
a hexagon 1–2–3–4–5–6–1 (each an identity of dimension N). Rows are the antipodal pairs {1,4}, {2,5}, {3,6}. Columns
are the two colour classes {1,3,5}, {2,4,6}. Every edge joins two rows and the two columns. A column-network is a
single cut (odd | even), with cost log₂ of the column rank. A row-network is a triangle network on the antipodal
pairs. Legs (Lean order): x1 y1 u1 v1 (ab), x2 y2 u2 v2 (ac), x3 y3 u3 v3 (bc), H = Π_q [x_q = v_q][y_q = u_q].

### 7.2 Theorem 4 (3×2 grid) [R][L]

**Theorem 4.** For every finite family of terms with Σ_t T_t = H, over any field and any alphabet of size N:

  N³ ≤ Σ_t min(rank flat_{b|ac} T_t, rank flat_{j|j'} T_t).

Since a row-network has rank flat_{b|ac} ≤ d_ab·d_bc ≤ 2^{cost} and a column-network has rank flat_{j|j'} ≤ 2^{cost},
this gives Σ_t 2^{cost_t} ≥ N³.

*Proof.* Define the contraction (pair the two legs at node (a,j), fix the bc-legs y3 = u3 = o):

  M(T)[(y1, y2, v2, v3), (u1, x3, u2, v1)] = Σ_z T(z, y1, u1, v1, z, y2, u2, v2, x3, o, o, v3).

(i) M(H) = [y1 = u1][y2 = u2][v2 = v1][v3 = x3] is a permutation matrix, rank N⁴. The pairing at (a,j) merges the
two edges 1–2 and 1–6 into one edge v1 – v2.
(ii) For fixed u2 = w the columns of M(T) form a pairing contraction of flat_{b|ac}(T)ᵀ (rows (y1,y2,v2,v3) are legs of
rows a and c, columns (u1, v1, x3) are legs of row b). So M(T) = Σ_w (block w) has rank ≤ N·rank flat_{b|ac}(T). The
only straddling leg is u2 (row c, placed with row b).
(iii) For fixed v1 = w the columns of M(T) form a pairing contraction of flat_{j|j'}(T): the rows (y1, y2, v2, v3) lie in
column j', and (u1, x3, u2) together with the paired x1 = x2 lie in column j. So rank M(T) ≤ N·rank flat_{j|j'}(T). The
only straddling leg is v1.
Then N⁴ = rank M(Σ_t T_t) ≤ Σ_t rank M(T_t) ≤ N·Σ_t min(…). ∎

Checked numerically on random terms for N = 2, 3 (`engine2d_lossy.out` (a)). The bound in (ii), (iii) is attained:
rank M(T) = N·r for generic T of rank r. *Lean* (`Grid32.lean`, general α, any field K, arbitrary terms):

    theorem Grid32.rankSum_ge [Nonempty α] {ι} (s : Finset ι) (T : ι → Tensor3 K α) (hsum : ∑ t ∈ s, T t = H) :
        Fintype.card α ^ 3 ≤ ∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank
    theorem Grid32.exists_expensive ... :
        ∃ t ∈ s, Fintype.card α ^ 3 ≤ s.card * min (flatB (T t)).rank (colFlat (T t)).rank

with the auxiliary lemmas `rank_M_H` (rank M(H) = |α|⁴), `rank_M_le_flatB`, `rank_M_le_col`, `rank_pair_le` (a pairing
contraction does not raise rank) and `rank_le_card_mul` (splitting the columns by one coordinate).

### 7.3 The lossy diagonal lemma (any configuration) [R]

Fix 2-labellings σ_R of the rows and σ_C of the columns. Choose a set E of crossing edges. At any node, two legs may
be paired, which merges two edges into one path whose ends lie at other nodes. Choose an orientation for each edge or
path (one end in X, the other in Y). A kept end leg ℓ at node (r,c) placed on side Z has **row loss** [σ_R(r) ≠ Z]
and **column loss** [σ_C(c) ≠ Z]. Let s_R and s_C be the total losses. Then every decomposition into row- and
column-networks satisfies

  Σ_t 2^{cost_t} ≥ N^{|E| − max(s_R, s_C)}.

*Proof.* Fix all legs that are neither kept nor paired. The target becomes a permutation matrix of size N^{|E|}
across X | Y. In a row-network, put W_r on side σ_R(r). The bonds that cross have total dimension ≤ 2^{cost}, and every
leg with row loss crosses at dimension N. Pairings are inside one node, hence inside one W_r and inside one column
tensor. So rank ≤ N^{s_R}·2^{cost}. The same holds for column-networks with σ_C, and subadditivity finishes. ∎

Theorem 4 is the case σ_R: a, c ↦ X, b ↦ Y and σ_C: j' ↦ X, j ↦ Y. There |E| = 4 (edges 4–5, 4–3, 6–5 and the merged
path 6–1–2), s_R = 1 (u2) and s_C = 1 (v1). A labelling also reaches 3 without any pairing (`engine2d_lossy.out` (b),
"3x2 no-merge best 3"). Theorems 1–3 are the case s_R = s_C = 0.

### 7.4 Theorem 5 (full grid levels) [R], counts [N]

Classify the nodes as *agreeing* (σ_R(r) = σ_C(c), types A_X, A_Y) or *disagreeing* (D). A crossing edge between
an A_X and an A_Y node is free. An edge between an agreeing node and a D node costs exactly one loss, in the row budget
or in the column budget according to the types (A_X–D₁ and A_Y–D₂ cost a row loss, A_X–D₂ and A_Y–D₁ a column loss,
with D₁ = (X,Y) and D₂ = (Y,X)). For the g×g level, g = 2h, with balanced labellings: there are h⁴ free edges, and
2h³(h−1) edges of each single-loss type. Taking all of them gives |E| − max(s_R, s_C) = h⁴ + 2h³(h−1) = 3h⁴ − 2h³,
out of Q = h²(2h−1)².

**Theorem 5.** For every decomposition of the g×g level (g = 2h) into row- and column-networks,
Σ_t 2^{cost_t} ≥ N^{3h⁴−2h³}. Hence max_t cost_t ≥ (3h⁴−2h³)λ − log₂T and **ρ ≥ h(3h−2)/(2(2h−1)²) − o(1) → 3/8**.

`engine2d_lossy.out` (b) checks this by brute force (with the optimal choice of subset and orientation, over all
labellings for g ≤ 5): e − s = 8 of 9 (g = 3), 32 of 36 (g = 4), 84 of 100 (g = 5) and 189 of 225 (g = 6), so ρ ≥ 4/9,
4/9, 21/50, 21/50. Consequence for the cap: correlated network decompositions of full levels have **α' ≤ log₂(8/3)
≈ 1.415** (Theorem 3 gave 3). The loss of Theorem 3 to "only 1/4 of the rectangles are diagonal" is mostly
recovered. What is left is the A_X–A_X and A_Y–A_Y edges (Proposition 7.6).

### 7.5 What the earlier methods could and could not do (certificates) [R][L]

(a) **Common cuts give only N² on the 3×2 grid [R].** Apply node-local maps that keep, fix or pair legs, and take
any leg cut that is a union of rows and a union of columns on the kept legs. Then every row keeps legs at one node
only (otherwise both columns fall on one side), so the cut has one node, with ≤ 2 legs, on one side, and rank ≤ N².
The "fake profile" of three single-bond row-networks of cost 2λ plus a column term of cost 2λ satisfies every such
inequality. This is why Theorems 1–3 could not exceed max cost 2λ here. Straddling legs are necessary: in the
min-cut model of all node-local maps plus one flattening (`engine2d_grid32/cert.py`, all 3¹² capacity patterns), the fake profile is violated by 1392
patterns, and 10 patterns force cost ≥ 3λ for both kinds of terms. The first of these is exactly the contraction M
of Theorem 4 (`cert3.py`).
(b) **Row-local (or column-local) invariants are useless [L].** H is obtained from T0 = Π_q [x_q = u_q][y_q = v_q] by
swapping x_q ↔ y_q in each rectangle's top row (`Grid32.H_eq_rowTwist_T0`). That is a row-local relabelling, and T0 has
column rank 1 (`rank_colFlat_T0`). Dually, H is a column-local relabelling of J = Π_q [x_q = y_q][u_q = v_q], which has
rank 1 across the row-b cut (`H_eq_colTwist_J`, `rank_flatB_J`). Hence any subadditive functional that is unchanged
by row-local relabellings and bounded on column-networks of cost 0 takes the same value on H as on a cost-0 term. It
cannot prove anything. This is the precise form of §4's remark that "a functional local to the grid nodes is not
bounded on row-networks". A valid argument must use maps that are local to the *nodes* and then break the row
structure in a controlled way, which is what the straddling legs do.

### 7.6 Proposition (the 3/8 limit of the 2-party lossy method) [R]

For every choice in §7.3 (2-labellings; legs kept, fixed or paired at nodes; orientations):

  |E| − max(s_R, s_C) ≤ ½ · #{legs at agreeing nodes whose partner leg is not at an agreeing node of the same type}.

*Proof.* |E| − max ≤ |E| − (s_R+s_C)/2 = Σ_paths (1 − loss/2), and a path's value splits over its two ends: ½ for an
agreeing end on its natural side, 0 for a D end (loss exactly 1), −½ for an agreeing end on the wrong side (loss 2).
Suppose an agreeing natural end ℓ₀ has its partner at a same-type agreeing node. Its path must continue through
pairings at same-type nodes (otherwise both ends sit on one side). Let ℓ be the first consumed (paired) leg on that
path whose partner is not at a same-type node. Then ℓ₀ ↦ ℓ is injective, and ℓ is a "useful" agreeing leg that is not
an end. So the number of agreeing natural ends is at most the number of useful agreeing legs. ∎

On the full level with label densities p (rows) and q (columns), the useful agreeing legs number
4Q·[pq(1−pq) + p̄q̄(1−p̄q̄)] + O(Q/g). With a = √(pq), b = √(p̄q̄) we have a + b ≤ 1 (AM–GM), and
a²−a⁴+b²−b⁴ ≤ 3/8, with the maximum at a = b = 1/2. Hence the method gives at most (3/4 + O(1/g))Q, so **ρ ≥ 3/8 is the
limit of the 2-party lossy method on full levels**. For the 3×3 level the bound is exactly 8 (agreeing nodes: a 2×2
block plus one node; each block node wastes one leg). [N] (`engine2d_lossy.out` (c), exhaustive over
labellings and edge subsets): every sub-configuration of the 3×3 grid with ≤ 8 rectangles, all configurations on the
4×2 grid, and all configurations with ≤ 7 rectangles on the 5×2 grid reach |E| − max = Q. So ρ ≥ 1/2 holds for all of
them, and the full 3×3 level is the smallest configuration found where the method falls short.

### 7.7 λ = 1 data [N]

At N = 2, after the node-local twist by ε at the even nodes, H is the matching of the six hexagon edges inside the
132-dimensional SL₂-invariant space of the 12 legs. A perfect matching m of the legs is simultaneously a row-network
of cost r(m) (pairs between rows) and a column-network of cost c(m). (`engine2d_grid32.out`, scripts in
`engine2d_grid32/`.)

* H is not in the span of cost-0 matchings (dimension 32), nor in that span plus any single cost-2 matching. It lies
  in the span of matchings of min-cost ≤ 2.
* MILP (HiGHS, terms counted separately): minimum Σ 2^{min(r,c)} ≥ 17 (dual bound, 300 s). The best found is 24 with six
  matchings, or 22 once its three column-type matchings are grouped into one column term of rank 10. The product
  decomposition gives 26, and the bound of Theorem 4 is 8.
* The weight 2^{(r+c)/2}, which governs tensor powers of λ = 1 decompositions, has minimum ≥ 38 > 8. So no λ = 1
  matching decomposition, tensored, gets below N³ in rank sum, even with exponentially many terms.
* These are consistent with Theorem 4, which makes them moot for the asymptotic question. They are not formalised.

### 7.8 Lean status (this section)

| claim | status |
|---|---|
| Theorem 4: Σ_t min(rk_{b\|ac}, rk_col) ≥ \|α\|³ for every family summing to H (3×2 grid, any field, any alphabet) | **Lean-proved (general)**: `Grid32.rankSum_ge`, `Grid32.exists_expensive`; axioms [propext, Classical.choice, Quot.sound] |
| rank M(H) = \|α\|⁴, rank M(T) ≤ \|α\|·rk_{b\|ac}(T), rank M(T) ≤ \|α\|·rk_col(T) | **Lean-proved (general)**: `rank_M_H`, `rank_M_le_flatB`, `rank_M_le_col` |
| no-go (b): H is a row-local relabelling of a column-rank-1 tensor and a column-local relabelling of a row-rank-1 tensor | **Lean-proved (general)**: `H_eq_rowTwist_T0`, `rank_colFlat_T0`, `H_eq_colTwist_J`, `rank_flatB_J` |
| row-network ⇒ rk_{b\|ac} ≤ d_ab d_bc ≤ 2^{cost}; column-network ⇒ rk_col ≤ 2^{cost} | [R] (Lemma 1.1-type, as in §1); not formalised |
| lossy diagonal lemma (§7.3), Theorem 5 (ρ ≥ 3/8 on full levels) | [R]; counts [N] for g ≤ 6; not formalised (needs a general configuration framework) |
| Proposition 7.6 (method limit 3/8), certificate (a) | [R]; min-cut model [N]; not formalised |
| λ = 1 matching data | [N] only |

### 7.9 What remains

1. **The full 3×3 level** (Q = 9). Proved S ≥ N⁸ (ρ ≥ 4/9). The 2-party lossy method is capped at 8 there. Wanted:
   S ≥ N⁹, or a decomposition with max cost ≤ (9−ε)λ. Candidates for the proof: m-party (CVZ) functionals with
   straddling legs, or a contraction that is not a single flattening.
2. **Full levels:** 3/8 ≤ ρ (proved). ρ ≥ 1/2 would close the c/log K cap for all correlated network decompositions.
   The obstruction to the method is exactly the A_X–A_X and A_Y–A_Y edges.
3. Lean: the lossy lemma for general configurations, and Theorem 5.
