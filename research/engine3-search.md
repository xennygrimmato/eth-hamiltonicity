# Engine 3: searches past the k-local barrier on Majdoddin's C, plus framework checks

5 Nov 2026. Scripts: `research/scripts/engine3/` (outputs `*.out` next to them). Sources: Anthropic
(hexagon:2610.00577) §2.4–2.5, Lemma 2, Def. 7, App. B, App. H; Majdoddin (arXiv 2610.41622) Def. 2.3, Def. 4.2 (L1–L5),
Prop. 4.23 (§4.7). Tags: **[R]** proved here (on paper), **[N]** exact computation (rational arithmetic via mod-p
ranks, p = 2³¹−1, or entrywise integer checks), **[C]** heuristic (real ALS, SAT timeouts), **[K]** known.

## 0. Summary

* **[R][N] The k-local barrier on C (Prop. 4.23) does not hold for non-local terms, and the gain is asymptotic.**
  The configuration C has one more structure that Prop. 4.23 does not use. Under merge 1, the six edges of C form three
  crossings (pair j = {a_j a_{j+1}, b_{j+1} b_{j+2}}). Under merges 0 and 2, each such crossing meets three groups, in
  the groupings {x}|{y,v}|{u} and {x,u}|{v}|{y}. Both refine the crossing's *column* split. So a crossing piece that is
  cheap column-wise can be evaluated under merge 0 or 2 by **routing one leg into a neighbouring group** (one bond of λ bits)
  and then using its column factorisation. Such a piece is non-local (it couples two bundles of merge 0), so it has
  full rank across Majdoddin's Q while it is cheap under merge 0.
  - Finite, exact: f_C = P⊗F⊗F + B⊗F⊗F (P = [x=u][y=v] and B = F − P on one pair; terms evaluated under merges 0 and 1)
    has two terms and network costs **5 and 4 bits at N = 2** (rank sum S = 48 < N⁶ = 64). At N = 3 the costs are
    5·log₂3 and 5·log₂3 (S = 486 < 729). At N = 4 they are 10 and 10.585 bits (S = 2560 < 4096). Term P⊗F⊗F has rank
    N⁶ across Q but costs 5λ, which is impossible for k-local pieces (Prop. 4.23(b)). This is only a constant-factor gain
    at one block.
  - Asymptotic, rigorous given Anthropic's pieces: with any crossing pieces of parameter ρ_x (Def. 7:
    c_row + c_col ≤ 4ρ_x λ + O(log λ), poly(λ) pieces) used on the three merge-1 crossings of C, and the routing
    evaluation, every term costs at most **(ρ_x + 1/4)·6λ + o(λ)** under its best merge. With App. B (ρ_x = 1/√2) this is
    **ρ_C ≤ 0.957 < 1**. With the App. B per-piece profile (c_row² + c_col² ≤ 4λ²) it is 0.911. Ideal crossing pieces
    (ρ_x = 1/2) would give 3/4 under this pessimistic accounting, and 2/3 if only the two extreme piece types occur.
    The eight-square pieces of Lemma 2 (ρ_x = 11/12) give nothing, and neither does any ρ_x ≥ 3/4.
  - These numbers stay far above 1/2. This route does not give the ρ < 1/2 that C was meant to give.
* **[R] Lower bounds on C for arbitrary (non-local) terms.** For network cost (and for c_flat) every decomposition has
  Σ_t 2^{(2/3)c_t} ≥ N², so max cost ≥ 3λ − O(log T), i.e. ρ_C ≥ 1/2. The proof fixes all b-legs, which leaves the
  a-triangle, a 3-party graph tensor in which every merge puts a_0, a_1, a_2 in distinct groups; then the uniform CVZ
  functional applies [K]. The whole flattening method (lossy keep/fix/pair contractions, all inequalities combined,
  §8.2 of engine2-decorrelated) certifies only **D_C = 2**, i.e. ρ ≥ 1/3 [N, exhaustive over all 3⁶ oriented edge sets].
  So the proved window on C for non-local terms is **[1/2, 0.957]**.
* **[N] Framework checks (task A).** Eight-square: R + C = 2[x=v][y=u] at all 4096 settings. R has ranks 8 and 64
  (row, column), C has 64 and 8. The Lemma 2 pieces at t = 2 have exact ranks 64/4096, 960/960 and 4096/64, which
  match App. H's eigen-count formula; its limit is 2 + log₂448 = 10.81 of 12 bits. Single-bit identity: P has ranks
  (4, 1) and B has (1, 4). The exact ranks of the rank-counted pieces match Σ_{z≤i} C(t,z)3^z for every t ≤ 5 and every
  i, and the worst piece tends to log₂12 = 3.585 of 4 bits (3.057 at t = 5).
* **[C] Searches below the two-term decomposition found nothing.** At N = 2, ALS stalls at residual ≥ 0.36 on every
  profile with S ≤ 40, and GF(2) SAT timed out on every profile, including the known S = 48 one. At N = 3 every profile
  cheaper than the known S = 486 stalls at residual ≥ 0.58.
* **Task C (hub ansatz on the 3×3 level at N = 4) was not run. It cannot be set up as a finite exact problem of a size
  that can be computed** (§4). Instead §4 states the smallest exact sub-question that I think is decidable.
* **Task D (reduced).** K4 with its three 2+2 merges at N = 2: rank sum S = 8 = N³ (input floor) is achieved by the
  single-bit identity on one matching. S ≤ 4 is exactly impossible over GF(2) [N, SAT UNSAT]. The flattening method
  certifies only N² there (D = 2). The S = 5–7 results are in §5.

## 1. Definitions implemented (`lib.py`)

* **Configuration**: nodes, edges (each edge is an equality of two strings of λ bits, with one leg at each end), and
  merges (partitions of the nodes). The target is the graph tensor ⊗_e I_N. Majdoddin's C: triangles {a_i}, {b_i},
  i ∈ Z₃; merge k has groups {a_i, b_{i+k}} (identical to his `config()` in `r123_idsearch.py`: strings X(i,j) at a_i,
  Y(i,j) at b_i, merge k pairs X(i,j) with Y(i+k, j+k)). Also the crossing (rows/columns), the hexagon = 3×2 grid
  (rows = antipodal pairs, columns = colour classes) and the 3×3 level K₃×K₃ (rows, columns).
* **(L4) cost of a term T under merge k.** Majdoddin defines it only for configurations that meet ≤ 2 groups. There it
  is log₂ of the rank across the split, summed over pieces, which is the edge weight of the merged instance. For terms
  that meet 3 groups (non-local, or "hyperedge" in his language) I implemented three variants:
  - **c_net** (the natural extension of (L4)): T is written as a triangle network on the groups, with arbitrary local
    tensors W_g on the legs of group g and bonds d_gh, and the cost is Σ log₂ d_gh, i.e. the bits of the merged
    instance. This is what the recursion pays. It is computed only as an upper bound, by explicit constructions or a
    search (SAT/ALS) at fixed bonds.
  - **c_flat** = min Σ e_gh s.t. Σ_{g∈S, h∉S} e_gh ≥ log₂ rank(T; S | rest) for all S (an LP; for 3 groups it is
    max(max_g r_g, (r_0 + r_1 + r_2)/2) with r_g = log₂ rank(G_g | rest)). This is a lower bound for c_net. It equals
    Majdoddin's charge on k-local pieces. Exact ranks.
  - **c_max** = max_g log₂ rank(G_g | rest) (coordinator's variant). It is weaker still: c_max(f_C) = 4λ, not 6λ (`cmax_C.out`).
  - A pure 3-party hyperedge cost (log of CP rank across the groups) is *not* comparable. f_C under one merge is the
    matrix-multiplication tensor ⟨N², N², N²⟩, so already one term costs 2ωλ in that accounting (5.61 bits at N = 2 via
    Strassen). I did not use it.
* **Min over merges**: a term is charged min_k c_k(T). The finite figure of merit is the rank sum S = Σ_t 2^{c(T_t)}
  (floors on C: N⁶ for k-local terms by Prop. 4.23; N² in the 2/3-power form for all terms, §0).
* **Asymptotic figure (product identities, (L2)).** One block identity per crossing (m = λ), with piece cost vectors
  (c₀, c₁, c₂). A term chooses a piece per crossing and is charged min_k Σ c_k. Then ρ ≤ max over mixtures p of
  min_k E_p c_k/(2λ) (an LP, `pair_game.py`). The LP can only overestimate, since real terms are mixtures of three atoms.

## 2. Task A: checks (`verify_A.py` → `verify_A.out`) [N]

| object | computed | App. H |
|---|---|---|
| eight-square R + C = 2F (N = 8) | true at all 4096 settings | (12)/(31) |
| R row/col rank, C row/col rank | 8 / 64, 64 / 8 | "ranks 8 and 64" |
| simple count per 3-bit block | 3 + 6 + 2 = 11 of 12 | 11 of 12 |
| Lemma 2 pieces, t = 2: (row, col) ranks of A₀, A₁, A₂ | (64, 4096), (960, 960), (4096, 64) | formula Σ_{z≤i} C(t,z)(N²−N)^z N^{t−z}: same |
| rank count, t → ∞ | 2 + log₂448 = 10.807 of 12 | 10.81 |
| single-bit F = P + B | true; P (4, 1), B (1, 4) | identity of App. H |
| its pieces A_i, t ≤ 5 | exact ranks = Σ_{z≤i} C(t,z)3^z (row), same with t−i (col), all i | eigenspaces 1 and 3 |
| worst piece, bits per bit | 2.000, 2.807, 2.844, 3.033, 3.057 (t = 1..5) → log₂12 = 3.585 | log 12 ≈ 3.58 of 4 |

## 3. Task B: Majdoddin's C with non-local terms

### 3.1 Structure used [R]
Pair j (j ∈ Z₃): x = X_{j,j+1} @ a_j, v = X_{j+1,j} @ a_{j+1}, y = Y_{j+1,j+2} @ b_{j+1}, u = Y_{j+2,j+1} @ b_{j+2}, so f_C =
Π_j [x_j = v_j][y_j = u_j] (`cpieces.py`). Merge 1: the pair is the bundle G_j | G_{j+1} with split {x,y}|{u,v} (row
split). Merge 0: x ∈ G_j, {y,v} ⊂ G_{j+1}, u ∈ G_{j+2}. Merge 2: {x,u} ⊂ G_j, v ∈ G_{j+1}, y ∈ G_{j+2}. Both 3-group
groupings refine the column split {x,u}|{y,v}. Consequences:
* P = [x=u][y=v] is a product of one bond (x–u, λ bits) and a factor internal to a group under merge 0 (and dually
  under merge 2). So c_net = c_flat = λ, while rank_Q(P) = N² (both of its equalities cross Q). Per pair, P costs
  (λ, 2λ, λ) and the single-bit B costs (2, 0, 2) bits (`pair_game.out`, m = 1).
* **Routing bound.** Any pair piece with column rank 2^{c_col} has c_net ≤ λ + c_col under merges 0 and 2 (send x to
  u's group, then factor across {x,u}|{y,v}), and ≤ 2λ always. Under merge 1 it costs c_row (it is 1-local there).

### 3.2 Finite decompositions (`explore_C.py`, `two_term_C.py`, `cmax_C.py`) [N]
* f_C cost vector (6, 6, 6)λ. rank_Q(f_C) = N⁶ (Prop. 4.23(a)), checked.
* Products of {P, B} on the three pairs at N = 2: costs (c₀, c₁, c₂) of PPP (3, 6, 3), PPB (4, 4, 4), PBB (5, 2, 5),
  BBB (6, 0, 6) (and permutations). rank_Q = 64, 16, 4, 1. So PPP and PPB have rank_Q > 2^{cost}: they are non-local
  pieces beating the Q-bound. The 8 products charged separately give S = 69.
* Best grouping of the 8 products into ≤ 3 summed buckets (one per merge, c_flat, exhaustive over 3⁸ assignments):
  **S = 48** = 2⁵ + 2⁴. The buckets are {P⊗·⊗·} = P⊗F⊗F under merge 0 and B⊗F⊗F under merge 1.
* The two-term decomposition f_C = P⊗F⊗F + B⊗F⊗F is exact over ℤ for every N. Network costs (explicit, = c_flat):

| N | cost P⊗F⊗F (merge 0) | cost B⊗F⊗F (merge 1) | S | N⁶ | max cost / 6λ |
|---|---|---|---|---|---|
| 2 | 5 | 4 | 48 | 64 | 5/6 |
| 3 | 7.925 (= 5 log₂3) | 7.925 (rank_row B = 3) | 486 | 729 | 5/6 |
| 4 | 10 | 10.585 (rank_row B = 6) | 2560 | 4096 | 0.882 |

  For general N, rank_row(B) = N(N−1)/2, so S = N⁵(N+1)/2 and max cost = 6λ − 1 + o(1): a factor ~2, not an exponent.
* c_max variant: c_max(f_C) = 4λ already. c_max(PPP) = 2λ under merges 0 and 2. P⊗F⊗F and B⊗F⊗F have c_max 4λ.
* **SAT over GF(2), N = 2** (`sat_C.py` → `sat_C.out`; triangle networks with fixed bonds; glucose4, 150 s per profile).
  Even the known S = 48 profile (merge 0 bonds (2,8,2) plus merge 1 (1,4,4)) **timed out**. At this size (4096 cubic
  XOR constraints, ≥ 10⁵ AND gates) SAT decides nothing within the budget. All 7 profiles that ran (the S = 48 sanity
  profile, four S = 32 two-term profiles, two S = 24 profiles) **timed out**. I stopped the run then. **No exact GF(2)
  statement about S < 48 on C was obtained.**
* **ALS over R** (`als_C.py`; block least squares, 150 sweeps × 4 restarts at N = 2) [C]: the known S = 48 profile
  converges (residual 2.7·10⁻¹⁰). Every profile with S ≤ 40 stalls at residual ≥ 0.36: (2,2,4)+(2,2,4) in several
  placements 0.62; three terms (2,2,2) 0.73; three terms (2,2,4) 0.36; (4,4,2)+(2,2,2) 0.51; (2,4,2)+(1,4,4) 0.51. Another
  S = 48 profile, (2,4,4)+(2,2,4), stalls at 0.11. At N = 3 the analogue of the known decomposition (S = 486) converges
  to 10⁻⁸. Cheaper N = 3 profiles all stall: (3,9,9)+(3,9,9) at S = 486 gives 0.58, two S = 324 profiles give 0.60 and 0.77, and
  three terms at S = 243 give 0.78. So no decomposition below S = 48 (N = 2) or below S = 486 (N = 3) was found [C].
  Best found trade-off: **2 terms, max cost 5λ of 6λ (N = 2, 3)**, against the k-local floor (every k-local
  decomposition has S ≥ N⁶ and a term of cost 6λ − log₂T).

### 3.3 Asymptotics through the merge-1 pairing (`pair_game.py` → `pair_game.out`)
Per crossing (2λ bits), pieces with costs (c₀, c₁, c₂) under merges (0, 1, 2); ρ_C = LP game value / 2λ.

| piece family on each crossing | cost used for merges 0, 2 | ρ_C | status |
|---|---|---|---|
| k-local pieces (Prop. 4.23) | — | 1 | [K] |
| single-bit identity, rank-counted A_i (m bits, m → ∞) | c_flat (lower estimate) | 0.929 | [N] ranks; c_flat is not a cost |
| same | routing network | 1.000 | [R] |
| same, finite m = 1..4 (per-block game, ignores the log(m+1)/m naming entropy) | c_flat / routing | 0.667/0.667, 0.770/0.813, 0.807/0.896, 0.824/0.935 | [N] |
| Lemma 2 eight-square (ρ_x = 11/12) | routing | 1 | [R] |
| any crossing pieces with ρ_x ≥ 3/4 | routing | 1 | [R] |
| **any Def. 7 pieces with ρ_x < 3/4** | routing | **ρ_x + 1/4** | [R] (LP over the whole segment; checked numerically at ρ_x ∈ {0.5, 0.7, 0.707, 0.72, 0.74, 0.749}) |
| **App. B (ρ_x = 1/√2)** | routing | **0.957** | [R] given Anthropic's App. B |
| App. B with per-piece profile c_row² + c_col² ≤ 4λ² | routing / c_flat | 0.911 / 0.800 | [R] if that profile holds (Majdoddin's description of App. B's shape) |
| ideal two-type pieces (row (2,0), col (0,2)) | routing (= c_flat here) | 2/3 | needs ρ_x = 1/2, open (Naslund Problem 12) |

Is c_flat achievable as a network for the rank-counted pieces? ALS [C] (`als_net.py` → `als_net.out`) says no at small m.
A_{m=2,i=1} under merge 0 with any 4-bit bond triple: residual ≥ 0.39 (c_flat 3.40). A_{m=3,i=2} with 5-bit triples:
residual ≥ 0.41 (c_flat 4.66), and with the 6-bit triple (4,2,8) still 0.27. The 2m-bit routings (8,1,8) and (4,1,4)
converge. So for this family c_net appears to be full (2m), and ρ = 1, not 0.929.

Why the gain caps where it does: under merges 0/2 a crossing is never cheaper than its column cost, and the routing
pays one extra λ. The adversary mixes a row-full piece (c_row = 2λ, c₀ = (4ρ_x − 1)λ) with a column-unit piece
(c_col = λ, c₀ = 2λ), which gives ρ_x + 1/4.

### 3.4 Lower bounds on C (`cert_flat.py` → `cert_flat.out`)
* [R] CVZ on the a-triangle (b-legs fixed): Σ_t 2^{(2/3)c_t} ≥ N² for c_net and for c_flat (rank(a_i | rest) ≤ rank(G_i | rest)
  because fixing legs gives a submatrix; F^θ ≤ Π rk^{1/3} ≤ 2^{(1/3)Σ r_g} ≤ 2^{(2/3)c_flat}). Hence ρ_C ≥ 1/2. For
  c_max this gives only Σ 2^{c_max} ≥ N².
* [N] Flattening optimum. For a lossy contraction with net group outflows n_g, d_k = |n₁| (2 groups) or
  max(max|n_g|, Σ|n_g|/2) (3 groups), and D = max over oriented edge subsets of min_k d_k. Values: crossing D = 1,
  hexagon D = 3 (= Theorem 4, sanity), **C: D = 2** (with only one or two of its merges: 4), **K4 with three 2+2 merges:
  D = 2**. On C the flattening world is strictly weaker than CVZ.
* Rank triangle inequality (coordinator's item 3): every 4-leg pair piece used here (P, B, F, A_i) satisfies it,
  necessarily so by Song–Chen–Sun–Hu (Majdoddin Prop. 4.22). The non-local effect lives at the 12-leg level (rank_Q vs
  merge cost), not in a violation of that inequality.

## 4. Task C (3×3 level, hub ansatz at N = 4): not run, and why

* The target has 36 legs. At N = 4 it has 4³⁶ ≈ 4.7·10²¹ entries. A hub term R_c has W_c on 12 legs plus bonds
  N⁴ × N⁴, i.e. 4²⁰ ≈ 10¹² unknowns, and the shape of W_a, W_b is exactly what is unknown. With W_a, W_b fixed to
  routings (pass 4 of row a's legs to c, fix the rest to vectors), the span is a sum of products with fixed vectors on
  ≥ 8 legs per side. Such terms cannot produce the identities on those legs without the column terms doing the same
  thing, so any fixed-shape linear system small enough to solve is a product ansatz. Products are excluded by §4.3 of
  clique-evaluation.md ("products force ρ ≥ 1/2"). I found no shape family that is both genuinely non-product (as §8.6
  requires) and of solvable size, so I report no feasible/infeasible verdict.
* Observation: R_c cannot even carry the six a–c identities, since 6λ > 4λ = log d_ac. So hub terms are far from
  every piece-built term. Cancellation must create both the a–b and the a–c structure.
* Smallest exact sub-question I would try next: the 3×3 level at N = 2 with *two-layer* terms (terms of the form
  X⊗Y over the two bits of N = 4, each layer a hub at N = 2). The fiber of the hub condition across layers is linear,
  but it is still 2³⁶ per layer. It is only feasible with the bit-flip/Pauli symmetry reduction (the target is invariant
  under X^{⊗2} on every edge), which I did not implement.

## 5. Task D (K4, reduced) (`k4.py` → `k4.out`)
Model: K4 with the three 2+2 merges (each merge keeps one perfect matching inside groups). A term under merge k is any
tensor, charged log₂ rank across the split, so one term per merge suffices and S = r₀ + r₁ + r₂. Results at N = 2 over
GF(2): S ≤ 4 UNSAT (all rank profiles, exact). S = 8 = N³ is achieved over ℤ by [x=v][y=u] = P + B on one matching
(merge 1 term P⊗rest of rank 4, merge 0 term B⊗rest of rank 4). The flattening certificate gives only S ≥ N² (D = 2).
S = 5: rank profiles (5,0,0) and (4,1,0) are UNSAT; (3,2,0), (3,1,1), (2,2,1) timed out. S = 6: all 7 profiles timed out
(glucose4, 90 s each). I stopped there. So the exact GF(2) minimum at N = 2 lies in {5, 6, 7, 8}. Comparison with N^{23/6} is not possible at N = 2 (1.0 vs 2^{3.83}:
the construction is a rectangular-matrix-multiplication statement at ω = 2 and has no meaningful N = 2 analogue). I
did not attempt it.

## 6. What I would try next

1. **Make the routing bound sharp, or find better merge-0 evaluations of crossing pieces.** The gap between c_flat and
   the routing network decides 0.80 vs 0.91 for App. B pieces. The concrete question: for App. B's A_s, viewed as a
   3-party tensor on {x}|{y,v}|{u}, is the triangle-network cost below λ + c_col? ALS at small sizes (as in `als_net.py`)
   needs an implementation of App. B pieces at small h.
2. **Pieces designed for C instead of the crossing.** The per-crossing game only sees costs (c₀, c₁, c₂) = (≥ c_col, c_row, ≥ c_col).
   A piece on a whole merge-1 bundle pair, or on all six edges, that is cheap under the 3-group groupings for reasons
   other than its column rank is the remaining possibility. Prop. 4.23 rules out only k-local ones, and §3.4 rules
   out ρ < 1/2.
3. **Exact decision at N = 2 needs a better encoding than plain CNF** (XOR-aware solver such as CryptoMiniSat, or
   symmetry breaking by the GL₁ gauge freedom on bonds and the Z₃ symmetry of C). The present encoding cannot even
   recover the known S = 48 solution in 150 s.
4. Task C: the symmetry-reduced two-layer hub ansatz of §4.

## Files
`lib.py` (ranks mod p, flattenings, c_flat LP, configurations), `cpieces.py` (pair structure of C), `verify_A.py`,
`explore_C.py`, `two_term_C.py`, `cmax_C.py`, `pair_game.py`, `als_net.py`, `als_C.py`, `sat_C.py`, `cert_flat.py`,
`k4.py`; outputs `*.out` (als_C2/als_C3 for N = 2/3). Disk use: < 200 KB.
