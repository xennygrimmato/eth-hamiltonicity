# Engine 3, Δ_3 at N₀ = 4 (task b) and N₀ = 2 with T = 4 types (task a)

Scripts and outputs: `research/scripts/engine3-delta3b/` (each `X.py` has an `X.out`; `d3lib.py` is copied from
`engine3-delta3/` with two matmuls switched to einsum for speed, same maths). [C] exact computation (network min-cut
bounds and ranks of restricted f; valid over every field), [N] numerical, [R] reasoning. Setting and criterion:
`engine3-open-door.md` §1.7, §3.2–3.2a. Throughout, the cost of a type τ under a merge is its D1 cost (min over triangle
networks on the merge's three groups of Σ log₂ bond dims), ν₃ = 3/2, and the criterion is the exact game value

  V(τ_1..τ_T) = max_{x∈Δ_T} min_k Σ_j x_j c_k(τ_j) + (3/2) log₂T,   ρ < 1/2 certified iff V < E m₀/2,  any trade iff V < E m₀.

(E m₀ = 9 m₀.) The per-type form "c₁ + c₂ + 3 log₂T < 9 m₀" is the special case of transpose-symmetric families.

## 0. Verdict

* **(b) N₀ = 4, ρ < 1/2: refuted exactly for every number of types T, every shape, every (real) bond dimension [C+R].**
  * R(4,4,4) + C(4,4,4) (the literal task) dies at the bit-doubled N₀ = 2 certificate o*: rank f = 2¹⁸, each term ≤ 2¹⁴
    (slack −229376). The 3·log₂2 = 1.5 bit budget of T = 2 needs every type to have other-merge cost < 9; it is irrelevant here.
  * T = 2, all shapes: three orientations of rank 2¹² suffice (§1.2). T = 3, all shapes: three orientations (§1.3).
    T ≥ 4: one orientation and pigeonhole give V ≥ 9 (T = 4 exactly 9, so not < 9).
  * So at N₀ = 4 the §1.7 count cannot certify ρ_Δ < 1/2 with any family of piece types, exactly as §3.2a found at N₀ = 2.
    This refutes the *criterion* (a sufficient condition); it does not prove ρ_Δ ≥ 1/2.
* **4/9 floor at N₀ = 4 [C]:** the net-flow (flatcert) floor is D = 4 of 9 at N₀ = 2, at N₀ = 4 (all 6⁹ bit orientations)
  and for fractional orientations (N₀ → ∞, 36 LPs). The finite refutations above come from the (3/2) log₂T charge and the
  per-type min-cut shapes, not from a higher floor.
* **(a) N₀ = 2, T = 4 (two row-(2,2,2) and two column-(2,2,2) types), any trade: not refuted by flattenings [C]; ALS finds
  nothing [N].** Hub other-merge shapes (one column alone on its side) are refuted exactly. General column shapes are not:
  455 integer column triples with product ≤ 511 pass the full flattening test in the transpose-symmetric family, the cheapest
  (5,6,6) (cost 7.49, V = 8.25 < 9). ALS: see §2.

## 1. Task (b), N₀ = 4 [C]

### 1.1 Bit orientations (`flat_bits.py`)
Each of the 9 edges carries 2 bits; each bit is fixed (restriction) or split X→Y / Y→X. Per edge only (p,m) = (#X-side at
lower node, #Y-side) matters: 6 states, 6⁹ = 10 077 696 orientations, rank of restricted f = 2^(Σp+m). Bound for a row (column)
triangle network with log-bonds x: min over the 8 side assignments of (opposite legs + cut bonds). Best network of total cost a
(LP, closed form validated against HiGHS on 600 instances, `flat_b_T2.py`):
  Φ_o(a) = min(L_const, min_g M_g + a, (M₀ + M₁ + M₂ + 2a)/3).
At o* (bit-doubled N₀ = 2 certificate): Φ(a) = min(18, 10 + a, (38 + 2a)/3): R(4,4,4) → 14, R(8,8,8) → 16, cost-8 hub
(16,16,1) → 18 (full).

| test (all 6⁹ bit orientations) | result |
|---|---|
| R(4,4,4)+C(4,4,4) | worst slack −229376 (2¹⁸ vs 2·2¹⁴) refuted |
| R+R+C (4,4,4) | worst slack −212992 refuted |
| one-orientation pigeonhole, forced type min(c_row,c_col) ≥ θ(T); V ≥ θ + 1.5 log₂T | T=2: 7 + 1.5 = 8.5; T=3: 6.415 + 2.377 = 8.79 (not refuted); T=4: 6 + 3 = 9.0; T=6: 9.29; T=8: 9.5; T=16: 10; T=64: 11 (refuted) |

T ≥ 4 in general: at the binding orientation (rank 2¹²) the inverse of Φ has slope ≤ 3/2, so θ(T) + 1.5 log₂T ≥ 9 for
log₂T ∈ [2,6], and 1.5 log₂T ≥ 9 for T ≥ 64 [R on top of C].

### 1.2 T = 2, every shape (`flat_b_T2.py`, `flat_b_cut.py`, `cert_b.py`)
V < 9 forces min(c_row, c_col) < 7.5 for both types. Two row-cheap types: (row g | rest) has rank 4⁶ = 2¹² but each has
rank ≤ 2^7.5 there. So τ₁ = R is row-cheap (a₁ < 7.5) and τ₂ = C column-cheap (b₂ < 7.5), with other costs a₂, b₁, and V < 9 ⟺
(a₂ − 7.5)₊(b₁ − 7.5)₊ < (7.5 − a₁)(7.5 − b₂) [R]. Three orientations of rank 2¹², normalised bounds Φ − 12 [C]:
  o₁ (rows 0,1 → row 2): row min(0, a−12, 2a/3−8), column 0;  o₂ = τ(o₁): row 0, column min(0, a−12, 2a/3−8);
  o₃: row and column min(0, a−8, 2a/3−16/3).
At o₁, R carries < 2^−4.5, so C needs ≥ 1 − 2^−4.5 there, hence b₁ ≥ 12 + log₂(1 − 2^−4.5) = 11.935. By o₂, a₂ ≥ 11.935.
o₃ needs 2^(a₁−8) + 2^(b₂−8) ≥ 1, so (7.5 − a₁)(7.5 − b₂) ≤ 0.25 (at a₁ = b₂ = 7). Then 4.435² = 19.67 > 0.25 [R]. Machine check
(cost-only relaxation, all shapes, valid for real costs by rounding up): a cutting plane over all 10⁷ orientations on grid h = 1/4
(11.4 M points) leaves 0 survivors after these 3 orientations, and so does the h = 1/16 recheck. The largest symmetric cheap
cost refuted by one orientation alone is A* = 7.0 (needed 7.5), so the three orientations are needed together.

### 1.3 T = 3, every shape (`flat_b_T3.py`)
θ = 9 − 1.5 log₂3 = 6.6226. V′ is attained on an edge of the simplex, so V < 9 ⟺ every type has min < θ and every
(row-cheap, column-cheap) pair meets the two-line condition. Three row-cheap: 3·2^θ < 2¹². By τ only 2 row-cheap + 1
column-cheap remains. Cutting plane, h = 1/4, column costs of the R's set to the supremum the pair condition allows (a valid
relaxation): 1 239 112 points, 0 survivors after 3 orientations (ranks 2¹², 2¹⁴, 2¹²). All three are bit-doubled N₀ = 2
orientations (states (2,0)/(0,2) only).

### 1.4 What was not run
The prompt's Z₃×Z₃ / τ-symmetric factorised ALS for (b) is unnecessary: every family it could find is refuted exactly above.

## 2. Task (a), N₀ = 2, T = 4

Exact criterion for types R_i = (3, 3+u_i), C_j = (3+v_j, 3): V = 3 + UV/(U+V) + 3 < 9 ⟺ 1/U + 1/V > 1/3 (U = max u_i,
V = max v_j). The symmetric case is other-merge cost < 9 (the note's 17 < 18 uses ranks product ≤ 2⁸, a sufficient
sub-case). Generic row (2,2,2) networks have column-group ranks (64,64,64), so column cost ≥ 9 (`generic_ranks.py`, exact mod
32749): every solution's pieces lie on a proper subvariety.

### 2.1 Flattenings (`flat_a.py`, `flat_a_lp.py`, `flat_a_shapes.py`, `flat_a_check.py`) [C]
* 2R(2,2,2)+2C(2,2,2) with no coupling: worst slack 0 (270 orientations tight). Those 270 alone force nothing: the cheapest
  column shape compatible with them is (2,2,2).
* Shape-relaxed (best other-merge shape chosen per orientation): passes for budget ≥ 5, refuted at ≤ 4 (−192).
* Hub other-merge shapes, every hub group, ranks (16,16), (16,31), (8,63), (4,64), (32,15), (2,64), (64,1), (8,8), (4,4),
  and all 36 mixed hub-group combinations: refuted (worst slack −192 … −432, at o = all + or similar).
* Integer column triples t, product ≤ 511 (12 544; 369 maximal), transpose-symmetric family: 455 pass (102 maximal). The
  cheapest are (5,6,6) (cost 7.492, V = 8.246), (5,6,7) and (6,6,6) (7.755). 16 392 unordered pairs of maximal shapes pass.
* Asymmetric game options tested: R column (4,4,3)/(4,4,2)/(3,3,3) with C unconstrained, refuted; (4,4,4)², refuted.
So flattenings cannot refute (a): (6,6,6)² and (8,8,7)² pass with slack 0.

### 2.2 ALS (`als_a.py`) [N]
Penalty ALS. Objective ‖f − ΣP‖² + μ Σ‖P_i − Q_i‖², where P_i is the cost-3 network and Q_i the other-merge network.
Every block is solved by exact least squares, with μ ramped 0 → 10. Score = max(residual, mismatch, both-sides residual).

| run | restarts × sweeps | min score | median | |
|---|---|---|---|---|
| planted control: f′ = 4 pieces, each a sum of 2 node-products, couplings (8,8,7) | 3 × 300 | 0.0076 | 0.087 | still descending (0.0074 / 0.087 / 0.234) |
| f_Δ, 2R(2,2,2)+2C(2,2,2), no coupling (a superset of every (a) family) | 20 × 400 | 0.950396 | 0.9685 | |
| same, long | 6 × 1500 | 0.952188 | 0.9667 | |
| f_Δ, couplings (6,6,6)/(6,6,6) (passes flattening, V = 8.38) | 8 × 200 | 0.968265 | 0.9683 | mismatch ≤ 0.008 |
| f_Δ, couplings (8,8,7)/(8,8,7) (V = 8.90) | 8 × 200 | 0.966787 | 0.9698 | mismatch ≤ 0.017 |

Even without the other-merge constraint, 2R(2,2,2)+2C(2,2,2) stays at relative residual ≥ 0.950, i.e. it captures under
10% of ‖f‖². The coupled runs sit at 0.967–0.968. The planted control shows the coupled solver does move toward an exact
solution when one exists, although slowly. No residual came near 10⁻⁸, so no exact reconstruction was attempted.
**[N] negative, not a proof:** the exact status of (a) is open. It is not excluded by any restriction flattening, and the
uncoupled four-term problem f = 2R + 2C (flattening slack 0) is itself undecided exactly.

## 3. What this leaves
* At N₀ = 2 and N₀ = 4 the §1.7 piece-type count cannot give ρ_Δ < 1/2 with any T [C at N₀ = 4; R at N₀ = 2 in §3.2a].
  All certificates are bit-doubled N₀ = 2 restrictions. The flatcert floor stays 4/9 at every N₀, so as m₀ grows the fixed log₂T charge
  becomes relatively negligible and nothing guarantees these refutations persist. The first open alphabet for ρ < 1/2
  is N₀ = 8 or beyond. N₀ = 8 bit orientations (10⁹) were not enumerated.
* Any trade at N₀ = 2 with T = 4 is open for flattenings and empty for ALS at these shapes.
