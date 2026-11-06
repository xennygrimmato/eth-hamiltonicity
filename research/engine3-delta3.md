# Engine 3, Δ_3: is there any trade on the three anti-diagonal triangles of Z_3²?

Scripts and outputs: `research/scripts/engine3-delta3/` (each `X.py` has an `X.out`). [N] = numerical. [C] = exact computation
(exact over every field unless stated otherwise). [R] = reasoning. Setting as in `engine3-open-door.md` §3.2: N₀ = 2, 18
strings, f_Δ = ⊗ of 9 equalities = T₀⊗T₁⊗T₂, where T_s is the triangle r + c ≡ s. Under rows, and also under columns, each T_s is
⟨2,2,2⟩ on the three groups, so f_Δ is a row network with bonds (8,8,8) (cost 9) and likewise a column network.

## 0. Verdict

* **Q1 is answered no, exactly [C].** f_Δ = R + C with R a row network with bonds (2,2,2) and C a column network with bonds
  (2,2,2) is impossible over every field. A single matrix flattening proves it: rank f = 512, but rank R ≤ 128 and
  rank C ≤ 128. The same flattening refutes (2,2,4)+(2,2,4) in all three placements, R+C+R and R+C+C with bonds (2,2,2) or
  (2,2,4), and R+C+D with a diagonal network D. The obstruction already appears on the restriction to two triangles
  (Majdoddin's C with two of its three merges): there rank f = 64, while each term has rank at most 16.
  Among all two-term identities R + C with bond dimensions in {1,2,3,4,6,8}, every pair with max(c_R, c_C) < 4.755 is refuted.
  A two-term trade at N₀ = 2 needs c_R, c_C < 4 when the other costs are generic (12), so **no two-term R + C identity
  gives a trade on Δ_3.** ALS agrees: residuals stay well above the exact Eckart–Young floor of 0.7071.
* **Q2 [C+N]:** f = R + τR with R row (2,2,2) is a special case of Q1 (τR is a column network with bonds (2,2,2)), so it is
  refuted exactly. ALS gives 0.98425 = √(31/32), with or without the column-rank coupling (8,2,2) or (4,4,2). At N₀ = 2,
  pieces costing (3,5) cannot meet the ρ < 1/2 criterion for any T ≥ 2 anyway, because 4 + log₂T ≥ 5 > 4.5.
* **Q3 [C]:** reproduced: flattening certificate 4 of 9 with rows and columns, and 4 of 9 with the diagonals added as a third
  merge. Core floor 3 of 9 in both cases. **Three merges buy nothing.**
* **Q4 [C+N]:** the rectangle control finds the App. H identity in 48 of 50 restarts. Planted R₀ + C₀ on Δ_3 is recovered in
  5 of 5 cases (at most 2 restarts each). On the 3×3 level, the 2⁹-term product decomposition at λ = 1 has
  max_t min(c_row, c_col) = 8 exactly. The finite flattening test passes every true identity it was given.
* **Caveat that matters more than Q1 [C+R]:** Strassen's identity already satisfies the §1.7 finite criterion on Δ_3.
  Each triangle is ⟨2,2,2⟩ and has rank 7, so f_Δ is a sum of 7³ = 343 terms, each a product over all 9 nodes. Each term
  costs 0 under rows and under columns. The criterion then gives 0 + log₂343 = 8.42 < 9 (ρ_Δ ≤ 0.936). Asymptotically
  ρ_Δ ≤ ω/3 < 0.791 (`strassen_check.py`, exact over ℤ on all 2¹⁸ entries). Either the framework means ρ relative to
  rank-one (ω-type) evaluation, or "ρ_Δ < 1 refutes the hyperedge extension of the rectangle-content conjecture" holds
  trivially. The same applies to any configuration whose cross-merge structure contains a triangle. **This must be settled
  before Δ_3 is used as a test of non-rectangle trades.** §3.2's "Upper bound: raw" is wrong as stated.

## 1. The exact refutation (Q1) [C]

`flat_finite.py`: for each restricted orientation o ∈ {0,+,−}⁹:
* 0 means both strings are fixed to a common value (the edge is removed).
* ± sends one string to side X and the other to side Y.

The restricted f is then a 0/1 permutation matrix of rank 2^{#oriented edges}.

A triangle network with bonds d has rank across X|Y at most

min over sides s ∈ {X,Y}³ of Π_g 2^{(legs of g on the side ≠ s_g)} · Π_{s_g≠s_h} d_gh.

This is a network min cut, valid over every field. Take the worst orientation o* = (1,1,1,1,1,−1,1,1,−1) (all edges split).
* rank f_Δ = 512 (`flat_verify.py`: exact over ℚ and mod 32749).
* Every row network with bonds (2,2,2) has rank ≤ 128, and so does every column network with bonds (2,2,2).
* Random integer R and C hit 128, 128 and 256 exactly, so the bound is attained.

Hence 512 > 256, and also > 384 for three terms. Two-triangle version (`flat_two.py`, o = (1,1,1,1,1,−1)): row 0 lies wholly on
side X and rows 1 and 2 each have one X-string, so R factors through 2 strings and 2 bonds: rank ≤ 16. Symmetrically
(column 2 lies wholly on side Y) rank C ≤ 16. Since 32 < 64, restricting the third triangle gives the full Δ_3 case.

| test (`flat_finite.py`, `flat_patterns.py`, `q3_threemerge.py`) | worst slack | verdict |
|---|---|---|
| R(2,2,2)+C(2,2,2) | −256 (512 vs 256) | refuted |
| R(2,2,4)+C(2,2,4), C(2,4,2), C(4,2,2) | −256 | refuted |
| R+C+R, R+C+C, bonds (2,2,2) or (2,2,4) | −128 | refuted |
| R+C+D (diagonal merge), (2,2,2) | −128 | refuted |
| 2R+2C (2,2,2); R+C+D+R; R+C+D (2,2,4) | 0 | passes |
| R(2,4,4)+C(2,4,4); R(4,4,4)+C(4,4,4); R(3,3,3)+C(3,3,3) | ≥ 0 | passes (go to ALS) |
| min max(c_R,c_C) over passing pairs (dims {1,2,3,4,6,8}) | 4.755 at (3,3,3)+(3,3,3) | |

Eckart–Young: ‖f − R − C‖/‖f‖ ≥ √(1 − 256/512) = 0.7071 for every two-term (2,2,2) pair; for three terms the floor is 0.5.

## 2. ALS (Q1, Q2) [N]

The method is block-exact least squares, reported as relative residual ‖f − Σ‖/‖f‖. Initial scales cycle over 0.1, 0.3 and 1.
A run stops when the improvement over 40 sweeps falls below 10⁻⁷. Validation: `check_basic.py` (f is recovered as a row or
column net (8,8,8) to 3·10⁻¹⁰; at (4,8,8) the residual is 0.7071, as it must be), planted recovery, and the rectangle control.

| run (`als_runs.py`) | restarts | min residual | median |
|---|---|---|---|
| Δ_3 R(2,2,2)+C(2,2,2) | 50 | 0.974604 | 0.9774 |
| Δ_3 R(2,2,4)+C(2,2,4) / C(4,2,2) | 20 / 20 | 0.952409 / 0.952401 | 0.9603 / 0.9558 |
| Δ_3 R(2,4,4)+C(2,4,4) | 30 | 0.902304 | 0.9141 |
| Δ_3 R(3,3,3)+C(3,3,3) | 30 | 0.929225 | 0.9338 |
| Δ_3 R(4,4,4)+C(4,4,4) | 20 | 0.798495 | 0.8221 |
| Δ_3 R+C+R (2,2,2) | 30 | 0.960660 | 0.9747 |
| two triangles R(2,2,2)+C(2,2,2) | 60 | 0.829850 | 0.8482 |
| two triangles R(4,4,4)+C(4,4,4) (control: f itself is (4,4,4)) | 5 | 7.8·10⁻⁵ | 6·10⁻⁴ |
| Q2 f = R+τR, R row (2,2,2) (`q2_sym_als.py`) | 10 | 0.984252 | |
| Q2 with R ≈ column net (8,2,2) / (4,4,2), μ → 10 | 8 / 8 | 0.984255 / 0.984251 (mismatch ≤ 0.5%) | |

* Every residual is bounded well away from 0, as the exact refutation requires.
* The patterns that pass flattening, (2,4,4)², (3,3,3)² and (4,4,4)², also stay at 0.80–0.93. These patterns would not give
  a two-term trade anyway, since (5+12)/2 + 1 = 9.5 > 9.
* Q2 sits at √(31/32): R + τR captures exactly 2 of the 64 units of norm², which is a rank-one piece of two triangles times
  one triangle.

## 3. Floors (Q3) [C]

`flatcert4.py` (copied, rerun, output identical) and `q3_threemerge.py` (independent: per-merge LP solved by linprog).

| merges | D (of 9) | histogram of the certified value | core floor |
|---|---|---|---|
| rows, cols | 4 | {0:1574, 1:7416, 2:7560, 3:2862, 4:270} | 3 of 9, H = one triangle |
| rows, cols, diagonals (r−c) | 4 | {0:2258, 1:9612, 2:6876, 3:900, 4:36} | 3 of 9 |

## 4. Sanity on the 3×3 level (Q4) [C]

`level_product.py`:
* App. H F = P − A holds exactly. The 9 rectangles partition the 36 strings.
* Each of the 2⁹ product terms has network cost equal to c_flat.
* max_t min(c_row, c_col) = 8. Histogram of the min cost: {0:2, 2:18, 4:72, 6:168, 8:252}.

`flat_sanity.py`: the finite test passes true identities (rectangle P + A: slack 0; 3×3 level, 512 product pieces, 4000 random
orientations: slack > 0) and refutes P alone and A alone.

## 5. What was not decided

* `flat_lp_qm2.out` is a partial run of an LP over all (row, column) bond-type families. It stopped after the q = 0 rows. Its
  results so far: flattening alone cannot exclude multi-term families. Examples: 64 product terms, or 16 terms of column
  cost 3. Strassen's 343 product terms confirm that such families exist. So the flattening world says nothing about
  identities with many terms; only the two- and three-term R + C questions are settled here.
* GF(2) or other finite-field SAT was unnecessary: the refutation holds over every field.
