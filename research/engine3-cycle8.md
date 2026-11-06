# The incidence 8-cycle (and the prism): exact flattening certificates and two-term identity searches

Scripts: `research/scripts/engine3-cycle8/` (outputs `*.out` next to them). Tags: **[N]** exact computation,
**[C]** heuristic (ALS), **[R]** reasoning. Instance and conventions as in `engine3-open-door.md` §3.3–3.4, §5.5:
8-cycle nodes n₁..n₈, G = {12|34|56|78}, H = {23|45|67|81}, 20 crossing edges (8 three-cell at cyclic distance 2,
12 two-cell at distance 3/4), N₀ = 2 (one bit per edge, two strings per edge), K₄ networks, raw cost 20 (12 on the
two-cell sub-configuration, where under each merge the 4 cycle-adjacent group pairs carry 1 edge and the 2 diagonal
pairs carry 4 edges each: raw bonds (2,2,2,2;16,16)).

## 1. The 4-group flattening LP and its closed form [R + N, `lp4.py`]

Reduction of `engine2-decorrelated.md` §8.2 with 4 groups: a contraction M is an orientation o ∈ {−1,0,1}^E (longer
paths only change node net flows); group excesses n_i = Σ_{v∈G_i}(out_v − in_v), Σn_i = 0. For a labelling σ the
inequality of M reads Σ_{σ=X} n ≤ e(σ), so a K₄ network with bond exponents e passes M **iff e(δS) ≥ |n_S| for all 7 cuts
S|S^c** (4 singletons AND the 3 pair cuts — the pair cuts are not implied by the singleton constraints). The LP

  d(n) = min Σ_{i<j} e_ij  s.t.  e(δS) ≥ |n_S| (7 cuts), e ≥ 0

has a dual polytope with 20 vertices, 15 maximal; exactly (checked against linprog on 5000 random n):

  **d(n) = max( max_i |n_i|,  max_{i<j} |n_i + n_j|,  ½ Σ_i |n_i|,  ½(|n_1+n_2| + |n_1+n_3| + |n_1+n_4|) ).**

(The six vertices (y_i, y_j, y_{ij|kl}) = ½ give ½(|n_i|+|n_j|+|n_i+n_j|) = max(|n_i|,|n_j|,|n_i+n_j|), already covered.)
For 3 groups this reduces to diff.py's max(max|n_r|, ½Σ|n_r|).

## 2. Exact flattening certificate D₈ [N, `d8_exact.py` → `d8_exact.out`]

Method: exact dynamic programming over the edges on the state (n^G, n^H) ∈ Z⁴×Z⁴ (all 3^E orientations; 2 192 865
reachable states for E = 20), min(d_G, d_H) evaluated on every state with the closed form. Independent check: the
scale-free (fractional, o ∈ [−1,1]^E = arbitrary multiplicities) value by LPs over all pairs of linear pieces of d_G, d_H
(64 pieces each). Results:

| configuration | D (integer, exhaustive) | D at multiplicity 2 (per unit) | fractional D | witness |
|---|---|---|---|---|
| all 20 edges | **13 of 20** | (not run: memory) | **13.000** | n^G = (−10,−3,8,5), n^H = (−8,3,10,−5) |
| 12 two-cell edges | **9 of 12** | 9 | **9.000** | n^G = (−6,−3,6,3), n^H = (−6,3,6,−3) |
| 8 three-cell edges | **4 of 8** | 4 | **4.000** | n^G = (−4,0,2,2), n^H = (−2,0,4,−2) |

So the local-search values of `flatcert3.out` are exact. **D₈ = 13 < 20 and D(two-cell) = 9 < 12: asymptotically,
flattenings (every single-contraction rank inequality, any node-local pre-processing, §8.2) do NOT forbid a two-cell trade
on the 8-cycle.** The best they prove is ρ ≥ 13/20 on the 8-cycle and ρ ≥ 3/4 on its two-cell part.

## 3. Finite (N₀ = 2, m = 1) flattening tests of explicit ansätze [N]

At m = 1 the flattening inequalities are much stronger than their asymptotic shadow, because the term count is explicit:
contraction M gives rank 2^{|E(M)|} for f and ≤ 2^{|E(M)| − gap_t(M)} for a term with bonds e_t, gap_t = max_S (n_S −
e_t(δS)); an identity with terms t needs Σ_t 2^{−gap_t(M)} ≥ 1 for every M (`flatgap.py`, exact over all reachable
states; controls in `flatgap_control.out`: the App. H rectangle identity and the two-rectangle identity with bond 4 pass,
the latter with bond 2 is excluded, matching ALS).

* **Two-cell 8-cycle, f = R + C with symmetric K₄ bonds** (adjacent 2, diagonals 2^a, 2^b) [`flatgap.out`]: excluded
  (over every field) for every pattern of cost ≤ 10, i.e. all those meeting the criterion (cost+12)/2 + 1 < 12:
  bonds 2 everywhere (cost 6): min Σ2^{−gap} = 0.0625; diag (4,4) cost 8: 0.25; diag (4,8) cost 9: 0.375; diag (2,16) cost 9:
  0.25; (8,8) cost 10: 0.75. Also R + C + R′ excluded for all of these except (8,8) (value exactly 1.0).
* **All bond patterns with power-of-2 dimensions** (`frontier.py`, `twoterm.py`): surviving (cost_G(R), cost_H(C)) Pareto
  frontier {(0,12), (10,11), (11,10), (12,0)}; same-merge pairs {(0,12),(11,11),(12,0)}. For an arbitrary two-term
  identity P1 + P2 (each piece with its true G- and H-costs, all four pairwise tests imposed) the minimal fixed-N₀
  criterion is **12.000 — not < 12: no two-term trade with power-of-2 bonds** [N]. R + R′ + C: no survivor meets the
  criterion (+log₂3).
* **Non-power-of-2 bond dimensions** (`realdims.py`, family: four adjacent bonds equal x ∈ 1..4, diagonals y, z ∈ 1..16):
  the GH frontier drops to e.g. (10.644, 10.644) (dims (2; 10,10) for both R and C) — for R + C with the other-merge costs at raw (12) the
  best criterion is **12.322** (`rc_crit.out`), still no trade. But the relaxation "every pair of single-merge tests
  separately" allows a criterion of **11.965 < 12** at pieces (10.644, 11.285), (11.285, 10.644): i.e. flattenings at m = 1
  do not exclude a two-term identity **if** both pieces are sub-raw under BOTH merges simultaneously. The joint test
  (each piece's rank bounded by the min of its two representations) was not completed (search space too large here).

Prism (same tests, 3 groups, raw 9): the ALS ansätze of `engine3-open-door.md` §3.3 are all **exactly impossible**:
R + C with bonds (2,2,2): 0.125; (4,4,4): 0.5; mixed (2,2,4): 0.1875; (2,4,4): 0.25; 3 terms R + C + R′ with (2,2,2),
(4,4,4), (2,2,4), (2,4,4), (2,4,8): excluded (0.1875, 0.75, 0.25, 0.375, 0.625). Power-of-2 frontier GH {(0,9),(7,8),(8,7),(9,0)};
minimal two-term criterion 9.000 (no trade). Real dimensions (all (x,y,z) ∈ 1..8³): R + C with raw cross costs best 9.232
(no trade); the four-test relaxation allows 8.652 < 9 at pieces (7.492, 7.755), (7.755, 7.585), again only with pieces
cheap under both merges.

## 4. ALS [C, `netals.py`, `als_runs.py`]

Generic ALS (exact least squares per group tensor, any number of terms and groups). Controls (`als_controls.out`):
rectangle App. H identity 50 of 50 restarts exact; two disjoint rectangles with 4 groups per merge (R bond 4 on (G₃,G₄),
C bond 4 on (H₃,H₄): an exact identity) 8 of 20 exact; same with bond 2 (excluded by §3) 0 of 10, min residual 0.7071.
Planted 4-group test (random G-network + random H-network, all K₄ bonds 2, on the two-cell leg structure; `als_planted8*.out`):
exact (2·10⁻¹⁰) at 44 sweeps in 1 of 3 restarts (the other two at 0.285 and 0.591 after 60 sweeps): the 4-group ALS can
find a bonds-2 R + C when one exists, but needs restarts (K₄ networks have loops; convergence is slow).

* **8-cycle two-cell, R + C, all K₄ bonds 2** (`als_cyc2.out`): 4 restarts × 60 sweeps, min relative residual
  **0.98426** (all four 0.9843). Consistent with §3: this ansatz is exactly impossible (flatgap value 0.0625 < 1), so the
  ALS run is a sanity check, not evidence.
* **Prism** (`als_prism_prism_*.out`, 6 restarts × ≤150 sweeps each; bonds listed for the group pairs (12,13,23)):

| ansatz | bonds | min residual | median | flattening (§3) |
|---|---|---|---|---|
| R + C | (2,2,2) | 0.9802 | 0.9818 | excluded (0.125) |
| R + C | (4,4,4) | 0.8489 | 0.8592 | excluded (0.5) |
| R + C | (2,2,4) | 0.9606 | 0.9649 | excluded (0.1875) |
| R + C | (2,4,4) | 0.9271 | 0.9298 | excluded (0.25) |
| R + C + R′ | (2,2,2) | 0.9891 | 0.9900 | excluded (0.1875) |
| R + C + R′ | (4,4,4) | 0.9252 | 0.9258 | excluded (0.75) |
| R + C + R′ | (2,2,4) | 0.9770 | 0.9801 | excluded (0.25) |
| R + C + R′ | (2,4,4) | 0.9617 | 0.9623 | excluded (0.375) |
| control R + C | (8,8,8) | 4.7·10⁻³ (2 restarts, still decreasing) | | trivially possible |

The 3-term residuals are worse than the 2-term ones (ALS lands in worse local minima from random starts), so the ALS
numbers are weak heuristics [C]; the exact exclusions of §3 supersede them. The earlier "no trade" evidence of
`engine3-open-door.md` §3.3 (d = 2: 0.988, d = 4: 0.927) is now a **theorem for those ansätze**: the two-term identities
with bonds (2,2,2) and (4,4,4) do not exist over any field (one contraction M certifies it).

## 5. What is now proved about two-cell trades on this instance

* [N] **D₈ = 13 of 20 exactly** (8-cycle, two merges), **9 of 12** on the two-cell edges, 4 of 8 on the three-cell edges;
  integer and fractional (scale-free) values coincide. Flattenings therefore do **not** forbid a two-cell trade here
  asymptotically; the best they give is ρ ≥ 0.65 (ρ ≥ 0.75 on the two-cell part). D₈ = 20 is false.
* [N] At N₀ = 2, m = 1, on the 12 two-cell edges: **no two-term identity P₁ + P₂ with power-of-2 bond dimensions meets the
  fixed-alphabet trade criterion** (minimum 12.000, equality, needs < 12); every f = R + C with K₄ bonds 2 (cost 6), and
  every symmetric pattern up to cost 10, is impossible over every field; R + R′ + C likewise has no criterion-meeting
  survivor.
* [N] With arbitrary bond dimensions (family: equal adjacent bonds, free diagonals) f = R + C with the other-merge costs at
  raw is still excluded (criterion ≥ 12.322); a general two-term identity is excluded by the separate pairwise tests only
  down to 11.965, i.e. **not excluded** if both pieces are below raw under both merges at once (costs ≈ (10.64, 11.29) and
  (11.29, 10.64)); the joint test was not run.
* [C] ALS found no decomposition (bonds 2: residual 0.984).
* Not proved: anything for T ≥ 3 general pieces, larger N₀, or the asymptotic question. The asymptotic flattening value 9/12
  leaves room for a trade; a proof of "no two-cell trade" (§5.5(c)) needs a non-flattening argument, as on the 3×3 level.
