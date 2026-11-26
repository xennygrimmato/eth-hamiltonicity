# S3 experiments: piece floors beyond the Euclidean prices

26 Nov 2026. Executor notebook for spec S3 (`research/ports/c1d1/notes.md`, D1.5 item 3), with the later
corrections from the theory agent (`research/sat3/notes.md` §5, §10).

Tags: **[N]** computed (command given), **[R]** proved here (short argument given), **[C]** conjecture.

Code: new module `tools/tensorlab/src/piecefloor.rs`. Existing modules are unchanged; all 35 + 2 Rust tests and the
7 Python smoke tests pass. The new pieces are:
- the driver `tools/tensorlab/examples/piecefloor.rs`;
- Python bindings `pf_b_mat`, `pf_one_tree`, `pf_limit_phi`;
- an independent plain-Python evaluator, `research/sat3/verify_pf.py`. It does not use tensorlab. It rebuilds the
  designs and recomputes ranks, tree distances and b-vectors from scratch.

The machine was shared, with load average 15–28 on 4 cores throughout, so the timings below are wall-clock under
that load.

```bash
cd tools/tensorlab
RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR=target/native cargo build --release --example piecefloor
B=target/native/release/examples/piecefloor        # all commands below are run from tools/tensorlab
```

## 0. Objective, direction, conventions

- A design has:
  - nodes and edges, each edge with two legs;
  - p merges, each with one hub per group.
- A placement puts legs and hubs at points of a metric space. The quantities are b_m = (L − H_m)/δ_m (b2 §1),
  with:
  - L = Σ_e w_e |legs of e|;
  - H_m = Σ_legs w|leg, own hub of m|;
  - δ_m = the largest hub–hub distance of m.
- A price gives one piece with c_m ≥ b_m·λ − o(λ) for all m at once.
- The floor is max over convex combinations of b⁺ of min_m. Every design here has automorphisms acting
  transitively on its merges, so the floor equals the max over placements of

  **value = (Σ_m b_m⁺)/p**, in units of λ per merge, and ρ = value / Σ_e w_e.

- **Direction: we MAXIMISE.** A larger value is a stronger lower bound on the cost of the best piece, i.e. a
  HIGHER floor for the level factor ρ.
  - A placement in a space whose finite subsets are prices when contracting fails, with value above the flat
    value, means the following. A p-merge engine with ρ in the window (flat value, that value) would prove
    contracting even if flats exist.
  - A search that finds nothing above the flat value only says that this search found nothing.
- Reference values:

| design | p | E | flat value E/√p (ρ) | other references |
|---|---|---|---|---|
| crossing | 2 | 2 | √2 = 1.41421 (0.7071) | cut value 1 (ρ 1/2) |
| K₄ = AG(2,2), 3 classes | 3 | 6 | 2√2 = 2.82843 (0.4714) | — |
| Δ₃ (rows, columns, diagonals) | 3 | 9 | 3√3 = 5.19615 (0.5774) | 9/√2 = 6.36396 (0.7071) = two-merge value = cap for every price (theory agent, Cor. 3.4) |

## 1. Calibration on the two-merge crossing (task 1)

| space | method | value | ρ | command / time |
|---|---|---|---|---|
| ℝ^4 | far-leg limit, annealed hubs | **1.414214** (8/8 chains) | 0.7071 | `$B far crossing - 4 40000 8` (<1 s) |
| Mat₂(F₂), √rk | EXHAUSTIVE: all 120 hub orbits under a ↦ αaβ + c, a ↦ aᵀ; exact optimal legs | **1.000000** | 0.5 | `$B exh crossing 2` (0.00 s) |
| Mat₃(F₂), √rk | EXHAUSTIVE: 3736 hub orbits; exact legs over all 512² leg pairs | **1.000000** | 0.5 | `$B exh crossing 3` (8–11 s) |
| Mat_μ, μ = 2..6 | annealing over all 8 points, 200k steps × 8 chains | 1.000000 (8/8 at every μ) | 0.5 | `$B anneal crossing μ 200000 8` |
| metrics with d and d² both metrics | SLSQP relaxation, 30 starts | 1.0 (one merge); 0.567 (both merges active) | 0.5 | `python3 research/sat3/snowflake_lp.py crossing 30 both 0` |
| single tripod / spider (4, 6 arms) | far-leg limit | 1.000000 | 0.5 | `$B far crossing 3 0 ...` |
| tripod × ℝ^k (k = 1, 2, 4), tripod², tripod³, spider4² × ℝ | far-leg limit | **1.414214** (exactly, never more) | 0.7071 | `$B far crossing 3,3 0 30000 8` etc. |

Weighted crossings (λ₁, λ₂), Mat₂ and Mat₃ exhaustive:
- (1, ½): 1.0, against the Euclidean value ‖λ‖₂ = 1.118.
- (1, 0.1): 1.0, against 1.005.

**Findings.**
1. [N] The two-merge value is **not geometry-independent**. Euclidean space and products of trees give exactly
   1/√2. √rank placements give 1/2, the flattening value. Single trees also give 1/2.
2. [N] The spec's calibration claim is false: the unit square {0, e₁₁, e₂₂, I} does not reproduce 2‖λ‖₂. It is
   one of the 120 enumerated hub placements in Mat₂, and every placement, including that square with optimal
   legs, gives at most 1.
3. [R] The reason is that √rk is the square root of a metric. For a leg x and two hubs h, h′:
   |d(x,h) − d(x,h′)| = |rk(x−h) − rk(x−h′)|/(d(x,h)+d(x,h′)) ≤ δ²/(d(x,h)+d(x,h′)).
   So a far leg cannot tell hubs apart, and the Euclidean far-leg mechanism (legs at ±M·u_e) is unavailable at
   every μ. The pull-back to Mat_μ itself is a bounded-scale space. The theory agent reached the same conclusion
   (raw placements realise distances only √1, …, √μ; notes §4). Its prices of interest when contracting fails
   are the hulls (§3 below), not the raw point sets.
4. Calibration of "search found nothing" against "nothing exists". On the crossing at μ = 2, 3 the exhaustive
   optimum (1.0) and the annealer agree.
   - On K₄ the annealer **fails** at μ = 3: 1.333 in 16/16 chains, while the exhaustive restricted search proves
     at least 2.0.
   - On Δ₃ at μ = 4 the annealer returned 0.0.
   - So annealing over raw matrix placements is a weak search, and its negative results carry little weight.

## 2. K₄ with three matchings (task 2, first part)

| space | method | value | ρ |
|---|---|---|---|
| ℝ^4 | far-leg | 2.828427 (8/8) | 0.4714 = √2/3 = flat |
| Mat₂ | EXHAUSTIVE, 17578 hub orbits, exact legs | **2.000000** | 1/3 |
| hubs in Mat₂ ⊂ Mat₃, legs anywhere in Mat₃ | EXHAUSTIVE, 17578 orbits × exact legs over 512² | 2.000000 (284 s) | 1/3 |
| Mat_μ μ = 2, 4, 5, 6 / μ = 3 | annealing 400k × 16 | 2.0 / 1.333 (annealer failure, see §1) | |
| single tripod, spider 4, 6 | far-leg | 2.000000 | 1/3 |
| tripod × ℝ^k (k = 1, 2, 4), tripod², tripod³ (k = 0, 2), spider4² × ℝ | far-leg | **2.828427 exactly**, never more | 0.4714 |

The theory agent then proved that every CAT(0) price gives at most 2√2 per merge on K₄ (quadrilateral midpoint
inequality, notes §3). So K₄ is settled: nothing beats the flat value. The numbers above agree. No further
compute was spent on K₄.

## 3. Δ₃ with three merges (task 2, main part)

### 3.1 Euclidean and matrix placements

- Euclidean far-leg optimum in ℝ²: 5.196132; ℝ⁴: 5.195694; ℝ⁶: 5.195774 (200k steps × 8 chains). That is 3√3
  up to annealing tolerance, matching b2 (`far_opt.py`; `verify_flat.py` gives 3√3 exactly for the
  orthogonal-simplex price; unit test `far_value_orthogonal_delta3`).
- Mat₂ annealing: 3.000 (7/16 chains; b = (−3.49, 9, −5.83): one merge full, the cut value).
  - The exhaustive Mat₂ run (about 6·10⁷ hub orbits) was started, then stopped when the theory agent
    reprioritised (raw matrix placements cannot realise far legs, §1 item 3).
  - μ ≥ 3 was dropped for the same reason.
- [C, from §1 item 3] Raw √rk placements on Δ₃ stay at or below the single-tree value 4 and far below 3√3.

### 3.2 Products of trees: far-leg (Busemann) limit

- Model: hubs in an ℓ₂-product of pods (stars with infinite arms) or of general trees, possibly × ℝ^k.
- Legs of edge e: sent to infinity at distance M along a geodesic line. In each tree factor the line runs between
  two distinct ends; in the flat factor it runs along ±w. The factors are weighted by unit coefficients.
- For fixed hubs the optimal line per edge is computed exactly:
  - per tree factor, the best ordered pair of ray roots (any vertex may carry a ray);
  - the coefficients are then proportional to the positive parts (`piecefloor::far_value`, `far_value_tree`).
- The search is over hub positions only (annealing).
- Every reported value was checked independently. `verify_pf.check_far` builds the explicit finite
  configuration with legs at distance M on the recomputed lines, and recomputes b with exact distances.

| hub space | best value (far-leg) | ρ | chains hitting | finite-M check (Python) |
|---|---|---|---|---|
| ℝ², ℝ⁴, ℝ⁶ | 5.1961 | 0.5773 | 1/8 each (others 5.19x) | M = 1e6: 5.1952–5.1947 |
| tripod, spider 4 | 4.000000 | 4/9 | 8/8 | 4.000000 at every M |
| tripod × ℝ, × ℝ² | 5.1961 | 0.5773 | | |
| tripod × ℝ⁴ | 5.479837 | 0.6089 | 1/8 | M = 1e6: 5.477096 |
| tripod × tripod (also spider4², spider6²) | **5.464101 = 2 + 2√3** | 0.6071 | 2/16 | M = 1e6: 5.463452 |
| tripod³ | 5.501322 | 0.6113 | 1/16 | M = 1e6: 5.499406 |
| **nine node-tripods** (theory agent) | **6.000000** | **2/3** | — | M = 1e2: 5.9136, 1e4: 5.99914, 1e6: 5.999991, 1e8: 6.000000 |

Commands:
- `$B far delta3 3,3 0 300000 16 7` and similar (logs `data/far_delta3.log`, `data/camp1_delta3.log`).
- `python3 research/sat3/check_ninetripods.py`.

**Nine node-tripods.**
- Configuration: one tripod factor per node n = (r,c). In that factor the three hubs R_r, C_c, D_{r−c} of n sit
  on the three arms at radius 1, and all other hubs sit at the centre. b = (6, 6, 6).
- The same value comes from the Rust `far_value` on the 9-factor pod product (unit test
  `one_tree_node_pod_delta3`).
- 2 + 2√3, 5.48 and 5.50 are local optima of the product search. The product search is a poor optimiser; this is
  why the one-tree reduction below matters.

### 3.3 One-tree reduction: Γ over single general trees

- Theory agent, notes §5.2 [R there]: on an edge- and merge-transitive design, the supremum of the far-leg value
  over all ℓ₂-products of trees is (1/p)√(E·Γ), where:
  - Γ = sup over ONE tree of S/D̄;
  - S = Σ_e (s_e)₊², with s_e = max_{r₊,r₋} Σ_k [d(r₊,r₋) − d(r₊,h^k_u) − d(r₋,h^k_v)];
  - D̄ = the mean over merges and same-merge hub pairs of d².
- Searched (`piecefloor::anneal_one_tree`): one finite tree with V vertices. Hubs sit at vertices, the topology
  changes by prune-and-regraft, edge lengths are free, and rays may attach at any vertex.

| V (Steiner vertices) | starts | chains | best Γ | value (1/3)√(9Γ) | chains at the best |
|---|---|---|---|---|---|
| 10, 13, 17, 21 | half node-pod, half random | 16 each | 36.000000 | 6.000000 | 16/16 each |
| 12, 17 | **random only** | 16 each | 36.000000 | 6.000000 | **32/32** |

Commands:
- `$B onetree delta3 V 300000 16 SEED`;
- `PF_NOSTART=1 $B onetree delta3 V 300000 16 SEED` (18–54 s each).
- Γ was recomputed in plain Python for all 7 saved trees (`verify_pf.check_onetree`); all agree.

**No-ansatz check (task D(iii)).**
- The finite configurations of the nine-tripod product at M = 3, 10, 30, 100 were taken as starts and annealed as
  finite point sets: legs are points, all 27 points move, 300k steps × 8 chains (`$B modelfrom delta3 FILE ...`).
- Values: start 2.463 / 5.073 / 5.706 / 5.914, after annealing 5.9707 / 5.9962 / 5.9968 / 5.9970.
- The finite optimum approaches 6 from below and never exceeds it, so the far-leg ansatz does not appear to hide a
  larger value.
- Random-start finite annealing in tripod², tripod × ℝ², ℝ³ is a weak search: best 4.0, 2.37 and 5.19 at 1M steps.

**Conclusion for Δ₃ [N].** Over ℓ₂-products of trees the value is **6 per merge (ρ = 2/3)**.
- That is above the flat 3√3 = 5.196 (ρ 0.577) and below the cap 9/√2 = 6.364 (ρ 0.707).
- Lower bound: an explicit, independently verified configuration.
- Upper side: numerical evidence only (Γ = 36 reached from random starts in every chain; no tree with Γ > 36
  found). No proof; the theory agent's E3 would certify it.
- Status for the algorithm: this beats the Euclidean value. Whether such tree-product sets are prices when
  contracting fails is the theory agent's §4 (hull) question, not settled here.

## 4. Full 3-nets AG(2,g) (task 4 / theory agent request c)

- Design: AG(2,g) with all C(g²,2) edges and the 3 classes x, y, y+x (GF(4) for g = 4). Internal edges are
  included.
- Edge orbits are computed under the semilinear maps that permute the three classes:
  - g = 3: 27 internal edges + 9 crossing;
  - g = 4: 72 + 48;
  - g = 5: 150 + 150.
- Columns of the table below:
  - Γ;
  - "sym": the value of the symmetrised product of the best tree, (1/p)Σ_O|O|√(mean_O s²/D̄), achieved;
  - "CS": the Cauchy–Schwarz bound (1/p)√(EΓ), an upper bound for every product, valid if Γ is the supremum;
  - all normalised by E.
- Search: one tree with 20 vertices, 100k steps × 16 chains, target Γ and target sym separately.

| g | E | Γ | sym ρ | CS ρ | flat ρ_orth(3,g) | cap |
|---|---|---|---|---|---|---|
| 3 | 36 | 90 | 0.5202 | 0.5270 | 0.4979 | 0.7071 |
| 4 | 120 | 324 | 0.5410 | 0.5477 | 0.5138 | 0.7071 |
| 5 | 300 | 840 | 0.5519 | 0.5578 | 0.5244 | 0.7071 |

- In every run the best tree was the node-pod: no tree beat it at these g.
- g = 7 was not run, because the limit problem (§5) supersedes it.
- Command: `$B onetree ag3-3 20 100000 16 5 gamma|sym` (35–235 s). Log: `data/onetree_ag.log`.
- Γ was rechecked in Python for g = 3, 4.

## 5. Large-net limit problem (theory agent E1)

- Definition (`research/sat3/limitnet.py`, `piecefloor::LimitNet`):
  - a quotient Q;
  - nodes Q², with hubs (k, a_k r + b_k c);
  - Φ = E_{n,n′}[c(n,n′)₊²]/D̄, with c(n,n′) = max_{r₊,r₋}[p·d(r₊,r₋) − F_n(r₊) − F_{n′}(r₋)];
  - level value √Φ/p;
  - flat Φ = p, cap p²/2.
- The evaluator is general-tree based and deduplicates nodes by their hub-vertex multiset.

**Reproduction [N].** These are exact (unit test `limit_index4_subgroup`):
- Z₃: 10/3;
- Z₄: 27/8;
- Z₂²: 27/8.

**Exhaustive over pods with radii in {0,1} and ≤ 4 arms** (arm permutations quotiented; `$B limitexh Q 3 A`):

| Q | labellings | best Φ | maximiser |
|---|---|---|---|
| Z₂ | 855 | 3 | flat |
| Z₃ | 86 472 | 3.333333333 = 10/3 | one class per merge on its own arm |
| Z₂² | 10 306 752 (77 s) | 3.375000000 = 27/8 | same |
| Z₄ | 10 306 752 (61 s) | 3.375000000 = 27/8 | same |

**General-tree annealing** (`$B limit Q 3 16 ITERS 8 SEED`; seeds: all subgroup labellings, plus random chains):

LIMIT_TABLE

## 6. Summary

SUMMARY

## Log

- 18:35: read the spec, b2, tensorlab.
- 18:45: piecefloor module; crossing and K₄ exhaustive.
- 18:50: far-leg evaluator. First hit: tripod² = 2 + 2√3 on Δ₃; message to main.
- 19:00: theory agent corrections; general trees, AG designs.
- 19:10: nine tripods verified (6); one-tree Γ = 36; AG table.
- 19:20: limit problem: reproduction, exhaustive pods, quotient scan.
