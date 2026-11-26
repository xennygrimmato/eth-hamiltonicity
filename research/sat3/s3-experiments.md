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

| Q | p | best Φ | level √Φ/p | maximiser | random-only chains (coset moves) |
|---|---|---|---|---|---|
| Z₃ | 3 | 10/3 | 0.6086 | index-3 subgroup tripod | 8/8 |
| Z₄ | 3 | **27/8** | **0.6124** | index-4 tripod | 8/8 reach 27/8 |
| Z₂² | 3 | **27/8** | 0.6124 | index-4 tripod | 8/8 |
| Z₅ | 3 | 3.36 = 84/25 | 0.6110 | point tripod (class 0 per merge) | 8/8 |
| Z₆ | 3 | 10/3 | 0.6086 | index-3 tripod | 7/8 |
| Z₈ | 3 | 27/8 | 0.6124 | index-4 tripod (lifted) | seeded only (random: 3.28) |
| Z₂³ | 3 | 27/8 | 0.6124 | index-4 tripod | seeded |
| Z₃² | 3 | 10/3 | 0.6086 | index-3 tripod | seeded |
| Z₂ × Z₄ | 3 | 27/8 | 0.6124 | index-4 tripod | seeded |
| Z₉ | 3 | 10/3 | 0.6086 | index-3 tripod | seeded |
| Z₁₂ | 3 | 27/8 | 0.6124 | index-4 tripod | seeded |
| Z₃ | 4 | 16/3 | 0.5774 = 1/√3 | index-3 tripod (theory formula) | 8/8 |
| Z₃² | 4 | 16/3 | 0.5774 | index-3 | seeded |
| Z₅ | 4 | 5.12 | 0.5657 | point | 5/8 |
| Z₇ | 4 | 4.898 = 240/49 | 0.5533 | point | 4/8 |
| Z₂, Z₄, Z₂² | 4 | 8 (= cap) | — | **invalid**: slopes 1 and −1 are not transversal in characteristic 2 (two merges coincide mod 2), not a net | |

- Annealing: 100k–150k steps × 8 chains on a tree of 16 vertices; Z₁₂ took 507 s.
- Logs: `data/limscan2.log`, `data/limscan3.log`, `data/limscan4.log` (Z₄², Z₂⁴, p = 4).
- Seeds: every subgroup labelling (classes of H on arm k+1, radius 1; Φ of every seed printed in the log).
- Moves: single hub, coset move (q + ⟨g⟩ of one or all merges to one vertex), edge length, prune-and-regraft.
- No quotient exceeded 27/8. The maximum over the subgroup family is θ = 1/4, Φ = 3(1−θ)(1+2θ).
- For Z₄ and Z₂² this is also the exhaustive optimum over {0,1}-pods with ≤ 4 arms (table above).
- For larger Q it is a search result. Random-only chains on Z₈ stall at 3.28 (the point labelling), so the
  annealer is not strong enough on its own there.

## 5b. Cones over metric graphs (coordinator request, after §5)

**Model.**
- A factor is the Euclidean cone C(G) over a finite metric graph G with girth ≥ 2π.
- Points are (vertex of the possibly subdivided G, radius), with
  d² = r² + s² − 2rs·cos(min(π, d_G)).
- Legs go to directions b, b′ ∈ V(G) at angle ≥ π (a line through the apex).
- The saving of a hub (r, x) towards b is r·cos(min(π, d_G(b,x))).
- Directions are restricted to vertices of the subdivided graph, so each value is a valid lower bound for that
  space.
- Code: `piecefloor::{ConeGraph, cone_gamma, cone_limit_phi, cone_product_b, anneal_cone}`.

**Reduction used [R, Cauchy–Schwarz as in notes §5.2].**
- For any family of factors and any design: value ≤ (1/p)√(E·max_f Γ_f), where:
  - S_f = Σ_e s_{e,f}²;
  - δ_k² ≥ Σ_f D̄_f (max ≥ mean over merges and pairs);
  - Σ_e √(Σ_f s²) ≤ √E·√(Σ_f S_f).
- For an edge- and merge-transitive design (Δ₃) the orbit product of the best factor attains the bound, and it is
  balanced (b_k equal for all k, by the transitive action on merges).
- So **products mixing factor types cannot beat the best single type**, and it suffices to optimise Γ of ONE
  cone.
- The same holds for Φ in the limit model.
- The "balanced value" requested is therefore the value itself.
  - Single-factor b-vectors are unbalanced; e.g. the plane on the crossing gives b = (2, 0).
  - A direct product evaluator (`cone_product_b`) is included and checked on the 9-tripod product: b = (6, 6, 6)
    exactly (unit test `cone_calibration`).
- Calibration: crossing in the plane (circle:8), in C(K₃,₃) and in pods → √2 per merge.


### One-factor reduction (lemma, with proof) [R]

**Lemma (one factor suffices).**
- Setting:
  - a design with edges e (weights w_e) and p merges;
  - a family 𝓕 of CAT(0) factor spaces, closed under relabelling hubs by design automorphisms;
  - hubs placed in an ℓ₂-product X = Π_f X_f of members of 𝓕;
  - legs sent to infinity along geodesic lines.
- In a single factor f let:
  - s_{e,f} ≥ 0 be the best far-leg saving of edge e, summed over merges with unit weights:
    s_{e,f} = max over lines of Σ_k [−β₊(h^k_u) − β₋(h^k_v)], clipped at 0;
  - D̄_f be the mean over merges k and same-merge hub pairs of d_f².
- Then the far-leg value per merge satisfies

  (1/p) Σ_k b_k ≤ (1/p)√(E·Γ_𝓕),

  with Γ_𝓕 = sup_f S_f/D̄_f, S_f = Σ_e w_e s_{e,f}², and E = Σ_e w_e (unit weights here).
- If the design's automorphism group acts transitively on the edges and on the merges (Δ₃, K₄, the crossing), and
  transitively on same-merge hub pairs, the bound is attained, with all b_k equal, by the ℓ₂-product of the
  orbit of an optimal single factor.

*Proof.*
1. Upper bound.
   - In a product the Busemann function of a line with unit coefficients (c_f) is Σ_f c_f β_f.
   - For an edge, the optimal line therefore gives Σ_k (saving)_k/δ = (1/δ)·√(Σ_f s_{e,f}²) (Cauchy–Schwarz over
     factors, coefficients c_f ∝ s_{e,f}). This uses a common δ; with different δ_k use δ_min, which only
     enlarges the bound.
   - Summing over e with Cauchy–Schwarz again: Σ_e √(Σ_f s²) ≤ √E·√(Σ_f S_f) ≤ √E·√(Γ Σ_f D̄_f).
   - Finally δ² = max_{k, pairs} Σ_f d_f² ≥ mean_{k, pairs} Σ_f d_f² = Σ_f D̄_f.
   - So (1/p)Σ_k b_k ≤ (1/p)√(E·Γ).
2. Attainment.
   - Take the product of the |G| copies f∘γ, γ ∈ G, of one factor.
   - Every edge then has Σ_γ s²_{γe} = (|G|/E)·S_f by edge-transitivity.
   - Every same-merge hub pair has Σ_γ d² = |G|·D̄_f by transitivity on pairs, so all δ_k coincide.
   - Then both Cauchy–Schwarz steps are equalities.
   - The per-merge values coincide because G is transitive on merges and the product is G-invariant.
∎

**Corollaries.**
- Mixing factor types cannot beat the best single type.
- For designs that are not edge-transitive (full nets), (1/p)√(EΓ) is still an upper bound for products of copies
  of the family. The orbit product attains (1/p)Σ_O|O|√(mean_O s²/D̄) (the "sym" values above, O = edge orbits).
- The same argument applies verbatim to Φ of the limit model.

**Δ₃, one cone, Γ.**
- Run: 200k steps × 16 chains seeded (three hubs of one node at three mutually far vertices, radius 1) + 8
  random-only chains.
- Command: `$B cone delta3 GRAPH SUBDIV 200000 16 5`; log `data/cone_delta3.log`.

| link G (subdivision) | n | best Γ | value per merge | random-only |
|---|---|---|---|---|
| pods:3, pods:6 | 3, 6 | 36 | 6.000 | 36 |
| circle:12, circle:24 (plane) | 12, 24 | 27 | 5.196 = flat | 27 |
| K₃,₃ (s2, s4), K₄,₄ (s2) (= pod × pod) | 15–33 | 36 | 6.000 | 36 |
| Heawood (s1) | 14 | 33.175 | 5.760 | same |
| Heawood (s2, s4), Heawood + 3 points (s2) | 35–77 | 36 | 6.000 | 36 |
| PG(2,3) incidence (s1) / (s2) | 26 / 78 | 33.175 / 36 | 5.760 / 6.000 | same |
| GQ(2,2) incidence (s1, s2), GQ + 3 points | 30–78 | 36 | 6.000 | 36 |
| K₃,₃ + 3 points (s2) | 18 | 36 | 6.000 | 36 |

- Heawood at s1 and PG(2,3) at s1 fall short only because they have no three vertices pairwise at angle π.
  Subdivision supplies them.
- Γ was recomputed in plain Python for the saved configurations (`verify_pf.check_cone`).

**Limit model, one cone** (`$B cone limit:Q:3 GRAPH SUBDIV 100000 8 7`; log `data/cone_camp2.log`):

| Q | link (subdivision) | best Φ | level |
|---|---|---|---|
| Z₄, Z₂² | pods:3; K₃,₃ (s2); Heawood (s2); Heawood + 3 points (s2); GQ(2,2) (s2) | 27/8 | 0.6124 |
| Z₄ | PG(2,3) (s1) | 3.2075 | 0.5970 |
| Z₅ | pods:3; K₃,₃ (s2); Heawood (s2) | 3.36 | 0.6110 |
| Z₈ | pods:3; K₃,₃ (s2); Heawood (s2) | 3.28125 | 0.6038 |

For Z₈ the cone annealer is seeded only with the point labelling, so it stays at that labelling's 3.28125. The
tree search with subgroup seeds gets 27/8 there (§5). This is a search weakness, not a property of the cones.

**Free links.** These are random metric graphs whose base-edge lengths are annealed under girth ≥ 2π (moves that
violate it are rejected), with hubs and directions at subdivision vertices:

| target | free link (N₀ vertices, edges, extra points; subdivision 2) | girth of the optimum | best | value |
|---|---|---|---|---|
| Δ₃ | (8, 10), (10, 14), (8, 10, +3), (12, 16), 2 seeds each | 6.46–7.67 | Γ = 36 in all 8 runs | 6.000 |
| limit Z₄ | (8, 10, +3), (10, 12) | 6.46, 7.35 | Φ = 27/8 | 0.6124 |

Log: `data/cone_camp3.log`. Nothing exceeds the tree-product values.

## 5c. The space of filtrations 𝒞_N(q) = Cone(building of GL_N(F_q)) × ℝ (coordinator request, after §5b)

**Model** (q1-notes §1; `piecefloor::{FiltSpace, filt_edge, filt_scores, anneal_filt, q1_placement}`; driver `$B filt`).
- Hubs are two-level filtrations "U at level a, V at level c" (a ≥ c), with U a point or a hyperplane of PG(N−1,q).
  - a and c are continuous; the type and the point are discrete.
  - Note: this is points and hyperplanes only. Subspaces of intermediate dimension and filtrations with more
    levels are not implemented.
- Legs: an exact far-leg optimum along ±d in a common apartment (frame f).
- [R] Entry levels of the flag of the ray F^{f,Td}:
  - a point contributes S_d(ℓ) = min_{supp_f ℓ} d (q1 Lemma 1.4);
  - a hyperplane ker φ contributes S_d(H) = Σd − max_{supp*_f φ} d;
  - so a hub contributes (a−c)S_d(U) + c·Σd.
- Every term is concave in d, so max_{|d|=1} of the edge saving is the distance from 0 to a convex hull. It is
  computed by Wolfe's min-norm-point algorithm with a separable linear oracle, then maximised over all frames
  (unordered bases up to scaling, all enumerated; or sampled when there are too many, which still gives a valid
  lower bound).
- Hub distances: d² = i(a−b)² + (k−i)(a−c′)² + (k′−i)(c−b)² + (N−k−k′+i)(c−c′)², with i = dim(U∩U′).

**Checks.**
- [N] Hub terms against exact filtration distances (q1_verify.dist) at T = 1e5 over 300 random frames, hubs and
  levels: max error 9.5e-5 (= O(1/T)).
- [N] d² formula: exact to 4e-15 over 500 random pairs. Script: `research/sat3/check_filt_terms.py`.
- [N] In N = 2 the point and hyperplane encodings agree (unit test).
- [N] Γ recomputed independently in plain Python (explicit hull vertices + NNLS) for the saved F₂ configurations:
  agrees (`verify_pf.check_filt`).
- [N] **Q1 Theorem A reproduced** (unit test `filtrations_q1_values`):
  - F₂² net, all 120 edges: balanced value 0.482843 (840 frames);
  - F₂³ net, 2016 edges: 0.582516 (83 328 frames, 300 s, run with `PF_SLOW=1`).
  - "Balanced" = the merge average. It is attained by the GL-orbit symmetrisation, or by the tie choices on
    rank-one edges. The per-edge argmax used for min_k breaks those ties arbitrarily (min_k 0.433, 0.569).
  - g = 16 (N = 6) was not run: 6.7·10⁷ frame candidates, and the restricted-frame mode is not implemented.

**Runs.** Commands are `$B filt DESIGN q N TARGET ITERS 8 1 [MAXFRAMES]`; logs `data/filt_camp.log` and
`data/filt_camp2.log`.

| design | space | frames | steps × chains | best | ρ (sym) | record compared with |
|---|---|---|---|---|---|---|
| Δ₃ | C₃(F₂) | 28 | 20k × 8 | Γ = 35.99990 | 0.666666 | 2/3 (Γ = 36) |
| Δ₃ | C₃(F₃) | 234 | 20k × 8 | Γ = 35.99990 | 0.666666 | 2/3 |
| Δ₃ | C₃(F₄) | 1120 | 2.5k × 8 | Γ = 34.455 | 0.6522 | 2/3 (under-converged) |
| Δ₃ | C₄(F₂) | 840 | 4k × 8 | Γ = 33.750 | 0.6455 | 2/3 (under-converged: contains C₃(F₂)) |
| Δ₃ | C₅(F₂), sampled 1500 | — | 1.5k × 8 | Γ = 32.790 | 0.6363 | 2/3 |
| Δ₃ | C₄(F₃), sampled 1500 | — | 1.5k × 8 | Γ = 33.161 | 0.6398 | 2/3 |
| K₄ | C₃(F₂), C₄(F₂) | 28, 840 | 5k, 3k × 8 | Γ = 12 (8/8) | 0.471405 | 0.4714 (theorem) |
| net of Z₄ (120 edges, orbits 48 + 24 + 48) | C₃(F₂) / C₃(F₃) | 28 / 234 | 1.5k / 600 × 8 | sym 64.245 / 63.684 | 0.5354 / 0.5307 | trees 0.5410 (CS 0.5477) |
| net of Z₅ (300 edges) | C₃(F₂) | 28 | 800 × 8 | sym 158.05 | 0.5268 | trees 0.5519 (CS 0.5578) |

**Reading.**
- No filtration-space placement beat any record.
- Δ₃ in C₃(F₂) and C₃(F₃): every chain converges to Γ = 36 from below (35.9999), i.e. the tree value 6 per merge
  again.
- The larger spaces (C₃(F₄), C₄(F₂), C₅, C₄(F₃)) ran far shorter (minutes instead of tens of minutes) and stop
  below 36. They contain the C₃(F₂) optimum, so these are under-converged searches. They do not show that
  nothing better exists there.
- Cyclic nets: the short filtration runs stay below the tree records.
- Limitations: point and hyperplane hubs only; small N; short runs on the expensive spaces.

## 6. Summary

Directions: all values are LOWER bounds on the cost of the best piece (larger = higher floor). "Record" means the
best value found by any search here.

1. **Calibration (crossing).**
   - Euclid and products of trees give 1/√2.
   - √rank placements in Mat_μ(F₂) give exactly 1/2: exhaustive at μ = 2, 3; annealing at μ ≤ 6.
   - The reason [R]: √rk is the square root of a metric, so far legs carry no information.
   - The spec's "unit square reproduces 2‖λ‖₂" is false.
2. **K₄.**
   - Mat₂ exhaustive: 1/3.
   - Euclid, products of trees, cones and filtration spaces: exactly √2/3 = flat, never more (consistent with the
     theory agent's CAT(0) theorem).
3. **Δ₃.**
   - Euclid: 3√3 (ρ 0.5774).
   - √rank raw placements: ≤ 4.
   - Products of trees: **6 per merge (ρ 2/3)**, an explicit, independently verified configuration (nine
     node-tripods, b = (6,6,6)). It beats the Euclidean value.
   - The one-tree reduction (lemma in §5b) and searches over single general trees (Γ = 36 from random starts),
     cones over 15 link graphs including free girth-constrained links, and filtration spaces C₃(F₂), C₃(F₃) all
     land on exactly 6, never above.
   - Cap 9/√2 = 6.364 (theory).
4. **Full 3-nets AG(2,g), g = 3, 4, 5** (one tree, symmetrised). ρ = 0.5202, 0.5410, 0.5519, against flat 0.4979,
   0.5138, 0.5244. The node-pod is the best tree found.
5. **Large-net limit.**
   - Φ = 27/8 (level 0.6124) is the best over all quotients tried: Z₂..Z₁₂, Z₂ᵏ (k ≤ 4), Z₃², Z₄², Z₂ × Z₄.
   - It is exhaustive within {0,1}-pods with ≤ 4 arms for Z₃, Z₄, Z₂², and the best of the annealing beyond that.
   - Cones over graphs reproduce the same values.
   - p = 4: 1/√3 at index 3 (Z₃, Z₃²); Z₅ 0.5657; Z₇ 0.5533. Characteristic-2 quotients are not valid 4-nets.
6. **Nothing exceeded any record** in any model. The numbers say "these searches found nothing": they are not proofs.
   The calibration in §1 shows that the raw-matrix annealer can fail (K₄, μ = 3), while the tree, cone and limit
   optimisers recover every known optimum from random starts.
7. **Price status.** Whether tree-product or filtration sets are prices when contracting fails is a theory
   question (notes §4, q1-notes §3). No claim is made here.

## Log

- 18:35: read the spec, b2, tensorlab.
- 18:45: piecefloor module; crossing and K₄ exhaustive.
- 18:50: far-leg evaluator. First hit: tripod² = 2 + 2√3 on Δ₃; message to main.
- 19:00: theory agent corrections; general trees, AG designs.
- 19:10: nine tripods verified (6); one-tree Γ = 36; AG table.
- 19:20: limit problem: reproduction, exhaustive pods, quotient scan.
- 19:45–20:30: cones over graphs (one-factor reduction), free links, limit with cones.
- 20:30–21:30: filtration space C_N(q); Q1 values reproduced; runs on Δ₃, K₄ and cyclic nets.
- Notes on the data folder: four early cone JSON files with a non-JSON edge format were deleted (their values are in
  `data/cone_delta3.log` / `cone_camp2.log`). `data/anneal_Delta3_mu4_s4.json` is the annealer failure (value 0)
  quoted in §1.
