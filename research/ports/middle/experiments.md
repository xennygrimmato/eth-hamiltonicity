# Experiments E-M1 … E-M4 (notes.md §9): rank placements against cuts

26 Nov 2026. Tags as in notes.md: [N] computed, [R] proved (or exact computation that is itself a proof),
[C] conjecture or reading. All values of β found by search are **lower bounds on β_ρ** for that μ. β_cut is
exact for n ≤ 32 and otherwise a **lower bound** from annealing. Normalisation as in notes §0/§9:
E_pairs = n⁻² Σ over ordered pairs, diagonal included; E_edges = mean over edges.

Code: `tools/tensorlab/src/rankplace/` (modules f2, graph, groups, spectral, cut, anneal, verify), driver
`tools/tensorlab/examples/rankplace.rs`, Python bindings `rp_*` (README of tensorlab). Independent checker:
`check_placement.py` (plain-Python rank recomputed from the saved edge list). Saved placements (JSON: graph
edge list, μ, f as hex u64 with row i = byte i): `data/rankplace/`. Raw logs of every run: `data/rankplace/logs/`.

Machine: 4 cores (Xeon 2.1 GHz), shared with other jobs throughout (load average 10–13), so wall times are
inflated by about 2–3×. Rank of a packed matrix: ≈ 5 ns (branch-free byte elimination). One annealing move
costs ≈ n rank evaluations (2n if accepted): ≈ 9 µs per move at n = 1024, μ = 6 (native build).

```bash
cd tools/tensorlab
RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR=target/native cargo build --release --example rankplace
B=target/native/release/examples/rankplace
```

## 0. Correctness checks [N]

- 26 Rust unit tests (rank against a reference eliminator: exhaustive for 3×3, random for μ ≤ 8; products and
  inverses; incremental annealing totals against recomputation from scratch for all three objectives and for
  ball moves; group orders |SL₂(F₈)| = 504, |SL₂(F₁₆)| = 4080, |SL₃(F₄)| = 60480, LPS orders 2184 and 12180;
  Lanczos against the dense solver; exact β_cut for Petersen 3/2, Heawood 12/7, Pappus 2, matching notes §3) and
  the Python smoke test all pass. The pre-existing tensorlab tests still pass.
- The notes' numbers are reproduced exactly. SL₂(F₈): E_pairs d_J = 1.8690, ratio 3.738. SL₂(F₁₆): j=1 gives
  1.9662, j=2 gives 3.3132 (ratio 6.6265). SL₃(F₄): E_pairs d_J = 2.2917 ≥ 3j−1 = 2. The conjugated-projection
  matrix placement f(g) = M_g P M_g⁻¹ (P = projection onto U^m along the complementary monomials) has D_f = 2·d_J
  exactly on all these groups: pair-rank histograms are supported on even ranks.
- **Kernel inequality (Proposition S, k = 1, 2, 3): satisfied on every placement found or constructed, with no
  violation in any run.** It is tight (0.5000 ≤ 0.5000) on the identity placement of Cay(Mat₃(F₂), rank one),
  as notes §4.4 predicts. Consequences (a) and (b) never fail. Their hypotheses are rarely met: (a) needs
  λ* ≤ 2^{−r−1}, and the bound 6r+4 exceeds μ ≤ 8 anyway.
- `check_placement.py` recomputed six saved placements (Heawood, SL₂(F₈) structured, rr6_n16, rr4_n32, SL₃(F₂)
  random generators, an E-M3 placement): all agree to 1e-9.

## 1. Calibration: what the search can and cannot find [N]

This section decides how to read every "found nothing" below.

| test | known value | best found from random starts | best found from cut starts | from the known placement (cold) |
|---|---|---|---|---|
| small cubic graphs (n ≤ 30), β_cut exact | β_cut | reaches β_cut for n ≤ 18; 90–100% for n = 24, 30 | ≥ β_cut, with small gains (§2) | – |
| random cubic n = 64…512 | β_cut (lb) | **72–85% of β_cut** | = β_cut | – |
| Cay(Mat₃(F₂), all 49 rank-one), n = 512 | identity: **2.2285**; β_cut = 1.531 | 1.79 (μ=2), 1.37 (μ=3) | 1.531 | 2.2285 (stays). Recovers **2.2165 from a 90%-randomised identity** at low temperature; the default (hot) schedule melts even a 10%-perturbed start to 1.80 |
| same, gradient-bounded r = 1 (maximise E_pairs) | 2.2285 | 0.65 | – | 2.2285 |
| SL₃(F₄), 12 generators, n = 60480, μ = 6 | structured **4.583** | 1.11 | 2.54 | 4.583 (no local improvement) |
| SL₃(F₄), gradient-bounded r = 2 | 4.583 | 1.07 | – | 4.583 |
| SL₂(F₈), μ = 6 | structured 3.738 | 3.78 (cut-type, not the structure) | 7.875 (= β_cut) | 3.738 (no local improvement) |
| SL₂(F₁₆), μ = 8 | structured 6.627 | 2.12 | 8.836 (= β_cut) | – |
| E-M3 sanity: the matrix search contains the diagonal (Boolean) one | max ≥ diag | **below its own diagonal restriction** at r ≤ 3 for d ≤ 8 (e.g. d=3, r=1: 1.21 vs 2.16) | – | – |

**Reading.** The annealer is good at cut-type optima seeded by good cuts. It finds small non-commutative
improvements of those, and it refines and repairs a structured placement once it holds a nucleus of it (10% of
the vertices suffice on Mat₃). It does **not** nucleate rigid algebraic placements from scratch: on both
positive controls where a placement beating the cuts is known, random-start chains reach 25–60% of it. So a
negative result on random graphs means only this: no excess over β_cut is reachable by local moves from cuts or
random starts. **It says nothing about placements with global linear structure.**

The β_cut lower bound also needed calibrating. The first cut heuristic (200·n flips) was too weak: cuts
S_xy = {v : yᵀf(v)x = 1} read off the matrix placements beat it by up to 17% (rr3_n512). Those apparent
"excesses" were artefacts; that heuristic was replaced. The production β_cut uses 50000·n flips × 8 chains, plus
polishing of all S_xy cuts of the best placements. These cuts are natural: Pr_{x,y}[yᵀMx = 1] = (1−2^{−rk M})/2,
so 1 − 2^{−D_f} is in the cut cone. At n = 512 the value still crept up by about 2% when the budget was
quadrupled.

## 2. E-M1: β_ρ versus β_cut [N]

`$B em1 d 16,32,64 1,2,3 2,3,4,6 1000000 8`, `$B em1 d 128,256 1,2 2,3,4,6 1000000 8`,
`$B em1 d 512 1 2,4,6 500000 8`, for d = 3, 4, 6. Each graph runs 8 chains per μ: 3 random starts, the best
cut, two direct sums of good cuts, and twice the best placement of the previous μ. That is 1M moves per chain
(0.5M at n = 512). Total about 19 min of wall time for all 51 graphs. β_found is the best over μ ∈ {2,3,4,6}
({2,4,6} at n = 512).

| d | n | graphs | λ₂ (range) | β_cut (range) | best β found (range) | max β_found/β_cut |
|---|---|---|---|---|---|---|
| 3 | 16 | 3 | 0.765–0.836 | 2.812–3.938 exact | 2.812–3.938 | 1.0000 |
| 3 | 32 | 3 | 0.828–0.916 | 3.438–5.625 exact | 3.438–5.625 | 1.0000 |
| 3 | 64 | 3 | 0.904–0.920 | 4.800–5.328 lb | 4.800–5.328 | 1.0000 |
| 3 | 128 | 2 | 0.919–0.943 | 5.535–6.273 lb | 5.535–6.273 | 1.0000 |
| 3 | 256 | 2 | 0.929–0.934 | 5.818–6.000 lb | 5.818–6.002 | 1.0002 |
| 3 | 512 | 1 | 0.937 | 6.093 lb | 6.093 | 1.0000 |
| 4 | 16 | 3 | 0.634–0.699 | 2.000–2.667 exact | 2.000–2.667 | 1.0000 |
| 4 | 32 | 3 | 0.753–0.797 | 2.667–2.888 exact | 2.691–2.888 | **1.0091** |
| 4 | 64 | 3 | 0.788–0.844 | 2.947–3.524 lb | 2.947–3.524 | 1.0034 |
| 4 | 128 | 2 | 0.841–0.846 | 3.348–3.632 lb | 3.348–3.632 | 1.0000 |
| 4 | 256 | 2 | 0.847–0.853 | 3.585–3.597 lb | 3.584–3.590 | 1.0014 |
| 4 | 512 | 1 | 0.857 | 3.656 lb | 3.656 | 1.0000 |
| 6 | 16 | 3 | 0.464–0.496 | 1.500–1.688 exact | 1.547–1.688 | **1.0312** |
| 6 | 32 | 3 | 0.634–0.649 | 2.000–2.182 exact | 2.012–2.182 | 1.0059 |
| 6 | 64 | 3 | 0.674–0.688 | 2.210–2.250 lb | 2.210–2.250 | 1.0000 |
| 6 | 128 | 2 | 0.700–0.721 | 2.327–2.389 lb | 2.327–2.389 | 1.0000 |
| 6 | 256 | 2 | 0.727–0.731 | 2.439–2.491 lb | 2.439–2.491 | 1.0000 |
| 6 | 512 | 1 | 0.739 | 2.526 lb | 2.526 | 1.0000 |

The per-μ rows are in `data/rankplace/logs/em1_*.md`. They include E_pairs, E_edges, the best random-start
chain, the worst chain, the best S_xy cut, and the cut-cone ratio of 1−2^{−D}.

Named and Cayley graphs (`$B named 400000 2,3,4,5`; `$B gstudy SPEC -- iters chains mus`):

| graph | n | d | λ₂ | β_cut | best β found (μ) | β/β_cut | note |
|---|---|---|---|---|---|---|---|
| K₃,₃ | 6 | 3 | 0 | 1 (exact) | 7/6 (2) | 1.167 | notes §3: 7/6 |
| Petersen | 10 | 3 | 1/3 | 3/2 | 3/2 | 1 | = notes |
| Heawood | 14 | 3 | 0.471 | 12/7 | **27/14 = 1.9286 (3)** | 1.125 | notes had 1.75. All edges rank 1; pair ranks 1/2/3 on 42/84/56 ordered pairs: the Fano-plane (F₂-linear) structure. Exceeds even 1/(1−λ₂) = 1.892 |
| Pappus | 18 | 3 | 0.577 | 2 | 2.1136 (3) / 2.1 (2) | 1.057 | notes: 2.056 |
| McGee | 24 | 3 | 0.667 | 2.25 | 2.3162 (2) | 1.029 | |
| Tutte–Coxeter | 30 | 3 | 0.667 | 2.5 (lb) | 2.5421 (2) | 1.017 | |
| LPS X^{5,13} = PGL₂(F₁₃) | 2184 | 6 | 0.708 | 2.601 | 2.601 | 1.000 | μ = 2,3,4; 300k moves × 8 chains |
| LPS X^{5,17} = PGL₂(F₁₇) | 4896 | 6 | 0.718 | 2.520 | 2.520 | 1.000 | μ = 2,3,4; 200k × 8 |
| PSL₂(F₁₃), 2 random generators + inverses | 1092 | 4 | 0.912 | 5.654 | 5.654 | 1.000 | |
| SL₂(F₈), 2 random generators + inverses | 504 | 4 | 0.867 | 4.667 | 4.667 | 1.000 | |
| SL₃(F₂) = PSL₂(F₇), 2 random generators, seeds 2–5 | 168 | 4 | 0.873–0.923 | 4.0–6.96 | = β_cut for 3 seeds; 4.046 (μ=4) for seed 3 | ≤ 1.012 | seed 1 generated a subgroup of order 24 only (discarded) |
| SL₂(F₈), elementary generators | 504 | 4 | 0.938 | 7.875 | 7.875 (cut) | 1.000 | structured 3.738 < β_cut |
| SL₂(F₁₆), elementary generators | 4080 | 4 | 0.965 | 8.836 | 8.836 (cut) | 1.000 | structured 6.627 < β_cut |
| **SL₃(F₄), 12 elementary generators** | 60480 | 12 | 0.8005 | 2.960 (lb; upper bound 1/(1−λ₂) = 5.013) | **4.583 (structured, μ=6)** | ≤ 1.549 | the search alone gives 2.54 |
| Cay(Mat₃(F₂), 49 rank-one) | 512 | 49 | 0.347 | 1.531 (= 1/(1−λ₂) up to 1e-4) | 2.2285 (identity) | 1.455 | positive control, dense |
| Cay(Mat₃(F₂), 14 random rank-one) | 512 | 14 | 0.857 | 7.0 | 7.0 (cut) | 1 | identity 2.23 < β_cut |
| cycles C₆₄, C₂₅₆; tori 8×8, 16×16 | | 2, 4 | | n/4 and a/2 | = β_cut | 1 | non-expander controls |

Conclusions for E-M1:

- [N] On random 3-, 4- and 6-regular graphs, n = 16…512, μ ≤ 6, **no placement found beats the best cut by more
  than 3.1%**. Gains above 0.5% occur only at n ≤ 32, and they shrink with n. On the LPS graphs (n = 2184,
  4896) and the cross-characteristic or random-generator Cayley graphs, the gain is 0 or about 1%. There is
  **no sign of β_ρ/β_cut growing with n** in anything the search can reach.
- [N] The visible non-commutative gains are all on small graphs with F₂-linear structure (Heawood, K₃,₃, Pappus,
  Mat₃). The largest relative gain among cubic graphs, 12.5% on Heawood, is the incidence structure of PG(2,2).
- [C] This matches the notes' reading (§6.1.2): spreading placements are special solutions tied to F₂-linear
  structure. But by §1, the search could not have found such structure on a random graph if it existed. The
  experiment tests the "generic local" part of (GE) only.
- [N] At the sizes reachable here, the positive controls do **not** yet beat cuts, except SL₃(F₄) and the dense
  Mat₃ control. SL₂(F_{2^k}) with 4 generators is a weak expander (λ₂ = 0.94–0.97), and cuts win there by
  about 2× at k = 3, 4. SL₃(F₄) is the only bounded-degree positive control with structured ratio > β_cut-lb:
  4.583 vs 2.960. But β_cut ≤ 5.013 is all that is proved, so even there β_ρ > β_cut is not certified at n = 60480.

## 3. E-M3: gradient-bounded placements [N]

`$B em3 d 256 s 8 1,2,3,4 400000 8`, for d ∈ {3,4,6,8,12,16} and s ∈ {1,2}; also n = 1024 for d = 8 and 16.
μ = 8. Objective: maximise E_pairs D with D ≤ r on every edge, starting from f ≡ 0, 8 chains × 400k moves.
Commutative baseline: the same search restricted to diagonal matrices (Hamming placements; E_pairs ≤ μ/2 = 4
for them). Wall time 1–4 s per row. The table shows seed 1; seed 2 agrees within ±0.1 (logs `em3_*.md`).

| d | log₂ d | λ₂ | r=1: matrix / diag | r=2 | r=3 | r=4 | matrix E_pairs / r at r = 1,2,3,4 |
|---|---|---|---|---|---|---|---|
| 3 | 1.58 | 0.929 | 1.21 / **2.16** | 2.73 / **4.00** | **4.38** / 4.00 | **6.15** / 4.00 | 1.21, 1.36, 1.46, 1.54 |
| 4 | 2 | 0.853 | 1.05 / **1.29** | 2.46 / **4.00** | 3.74 / **4.00** | **5.24** / 4.00 | 1.05, 1.23, 1.25, 1.31 |
| 6 | 2.58 | 0.731 | 0.85 / 0.92 | 2.10 / **3.19** | 3.18 / **4.00** | **4.49** / 4.00 | 0.85, 1.05, 1.06, 1.12 |
| 8 | 3 | 0.640 | 0.75 / 0.77 | 2.03 / **2.46** | 3.04 / **3.63** | 4.14 / 4.00 | 0.75, 1.02, 1.01, 1.03 |
| 12 | 3.58 | 0.533 | 0.59 / 0.63 | **2.00** / 1.73 | 2.96 / 2.94 | 4.08 / 4.00 | 0.59, 1.00, 0.99, 1.02 |
| 16 | 4 | 0.467 | 0.50 / 0.51 | **1.99** / 1.55 | 2.65 / 2.59 | 4.00 / 4.00 | 0.50, 1.00, 0.88, 1.00 |
| 8, n=1024 | 3 | 0.657 | – | 1.97 / 2.07 | 2.86 / 3.30 | 4.07 / 4.00 | –, 0.98, 0.95, 1.02 |
| 16, n=1024 | 4 | 0.476 | – | 1.94 / 1.82 | 2.74 / 2.49 | 3.98 / 3.64; r=5: 4.84 / 4.00 | –, 0.97, 0.91, 0.99, 0.97 |

Reading:

- [N] **Bold** marks the better of the two searches. The matrix search is often worse than its own diagonal
  restriction (d ≤ 8, r ≤ 3), so the true maximum is at least the larger of the two. This is calibration
  item 9 of §1.
- [N] For d ≥ 8 every r-Lipschitz placement found has E_pairs ≈ r (between 0.9r and 1.03r). The pair-rank
  histograms are concentrated at rank exactly r: placements are "everything at distance r", not spreading.
  This is the notes' prediction "bounded, ≈ r + O(1), when 2^r < d/2" (§4.2–4.3), and it holds here even for r
  above log₂ d (d = 8, r = 4; d = 12, r = 4).
- [N] For d = 3, 4 the matrix placements spread beyond r: E_pairs/r rises to 1.54 (d = 3) and 1.31 (d = 4) at
  r = 4, above the Boolean ceiling μ/2. This is the regime r > log₂ d, where the kernel lemma constrains nothing
  (for cubic graphs the window is empty, §4.2(d)). That gives a threshold-like picture: spread at r > log₂ d
  for d ≤ 4, none visible for d ≥ 8 up to r = 4–5.
- Caveats. μ = 8 caps E_pairs at 8, and the graph-metric Lipschitz bound min(μ, r·d_G) is 6–7.9 for all rows
  with r ≥ 2. So "spread" at d ≥ 8 could only show as E_pairs between r and about 8: the window is narrow and
  the search is weak (§1). [C] The d ≤ 4 spreading is ordinary low-degree behaviour: tree-like balls let
  Lipschitz maps grow with the distance, and the ratio stays ≈ 1.3–1.5, far below β_cut ≈ 3.6–6. It is not
  evidence against (GE).
- Controls: Cay(Mat₃, rank one) with r = 1: the structured value is 2.2285; the search from zero finds 0.65,
  the diagonal search 0.43. SL₃(F₄) with r = 2: structured 4.583, from zero 1.07, diagonal 0.75. **A spreading
  bounded-gradient placement that is known to exist was not found from zero in either case.**

## 4. E-M4: λ₂ of Cay(SL₃(F₂[x]/(p)), e_ab(1), e_ab(x)) [N]

`$B em4 2 111 400`, `$B em4 3 1011 300`, `$B em4 3 1101 300`. Lanczos on 1^⊥: with full reorthogonalisation
for n = 60480, plain three-term recurrence for n = 16.5M. The λ₂ estimates at 1/4, 1/2, 3/4 and all of the
steps agree to 6 digits.

| p | n | λ₂ | λ_min | bound 3/4 − 2^{1−3j} (M2″) | bound from the placement, 4.2(e) | E_edges d_J | E_pairs d_J (≥ 3j−1) | d_J histogram | wall |
|---|---|---|---|---|---|---|---|---|---|
| x²+x+1 | 60 480 | **0.800505** | −0.595 | 0.5 | 0.6786 | 0.5 | 2.2917 | [168, 3528, 35280, 21504] | 29 s |
| x³+x+1 | 16 482 816 | **0.877328** | −0.609 | 0.5 | 0.7103 | 0.5 | 2.9052 | [168, 17640, 1526448, 14938560] | 470 s (BFS 43 s) |
| x³+x²+1 | 16 482 816 | **0.879798** | −0.611 | 0.5 | 0.7103 | 0.5 | 2.9052 | same | 548 s |

[N] The bound λ₂ ≥ 3/4 − 2^{1−3j} holds with room: j = ⌊k/2⌋ = 1 for both degrees, so the bound is only 1/2.
λ₂ grows from k = 2 to k = 3, consistent with λ₂ → 1 − (spectral gap of the (T)-family). The 4.2(e) bound from
the Grassmann placement is sharper (0.68, 0.71) but still well below the true value. The two cubic moduli give
different graphs (λ₂ differs in the 3rd digit) with the same d_J statistics, as they must.

## 5. E-M2: extreme rays of MET₆ in the rank cone [N]/[R]

`python3 em2_met6.py 4000 6` (18 s). Rays were found as LP optima (HiGHS) of 4000 objectives, half Gaussian and
half sparse "reward a random pattern". This gave 7 S₆-orbits with sizes 6 + 15 + 10 (cuts) + 60 + 90 + 10 + 90
= 281 rays. [K*] The literature count I recall is 296 rays in 7 orbits; the orbit count agrees, and the 15-ray
difference is unresolved (either my recollection or one orbit size).

| orbit representative (d₀₁,d₀₂,…,d₄₅) | orbit size | in 𝒦^{rk}? |
|---|---|---|
| three cut orbits | 6, 15, 10 | yes (diagonal placements) |
| [0,1,1,1,2,1,1,1,2,2,2,1,2,1,1] (K₂,₃ metric with a doubled point) | 60 | **yes, exactly: D_f = δ with μ = 2** [R] |
| [0,1,1,2,2,1,1,2,2,2,1,1,1,1,2] | 90 | **yes, μ = 2** [R] |
| [1,1,1,2,2,2,2,1,1,2,1,1,1,1,2] (K₃,₃ graph metric) | 10 | **yes, μ = 2** [R] (notes §3) |
| [1,1,1,2,2,2,2,1,1,2,1,1,1,3,2] (contains a distance 3) | 90 | **not found**: c = 1, μ = 3…8 best L1 error 2; c = 2, μ = 6…8 error 3–4 (40 restarts × 40k moves each); c ≥ 3 impossible at μ ≤ 8 |

The certificates (f as hex) are in `data/rankplace/logs/em2.md` and were re-verified by exact rank. 2^{−cδ} is
PSD for c = 1…8 on the last ray, so the kernel lemma does not exclude it. Its membership is open: "not found"
with μ ≤ 8 only.

## 6. Status summary

| item | status |
|---|---|
| module `rankplace` (+ Python `rp_*`), tests | done, all tests pass [N] |
| structured placements and notes §5.2 table | reproduced exactly [N] |
| kernel inequality on every placement | never violated [N] (it is a theorem: no bug detected) |
| E-M1: β_ρ/β_cut on random 3/4/6-regular graphs, n ≤ 512; LPS n = 2184, 4896 | ≤ 1.031, no growth with n, within search reach [N] |
| E-M1 positive controls | SL₂(F₈), SL₂(F₁₆): cuts beat the structure at these sizes. SL₃(F₄): structure/β_cut-lb = 1.55 (not certified > 1). Search does not rediscover the structure [N] |
| E-M3 | E_pairs ≈ r for d ≥ 8 up to r = 4–5; spread beyond r only for d ≤ 4 at r > log₂ d; matrix search weaker than its Boolean restriction at small r [N] |
| E-M4 | λ₂ = 0.8005 (k=2), 0.8773 and 0.8798 (k=3), vs bound 0.5 [N] |
| E-M2 | 6 of 7 orbits of MET₆ rays are rank metrics (μ ≤ 2); one orbit not found with μ ≤ 8 [N]/[R] |

What would make the negative E-M1 result informative: a search that nucleates linear structure. Two options:
(i) equivariant search on Cayley graphs, over M with f(g) = P_g⁻¹MP_g (notes §1.5), which needs μ beyond 8 for
LPS (permutation module of dimension q+1); (ii) a coboundary or SAT formulation of "all edges rank ≤ r,
E_pairs ≥ t" for small n. Neither was attempted.
