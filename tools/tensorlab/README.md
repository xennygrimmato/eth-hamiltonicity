# tensorlab

Small, fast, parallel (rayon) Rust tools for experiments on tensor prices (the asymptotic spectrum of
tensors), with optional Python bindings (PyO3 / maturin, module `tensorlab`). The Rust core needs no
Python; the bindings sit behind the `python` cargo feature.

## Build

```bash
cd tools/tensorlab
cargo test --release                      # Rust unit tests (no Python needed)
pip install maturin numpy                 # once
maturin build --release -o target/wheels  # builds the abi3 wheel with feature "python"
pip install --force-reinstall --no-deps target/wheels/tensorlab-*.whl
python tests/test_smoke.py                # or: python -m pytest tests/
```

Build output goes to `target/` (git-ignored). Drivers for the K_{2,3} computation are Rust examples:

```bash
cargo run --release --example e3a_fq  -- resh 2000    # f_Q: triangle + Reshetnyak inequalities
cargo run --release --example e3a_fq  -- box 1000     # f_CAT5: triangle + Gromov-Sturm box inequalities
cargo run --release --example e3a_cat -- w5            # checks on W5
cargo run --release --example e3a_cat -- trees 2 30    # products of 2 trees, all topologies
cargo run --release --example e3a_cat -- cone 0 3000   # Euclidean cone over the Heawood graph
cargo run --release --example e3_n5                    # N5 (sqrt-rank points) and W5 in tripod x R
cargo run --release --example e3_scan -- w5 2 15       # instances where the W5 bound is furthest below cuts
# ALS restriction search on K_{2,3}: Ds d12 d23 d13 duu starts sweeps [r|c] [seed] [LM iterations]
cargo run --release --example e3b_als -- 4 3 3 3 3 64 1500 r 5 300
cargo run --release --example e3b_border -- 2 2 2 2 2 1 1 16 1000   # Ds d.. K h starts sweeps
cargo run --release --example e3b_table -- 3 3 32 600 300          # calibration table, all demand vectors
python python/f2sat.py                                 # exact F_2 restriction by SAT (python-sat)
```

## Modules

| module | contents |
|---|---|
| `metric` | `Metric {n, d}` with distances in pair order (0,1),(0,2),…; constructors (Euclidean points, graph metrics, l2 products, cut metrics, `sqrt_rank_f2(mu)`); inequality families as `Constraint` values with value + gradient: triangle, Euler quadrilateral, Reshetnyak quadruple (AN Lemma C.4(b)), Gromov–Sturm box inequalities with an exact oracle `box_min` (Toyoda 2020: for at most 5 points these characterise subsets of CAT(0) spaces); l1-embeddability by NNLS over the cut cone, hypermetric (pentagonal) test, Gram-matrix Euclidean test, F_2 ranks. |
| `opt` | `RatioProblem` (minimise N.d / D.d subject to constraints and bounds); augmented Lagrangian + projected Barzilai–Borwein inner solver; parallel `multistart`; `kkt_polish` (Gauss–Newton on the KKT system of the active set: gives machine-precision points, active constraints and multipliers for certification); `minimize_box` for any smooth function on a box. |
| `models` | CAT(0) model spaces: `binary_trees(n)` (all tree topologies), `TreeProduct` (l2 products of metric trees; lines are trees), `min_ratio_tree_products`, `min_ratio_euclidean`, `GraphCone` (Euclidean cone over a metric graph, CAT(0) for girth >= 2π; `heawood_edges`), `min_ratio_graph_cone`. |
| `tensor` | `Tensor<T>` for `T = f64 / Complex64` with labelled axes: permute, matricise, `contract` (pairwise tensordot), `apply` a local map, `flattening_rank`; `Network` = EPR wire network (parties, wires (p,q,dim)), `dense()` graph tensor, `cut_log_rank`. |
| `restrict` | `contract_all` (greedy network contraction), `apply_maps`, `environment`, `als_multistart` (parallel ALS with decaying Tikhonov regularisation, gauge balancing, residual and norm histories), `lm_refine` (Levenberg–Marquardt on all maps jointly, real case), `residual_dense` (independent check through the dense S), `cut_check` / `cut_table` (flattening-rank necessary conditions). |
| `restrict` (border) | `border_multistart(net, T, K, h, opts)`: maps polynomial in ε of degree K, target ε^h T; `border_check` evaluates (⊗A(ε))S/ε^h through the dense S at given ε (the only trustworthy test, see Caveats). |
| `rankplace` | placements V(G) → Mat_μ(F₂) (μ ≤ 8, bit-packed), rank-metric Poincaré ratios vs cuts and λ₂; see the section below. |
| `k23` | the K_{2,3} instance: parties u1,u2,v1,v2,v3 = 0..4, weights, `w5(l,h)`. |
| `python/f2sat.py` | exact F_2 restriction search for tiny wire networks (Tseitin AND + XOR chains, CaDiCaL via python-sat), with an independent evaluator `verify_f2`. |

Python API (all distances as flat lists in pair order): `pairs, pair_index, metric_report, box_min,
sqrt_rank_f2, k23_w5, k23_weights, min_ratio(n, num, den, families, starts, seed, keep)`,
`min_ratio_tree_products, cut_table, als(nparties, supply, demand, starts, sweeps, complex, seed, reg0)`,
`network_dense`. Families: `"triangle", "euler", "reshetnyak", "box"`.

## rankplace (rank-metric placements on graphs)

`rankplace` studies placements f: V(G) → Mat_μ(F₂), μ ≤ 8, and the ratio β(f) = E_pairs D_f / E_edges D_f,
D_f(u,v) = rank(f(u) − f(v)) (pairs: ordered, diagonal included; edges: uniform), against cut metrics and
spectral bounds (research/ports/middle/notes.md §4, §5, §9). Submodules: `f2` (one matrix per u64, row i = byte i,
branch-free rank), `graph` (random d-regular, cycles, tori, named cubic graphs), `groups` (GF(2^k), Cayley graphs
of SL₂/SL₃(F₂[x]/(p)) with elementary or random generators, LPS X^{p,q} via PGL₂/PSL₂(F_q), Cay(Mat_μ(F₂),+)
with rank-one generators, structured placements g ↦ gW and g ↦ M_g P M_g⁻¹), `spectral` (dense / Lanczos λ₂),
`cut` (β_cut exact for n ≤ 24, else sweeps + annealing; cuts S_xy = {v : yᵀf(v)x = 1} read off a placement),
`anneal` (parallel simulated annealing with exact incremental updates; objectives ratio / Lagrangian /
E_pairs under an edge-rank bound; optional diagonal-only = Boolean baseline), `verify` (kernel inequality
of Proposition S for k = 1, 2, 3, consequences (a)–(c), spectral bound (e), JSON output).

```bash
# build the driver for this machine (about 1.7x faster than the portable build)
RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR=target/native cargo build --release --example rankplace
B=target/native/release/examples/rankplace
$B bench
$B named 400000 2,3,4                              # small cubic graphs, exact beta_cut
$B em1 3 64,128 1,2 2,3,4,6 1000000 8              # random cubic graphs: d ns seeds mus iters chains
$B control sl3 2 200000 4 6                        # SL3(F4): structured placement, search from random and from it
$B gstudy lps 5 13 -- 300000 8 2,3,4               # generic: SPEC -- iters chains mus
$B glagr mat 3 0 1 -- 3 400000 1.6,1.9 4           # Lagrangian sweep: SPEC -- mu iters gammas chains
$B ggrad rr 8 256 1 -- 8 1,2,3,4 400000 8          # gradient-bounded: SPEC -- mu rs iters chains
$B em4 3 1011 300                                  # lambda_2 of Cay(SL3(F8)) by Lanczos (n = 16.5M)
python3 ../../research/ports/middle/check_placement.py ../../research/ports/middle/data/rankplace/*.json
```
Graph SPECs: `rr d n seed | named NAME | lps p q | sl m k [modulus] | slrand m k count seed | psl2rand q count seed |
mat mu count seed | cycle n | torus a b`. Placements go to `$RANKPLACE_OUT` (default
`research/ports/middle/data/rankplace`). Python: `rp_rank, rp_random_regular, rp_sl_cayley, rp_lps, rp_spectrum,
rp_beta_cut, rp_evaluate, rp_anneal, rp_verify` (graphs as (n, d, flat adjacency list)).

Caveat: the annealer is a local search. It reliably finds cut-type optima seeded by good cuts and small
non-commutative improvements of them, but it does **not** rediscover rigid algebraic placements from random starts
(see the calibration in research/ports/middle/experiments.md); values are lower bounds on β_ρ.

## Caveats

- `opt` is a local method with many starts: a minimum found this way is a numerical result, not a
  global certificate. Use the reported active set and multipliers to certify by hand or exactly.
- The box constraints are nonsmooth where the minimiser over (t,s) jumps; the Danskin gradient is
  used. In practice this converges, but check `max_violation` against `box_family_all_orders`.
- ALS and LM report residuals. A small residual does not prove a restriction. Residual -> 0 together
  with growing map norms points to a degeneration (border), not a restriction.
- The border ALS objective (coefficients of ε^0..ε^h) can creep towards 0 while the coefficients
  blow up, even on instances proven impossible (2 → (2,2,2,2) reaches 1e-2). Trust only `border_check`.
- Dense environments limit `restrict` to roughly 2^28 environment entries per party (for K_{2,3},
  wires of dimension <= 6).
