# E3 notebook: the K_{2,3} tensor-rate problem (ideas-ports.md Ad.2)

Status tags: [N] computed numerically, [R] proved here (short proof given), [C] conjecture, [X] dead.
Tools: `tools/tensorlab` (Rust + rayon, PyO3 bindings; see its README). All commands below run from
`tools/tensorlab` after `cargo build --release --examples`. Machine: 4 cores, 3 of them shared with a
niced background job, so the timings are wall-clock under load.

Setup. Points / parties 0 = u1, 1 = u2, 2 = v1, 3 = v2, 4 = v3. Supply S = six wires u_i v_j. Demand
T = v1v2, v2v3, v1v3, u1u2. R(d) = Σ_S d / Σ_T d. f* = min over spectral d of R(d), and spectral ⊆ CAT(0).

## Summary

| quantity | value | status |
|---|---|---|
| min R over triangle-only metrics (flow dual) | 3/4 | [N] (sanity check; known) |
| min R over triangle + Euler quadrilateral (squared diagonals ≤ squared sides) | 0.893020459468 | [N] |
| f_Q: min R over triangle + all Reshetnyak quadruple inequalities | 0.944605973782578821168757419… = root of 58x³ − 14x² − 29x − 9 | [N] (60-digit KKT solve + PSLQ) |
| f_CAT5: min R over 5-point subsets of CAT(0) spaces (triangle + Gromov–Sturm box inequalities, exact by Toyoda's theorem) | 0.948683298050505 = 3/√10, at W5 | [N] (1000/1000 starts; KKT residual 1e-15) |
| min R over products of 1, 2, 3 trees; R^4; cone over the Heawood graph | 1; 3/√10; 3/√10; 1; 3/√10 | [N] |
| min R over Euclidean configurations | exactly 1 (ℓ2 ⊂ ℓ1); Ad.2's "≥ 1.078" is wrong | [R] |
| exact single-shot rate 1 (all wires dim D → dim D), any D, any field | impossible | [R] |
| rate 1 at bond dimension 2, border (degeneration) over C | impossible | [R] |
| any protocol beating 3/4 found by ALS/LM at the sizes tried | none (best residual 0.64 at 16 → 9) | [N], scope below |

Consequence. Prices are CAT(0) (thm_cn), so f* ≥ f_CAT5. If f_CAT5 = 3/√10 is the global minimum
(numerically it is), then **f* ≥ 3/√10 = 0.948683 unconditionally**. With the hull claim (W5 is a price
when contracting fails), we would have f* = 3/√10 exactly under ¬contracting. A protocol with rate
> 3/√10 then refutes "W5 is a price".

## (a) Geometry

### Which inequalities, and why CAT(0) implies them
- Triangle inequalities: 30 on 5 points (3 per triple).
- Reshetnyak quadruple inequality (AN Lemma C.4(b); Reshetnyak 1968, in the form of the
  Berg–Nikolaev quasilinearisation): |xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv| for all x,y,u,v. It holds
  in every CAT(0) space. After deduplication (the inequality is invariant under (x,y,u,v) → (y,x,v,u)
  and → (u,v,x,y)) there are 6 per 4-set, so 30 on 5 points. It implies the Euler quadrilateral
  inequality (squared diagonals ≤ squared sides, = EG (4.5)) through 2ab ≤ a² + b². Coincident
  points reduce it to the triangle inequality. **This is the family used for f_Q.**
- Gromov–Sturm box inequalities (Toyoda, AGMS 2020, arXiv:1907.09074v2, Def. 1.1, checked from the
  arXiv text): for all t,s ∈ [0,1],
  (1−t)(1−s)|xy|² + t(1−s)|yz|² + ts|zw|² + (1−t)s|wx|² ≥ t(1−t)|xz|² + s(1−s)|yw|².
  **Toyoda Thm 1.3: a metric space with at most 5 points embeds isometrically in a CAT(0) space iff it
  satisfies these inequalities.** So the box family defines f_CAT for 5 points exactly. Only 3
  cyclic orders per 4-set are needed (rotation maps (t,s) → (1−s,t)), so there are 15 constraints.
  The oracle minimises the quadratic over the square exactly (corners, edges, interior critical point:
  `metric::box_min`, tested against a 401² grid and Toyoda's Example 1.2).

### f_Q [N]
Command: `./target/release/examples/e3a_fq resh 2000` (37.7 s): 2000/2000 feasible starts reach the
same value 0.944605973782579, KKT residual 4e-16, all multipliers > 0.
Minimiser (v1 ↔ v3 symmetric; scaled to max 1):
u1u2 = 0.399682, u1v1 = u1v3 = 0.572405, u1v2 = 0.427595, u2v1 = u2v3 = 0.494730, u2v2 = 0.639539,
v1v2 = v2v3 = 1, v1v3 = 0.989460.
Active constraints: triangles v1v2 = u1v1 + u1v2, v2v3 = u1v2 + u1v3, v1v3 = u2v1 + u2v3. Six
Reshetnyak equalities, two per quadruple {u1,u2,vi,vj}:
u1u2² + vivj² = u1vj² + u2vi² + 2·u1vi·u2vj, and the same with i ↔ j.
Exact value: the symmetric reduction (a = u1v1, b = u1v2, c = u2v1, e = u2v2, h = u1u2;
active E1 = h² + (a+b)² − b² − c² − 2ae, E2 = h² + (a+b)² − a² − e² − 2bc, E3 = h² + 4c² − (a+c)²)
was solved to 60 digits (`scratchpad e3/exact_fq.py`, mpmath findroot on the KKT system). It gives
0.944605973782578821168757419020357545822644107482405012603143, and PSLQ finds
58x³ − 14x² − 29x − 9 = 0. The cubic has no rational roots. The independent check at 60 digits over
all ordered quadruples and triangles gives max violation 5e-63. (A sympy Gröbner certificate of the
cubic did not finish in 10 min: [N], not [R].)
The minimiser is **not** CAT(0): it violates the box inequalities for the cycles (u1,vi,u2,vj).
- (v1,v2): min Q = −6.92e-4 at (t,s) = (0.241881, 0.535027).
- (v1,v3): min Q = −8.05e-4 at (0.759442, 0.5).
- (v2,v3): min Q = −6.92e-4 at (0.241881, 0.464973).

So f_Q < f_CAT. The Reshetnyak family is not enough on 5 points; the extra condition is the box
family at off-centre (t,s) (equivalently the rigidity in the equality case of C.4(b)).

With triangle + Euler only: `e3a_fq euler 400` gives 0.893020 (346/400 starts; other local minima
0.894, 0.900, 0.9028, 0.9129, 0.9487). Triangle only: 0.75 (400/400).

### f_CAT5 [N]
Command: `./target/release/examples/e3a_fq box 1000` (70.6 s). All 1000/1000 starts end at
0.948683298050505 (3/√10 = 0.948683298050514). The minimiser is W5 (uu : uv : vv = 1/3 : √10/6 : 1).
Active set: exactly the three box inequalities for the cycles (u1, vi, u2, vj), each at (t,s) = (1/2,1/2)
(that is, the Euler equality uu² + vivj² = 4uv²), each with multiplier 2√10 (normalisation
Σ_T d = 1). No triangle is active. This is a local KKT certificate only. The global statement
"R ≥ 3/√10 on all 5-point CAT(0) configurations" is [C], backed by 1000 starts. A proof has to use
(t,s) ≠ (1/2,1/2) away from W5, because the Euler inequalities alone give 0.893.

### Model spaces [N]
- `e3a_cat w5`: W5 (l=3, h=1) has R = 0.948683298050514. Triangle, Reshetnyak, Euler and box
  inequalities all hold, with the Euler/Reshetnyak equality on the {u,u,v,v} quadruples. It is not ℓ1:
  cut-cone NNLS relative residual 2.47e-2, and the pentagonal inequality with b = (−1,−1,1,1,1) is
  violated by 1.026. **For this b the pentagonal inequality is exactly R ≥ 1**, so R < 1 ⇔ the
  pentagonal violation. Gram min eigenvalue −7.08 (not Euclidean). Minimum cut ratio 1.
- `e3a_cat trees 1 20`: single trees give 1 (trees are ℓ1).
- `e3a_cat trees 2 30` (all 120 unordered topology pairs × 30 starts, 12 s): minimum 3/√10 at W5.
- `e3a_cat trees 3 12` (680 triples, 47 s): minimum 3/√10 at W5.
- `e3a_cat euclid 4 200`: minimum 1 (degenerate line configurations). [R] Euclidean metrics are ℓ1,
  so R ≥ 1. The value 1.078 in Ad.2 is presumably a non-degenerate local minimum.
- `e3a_cat cone 0 3000` (Euclidean cone over the Heawood graph with edges π/3, girth 2π checked;
  77 s): minimum 3/√10 at W5 (it lies in the cone: tangent cone of the Ã2 building).
- `e3_n5`: N5 = √rank on {0, I, e11, e21+e22, e12+e22} ⊂ Mat_2(F_2) (u1,u2,v1,v2,v3 in that order).
  It has uu = vv = √2 and uv = 1, so R(N5) = 1.0607. It is realised exactly in the tripod × R diamond
  (u at heights ±1/√2 on the spine, v at leg distance 1/√2), with max error 2e-16. The three
  quadrilaterals (n, t_i, s, t_j) have Euler equality, so they are flat squares. W5 (l = 1/(2√2),
  h = l/3) sits in the same diamond exactly. N5 is **ℓ1-embeddable** (NNLS residual 4e-16) but not
  Euclidean (Gram eigenvalue −0.30).

### Instance scan for the coordinator's request 2 [N]
`e3_scan w5 2 15`, `e3_scan n5 2 10` (each of the 10 pairs is unused, supply ×1..2 or demand ×1..2;
9.8M instances, 5 s). The bounds are f_cut (15 cuts), f_flow (min over the 25 extreme rays of MET_5:
15 cuts + 10 K_{2,3} path metrics) and f_d.
- N5: **no instance** has f_N5 < f_cut, and none can on these five parties, because N5 is ℓ1 [R].
  Refuting "N5 is a price" needs hub parties.
- W5, top instances by f_cut/f_W5:
  1. K_{2,3} itself (and its scalings ×2): gap 1.05409, f_cut 1, f_W5 0.94868, f_flow 0.75.
  2. supply u1v1×2, u1v2×2, u1v3, u2v1, u2v2, u2v3; demand u1u2, v1v2×2, v1v3, v2v3:
     gap 1.02774, f_cut 1, f_W5 0.97301, f_flow 0.8.
  3. supply u1v1×2, u1v2, u1v3×2, u2v1×2, u2v2×2, u2v3; demand u1u2, v1v2×2, v1v3×2, v2v3:
     gap 1.01193, f_cut 1, f_W5 0.98821, f_flow 0.8333.
  4. supply u_iv_j with u1-side ×2, u2-side ×1; demand u1u2, v-triangle ×2: gap 1.00139.

  So K_{2,3} is the best place to look; every other instance has a much smaller gap.

## (b) Protocols

Driver: `e3b_als Ds d12 d23 d13 duu starts sweeps [r|c] seed [LM]`. Supply: six wires of dimension
Ds. Demand: v1v2 = d12, v2v3 = d23, v1v3 = d13, u1u2 = duu. Single-shot rate = min log d / log Ds.
Every run first checks all 15 cut flattening ranks (`restrict::cut_check`). All runs below pass
that check unless stated. "res" = ||(⊗A)S − T|| / ||T||, rechecked through the dense S
(`residual_dense`, an independent code path).

### Exact obstructions [R]
1. **Rate 1, single shot, any D, any field: impossible.** Equal wire dimensions make every v-cut tight
   (D² = D²), so each A_v is invertible. Then (A_u1 ⊗ A_u2)S = M1 ⊗ M2 = (⊗A_v⁻¹)T, where M_i is A_{u_i}
   applied to u_i's three legs. For a product M1 ⊗ M2, rank_{u1} ≤ rank_{u1u2}. In T these ranks are
   D and 1. The same argument kills (4,4,4,3), (4,4,4,2) at D = 4 and (3,3,3,2) at D = 3, and in
   general any instance with v-cuts tight and duu ≥ 2.
2. **Bond dimension 2: no degeneration (border restriction) of S_2 onto any T with v1v2 = v2v3 = v1v3 = 2,
   over C.** Pair the u1 and u2 outputs with e1*. The v-part becomes the triangle Δ = ⟨2,2,2⟩ on one
   side and (⊗A_v)(X ⊗ Y) with X, Y ∈ (C²)^{⊗3} on the other. Border rank ≤ 2·2 = 4 < 7 = brank⟨2,2,2⟩,
   and the set of border rank ≤ 4 is closed. This covers rate 1 at bond dimension 2 in the border sense.
   With bond dimension D in general, the bound reads brank⟨d,d,d⟩ ≤ g(D)², with g(D) the maximal border
   rank in C^D ⊗ C^D ⊗ C^D (g(3) = 5), so it gives nothing for D ≥ 3.

### Numerical runs [N]
| instance (Ds; d12,d23,d13,duu) | rate | method / scope | best res | comment |
|---|---|---|---|---|
| 2; 2,2,1,1 | — | ALS 16×400 | 8e-15 | routing exists (sanity) |
| 2; 2,2,1,1 | — | F_2 SAT | SAT, verified | sanity of the SAT encoder |
| 2; 2,2,2,1 | — | ALS 64×500 + LM 5000 | 0.6695 floor | excluded by [R]2 |
| 2; 2,1,2,2 | — | ALS 16×400 | 0.500 | |
| 2; 2,2,2,2 | 1 | ALS R 64×500 + LM 20000; ALS C 64×3000 | 0.790569 = √(5/8) floor, R and C | excluded exactly ([R]1) and border ([R]2) |
| 3; 2,2,2,2 | 0.631 | ALS R 32×30000; LM 20000 | 6.3e-2 (ALS), 5.7e-3 (LM, norm 39 → 87, still falling) | border-like (residual falls while norms grow); rate < 3/4 anyway |
| 3; 2,2,2,2 | 0.631 | ALS C 16×5000 | 0.179 | |
| 3; 3,3,3,2 | 0.631 | ALS 32×600 | 0.818 | excluded by [R]1 |
| 4; 3,3,3,3 | 0.792 | ALS R 64×1500 + LM 300 on the best 3 | 0.6437 | no sign of a protocol |

Additional tools and runs:
- **Border ALS** (`e3b_border Ds d12 d23 d13 duu K h starts sweeps`): maps A_p(ε) = Σ_{k≤K} ε^k A_p^(k),
  fitting the coefficients of ε^0..ε^h of (⊗A(ε))S to (0,…,0,T). Environment polynomials come from
  evaluation at roots of unity plus an inverse DFT.
  **Calibration failure:** on the proven-impossible 2 → (2,2,2,2) the objective still reaches 1.4e-2
  (K=1,h=1), 3.4e-2 (K=1,h=2), 1.1e-2 (K=2,h=2) and 7.3e-3 (K=1,h=1, 4000 sweeps), with growing
  coefficients. The independent dense check |(⊗A(ε))S/ε^h − T|/|T| at ε = 1e-1, 1e-2, 1e-3 stays
  O(1)–O(10²). So the objective by itself is meaningless (it can creep towards 0 as the coefficients
  blow up); only the dense check counts. On 3 → (2,2,2,2): objective 1.05e-2, dense check
  60 / 1.2 / 10.5, so not a border solution either. [N]
- **F_2 SAT** (`python/f2sat.py`): the encoder is validated (swap SAT, no-wire UNSAT, K23 2 → (2,2,1,1)
  SAT with an independent check). 2 → (2,2,2,1) got no verdict from CaDiCaL in 25 min (naive encoding,
  no symmetry breaking); stopped. Exact rate 1 over F_2/F_3 needs no SAT: [R]1 holds over every field.
- **Calibration table** (`e3b_table Ds dmax starts sweeps lm`): all demand vectors with entries
  ≤ dmax. f_flow = fractional routing value (min over the 25 extreme rays of MET_5; ≥ 1 means
  routable). f_CAT5 = min over box-feasible metrics: **a lower bound on the asymptotic rate**, since
  prices are 5-point CAT(0); ≥ 1 means asymptotically achievable. f_W5: an upper bound only if W5 is a
  price (¬contracting + hull). f_cut: an unconditional upper bound.
  Ds = 2: the only non-routable vector is (2,2,2,2) (excluded by [R]1).
  Ds = 3 (ALS 32 × 600 + LM 300 on the best 2):

  | demand (d12,d23,d13,duu) | f_flow | f_CAT5 | f_cut | best residual |
  |---|---|---|---|---|
  | (3,3,2,2) and permutations | 0.9197 | 1.0000 | 1.0 | 0.688–0.707 |
  | (3,2,2,3) and permutations | 0.9197 | 1.1842 | 1.1403 | 0.707 |
  | (3,3,2,3) and permutations | 0.8262 | 0.9998 | 1.0 (f_W5 = 1.067) | 0.79–0.81 |
  | (3,3,3,2), (3,3,3,3) | 0.826 / 0.75 | 0.979 / 0.9487 | 1.0 | excluded by [R]1 |

  So (3,2,2,3) (v1v2 = u1u2 = 3, the other two = 2) is beyond routing but asymptotically achievable
  with margin 18% (f_CAT5 = 1.18). Even so, no single-shot restriction appears (residual 0.707).
  Single-shot tensor coding at these sizes looks no better than routing.
  These are non-uniform demand vectors: they test weighted inequalities, not the uniform rate.

Remark from the theory agent (recorded at the coordinator's request): a protocol beating 3/√10 must use
an identity that is false in buildings, beyond the crossing identity and the one-point extension
(those two together reach exactly 3/√10). So generic-start ALS is the right tool for rates
> 3/√10, while structured constructions are the right tool for rates in (3/4, 3/√10]. Since
f* ≥ 3/√10 (nearly proved), protocols with rates in (3/4, 3/√10] exist asymptotically. The failures
above say something about the sizes, not the truth.

(See the end of the notebook for the runs still in progress.)

## What I would run next
- A border ALS with maps polynomial in ε (A = A0 + εA1). The degeneration question at 3 → 2 and
  4 → 3 needs it; the norm-growth diagnostic is only suggestive.
- 5 → 4 (rate 0.861) and 6 → 5 (0.898) with more starts. Above 3/√10 the smallest uniform sizes are
  10 → 9 (0.954) and 11 → 10: dense targets of 81⁴ ≈ 4.3e7 entries, out of reach of the dense
  environment code. That needs a contraction that never forms the dense environment
  (Gram matrices through the doubled network).
- A proof of R ≥ 3/√10 on 5-point CAT(0) configurations: use the box inequalities at the active
  points found near each local configuration (the multistart shows no other basin).
- Non-uniform instances from the scan (#2 above, f_W5 = 0.973 vs f_cut = 1): a single-shot test there
  needs wires of dimensions 4/2 mixtures. Feasible.
