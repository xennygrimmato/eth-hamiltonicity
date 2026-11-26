# ivcert: interval certificates for the hull-lemma inequalities

Notebook, 26 Nov 2026. Tool: `tools/ivcert/` (Rust + rayon; README there). Statements are taken from
`research/ports/hull/notes.md` §3.3.

## 0. What is rigorously proved (computer-assisted), and what is not

| # | Statement | Status |
|---|---|---|
| 1 | **(I)** F(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1+9 sin²((θ_i+θ_j)/2)) ≥ 3 on [−π/2,π/2]³ | **CERTIFIED** (401 leaves; 1014 leaves without symmetry); checker OK |
| 2 | **(CL\*)** Φ(ψ) ≥ 0 on the full cube [−π/2,π/2]⁶, covering every hub pattern (spec §3.3(b)) | **CERTIFIED**: 9 certificates (92k + 8 × ~11k leaves), plus one 3-line analytic corner lemma (§2.3); checker OK on all |
| 3 | Book claim (direct, 6 parameters after scaling): Σ_S ≥ (3/√10)·Σ_T in every book | numerically re-checked (§3.1). A direct certificate is in progress (§3.2). Note that it already **follows rigorously** from Prop. 3.1 [R] + Prop. 3.2 [R] + item 2 |

Consequence for the notes: Theorem 5 (R ≥ 3/√10 on five-point CAT(0) sets) is now a computer-assisted
proof, given the [R] Propositions 3.1 and 3.2. The certified statement is (CL\*) exactly as written in
§3.3(b), on the whole cube, so no case distinction is needed.

## 1. Trust base

* IEEE-754 binary64 with round-to-nearest for `+ − × ÷ √`, and a correctly rounded fma (`f64::mul_add`).
* `tools/ivcert/src/interval.rs`, outward rounding. Each endpoint is the round-to-nearest result, moved one
  ulp when the exact error has the wrong sign: TwoSum for sums, the sign of an fma residual for × ÷ √.
  Exact results stay exact. This is how F(0) = 3, Φ(0) = 0 and G(W5) = 0 come out as exact intervals.
* `elem.rs`: sin and cos only, by Taylor series with a Lagrange remainder. The π enclosure is checked
  against 30 digits; no libm is used. (CL\*) and the book problem use no transcendental functions at all.
* `ad.rs`: forward-mode interval AD (gradient and Hessian). `sqrt` near 0, division by an interval
  containing 0, and `abs` of an argument that is not sign-definite all give INVALID derivatives. So no
  non-smooth calculus is used: such boxes close only by the natural extension, or they are split.
* `linalg.rs`: Gershgorin after a congruence with an explicit float P (certified nonsingular), and
  interval Cholesky.
* `bnb.rs`: the leaf tests N, M, T, C, G, K, P, X (README).
* The problem files `problems/*.rs`. Each formula, each symmetry claim and each excluded region is
  stated in that file's doc comment and repeated below.
* The checker `ivcheck` shares the arithmetic and leaf-test code with the prover, but not the search.
  It rebuilds every box from the preorder tree, so coverage is structural. It re-runs the stated test on
  each leaf, and requires the header (problem name, bound, domain) to match the built-in problem bit for
  bit.

Tests: `cargo test --release` runs 18 tests. They cover known-true claims; false claims refused with
exact counterexamples (`bowl2:c=1e-9`, `hull3:c=3.0001`, `hull3:k=2`, `clnear:…:k=2`); true claims with a
non-isolated or boundary equality, which are correctly not proved (`ring2:c=0`, `hull3:k=8`); tampered
certificates rejected (5 kinds); and agreement of the interval evaluators with plain floats, including
the ψ-form against the σ-form of (CL\*).

## 2. Proofs

### 2.1 (I): problem `hull3`

The domain is the float box [−PI_HI/2, PI_HI/2]³, which contains [−π/2,π/2]³. Symmetry: S₃ × {±1};
fundamental domain θ₁ ≥ θ₂ ≥ θ₃, Σθ ≥ 0.

* The equality point 0 is handled by the convexity test on the 8 boxes that have 0 as a corner; together
  they make up [−π/32, π/32]³. On each box the interval Hessian is certified PD by Gershgorin after the
  congruence PᵀHP (plain Gershgorin fails at 0: diagonal 4, off-diagonal 2.5). F(0) = [3,3] and
  ∇F(0) = [0,0] are obtained by exact interval evaluation, since sin 0 = 0 and cos 0 = 1 are exact. So
  the leaf bound is exactly 3.
* Elsewhere: 63 natural and 144 Taylor-2 leaves, with a minimum certified bound of 3.00072. (I) is
  analytic on the cube, because √(1+9 sin²) ≥ 1, so no non-smooth points arise.
* Run: 400 splits, depth ≤ 19, 0.4 s. Without symmetry: 346 N + 660 T + 8 C, 0.9 s.
* Remark: with 9 replaced by 8, equality also holds at the corner (π/2, π/2, −π/2), and the tool
  correctly fails to close boxes there. With 9 replaced by 2 it refutes the claim at
  (π/4, −π/4, 0) with F = 2.808.

### 2.2 (CL\*): reformulation

With σ = sin ψ, cos ψ = √(1−σ²) ≥ 0 and cos μ_i √(1+9 sin²δ_i) = ½√((c_ij+c_ik)² + 10(σ_ij−σ_ik)²),
(CL\*) is **exactly equivalent** to

    Φ(σ) = ½ Σ_i √((c_ij + c_ik)² + 10(σ_ij − σ_ik)²) − 3 + (3/2) Σ_{i<j} |σ_ij + σ_ji| ≥ 0  on [−1,1]⁶,  c = √(1−σ²).

The domain box is exact. This matters because the six corner equalities lie on the boundary, so an
outward-widened π/2 box would contain points where Φ < 0. The formula is algebraic. Python agrees
between the two forms to 5e−12 on 10⁵ random points, and so does the unit test.

Symmetry: S₃ relabelling of the vertices acts on the six ordered pairs, and the global flip is σ ↦ −σ.
Nothing else: swapping ψ_ij ↔ ψ_ik alone does not preserve the ε-terms. Fundamental domain:
w₁ ≥ w₂ ≥ w₃ and w₁+w₂+w₃ ≥ 0, where w_i = σ_ij + σ_ik. A permutation π sends w_i to w_{π(i)} and the
flip negates every w.

### 2.3 (CL\*): the non-smooth point 0 and the corners

**Central region.** On |σ|_∞ ≤ ½ use a_k = (σ_ij − σ_ji)/2 and e_k = (σ_ij + σ_ji)/2, for k = 12, 13, 23.
Then |ε_k| = 2|e_k|, so the kink lies on coordinate hyperplanes. The 8 orthants e_k ∈ s_k·[0, ½],
a ∈ [−½, ½]³ are smooth problems `clnear:rho=0.5:s=±±±` with gain term 3 Σ s_k e_k. Every σ in
[−½,½]⁶ maps into one of them, and conversely σ = (a+e, e−a) ∈ [−1,1]⁶.

Equality at 0, a corner of every orthant box, is closed by the new **gain test** (leaf G). Its
ingredients:

* Taylor-2 at the anchor 0.
* The a-block Hessian is certified PD: λ_min ≥ λ_min(PᵀH_aa P)/‖P‖_F². This is the (I)-slice.
* The e-gradient gives a linear gain γ = min_k inf(∂_{e_k}Φ(0)·s_k) = 3, computed exactly.
* The cross block is bounded by β = ‖H_ae‖_F, and Gershgorin gives μ for H_ee.

The resulting bound is Φ(x) − Φ(0) ≥ ‖e‖₁(γ − w_e(β²/(2λ) + max(0,−μ)/2)) ≥ 0. This makes the
theory agent's sketch (vertex terms change by ≲ 5r|ε| against the gain (3/2)|ε|) rigorous on the box.
Each orthant has 8 gain leaves; their hull is [−1/32,1/32]³ × (e-side 1/32 to 1/16).

| orthant | leaves (N / T / G) | time |
|---|---|---|
| +++, −−− | 5035 / 3565 / 8 | 1.0 s |
| ++−, −−+ | 7556 / 4121 / 8 | 1.2 s |
| +−+, −+− | 7448 / 4145 / 8 | 1.2 s |
| +−−, −++ | 7244 / 4172 / 8 | 1.1 s |

**Corners: analytic lemma (X leaves).** Region: for a pair {j,k} and a sign s, s·σ_jk ≥ 15/16 and
s·σ_kj ≥ 15/16. Put d₁ = 1 − sσ_jk and d₂ = 1 − sσ_kj, both in [0, 1/16]. Then:

* V_j ≥ c_jk/2 = ½√(d₁(2−d₁)) ≥ ½√d₁, and likewise V_k ≥ ½√d₂;
* V_i ≥ 0, and the other two |ε| are ≥ 0;
* |ε_jk| = 2 − d₁ − d₂.

Hence Φ ≥ ½(√d₁ + √d₂) − (3/2)(d₁ + d₂) ≥ 0, since 3d ≤ √d for d ≤ 1/9. The region contains all six
equality corners of §3.3(c): at each of them one pair has σ_jk = σ_kj = s. A sampled check of the region
gives min Φ = 0.83 away from the corner points themselves.

**Outer region.** Problem `clstar:rho=0.5`: [−1,1]⁶ minus the central cube (X leaves backed by the 8
clnear certificates) and minus the corner regions (X leaves backed by the lemma). Result: 79 752 natural,
1 696 Taylor-2, 10 678 pruned and 69 X leaves; 92 194 splits, depth ≤ 39, 3.4 s. Without symmetry:
520 956 N + 7 920 T + 94 X, 19 s. The trivial region Σ|ε| ≥ 2 closes by the natural extension, and the
boundary faces |σ| = 1 (where √(1−σ²) is not differentiable) close by the natural extension too.

**Earlier attempt with ρ = 1/8.** This failed just outside the central cube, near the slice ε = 0. There
the only smooth-free tests are first order, while Φ ≈ 0.75|θ|² is small. Enlarging the central
(a,e)-region to ρ = ½, the largest value for which σ = a ± e stays in [−1,1], removed the problem.

Falsification check: with 9 replaced by 2 the tool refutes `clnear:…:s=+++:k=2` and `clstar:k=2` with
exact counterexamples, for example σ = (0.4921875, 0.4453125, −0.5078125, −0.0078125, −0.453125,
−0.015625) with Φ ∈ [−5.6514e−4, −5.6514e−4].

## 3. The book claim

### 3.1 Numerical re-check (different methods from Nelder–Mead)

Setup: spine u₁ = (0,−1), u₂ = (0,1); v_j = (ρ_j ≥ 0, s_j). The pair distance is
d^Z_jk = min_{t∈[−1,1]} |v_j − (0,t)| + |v_k − (0,t)|, computed exactly by clamping the unfolded crossing
point. This is the correct book metric: paths may cross only the segment, not the whole spine line.
Script: `scratchpad/book_numeric.py`, not kept.

* L-BFGS-B, 600 multistarts at random scales: min 0.94868329806 at ρ = (3.00003, 2.99999, 3.00001),
  s ≈ 0, which is W5(ℓ, ℓ/3) (ρ = 1.5·D, foot at the midpoint). The other local minima found are 0.9519,
  0.9613, 0.9703, 0.9999 and 1.
* Differential evolution (popsize 40, tol 1e−13): 0.94868329805052 at (3,3,3,0,0,0).
* Basin hopping (300 iterations): 0.9486832981 at the same point.
* 3·10⁵ uniform random points in [0,8]³ × [−6,6]³: min 0.9511.
* The Hessian of G = √10·Σ_S − 3Σ_T at W5 (with D = 2) has eigenvalues 0.2, 0.2, 0.2, 0.3, 0.3, 1.8:
  positive definite, so the minimiser is isolated after scaling.

All of this agrees with the notes' record: minimum 3/√10 = 0.948683298050514 at W5.

### 3.2 Direct certificate (stretch goal)

Problems `book:m=128` and `bookface:f=rho|s:m=128` (`problems/book.rs`). G is positively homogeneous of
degree 1 in (h, ρ, s). The domain is covered by:

* region A: h = 1, ρ ∈ [0,128]³, s ∈ [−128,128]³;
* two face problems: max(ρ_j, |s_j|) = 1 and h ∈ [0, 1/128], reduced by page permutations and s ↦ −s
  to ρ₁ = 1 or s₁ = 1.

d^Z is evaluated branch-wise, using enclosures over the box:

* line formula when y* ∈ [−h, h];
* g(±h) beyond the ends;
* g(h·τ) with τ a constant enclosure of the minimiser when the box straddles an end (Danskin: C¹ only);
* a value-only enclosure when ρ_j + ρ_k may vanish.

At W5 every term is exact (√100 = 10), so G(W5) = 0 exactly.

What was needed:

(a) **An exact critical point.** The interval gradient at W5 is not exactly 0, because AD forms
0.5/10 = 0.05, which is inexact. The problem therefore declares the anchor critical. The analytic proof
is two lines: G is even in s, and ∂_ρ G = 2·10·3/10 − 3·2·6/6 = 0. The tool still checks that the
gradient enclosure contains 0.

(b) **A new leaf test K (hull-convexity).** The Hessian at W5 is ill-conditioned (λ_min = 0.2, entries
up to 1.8). Neighbouring boxes therefore never close by the Taylor-2 form: the interval cross terms lose
about as much as the margin, at every scale. K certifies the Hessian PD on a bisection cover of
hull(box, W5), so G is convex on that hull. This needs G to be C¹, which holds by Danskin. Then
G ≥ G(W5) = 0 on the box.

(c) **Boxes where v_j lies on the spine line.** These use the value-only enclosure g(T), with T the
clamp of hull(s_j, s_k), together with upper bounds g(±h) and g(0). These configurations are not smooth
(a distance vanishes), so only the natural extension applies there.

**Status: NOT completed.**

* Region A (`book:m=128`, run with `--max-depth 120 --hull-max 0.5`) was stopped after 58.7·10⁶ nodes
  (about 40 min, on a machine shared with other jobs; load 16 on 4 cores). It had **0 failing boxes and
  no counterexample** up to that point, but the run is not a certificate. Nodes were being produced at
  0.8–5·10⁶ per minute, and the total is unknown, plausibly 10⁹ or more.
* The face problems (`bookface:f=rho|s`) were not run to completion either.
* Two earlier runs were lost. One was killed by OOM at 33·10⁶ nodes, before subtrees were streamed to
  text; the tree is now serialised as it is built, so memory stays around 0.5 GB. The other was stopped
  to fix an enclosure.

Where the time goes: configurations in which some v_j lies near the spine line (ρ_j ≈ 0), and
especially near u₁ or u₂. There a distance vanishes and the d^Z branch can only be enclosed, not
differentiated, so only the natural extension applies. The margin of G is O(1) there, but the region
is six-dimensional and the cancellation between √10·Σ_S and 3Σ_T (both ~20) forces widths of
10⁻²–10⁻³.

The K test works near W5: the unit test `book_hull_convexity_near_w5` closes, with bound exactly 0, a
box at distance 5·10⁻⁴ that Taylor-2 cannot close, and the box [3±1/32]³ × [±1/32]³ with a 15-box PD
cover. The interval Hessian is too wide for a PD cover of [3±1/8]³ × [±1/8]³ within 4096 boxes, so
`--hull-max` should be about 0.06, not 0.5. With 0.5 the run wastes PD-cover attempts.

What a complete direct certificate would need:

1. A problem-specific reduction in the near-spine region, for example monotonicity of G in ρ_j for
   small ρ_j (a one-variable lemma) or a separate treatment of "v_j = u_i".
2. A smaller region A: M = 128 is far more than needed. A sharper face bound than
   G ≥ 0.32Σr − 25h would allow M ≈ 8.
3. Hours of CPU on an unloaded machine.

None of this is needed for Theorem 5, because the calibration (Prop. 3.2) plus the certified (CL\*)
already imply the book claim. A direct certificate would only be an independent check of Prop. 3.2's
algebra. The notes' own random-book check (20 000 books) and the numerics in §3.1 already give such a
check numerically.

## 4. Files

* Tool: `tools/ivcert/` (sources, README, tests, `run_proofs.sh`, `examples/debug_box.rs`).
  `.gitignore` covers `target/` and `certs/`.
* Small certificates: `tools/ivcert/certificates/hull3.cert` (7 KB) and `hull3-nosym.cert` (19 KB).
  These could be committed.
* Large certificates (13 MB, gitignored), regenerated by `tools/ivcert/run_proofs.sh` (about 35 s):
  `tools/ivcert/certs/`.

| file | sha256 |
|---|---|
| clnear_rho0.5_s+++.cert | c8ee406f21236a845eb1b7999ca4425ef4dd582b2ea1d3df14850051d8d9588c |
| clnear_rho0.5_s++-.cert | 2b0f55fba638d34a089c6117d5cfdd4e1afe28f5918c2a61ba4d115b58ca6e5b |
| clnear_rho0.5_s+-+.cert | 65c523c53b9672b6a67cf418f5b87385d78583fb90a87a2bd0222b29eda50448 |
| clnear_rho0.5_s+--.cert | e17a14bade0bf055ba0077effb2db85fb3ed6b47a722fdac373f994aa97b365d |
| clnear_rho0.5_s-++.cert | 7bcb152ebe50b6ca957f83816d9d6bae81af84b353fc6d4da565ad252105e40c |
| clnear_rho0.5_s-+-.cert | 554ac14e026e09293aa35e8b23116800a729a65438130b9a391c24d82fdb5d8a |
| clnear_rho0.5_s--+.cert | f35125591027359a127ce486412d401aeb752af0feb4314345ac219056d1b2c7 |
| clnear_rho0.5_s---.cert | 6e70a18d451bdb9fec33b36ea8f4e99649be61a3d9479647252434077f11e877 |
| clstar_rho0.5.cert | 13a83a9dfb2c4486c2b27c96d8e3d9ce6b7aab3a875b7a9d58c98d1931cd08a0 |
| clstar_rho0.5_nosym.cert | 5656297f4b7a1224bd4d7d8b64fa180c5c0a8d13227c7032c721f5cc491c10d9 |

The certificates are deterministic, so regenerating them gives the same files, as long as no code change
alters a leaf decision.
