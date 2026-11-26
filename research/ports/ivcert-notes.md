# ivcert: interval certificates for the hull-lemma inequalities

Notebook, 26 Nov 2026. Tool: `tools/ivcert/` (Rust + rayon; README there). Statements are taken from
`research/ports/hull/notes.md` §3.3.

## 0. What is rigorously proved (computer-assisted), and what is not

| # | Statement | Status |
|---|---|---|
| 1 | **(I)** F(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1+9 sin²((θ_i+θ_j)/2)) ≥ 3 on [−π/2,π/2]³ | **CERTIFIED** (401 leaves; 1014 leaves without symmetry); checker OK |
| 2 | **(CL\*)** Φ(ψ) ≥ 0 on the full cube [−π/2,π/2]⁶, covering every hub pattern (spec §3.3(b)) | **CERTIFIED**: 9 certificates (92k + 8 × ~11k leaves), plus one 3-line analytic corner lemma (§2.3); checker OK on all |
| 3 | Book claim (direct, 6 parameters after scaling): Σ_S ≥ (3/√10)·Σ_T in every book | numerically re-checked (§3.1). A direct certificate is in progress (§3.2). Note that it already **follows rigorously** from Prop. 3.1 [R] + Prop. 3.2 [R] + item 2 |
| 4 | **S(9/10)**: K_{2,3} refined bracket Br′(σ; 9/10, 6/5) ≥ 0 on the hard region 𝓕′₁ (k2m notes §5.4) | **CERTIFIED** (§5): 16 certificates, 23.3M leaves; ivcheck and ivcheck2 OK |
| 5 | **(CL\*\*₀)**: Br′(σ; 12/13, 15/13) ≥ 0 on 𝓕′₁, equality at σ = 0 | **CERTIFIED** (§5): 24 certificates, 62.1M leaves; ivcheck and ivcheck2 (with its own origin lemma) OK |

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

## 5. K_{2,3} refined bracket on the hard region: S(9/10) and (CL\*\*₀)

Source: `research/ports/k2m/notes.md` §5.2 (Proposition C′, the formulas for N_i in the six exit sines) and
§5.4 (Lemma R, "Certificate spec"). The formula, the region and every definition were taken from §5.4
as written. Problem file `tools/ivcert/src/problems/k2m.rs`; scripts `tools/ivcert/run_k2.sh` (prover and
ivcheck) and `tools/ivcheck2/run_k2.sh` (independent check).

### 5.1 Statements certified

With σ = (σ₁₂,σ₁₃,σ₂₁,σ₂₃,σ₃₁,σ₃₂) ∈ [−1,1]⁶, c = √(1−σ²), τ = √(1−λ²). For a vertex (u,v): Q = u+v,
W = (c_u+c_v)² + Q², C = ½√(τ²(c_u+c_v)² + (u−v)²) + (λ/2)|Q|, and N = 1 if 2|Q| ≥ λW, N = C otherwise.
Then E = Σ_{i<j}|σ_ij+σ_ji|, X = Σ|Q_i| − E, and Br′ = N₁+N₂+N₃ − (λ/2)X − η. The region is
𝓕′₁ = {Q₁ ≤ 0, Q₂ ≥ 0, Q₃ ≥ 0, 2|Q₁| ≤ λW₁, 2Q₂ ≤ λW₂}.

* **S(9/10)** (λ, η) = (9/10, 6/5): **Br′ ≥ 0 on 𝓕′₁. CERTIFIED** (ivcert + ivcheck; ivcheck2: see §5.5).
  The certificates prove 10·Br′ ≥ 0. The true minimum is +0.0627 (below), but a leaf bound is only ≥ 0,
  so the certified margin is just "≥ 0". By the mutation tests, even 10·Br′ ≥ 10⁻⁴ is not what these
  certificates prove.
* **(CL\*\*₀)** (λ, η) = (12/13, 15/13): **Br′ ≥ 0 on 𝓕′₁, with equality at σ = 0. CERTIFIED** (ivcert +
  ivcheck; ivcheck2: §5.5).

*Coverage, and why 𝓕′₁ is enough.* Lemma R (notes §5.4, a hand proof, not checked here) gives Br′ ≥ 0 off
𝓕′ = {frustrated at some v_i, v_i curved, and another vertex curved}. Two symmetries preserve Br′:
- the page permutations σ_ij ↦ σ_π(i)π(j) (Q_i ↦ Q_π(i), W_i ↦ W_π(i), the pairs are permuted);
- the flip σ ↦ −σ (c, |Q|, |ε| and (u−v)² are unchanged; Q changes sign).

Using them, one can move the frustrated vertex to page 1 with Q₁ ≤ 0 ≤ Q₂, Q₃, and the second curved vertex to
page 2 (if it is v₃, the exchange of pages 2 and 3 does it). "Curved" (|μ| < κ) closes to 2|Q| ≤ λW. So
𝓕′ ⊂ ∪_{g ∈ S₃×Z₂} g(𝓕′₁), and the certified set is exactly the closed region that the notes say remains.
Numerical check of the complement (scratch script, 3·10⁵ draws, half of them near the faces): at the
1.4·10⁵ points that lie in no image of 𝓕′₁, min Br′ = +0.0034 (λ = 9/10) and +0.0032 (λ = 12/13). Both
minima are near the cut-type zeros of Lemma R. No negative value.

*Spec questions.* None was blocking. Two remarks:
- "2Q₂ ≤ λW₂" is written without |·|. It is used as written; it equals 2|Q₂| ≤ λW₂ on Q₂ ≥ 0.
- Only N ≥ C (true everywhere: N ∈ {C, 1} and C ≤ 1) and N = 1 where 2|Q| ≥ λW are used. The claim "N = C
  on the curved boundary" is not needed.

### 5.2 Numerical reproduction (before certifying)

A plain float implementation of the spec (N via the linear test, X with |Q|) agrees with the
trigonometric definition N = cos((κ−|μ|)₊), sin κ = λ cos δ, to 9·10⁻¹⁶ on 5000 points.
- S(9/10): 4·10⁵ uniform points (11.8% lie in 𝓕′₁) give min 0.126. 400 SLSQP local searches with the five
  constraints give **min Br′ = +0.0627157**, at σ ≈ (−.7434, −.9631, .7434, −.7434, .9631, .7579). This
  point is on the boundary 2|Q₁| = λW₁ ("v₁ becomes linear") with Q₂ = 0, as in the notes. The same value
  also occurs at a point with v₃ curved.
- (CL\*\*₀): the minimum is 0 at σ = 0 only. Restricted to |σ|₂ ≥ r, the minimum is 1.7·10⁻⁴ (r = .05),
  6.6·10⁻⁴ (.1), 2.6·10⁻³ (.2) and 1.6·10⁻² (.5), roughly 0.066|σ|². On the slice e = 0,
  min Br′/t² = 0.13 > 0.
- No negative value was found anywhere in 𝓕′₁.

### 5.3 Encoding

*Pieces.* 𝓕′₁ is covered by 16 closed pieces
P(case, s) = 𝓕′₁ ∩ {2Q₃ ≤ λW₃ (case c) | 2Q₃ ≥ λW₃ (case l)} ∩ {s_k ε_k ≥ 0, k = 12, 13, 23},
with s ∈ {±}³ the signs of ε₁₂ = σ₁₂+σ₂₁, ε₁₃ = σ₁₃+σ₃₁, ε₂₃ = σ₂₃+σ₃₂. On a piece, every |·| has a
fixed sign. Moreover N₁ = C₁ and N₂ = C₂ (only N ≥ C is used), N₃ ≥ C₃ in case c, N₃ = 1 in case l, and
C_i − (λ/2)|Q_i| = V_i := ½√(τ²(c+c′)²+(u−v)²) exactly. So on the piece:
- case c: Br′ ≥ f := V₁+V₂+V₃ + (λ/2)Σ_k s_kε_k − η;
- case l: Br′ = f := V₁+V₂ + 1 − (λ/2)Q₃ + (λ/2)Σ_k s_kε_k − η.

These are smooth wherever every c > 0. There is no kink and no case distinction inside a box, so mean-value
and Taylor forms work across the planes ε = 0 and Q = 0. Positive part, arcsin and cos of a clipped
argument never appear: they are eliminated exactly by the algebraic form of §5.2.

*Exact constants.* The prover evaluates f_M = M·f with M = lcm of the denominators of λ and η. Then
M·V = ½√(A(c+c′)² + B(u−v)²) with integers A = M²τ², B = M², and M λ/2 and M η are exact floats:
- S(9/10): M = 10, A = 19, B = 100, 9/2, 12;
- (CL\*\*₀): M = 13, A = 25, B = 169, 6, 15. Here f_M(0) = 3·½√100 − 15 = 0 exactly.

*Region handling.* A box is closed as X ("excluded") only if interval evaluation of one of the piece's
defining inequalities, as written above (with an enclosure of λ), has upper end < 0 on the whole box. Every
box that meets the piece is proved. A box centre with f < bound counts as a counterexample only if it is
certainly inside the piece. This is a new optional hook `Problem::point_in_domain` (default true) in
`bnb.rs`; without it the prover reported "counterexamples" outside the region, where f (the old
bracket) is negative. Existing problems are unaffected: `run_proofs.sh` reproduces all twelve old
certificates bit for bit (same sha256 as §4).

*The origin, for (CL\*\*₀).* The notes suggested the `clnear` gain test. It does not close here. Boxes that
touch the face e = 0 next to the origin box, but do not contain the anchor 0, cannot be closed by
centre-based forms: the linear gain λ|e| cancels between f(c) and the gradient term, and what remains is the
quadratic part in a (~0.066|a|²) against cross terms H_ae·|a||e| of the same order. This ratio does not
improve under refinement (scale invariance), so the run stalls at depth 60 next to 0. The fix is a change of
variables in the central orthants: x = (a₁₂,a₁₃,a₂₃,t₁₂,t₁₃,t₂₃) with e_k = s_k t_k², σ_ij = a_k+e_k,
σ_ji = e_k−a_k, a ∈ [−R,R]³, t ∈ [0,T]³, R = T².
- t ↦ s t² maps [0,T] onto s[0,R], so the 8 orthant boxes cover the (a,e)-image of the σ-cube [−R,R]⁶.
- There f is smooth, and 0 is a smooth strict minimum: ∇f(0) = 0 exactly and Hess f(0) = diag(Hess_a,
  2Mλ·I).
- 8 certified-convexity leaves (C, anchor 0) close it, and Taylor-2 does the rest.
- T = 181/256, R = T² = 32761/65536 ≈ 0.49989 (exact). The case-c far pieces exclude [−R,R]⁶ (X).
- The case-l pieces need no central exclusion: on [−R,R]⁶, 2Q₃ ≤ 4R < 2.77 ≤ λW₃, so case l does not meet
  it (and the far case-l certificates cover the whole cube anyway).

*Cross-checks of the encoding.* The two independent formulas (§5.5) agree to 2·10⁻¹⁴ with each other, with the
plain float Br′ and with the trigonometric form, at 2·10⁴ + 1.2·10⁴ random points. For every piece, the
membership test of each encoding agrees with the float membership at every point
(`selftest_k2.py`; the scratch script `xcheck.py` for the Rust side).

### 5.4 Prover runs (ivcert, 4 cores shared with other jobs, 2026-11-26)

`tools/ivcert/run_k2.sh all` (`--max-depth 60`). Each certificate was re-checked by `ivcheck` (same code
base) right after it was written: all 40 VERIFIED. Leaf tags: N natural, M mean value, T Taylor-2,
C certified convexity, X outside the piece / central cube; F (unclosed) = 0 everywhere. No G, K or P
leaves.

| job | certificates | leaves | N | M | T | C | X | prover time |
|---|---|---|---|---|---|---|---|---|
| S(9/10) | 16 far | 23 301 450 | 9 038 375 | 1 447 653 | 368 291 | 0 | 12 447 131 | 1020 s |
| (CL\*\*₀) | 16 far + 8 near | 62 113 501 | 23 719 742 | 4 558 954 | 993 288 | 64 | 32 841 453 | 1251 s |

Per certificate (time in s; the last column is the smallest certified bound among non-convexity leaves.
It is tiny because boxes that straddle the piece boundary have f ≈ 0 just outside the piece.)

| certificate | result | time | leaf counts | leaves | min bound |
|---|---|---|---|---|---|
| s910 case=c:s=+++ | PROVED, ivcheck VERIFIED | 120 | N 1237985 M 155808 T 47433 C 0 X 1380565 F 0 | 2821791 | 0.000000380 |
| s910 case=c:s=++- | PROVED, ivcheck VERIFIED | 38 | N 267574 M 93452 T 54249 C 0 X 504231 F 0 | 919506 | 0.000000573 |
| s910 case=c:s=+-+ | PROVED, ivcheck VERIFIED | 137 | N 1529833 M 181636 T 31489 C 0 X 1827126 F 0 | 3570084 | 0.000000046 |
| s910 case=c:s=+-- | PROVED, ivcheck VERIFIED | 46 | N 302375 M 97068 T 49296 C 0 X 562008 F 0 | 1010747 | 0.000000218 |
| s910 case=c:s=-++ | PROVED, ivcheck VERIFIED | 189 | N 1814348 M 185230 T 36621 C 0 X 1929486 F 0 | 3965685 | 0.000000027 |
| s910 case=c:s=-+- | PROVED, ivcheck VERIFIED | 56 | N 333979 M 108317 T 53915 C 0 X 603624 F 0 | 1099835 | 0.000000328 |
| s910 case=c:s=--+ | PROVED, ivcheck VERIFIED | 229 | N 2009500 M 232374 T 15319 C 0 X 2637240 F 0 | 4894433 | 0.000000001 |
| s910 case=c:s=--- | PROVED, ivcheck VERIFIED | 62 | N 370855 M 97608 T 41909 C 0 X 694539 F 0 | 1204911 | 0.000000300 |
| s910 case=l:s=+++ | PROVED, ivcheck VERIFIED | 27 | N 210832 M 41315 T 3448 C 0 X 370393 F 0 | 625988 | 0.000062460 |
| s910 case=l:s=++- | PROVED, ivcheck VERIFIED | 7 | N 34004 M 19913 T 4318 C 0 X 98736 F 0 | 156971 | 0.000000000 |
| s910 case=l:s=+-+ | PROVED, ivcheck VERIFIED | 26 | N 184154 M 50558 T 8405 C 0 X 375516 F 0 | 618633 | 0.000000000 |
| s910 case=l:s=+-- | PROVED, ivcheck VERIFIED | 9 | N 32980 M 18751 T 4794 C 0 X 120637 F 0 | 177162 | 0.000001041 |
| s910 case=l:s=-++ | PROVED, ivcheck VERIFIED | 37 | N 332066 M 62403 T 452 C 0 X 551876 F 0 | 946797 | 0.000012423 |
| s910 case=l:s=-+- | PROVED, ivcheck VERIFIED | 7 | N 45623 M 19622 T 4420 C 0 X 129391 F 0 | 199056 | 0.000000000 |
| s910 case=l:s=--+ | PROVED, ivcheck VERIFIED | 23 | N 294738 M 58041 T 6232 C 0 X 504330 F 0 | 863341 | 0.000000000 |
| s910 case=l:s=--- | PROVED, ivcheck VERIFIED | 7 | N 37529 M 25557 T 5991 C 0 X 157433 F 0 | 226510 | 0.000000000 |
| cl0 near case=c:s=+++ | PROVED, ivcheck VERIFIED | 2 | N 3762 M 231 T 7303 C 8 X 1577 F 0 | 12881 | 0.000027396 |
| cl0 near case=c:s=++- | PROVED, ivcheck VERIFIED | 1 | N 817 M 13 T 5821 C 8 X 1397 F 0 | 8056 | 0.000010446 |
| cl0 near case=c:s=+-+ | PROVED, ivcheck VERIFIED | 2 | N 3643 M 216 T 7969 C 8 X 1861 F 0 | 13697 | 0.000054486 |
| cl0 near case=c:s=+-- | PROVED, ivcheck VERIFIED | 1 | N 730 M 22 T 5386 C 8 X 1629 F 0 | 7775 | 0.000015738 |
| cl0 near case=c:s=-++ | PROVED, ivcheck VERIFIED | 2 | N 3716 M 208 T 7992 C 8 X 1799 F 0 | 13723 | 0.000006532 |
| cl0 near case=c:s=-+- | PROVED, ivcheck VERIFIED | 1 | N 724 M 16 T 5500 C 8 X 1550 F 0 | 7798 | 0.000015738 |
| cl0 near case=c:s=--+ | PROVED, ivcheck VERIFIED | 2 | N 3638 M 240 T 8026 C 8 X 1979 F 0 | 13891 | 0.000049542 |
| cl0 near case=c:s=--- | PROVED, ivcheck VERIFIED | 1 | N 687 M 61 T 4653 C 8 X 1645 F 0 | 7054 | 0.000010660 |
| cl0 case=c:s=+++ (rho=R) | PROVED, ivcheck VERIFIED | 248 | N 2971481 M 490387 T 128395 C 0 X 3378973 F 0 | 6969236 | 0.000000069 |
| cl0 case=l:s=+++ | PROVED, ivcheck VERIFIED | 25 | N 442584 M 92085 T 6486 C 0 X 665854 F 0 | 1207009 | 0.000003920 |
| cl0 case=c:s=++- (rho=R) | PROVED, ivcheck VERIFIED | 49 | N 607600 M 336946 T 135091 C 0 X 1375594 F 0 | 2455231 | 0.000000045 |
| cl0 case=l:s=++- | PROVED, ivcheck VERIFIED | 5 | N 54374 M 35231 T 6775 C 0 X 163045 F 0 | 259425 | 0.000003219 |
| cl0 case=c:s=+-+ (rho=R) | PROVED, ivcheck VERIFIED | 156 | N 4056648 M 526369 T 84915 C 0 X 4838488 F 0 | 9506420 | 0.000000010 |
| cl0 case=l:s=+-+ | PROVED, ivcheck VERIFIED | 22 | N 405055 M 120527 T 16102 C 0 X 722060 F 0 | 1263744 | 0.000000000 |
| cl0 case=c:s=+-- (rho=R) | PROVED, ivcheck VERIFIED | 61 | N 632541 M 389665 T 129366 C 0 X 1428189 F 0 | 2579761 | 0.000000135 |
| cl0 case=l:s=+-- | PROVED, ivcheck VERIFIED | 6 | N 53654 M 30971 T 7203 C 0 X 204924 F 0 | 296752 | 0.000000000 |
| cl0 case=c:s=-++ (rho=R) | PROVED, ivcheck VERIFIED | 191 | N 4967433 M 592644 T 99116 C 0 X 5464183 F 0 | 11123376 | 0.000000010 |
| cl0 case=l:s=-++ | PROVED, ivcheck VERIFIED | 35 | N 917061 M 174608 T 221 C 0 X 1485160 F 0 | 2577050 | 0.000002267 |
| cl0 case=c:s=-+- (rho=R) | PROVED, ivcheck VERIFIED | 71 | N 738342 M 435264 T 144093 C 0 X 1631793 F 0 | 2949492 | 0.000000165 |
| cl0 case=l:s=-+- | PROVED, ivcheck VERIFIED | 8 | N 89828 M 40251 T 7343 C 0 X 259440 F 0 | 396862 | 0.000000000 |
| cl0 case=c:s=--+ (rho=R) | PROVED, ivcheck VERIFIED | 265 | N 5960970 M 710848 T 40487 C 0 X 7818693 F 0 | 14530998 | 0.000000082 |
| cl0 case=l:s=--+ | PROVED, ivcheck VERIFIED | 30 | N 849250 M 165601 T 10054 C 0 X 1305067 F 0 | 2329972 | 0.000000000 |
| cl0 case=c:s=--- (rho=R) | PROVED, ivcheck VERIFIED | 58 | N 879067 M 364175 T 114720 C 0 X 1763366 F 0 | 3121328 | 0.000000246 |
| cl0 case=l:s=--- | PROVED, ivcheck VERIFIED | 9 | N 76137 M 52375 T 10271 C 0 X 323187 F 0 | 461970 | 0.000000000 |

The near-origin orthants are cheap (7–14k leaves, 1–2 s each). The 8 C leaves per orthant are the boxes
at 0. Case-c far pieces with ε₂₃ ≥ 0 are the largest (up to 14.5M leaves). About half of all leaves are X
(boxes outside the piece).

### 5.5 Independent check (ivcheck2)

`tools/ivcheck2/run_k2.sh` (README §k2). The encoding there is written from the notes: C, N, X
verbatim, with the signs of Q_i and ε_k fixed by the piece. It runs in Arb (python-flint) with its own
piece test, a hand-written gradient (checked against sympy) and its own origin lemma. It uses only the
boxes of each certificate (and the tag X, which it re-checks). *Independence caveat:* the same author
wrote both encodings, in the same session. They share the piece and coordinate conventions (stated in the
header of `k2m.rs`) and nothing else. The stacks, the form of the formulas, the gradients and the origin
argument are different, and the two encodings are compared numerically (`selftest_k2.py`).

Origin lemma (`originlemma.prove_k2near`), for (CL\*\*₀) on G = [−1/16,1/16]⁶ in (a,e):
- Br′ ≥ Br = V(a,e) + λΣ|e_k| − η everywhere.
- g(a) = V(a,0) has g(0) = 3τ = η (exact).
- Hess g is PD on [−1/16,1/16]³ (8³ sub-boxes, smallest leading minor ≥ 0.0772).
- L_k = sup_G |∂V/∂e_k| ≤ 0.27537 < λ (3⁶ sub-boxes).
- So Br′ ≥ 0 on G. (With 8 sub-boxes per axis the Hessian test fails at radius 1/8; 1/16 suffices.)

| job | leaves | X confirmed outside (own test) | X in central cube | per-leaf: lemma / nat / mvf / bisected | extra splits (max depth) | time | verdict |
|---|---|---|---|---|---|---|---|
| S(9/10) | 23 301 450 | 12 447 131 | – | 0 / 9 178 803 / 1 308 258 / 367 258 | 685 911 (8) | 1397 s (4 workers) | **VERIFIED**, all 16 |
| (CL\*\*₀) | 62 113 501 | 32 724 722 | 116 731 | 1 412 / 24 067 997 / 4 219 871 / 982 768 | 1 877 239 (10) | 3771 s (4 workers) | **VERIFIED**, all 24 |

`k2cover.py` confirms that, for each job, all 16 pieces are verified. For (CL\*\*₀) it also confirms that the
central cube [−R,R]⁶ of each case-c piece is covered by all 8 verified near orthants with T² = R: COVER OK
for both jobs. Logs and JSON: `tools/ivcheck2/results/k2_*`.

*A bug found by the mutation test, now fixed.* In the first version of `K2Spec.mvf`, the value was
scaled by M but the gradient was not. The mutation run (`--shift 1e-7` on a near certificate) then
"verified" the origin boxes, which is wrong. After the fix that run fails exactly the 8 origin leaves.
`selftest_k2.py` now checks that the nat and mvf enclosures contain point values on random boxes; it
reports 2209 failures with the old code and 0 now. All ivcheck2 results above are from runs after the fix.

### 5.6 Mutation tests (the certificates are not vacuous)

* ivcert prover (`cargo test --release`, test `k2_pieces`, all 9 tests pass):
  - with bound 10·Br′ ≥ 2 on P(l,+++), an exact counterexample inside the piece is reported (e.g.
    σ = (−0.4921875, −0.9765625, 0.4921875, 0.015625, 0.984375, 0.484375), 10·Br′ = 1.78346);
  - with bound 0.7 (just above the minimum 0.627) it is NOT PROVED;
  - the near orthant with bound 10⁻⁶ is NOT PROVED;
  - a depth-limited run has negative box centres outside the piece and reports no counterexample.
  The driver now lists exact counterexamples before depth-limit failures (before this change they could be
  hidden among the first 20 printed failures).
* ivcheck on certificates with the header bound raised:
  - near orthant s=+−+, c = 10⁻⁶: REJECTED, 8 leaves (the C leaves at 0);
  - S(9/10) P(l,+++), c = 0.65: REJECTED, 243 652 leaves;
  - same piece, c = 10⁻⁴: REJECTED, 82 leaves (so the certified margin really is only ≥ 0).
* ivcheck2 `--shift`:
  - near s=+−+, shift 10⁻⁷ (origin lemma disabled): NOT VERIFIED, 8 leaves;
  - S(9/10) P(l,+++), shift 0.07 > 0.0627 (extra depth 3): NOT VERIFIED, 72 064 leaves, starting near
    σ ≈ (−.84, −.91, .78, −.03, .97, −.06).

### 5.7 What is and is not proved

* **Proved (computer-assisted, two checkers):** Br′(σ; 9/10, 6/5) ≥ 0 and Br′(σ; 12/13, 15/13) ≥ 0 on the
  closed region 𝓕′₁, hence on all its S₃×Z₂ images.
* **Not checked here:**
  - Lemma R, the hand reduction to 𝓕′ (only sampled, §5.1);
  - Proposition C′, (3.1) and C.3/C.4(a);
  - the convexity step "one certified λ₂ covers all smaller λ";
  - the consequences listed in notes §5.4 (threshold of Theorem E lowered from w₁ = 1.9134 to w ≥ 4/3, and
    (★) 13Σ_S ≥ 12Σ_vv + 15D with the exact rate 3/(2+w) for all w ≥ 5/4). These follow from the
    certificates only together with those [R] statements.
* No strict positivity margin is certified for S(9/10), only ≥ 0, although numerically min = +0.0627.
  (CL\*\*) with λ as a seventh variable was not attempted.

### 5.8 Files and hashes

Certificates: `tools/ivcert/certs/k2/` (950 MB, under the existing `certs/` ignore rule, so not in git).
They are regenerated deterministically by `tools/ivcert/run_k2.sh all` (about 40 min on 4 shared cores);
the independent check is `tools/ivcheck2/run_k2.sh` (about 90 min). Code added:
- `src/problems/k2m.rs`, with registration in `driver.rs` and `problems/mod.rs`;
- `Problem::point_in_domain` in `bnb.rs`;
- counterexample-first reporting in `driver.rs`;
- `examples/k2_points.rs` and `examples/k2_box.rs` (debugging aids);
- test `k2_pieces`;
- in ivcheck2: `K2Spec` in `problems.py`, `prove_k2near` in `originlemma.py`, the k2 branch of `check.py`,
  `selftest_k2.py`, `k2cover.py` and `run_k2.sh`.

sha256 (`tools/ivcheck2/results/k2_sha256.txt`):

| file | sha256 |
|---|---|
| cl0_c_s+++.cert | b1876642b1aa86ef2ad0b617445775573e14669879b25a7a9ac600ce8cc4e00d |
| cl0_c_s++-.cert | dcaf8f6fe6a83bb326cc9d67c3fa9dfc7d49be50c0fb6b4c5834d1725f5df321 |
| cl0_c_s+-+.cert | fb7ef7fad46079af51e15feb57f967cfbc858a20444cc8e9c3d1039b214d57c5 |
| cl0_c_s+--.cert | c59063f2772d70efb2e8f6d367e3d2ff01921f6e08c4f114a4c9d17c602e152f |
| cl0_c_s-++.cert | e2d897b375f7305bf619fa662b67e2ac1834d15d77a456a44f36ca49d93f6cca |
| cl0_c_s-+-.cert | 69ed746c152b55cc713d7dfbee753fe9a654da18144499726d09861f8b3c018b |
| cl0_c_s--+.cert | 5625d8e5c07dd686ccaf07f4133efb4ff2505e8c00706b5c5e76f7c3586b35cc |
| cl0_c_s---.cert | 8c30fcdf6fc387c9b7ef714d51a719044a31111e9a3c994309c57549bc458142 |
| cl0_l_s+++.cert | 6190f40f60b7d99ac5983b002898ea127d908a94eea6c1a7e1c8a5cefeaebd10 |
| cl0_l_s++-.cert | 065c80bfaab66b71e5001b96e1c4725a9cb24c245d0295a7218dd424fa565bf3 |
| cl0_l_s+-+.cert | fda785b349578bd0d26c9ac7443464ed2cd4c00bf3d4e30c34992359f764499c |
| cl0_l_s+--.cert | 661798ca99300bec6a69f811493c846834c890c661e0a777b04bc1ce661ea8e7 |
| cl0_l_s-++.cert | 7833b883da09df9067b6549f90ba8112bcceee61b87fc3601473b58d865ef471 |
| cl0_l_s-+-.cert | 7185806d583a75790da50895b41e3de817a67970b7edce119a0216897d5c33f3 |
| cl0_l_s--+.cert | e7bc18ca451a2185b2aca2487a4be29b7e73253fc9b864cd900d8272f7542d50 |
| cl0_l_s---.cert | 8cc42f3a7f4d50badf474c8002a57affd3e8105d3c9212ee37a65e19bf5d5e7d |
| cl0_near_s+++.cert | 1386969d213ce6922ed52bac044957ae4ccf6c97e6d3659fa0e166589ad11b90 |
| cl0_near_s++-.cert | 29b9d9379b7e5b8d96685fd3fbe69e2c2e4977dc67dd8035cb662f9b6ab65491 |
| cl0_near_s+-+.cert | b79fb153b7434897759ceaa998cb46218b65bbda5a7caa4171a4871760c0be3d |
| cl0_near_s+--.cert | 6520983989591c490be4fa7b649fa42c09232fd18635acbb9dbb0e8dbbfedc26 |
| cl0_near_s-++.cert | f402f48c2649c6108df6770118c2d7fecb4e4f9ddcd1b3a56ce81f40b79a2069 |
| cl0_near_s-+-.cert | dbdc83fbab76cfde3493566e30d81f6398a7d51d197afdcaf6d53bc707dd9cdb |
| cl0_near_s--+.cert | 823b0538df7c54ce204d4ab83bdcc4158f806142567af8c85ce09b53d2530120 |
| cl0_near_s---.cert | dd3092ea471cbda5615b271fbb9d5b71a98d8ef810eed373a6e1d331eb9e87b7 |
| s910_c_s+++.cert | b6739878b1987f76cbf175745b2e6f8d1daf1f4ed13168cef3b1849080ff76b5 |
| s910_c_s++-.cert | d8c2adb4ec49c4409d48c3ee7a23ef71a8e783d32c73604bce974669cf1971d5 |
| s910_c_s+-+.cert | 47998397c1ab4e1f38a8b670a1da174ac5b6b6d4dc596212857b01814849d720 |
| s910_c_s+--.cert | 7787b1db901809702b3fef0859cb167933a4350ee02d8b890a98066df6480a19 |
| s910_c_s-++.cert | c2661a17b2d5bad77b2f414aa1c528bb3a1d7ad061d175f64c0f55955fdf120d |
| s910_c_s-+-.cert | 2b4289e9149ae2b177364f38b7bc840bf54fd086e63c512c0dcbec69c1b91c62 |
| s910_c_s--+.cert | 519ad6aa2b09367570cabbc2f08a4236c842703cf346e373715c7925c7f01b87 |
| s910_c_s---.cert | 6b1320c36fbe562405e2ca10393234e72a86859a495b7b64e131638a4de7c70e |
| s910_l_s+++.cert | faf2cba9842fc7f2dcdffd0568efd7b65c43a6ec885929a355941690b39965a0 |
| s910_l_s++-.cert | 8e4db1014f69b0317540a665865545006a9bb48f7a3c8be3e08cc819c3b7a171 |
| s910_l_s+-+.cert | b45d84ff866de39b0da830c084b0ebd66125756352a6cb19a13ebf27c4362693 |
| s910_l_s+--.cert | 0ff4c506d9737bfdd44c9b940e12db39bc9a9d268f34a9ba710f0b9beaea3d6a |
| s910_l_s-++.cert | 720ec5bd31dec85b3265335c7703e64c030610e49e357699fea2c27dc0ff7ced |
| s910_l_s-+-.cert | 7e4024a1f218647147ef7ec66f12159afa4d9878c241c08d190ae6e4528b50e9 |
| s910_l_s--+.cert | bab5a56865ec1caa57e13dfe6832ebaf8e5f338045a13e81b35971863784cf64 |
| s910_l_s---.cert | 68281f0c29ec0acaa568b0a91deac3f2ec324ff67bbebe08aec9c04637993e06 |
