# ivcheck2 — independent second check of the (CL*) and hull3 certificates

This directory re-proves, by its own means, the inequalities whose certificates are produced by
`tools/ivcert`. It treats a certificate only as a list of boxes that are claimed to cover the
domain. The prover's per-leaf data (lower bounds, centres, preconditioners, test kinds) is ignored.
The only tag that has meaning here is `X` ("excluded: covered by another argument").

**Independence.** No code from `tools/ivcert` is used or was read, apart from the header comment of
`src/cert.rs` (the file format) and the header comment of `src/problems/clstar.rs` (the problem
statement and covering argument). The interval arithmetic, the functions, the gradients, the
equality-point argument and the leaf strategy are all new, and they run in a different stack
(Python with Arb instead of Rust with f64).

## Statements verified

* **hull3** (warm-up): F(θ) = Σ_{i<j} cos((θ_i−θ_j)/2) √(1+9 sin²((θ_i+θ_j)/2)) ≥ 3 on
  [−π/2, π/2]³. The certificate's float box [−1.5707963267948968, 1.5707963267948968]³ is checked
  against Arb's π to contain the exact cube.
* **(CL\*)**: Φ(σ) = ½ Σ_i √((c_ij+c_ik)² + 10(σ_ij−σ_ik)²) − 3 + (3/2) Σ_{i<j} |σ_ij+σ_ji| ≥ 0 on
  [−1,1]⁶, where c = √(1−σ²). It is covered by three pieces:
  1. the six corner regions {sσ_jk ≥ 15/16, sσ_kj ≥ 15/16}, handled by the corner lemma below;
  2. the central cube |σ|∞ ≤ 1/2, handled by the eight `clnear` orthant certificates in
     (a, e) coordinates plus the origin lemma below;
  3. the rest, handled by the no-symmetry certificate `clstar_rho0.5_nosym.cert`. Its `X` leaves
     are checked, with exact float comparisons, to lie inside piece 1 or piece 2.

## What is checked (`check.py`)

1. **Coverage.** The split tree is rebuilt from the preorder lines. Each `S d` line replaces
   [lo, hi] by [lo, m] and [m, hi], with m = lo + 0.5(hi−lo) computed in IEEE double and
   lo < m < hi checked. So the leaves tile the root box by construction. As a separate check,
   the leaf volumes are summed in exact rationals (`fractions.Fraction`) and must equal the domain
   volume. The leaf count must equal the `end` count. `P` and `F` leaves make a certificate
   unusable here. The root domain must be exactly the stated one:
   * [−1,1]⁶ for clstar;
   * a ∈ [−½,½]³ and e_k ∈ s_k[0,½] for each of the 8 sign patterns of clnear. Together these
     cover [−½,½]⁶ ⊇ the (a, e)-image of the central σ-cube, since |a_k|, |e_k| ≤ ½ there.
2. **Excluded leaves** (clstar only). Each one must lie in [−½,½]⁶ or in a corner region.
3. **Leaf bounds.** On every other leaf, f ≥ bound is proved by the first method that works:
   * `lemma`: the box lies in the origin region G (hull3, clnear);
   * `nat`: natural interval extension. |·| is exact interval abs, and √(1−σ²) and sin²/cos use
     exact monotonicity ranges;
   * `mvf`: mean-value form f(m) + Σ G_i (x_i − m_i). G is a hand-derived interval gradient of
     the smooth vertex part. Each |ε| term uses the exact identity |u|−|w| = t(u−w) with
     t ∈ [−1,1], or the sign when it is fixed on the box. The gradients are cross-checked
     against sympy in `selftest.py`;
   * `bisect`: the box is bisected along its widest coordinate and the pieces are retried, up to
     24 extra levels. A piece that still fails is reported with its box.

## Arithmetic and trust base

* **Arb**, through python-flint 0.9.0, which bundles FLINT 3.6.0 (Arb is part of FLINT). Python is
  3.13 and sympy is 1.14.0. Arb is a mature ball-arithmetic library with rigorous error bounds;
  each operation returns a ball that is guaranteed to contain the exact result.
* `ivarb.py` (about 150 lines, our code) is an endpoint interval type. Each endpoint is an exact
  Arb number; it is computed by an Arb ball operation and then rounded outward with
  `lower()`/`upper()`.
  * Case distinctions use Arb comparisons, which are True only when the relation is certain.
    Every fallback branch is still a valid enclosure.
  * Working precision is 64 bits. Leaf boxes are exact floats, so they are exact Arb inputs.
  * NaN and infinity are rejected at the acceptance test (`is_finite()`).
* `problems.py` holds Φ, F and their gradients, written from the statement.
* `originlemma.py` turns sympy expressions into Arb ball functions. All constants become exact
  Arb rationals, and sqrt/sin/cos are Arb's rigorous ball functions.
* `selftest.py` is a guard, not part of the proof. It checks:
  * point values against plain float formulas;
  * that interval enclosures contain sampled values;
  * the gradients against sympy;
  * clnear(a, e) = clstar(σ = (a+e, e−a));
  * the trigonometric identity;
  * the equality corners.

## Equality point 0 (`originlemma.py`) — what is proved

* **hull3, on C = [−⅛,⅛]³.**
  * F(0) = 3 exactly.
  * F is even, so ∇F(0) = 0 (both facts are checked symbolically).
  * C is cut into 32³ sub-boxes. On each one, the Arb enclosures of the symbolic Hessian entries
    have all three leading principal minors > 0, with minimum lower bound 3.02. By Sylvester's
    criterion, every symmetric matrix with entries in those balls is positive definite.
  * So F is convex on C with a critical point at 0, and F ≥ 3 on C.
* **clnear, on G = [−⅛,⅛]⁶ in (a, e).** Write Φ = V(a,e) − 3 + 3Σ|e_k|, where V is the sum of the
  vertex terms.
  * g(a) = V(a,0) has g(0) = 3, and g is even (global flip σ → −σ), so ∇g(0) = 0.
  * The Hessian of g is positive definite on [−⅛,⅛]³, by the same method on 16³ sub-boxes
    (minimum minor lower bound 1.76). So g ≥ 3.
  * L_k = sup_G |∂V/∂e_k| ≤ 2.063 < 3, from Arb enclosures of the symbolic derivative on 4⁶
    sub-boxes.
  * The mean value theorem along (a,0) → (a,e), a segment inside G, gives
    Φ(a,e) ≥ (g(a)−3) + Σ(3−L_k)|e_k| ≥ 0 on G.
  * G contains every part of an orthant box within sup-distance ⅛ of 0. That covers all the
    leaves touching the origin (the prover's `G`/`C` leaves). Leaves larger than G are bisected
    first.

The lemma is re-proved at the start of every `check.py` run that involves hull3 or clnear.

## Corner lemma (piece 1), by hand

Fix a pair {j,k}, a sign s, and the third vertex i. Assume sσ_jk ≥ 15/16 and sσ_kj ≥ 15/16, and put
d₁ = 1 − sσ_jk and d₂ = 1 − sσ_kj, both in [0, 1/16]. Then:

* Every vertex term V_m = ½√((c+c')² + 10(·)²) satisfies V_m ≥ ½(c+c') ≥ 0, because c, c' ≥ 0.
* Vertex j contains c_jk, so V_j ≥ ½ c_jk = ½√(1−(1−d₁)²) = ½√(d₁(2−d₁)) ≥ ½√d₁. In the same way,
  V_k ≥ ½√d₂. Also V_i ≥ 0.
* σ_jk and σ_kj have the same sign s, so |σ_jk+σ_kj| = 2 − d₁ − d₂. The other two absolute values
  are ≥ 0.
* Adding up: Φ ≥ ½√d₁ + ½√d₂ − 3 + (3/2)(2 − d₁ − d₂) = Σ_{t=1,2} ½√d_t (1 − 3√d_t).
  This is ≥ 0 because √d_t ≤ ¼ < ⅓.

So Φ ≥ 0 on every corner region; on the faces sσ_jk = 15/16 the bound is at least 1/32.

**Equality set.** In the corner region, equality needs d₁ = d₂ = 0, V_i = V_j = V_k = 0 and the
other two absolute values equal to 0. That forces
σ_jk = σ_kj = σ_ji = σ_ki = s and σ_ij = σ_ik = −s.

In words: both vertices of the pair have both coordinates equal to s, and the third vertex has both
coordinates equal to −s. For example, for {12} and s = +1, σ = (σ12, σ13, σ21, σ23, σ31, σ32) =
(1, 1, 1, 1, −1, −1). `selftest.py` evaluates Φ = 0 exactly at all six such corners.

The description "σ_jk = σ_kj = s, the other four = −s" in the task statement is not an equality
point: at σ = (1, −1, 1, −1, −1, −1), Φ = 12.32.

**Rigorous numerical confirmation** (`corner.py`):
* the factored form ½√d(1−3√d) ≥ 0 is checked on 4096 interval pieces of [0, 1/16];
* Φ ≥ 0 is proved by branch and bound on all 12 five-dimensional boundary faces
  {sσ_p = 15/16, sσ_q ∈ [15/16,1], other four coordinates ∈ [−1,1]} of the six corner regions.
  This takes 3252 boxes, all closed by natural extension.

## Identity

`selftest.py` checks symbolically (sympy) that

cos μ √(1+9 sin²δ) = ½√((cos ψ₁+cos ψ₂)² + 10(sin ψ₁ − sin ψ₂)²),

with μ = (ψ₁+ψ₂)/2 (the half-sum) and δ = (ψ₁−ψ₂)/2 (the half-difference). The squares agree, the
difference simplifies to 0, and both sides are ≥ 0 because |μ| ≤ π/2.

Directly: cos ψ₁ + cos ψ₂ = 2 cos μ cos δ and sin ψ₁ − sin ψ₂ = 2 cos μ sin δ, so the right side is
|cos μ| √(cos²δ + 10 sin²δ). With the roles of μ and δ swapped, the identity is false (checked
numerically).

## Results (run of 2026-11-26, 4 cores, certificates regenerated by `ivcert/run_proofs.sh`)

| certificate | leaves | X | per-leaf: lemma / nat / mvf / bisected | extra splits (max extra depth) | wall time | verdict |
|---|---|---|---|---|---|---|
| hull3-nosym (certs/ and committed certificates/) | 1014 | 0 | 16 / 344 / 0 / 654 | 1320 (3) | 0.2 s | VERIFIED |
| clnear s=+++ and s=−−− | 8608 | 0 | 3330 / 3199 / 0 / 2079 | 15214 (7) | ≈2.5 s | VERIFIED |
| clnear s=++− and s=−−+ | 11685 | 0 | 5089 / 4236 / 0 / 2360 | 12680 (6) | ≈2.3 s | VERIFIED |
| clnear s=+−+ and s=−+− | 11601 | 0 | 5036 / 4204 / 0 / 2361 | 12717 (6) | ≈2.3 s | VERIFIED |
| clnear s=+−− and s=−++ | 11424 | 0 | 4943 / 4106 / 0 / 2375 | 12881 (6) | ≈2.3 s | VERIFIED |
| clstar_rho0.5_nosym | 528970 | 94 (64 central, 30 corner) | 0 / 520956 / 6852 / 1068 | 2636 (5) | 13 s (+8 s parse) | VERIFIED |

Notes on the table:
* For bisected leaves, the pieces were closed by nat, mvf or lemma.
* Each clnear row is per certificate.
* For every certificate, coverage passed: volume equal, leaf count equal, no P or F leaves, and
  the domain is the stated one.

**Overall: VERIFIED.** No discrepancy with the first verification: every leaf the first checker
accepted was closed here. About 20–24% of clnear leaves and 0.2% of clstar leaves (mostly the
prover's Taylor-closed `T` leaves) needed extra bisection here, because no second-order form is
used here.

**Mutation sanity check.** With Φ replaced by Φ − 0.001 and the lemma disabled, the clnear s=+++
run fails 898 leaves, including the 8 at the origin. So the checker is not vacuous.

SHA-256 of the checked certificates are in `results/sha256.txt` after a run, for example
clstar_rho0.5_nosym `5656297f…10d9` and hull3-nosym `0d2e100d…2f01`.

## Re-running

```
pip install python-flint sympy           # python-flint 0.9.0, sympy 1.14.0 used
tools/ivcert/run_proofs.sh               # optional: regenerate certificates into ivcert/certs
tools/ivcheck2/run_all.sh                # ~1 minute on 4 cores; CERTS=dir JOBS=n to override
```

`check.py CERT... [--jobs N] [--json OUT]` checks individual certificates.
