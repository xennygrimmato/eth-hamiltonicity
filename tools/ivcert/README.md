# ivcert — rigorous interval branch-and-bound certificates

`ivcert` proves inequalities `f(x) >= c` on a box. It writes a certificate, and the separate
binary `ivcheck` re-verifies it without doing any search. It is written in Rust with rayon and has no other
dependencies.

```
cargo build --release
./target/release/ivcert hull3 --out certs/hull3.cert     # prove
./target/release/ivcheck certs/hull3.cert                # re-verify
./run_proofs.sh                                          # regenerate + check all certificates of the hull notes
cargo test --release                                     # unit + end-to-end tests
```

Prover options: `--max-depth D`, `--no-mv`, `--no-taylor2`, `--no-convex` (disables the convexity and gain
tests), `--no-symmetry`, `--threads T`. Exit code 0 means proved; 1 means not proved (counterexamples and
unclosed boxes are printed).

## Trust base

* IEEE-754 binary64 arithmetic: round-to-nearest `+ - * / sqrt` and a correctly rounded `f64::mul_add`
  (fma). Rust does not contract or reorder float operations. x86-64 uses SSE2.
* `src/interval.rs`. Each endpoint is the round-to-nearest result, corrected by one ulp
  (`next_up`/`next_down`) when the exact error has the wrong sign. The error comes from TwoSum for sums.
  For products, quotients and sqrt it is the sign of an fma residual. Exact results stay exact, which
  matters at equality points such as F(0) = 3 and sin 0 = 0. Results with |x| < 1e-280 are widened
  unconditionally to avoid underflow.
* `src/elem.rs`. sin and cos use only the interval operations. The π enclosure [f64(π), next_up] is
  checked against 30 decimal digits in a test. Range reduction is by q·[π/2]. The Taylor polynomial is
  evaluated by Horner's rule with the Lagrange remainder |r|^m/m!. Interval arguments are handled through
  the endpoint values plus every critical point (j+½)π or jπ that may lie in the interval. libm is not
  used; it appears only in tests, as an approximate cross-check.
* `src/ad.rs`. Forward-mode AD over intervals (gradient and Hessian) is the chain rule with interval
  enclosures. `sqrt` of an argument that may be 0, division by an interval containing 0, and `abs` of an
  argument that is not sign-definite all give INVALID derivatives. Such boxes are then closed only by the
  natural extension, or they are split. No non-smooth calculus is used.
* `src/linalg.rs`, `src/bnb.rs`. These hold the leaf tests below and the positive-definiteness tests.
* The problem definition: its formula, its symmetry claim (`outside_fundamental`) and any `excluded`
  regions with the lemma that covers them. These are stated in the doc comment of each problem file.

The checker shares this code (intervals, AD, leaf tests and problem definitions) with the prover. It does
not share the search: it rebuilds every box from the preorder tree, which makes coverage of the domain
structural, and it re-runs the named test on each leaf. The header must match the built-in problem
(name, bound and domain, bit for bit).

## Leaf tests (B the closed box, c its float centre)

| tag | test | bound |
|---|---|---|
| N | natural interval extension | f(B) |
| M | mean value | f(c) + ∇f(B)·(B−c) |
| T | Taylor-2 | f(c) + ∇f(c)·(B−c) + ½ (B−c)ᵀ∇²f(B)(B−c) |
| C | certified convexity, anchor x* ∈ B | ∇²f(B) PD ⇒ f ≥ f(x*) + ∇f(x*)·(B−x*) |
| G | gain test (partial convexity + linear gain) | see `lb_gain_h` in `bnb.rs` |
| P | symmetry pruning | box misses the problem's closed fundamental domain |
| X | excluded | box lies in a region covered by a stated lemma or by another certificate |

* **C, positive definiteness.** The Hessian enclosure H is symmetrised by intersection. Then either
  (a) A = PᵀHP is computed in interval arithmetic and checked PD by Gershgorin discs, with an explicit
  float P stored in the certificate (P ≈ V Λ^{-1/2} from a Jacobi eigendecomposition of mid H; its
  nonsingularity is certified by the same test on PᵀP), or (b) interval Cholesky is run and every pivot
  must be > 0.
* **G, gain test.** The coordinates split into a convex block C and a linear block L. The box lies on one
  side of x* in every L coordinate. The gradient at x* satisfies g_k·sign ≥ γ > 0 on L. λ_min(H_CC) ≥ λ is
  certified as λ_min(PᵀH_CC P)/‖P‖_F². The cross block satisfies ‖H_CL‖ ≤ ‖·‖_F = β. Gershgorin gives μ on
  H_LL. Then f − f(x*) ≥ S₁(γ − w_L(β²/2λ + max(0,−μ)/2)), where S₁ = ‖d_L‖₁ and w_L is the L-width. This
  closes equality points where f has a kink or a constrained minimum: the gain in L is linear and f is
  strictly convex in C.

Splitting bisects the widest coordinate at the float midpoint. Parallelism comes from `rayon::join` on the
top 22 levels. The tree depends only on the boxes, so certificates are deterministic. At every split the
centre value is checked: if `f(c).hi < c` holds, that is an exact counterexample (c is an exact float) and
it is reported.

## Certificate format

See `src/cert.rs`. The format is text, line-based and preorder: `S d` for a split, then leaves
`N`, `M`, `T`, `C`, `G`, `P`, `X` or `F`. Floats that matter, such as anchors and preconditioners, are
written as hex bit patterns. A certificate containing `F` (an unclosed box) is rejected.

## Adding a problem

Implement `bnb::Problem<N>`: `name`, `statement`, `domain`, `bound`, a generic `eval<T: Scalar<N>>`, and
optionally `special_points`, `outside_fundamental`, `excluded`, `linear_block`. Then register the name
prefix in `driver.rs`. Problems are parsed from names such as `hull3:k=9:c=3`, and the checker rebuilds
the problem from the name stored in the certificate.

## Problems shipped

* `hull3`: inequality (I), F(θ) ≥ 3 on [−π/2,π/2]³ (`k`, `c` are parameters, for tests only).
* `clstar:rho=1/2` and `clnear:rho=1/2:s=±±±`: inequality (CL*) of the hull notes, in sine coordinates
  (see the doc comment of `problems/clstar.rs`).
* `book:m=M`, `bookface:f=rho|s:m=M`: the direct 6-parameter book claim (see `problems/book.rs`).
* `bowl2`, `valley2`, `ring2`: test functions with known minima (see `problems/testfns.rs`).

The tests (`tests/known.rs`) cover:

* known-true claims, which are proved and checked;
* false claims, which are refused with an exact counterexample (`bowl2:c=1e-9`, `hull3:c=3.0001`,
  `hull3:k=2`, …);
* true but non-isolated or boundary-equality claims (`ring2:c=0`, `hull3:k=8`), which are not proved and
  give no counterexample;
* tampered certificates, which are rejected.
