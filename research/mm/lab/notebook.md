# lab notebook — non-algebraic n² matrix multiplication over F₂

Newest at the bottom. Each entry: idea → ran → result → what it changes.

## 0. Setup (2026-11-26)
pip: python-sat, z3-solver, pycryptosat (CryptoMiniSat, native XOR clauses).
Scripts: `mc_sat.py` (E1 exact MC via SAT + CEGAR on input rows), `e2_wordram.py`, `e3_pack.py`.

## E1a. Matrix–vector 2×2·2×1 Boolean multiplicative complexity
- Idea: smallest case of "function, not formal identity": XOR-AND circuits, XOR free, gates may
  feed gates, x²=x allowed. Bilinear rank of ⟨2,2,1⟩ is 4.
- Ran: `python3 mc_sat.py 2 2 1 3` and `... 4`.
- Result: k=3 UNSAT (certified on 42 of the 64 rows, 39 s), k=4 SAT. **MC = 4 = rank.** (Trivial
  case — two independent inner products of length 2, each needs 2 ANDs by Mirwald–Schnorr's
  "half the rank of the symplectic matrix" for a single quadratic form.)
- Changes: nothing yet; sanity check of the encoder.

## E2. Word-RAM baselines (w = 64)
- Ran `e2_wordram.py`: M4RM (Gray-code tables, k = log n − 1) and Strassen–Winograd over F₂ with
  M4RM base at 256; exact 64-bit word-op counts; checked against numpy product up to n=1024.
- Result (word ops):

  | n | M4RM | Strassen+M4RM |
  |---|---|---|
  | 512 | 4.25e5 | 4.75e5 |
  | 1024 | 2.91e6 | 3.39e6 |
  | 2048 | 2.05e7 | 2.40e7 |
  | 4096 | 1.48e8 | 1.69e8 |

  M4RM local exponent 2.70, 2.77, 2.82, 2.85 (it is ≈ 2n³/(w log n)); Strassen slope ≈ 2.82
  (→ 2.807). Word ops per output bit at n=4096: 8.8 (M4RM) and growing ∝ n/(w log n).
- Changes: word parallelism + tables give exactly a w·log n factor over n³, i.e. polylog. To reach
  n²·polylog the per-output cost must be polylog, so the n-fold "sharing" has to come from a
  genuinely different source than packing bits into words. (This is the Ω-side statement:
  any word-RAM algorithm with w = O(log n) is a Boolean circuit of size ~ ops·w·polylog, so it
  inherits whatever Boolean circuit lower bound holds.)

## E3. Kronecker / polynomial packing
- Idea: one big-integer (= univariate polynomial) product computing all n² inner products.
- Ran `e3_pack.py pack`: z3 search for the smallest exponent range L of a *monomial* packing
  (A_ik ↦ z^{α(i,k)}, B_kj ↦ z^{β(k,j)}, C_ij read off at one coefficient, no garbage may land on
  a read-off coefficient; garbage may alias garbage). Exact minimum:
  n=2: L=6, product length 11 (n³ = 8). n=3: L=21, product length 41 (n³ = 27), 179 s.
  `e3_pack.py scale`: standard stride packing (A stride 2n−1, B stride n(2n−1), slot width
  log n + 2 bits), verified up to n = 128; B-integer has ≈ 2.5·n³·log n bits as expected.
- Result: packing length grows like ≈ 1.5 n³ at n=2,3; the stride construction is ~2n³ slots.
  With n·polylog integer multiplication the bit complexity is n³·polylog: worse than M4RM.
- General obstruction (two sentences):
  (i) Monomial packing into ANY commutative product is exactly a triple-product-property
  embedding into an abelian group / Z-interval, and Cohn–Umans' abelian bound |S||T||U| ≤ |G|
  forces length ≥ n³ (data above: 11 ≥ 8, 41 ≥ 27).
  (ii) Even non-monomial linear packings (arbitrary linear pre/post-maps, garbage allowed to
  alias) make ⟨n,n,n⟩ a restriction of univariate polynomial multiplication of length D, whose
  rank is O(D) (2D−1 over big fields, O(D) over F₂ via Chudnovsky/Shparlinski–Tsfasman–Vladut);
  hence D ≥ rank(⟨n,n,n⟩)/O(1) ≥ n^{9/4}/O(1) under the claimed theorem. So packing is
  just a bilinear algorithm in disguise and cannot beat 9/4. The only loophole is a packing whose
  read-out is *non-linear* (carries, overflow, comparisons), which is no longer "Kronecker".
- Changes: kill E3 as a route. 2-D (bivariate) packing is still a commutative group algebra
  (Z²), same obstruction.

## E1b. 2×2·2×2 over F₂, Boolean-QUADRATIC model (ANDs of affine forms, x²=x allowed)
- Idea: first relaxation of "formal identity": products of affine forms in all 8 inputs (A and B
  entries may be mixed inside one factor, squares x_i² = x_i are free), outputs = XOR of products
  + affine. Over F₂, Boolean quadratic functions modulo affine functions ≅ alternating 2-forms
  (the diagonal becomes linear), and a product L₁L₂ ↦ l₁∧l₂. So the Boolean-quadratic MC of a
  system = fewest decomposable 2-forms whose span contains the target space W.
- Ran: `quad_alt.py 2 2 2 7` (SAT, 0.1 s, alternating-form XOR encoding; finds a 7-product
  scheme mixing A- and B-entries inside factors). k=6 SAT run stalled (>20 min) →
  `quad_enum.c`: exact enumeration. 10795 decomposable forms on F₂⁸, 10705 classes mod W
  (dim W = 4). k decomposables span ⊇ W ⇒ their classes span ≤ k−4 dims of Λ²/W; for k=6
  enumerate all 57.3M class pairs. Positive controls (targets needing exactly 5 and 6) correct.
- Result: k ≤ 6 impossible. **Boolean-quadratic MC(⟨2,2,2⟩) = 7 = bilinear rank.** 3 s.
- Changes: x² = x and mixing A/B inside factors buy nothing at 2×2 in the quadratic model.
  (Literature agrees: Winograd 1971 / Hopcroft–Kerr 1971 lower bound 7 for quadratic
  algorithms; this is an independent machine check of the Boolean variant over F₂.)
  Literature status of the *general* model (AND gates fed by degree ≥ 2 intermediates):
  Mirwald–Schnorr (TCS 102, 1992) prove quadratic circuits optimal for quadratic maps with 1 or
  2 outputs; for ≥ 3 outputs it is OPEN (Boyar–Find question). arXiv 2608.30238 (Aug 2026)
  settles one instance: 4-term binary polynomial multiplication has unrestricted MC 9 = quadratic
  bound. So "does gate reuse at degree > 2 ever save an AND for a bilinear map" is genuinely open.
- Free Mirwald–Schnorr bound (lead's suggestion): any XOR of outputs Σ c_ik C_ik is the single
  form xᵀ(c⊗I)y with MC = rank(c⊗I_n) ≤ n²: gives only 4 (2×2) and 9 (3×3). Useless here.
- Total gate count remark: at fixed size the naive 2×2 circuit (8 AND + 4 XOR = 12) beats
  Strassen–Winograd (7 + 15 = 22); total gate counts at constant size say nothing about the
  exponent. Exponents come only from recursion, and recursion needs block-compatibility
  (bilinear over a ring). A non-bilinear Boolean saving at size 2 would NOT recurse (x² = x
  fails in M_n(F₂)), so a constant-size gap is only a curiosity unless it grows with n.
