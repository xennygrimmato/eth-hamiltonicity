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

## ideas-E5. Derived-exponent atlas (no solver)
- Ran `e5_atlas.py` (output `e5_atlas_out.txt`): claimed exact formula
  w(x,y,z) = x+y+max(0,(x+y)z−xy)²/(4xyz) vs the ω=2 world max-pair-sum; bisection for balance points.
- AT THE IDEAL value: ⟨n,n^k,n⟩ for k ≤ 1/2 (n²); Zwick/unweighted directed APSP n^{2.5}
  (μ = 1/2 in both worlds); fully sparse product (ABFK balance equation as transcribed in
  ideas-n2 §1, w(σ−1,2−σ,1+r−σ)=σ): m^{4/3} at m_out=m, m^{7/6} at m_out=m^{1/2}, ideal for all
  m_out ≤ m_in.
- NOT ideal: ⟨n,n^{0.6},n⟩ 2.0167, ⟨n,n^{0.75},n⟩ 2.0833, ⟨n,n^{1.5},n⟩ 2.6667 (vs 2.5),
  α = 1/2 (vs 1), sparse with m_out = m^{1.25}: 1.4221 (vs 1.4167), m^{1.5}: 1.5345 (vs 1.5).
  Square-ω-only formulas (AYZ triangle 18/13, k-clique 9t/4, bounded-difference (min,+) 2.625,
  det/rank 2.25) were not re-optimised with rectangular blocks → only upper bounds.
- Caveat: ABFK equation not independently derived by me.

## ideas-T5 first experiment ("few thin products after non-linear preprocessing") — closed on paper
- Claim: if for EVERY input pair AB = Σ_{t≤s} F_t G_t with F_t ∈ F₂^{n×√n}, G_t ∈ F₂^{√n×n}
  (F_t, G_t arbitrary functions of anything at all), then rank(AB) ≤ s√n pointwise. A random
  product has rank n − O(1) over F₂, so s ≥ √n − o(1). s = √n is achieved trivially (split the
  inner index). So the pass criterion "< √n thin products" is impossible for any preprocessing
  class; the decomposition route costs √n·n^{2+o(1)} = n^{2.5}. No computation needed (checked:
  rank of random 16×16 / 64×64 F₂ products is n−O(1), standard).

## ideas-E7. Cyclic (twisted-convolution) form of M_n(F₂) — PASS (set-up only)
- `e7_cyclic.py`: M_n(F₂) = End(F_{2^n}) = F_{2^n}[x;Frob]/(xⁿ−1), L(z)=Σ a_i z^{2^i},
  c_k = Σ_{i+j≡k} a_i·b_j^{2^i}. Coefficient→matrix map is an F₂-linear bijection (rank n²) and
  the product identity holds on 50 random pairs, n = 2..8.
- Cost: naive is n² F_{2^n}-multiplications (MC Θ(n) each) ≈ n³; Frobenius is XOR-only. Fast
  skew-polynomial multiplication is algebraic, so bounded by the same ω. No gain seen.

## E1c. Unrestricted model (gate reuse, degree > 2 intermediates): exact span search `mc_span.c`
- Idea: the SAT encodings (CEGAR `mc_sat.py`, all-rows `gen_full.py`, orbit-split `gen_orbit.py`,
  + lex symmetry breaking) could not even re-find MC = 6 for 3-term polynomial multiplication in
  10 min. Replace by a search over the SUBSPACE S_j = span{1, inputs, G_1..G_j} of truth tables:
  a circuit is a chain S_{j+1} = S_j + ⟨u·v⟩ (u,v ∈ S_j) with T ⊆ S_k. Key facts:
  (a) rem(S) = dim((S+T)/S) drops by ≤ 1 per gate → prune rem > k−j;
  (b) a "reducer" gate (u·v ∈ S+T) leads to S+⟨t⟩ for a class t of T mod S — at most 2^rem − 1
      successors, whatever u, v are; (c) for fixed u, v ↦ u·v is F₂-linear, so reachability of
      each class is one rank test per u; (d) "helper" gates (all other products) allowed only while
      rem ≤ k−j−1; (e) memoise on the RREF of S (128-bit hash; collision risk ignored).
  First gate ranges over the 72 orbits of planes under GL₂(F₂)³ ⋊ transpose (432 elements; orbit
  sizes sum to 10795; checked that the group preserves span T).
- Calibration (all exact, seconds): F₄ mult MC = 3, 2-term poly mult = 3, 3-term poly mult = 6
  (k=5 refuted with 8 states, k=6 found with 334 states) — matches Morse arXiv:2608.30238
  (Mul₂ = 3, Mul₃ = 6).
- Results (unrestricted model, exact unless noted):
  - ⟨2,2,1⟩ (≅ ⟨1,2,2⟩ by transposition): MC = 4 (E1a, CEGAR SAT k=3 UNSAT). = rank.
  - ⟨1,2,3⟩: k=4 refuted by `mc_span` (all 10795 first-gate planes, 10865 states); k=6 exists
    (quadratic). MC ∈ {5, 6}; k=5 NOT settled (search needs ~hours without orbit reduction).
  - ⟨2,2,2⟩: **k=5 refuted** (72 orbits, 75 states, 0.06 s) → unrestricted MC ≥ 6 certified
    (modulo trusting the code + orbit computation; no DRAT-style proof object).
    k=6: 3 of 72 first-gate orbits refuted (≈4.5 min/orbit, ~42k states each); full run would
    take ≈ 1.8 h on 3 cores; STOPPED on lead's instruction (priority change). So: 6 ≤ MC ≤ 7.
    **UPDATE 26 Nov (late): the remaining 69 orbits were run (`run_k6.sh`, three shards, niced, several hours
    wall time because of contention). All 69 report "none" (`k6_log{0,1,2}.txt`, 23 each; verdicts in
    `k6_out{0,1,2}.txt`: NO CIRCUIT, 971007 / 1308960 / 1139984 states). With orbits 0–2 refuted earlier, all 72
    first-gate orbits are refuted: there is no circuit with 6 AND gates (XOR free) for the 2×2 matrix product over
    F₂. Hence unrestricted MC(⟨2,2,2⟩ over F₂) = 7 [N].** Trust base: `mc_span.c`, the orbit computation
    (`orbits.py`, `plane_orbits.json`), the pruning rules (a)–(e) above, and the 128-bit state hash (collisions
    ignored). No independent proof object.
    Literature (check of 26 Nov, `research/ports/literature-check.md` topic C): the lower bound MC ≥ 6 is already
    claimed in a public machine-generated register (entries MF-149 / MF-180, 4 Sep 2026), which calls 6 versus 7 open;
    the cited 2026 paper on polynomial multiplication (arXiv:2608.30238) does not treat matrices; Boyar–Find leave the
    many-output case open. So "≥ 6" is not new, and "= 7" appears to be new but rests on this one search. An
    independent re-verification by a different method is in progress (`tools/mc222/`).
    Why k=6 is costly: helpers (gates not landing in S+T) are allowed at positions 1–2, so the
    second gate ranges over all ~2^18 products; positions 3–6 must all be reducers.
  - Boolean-quadratic MC(⟨2,2,2⟩) = 7 (E1b) and Qf = R = 7.
- Changes: no gap found anywhere; the unrestricted question at 2×2 is reduced to 69 orbit
  subtrees of a ~4-minute search each — a cheap job to finish later if anyone cares.

## Tiny bilinear-map sweep (lead's E5) — status: PARTIAL
- `e5_sweep.py` computes R (bilinear rank), Qf (formal commutative quadratic), Qb (Boolean
  quadratic), MC (unrestricted) per map. Completed rows: trunc2 (mult mod x²) 3/3/3/3,
  polymul2 3/3/3/3, F₄ 3/3/3/3; plus via mc_span polymul3 R=6, MC=6; ⟨2,2,1⟩ 4/–/4/4;
  ⟨2,2,2⟩ 7/7/7/≥6. The SAT-based MC column was the bottleneck (stalled at polymul3); the
  random-map part was never run. Fix: plug a generic target loader into `mc_span.c` (seconds per
  map at ≤ 6 inputs) and rerun. No map so far has MC < Qb or Qb < Qf.

## Summary of intuition after this session
- Every route to n²·polylog over F₂ that I could test closes with a reason: word tricks = w·log n
  (E2); packing = bilinear in disguise, ≥ n^{9/4} (E3); thin-product decompositions need ≥ √n
  pieces pointwise by rank (T5); the twisted-convolution form is algebraic (E7). At the
  AND-count level, x²=x buys nothing for 2×2 in the quadratic model (7), and gate reuse buys at
  most one AND (≥ 6 certified, 7 suspected); no tiny map shows any gap.
