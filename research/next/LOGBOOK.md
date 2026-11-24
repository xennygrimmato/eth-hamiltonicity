# Logbook: after VP ≠ VNP (lead's hypotheses and findings)

Kept by the lead. Newest entries at the bottom. Tags: [L] machine-checked in Lean, [R] proved on paper by a helper,
[V] independently reviewed, [N] computed, [C] conjecture, [X] refuted or dead. "Unreviewed" means one helper's
notebook only. Folder names refer to `research/next/` unless a path is given.

## Standing targets (chosen by the user)

1. The link between the ETH counting engine (3-SAT) and the VP ≠ VNP proofs; a faster #3-SAT algorithm.
2. P_ℂ ≠ NP_ℂ in the Blum–Shub–Smale model.

Not a target: Boolean P vs NP. Nothing below bears on it.

## 24 Nov 2026

### Inputs
- Anthropic, "VP ≠ VNP over every field": permanent needs > m^{c(log m)^{1/3}} gates, also for approximating circuits.
  The proof splits into a flat case and a contracting case; the paper does not know which holds.
- OpenAI posted an independent proof with exponent 5/4.
- Ni (15 Nov): exact π(N) and prime finding in N^{o(1)}, built on our library.

### Finding 1. Twin-prime counting [L]
- Exact π₂(N) on one deterministic Turing machine in N^{o(1)}; `lean-twins/`, commit 47ed17e; no sorry, standard axioms.
- Ni's `primeCounting_time` reproduced in our setup [L].
- Goldbach, Sophie Germain, fixed k-tuples by the same method [R, V for the method; no Lean yet] (`x1/`, `review-x1.md`).
- Corrections from review: Mertens is not new (Õ(√x) known; Ni anticipates it); k-tuples only for fixed k.
- Trust base: Mathlib and engine oleans reused prebuilt; no from-scratch build, no second-kernel check yet.

### Finding 2. Engine pieces versus the VP ≠ VNP dichotomy [R, under review]
- Win-win (b2, `research/vpvnp/b2/`): a piece family beating the flat floor forces the contracting case, hence the
  stronger permanent bound. In the flat case p fully crossing merges have floor 1/√p; Appendix B's 1/√2 is optimal for
  two merges.
- The two labs' dichotomies differ but one implies the other; one explicit identity would decide it (`two-proofs.md`).
- The paper's own toolkit cannot decide the dichotomy (c1); reduced to: is √rank on Mat_μ(F₂) a price?

### Finding 3. Why 1/√2 is rigid [R, under review]
- Engine pieces sit exactly on the threshold, zero first-order saving (x3).
- Crossing exponent = trade-off curve of two-term splittings SWAP = R + L (x6 Prop. 1).
- Ladder theorem: the determinant template cannot certify below 1/√2 (x6). Covers Schur/Cauchy, Pfaffian,
  q-deformed and multi-dimensional kernels.
- Coordinate grids of any dimension cannot beat the current exponent (x4).
- Affine-plane levels: flat floor falls like 1/√p, no new barrier; everything reduces to "is 1/√p attainable for
  p ≥ 3?" (z1). Smallest test instance: K₄ with its three perfect matchings.
- Characteristic 2 loses both known identities (z1) [X].
- Weyl-diagonal pieces excluded by Donoho–Stark (x7) [X]. Two-piece construction on K₄ impossible (z1) [X].
- Three-wire fusion impossible inside the generalised Meixner ansatz (x7); outside it: open.
- x3's ⌈n²/4⌉ conjecture for two-term splittings is false asymptotically (x6) [X].

### Finding 4. Corollaries of VP ≠ VNP [R, unreviewed] (`research/vpvnp/c2/`, `y1/`)
- Deterministic identity testing in time 2^{s^{o(1)}}; Noether normalisation; Edmonds' problem.
- Border determinantal complexity of the permanent superpolynomial.
- P_ℂ ≠ PAR_ℂ (Bürgisser 2004 plus the border bound; credit accordingly).

### Finding 5. P_ℂ vs NP_ℂ [R, under review] (`y2/`, `ideas-pc-npc.md`)
- Reduction: P_ℂ(nu) = NP_ℂ(nu) ⇒ an easy nonzero multiple Q = N_g·H of N_g = ∏_e (y − g(x,e)).
- N_g is hard; the cofactor H must be border-hard; Artinian/local methods cannot finish.
- Sufficient: Span Conjecture (low-degree polynomial roots of an easy Q(x,y) span a small space).
- Dead: degenerations, cheap symmetrisation, restriction to curves [X].
- Lead's assessment: a map of the gap, not progress across it. The Span Conjecture is τ-type and likely hard.

### Dead ends recorded
- Matrix multiplication exponent via price geometry: the inequalities are scale-invariant, triangles are unconstrained
  (x2) [X].
- Flat-case hub method capped at exponent k^{3/2} (b1): proved in the paper's regime, conjectured in general.
- Engine rate correction: proven rate is (log K)^{-1/2}; c/log K is the ideal-piece cap, not achieved.

### Lead's hypotheses (to be tested)
- H1 [C]: the flat case holds, so the engine's pieces are optimal and the dichotomy never gives the stronger bound.
  Evidence: five failed attacks on 1/√2, each with a structural reason. Against: nothing proves flatness; the
  three-merge route is not excluded.
- H2 [C]: if a better piece exists it is a three-merge object on K₄/Δ₃ built from a multivariate orthogonal-polynomial
  family (three-wire fusion). This is the only route nobody has excluded.
- H3 [C]: x7's rank inequality rk(A|BCD) ≤ rk(AB|CD)·rk(AC|BD) is the known Cadney–Huber–Linden–Winter rank
  inequality (2014). w1 is checking.
- H4 [C]: the generic-path step of the P_ℂ reduction is the weakest link (does one path give a multiple of all of N_g?).
  The referee is checking this first.
- H5 [C]: an unconditional P ≠ NP separation is provable now for a restricted BSS model (tests of bounded y-degree, or
  products of low-degree factors). pc1 is working on it.

### Review of Findings 2 and 3 (`review-link.md`) — none broken, six of nine sub-claims need fixes [V]
- Multi-hub routing lemma with one spectral point: correct.
- Flat floors (Eλ/√p; 3√3λ on Δ₃; 2‖λ‖₂ on the crossing): correct; scripts re-run.
- Win-win: correct with two fixes.
  - The sharp trigger is "every piece has min_k c_k ≤ (E/√p − η)λ". This is strictly weaker than ρ < 1/√2:
    pieces costing (1.3λ, 2λ) and (2λ, 1.3λ) would refute the planar hypothesis with ρ_× = 0.825.
    So the contracting case could be proved WITHOUT speeding up the engine. x3's "i.e. ρ_× < 1/√2" was wrong.
  - State the field: an identity over k gives contracting over the algebraic closure of k.
- Theorem 1 (two merges ⇒ ρ ≥ 1/2) holds over every field: correct; the flag can be removed.
- Prop. 1 / Cor. 1′ of `two-proofs.md`: correct once a small extension lemma (E.7′) is stated.
- x6 Prop. 1: needs limsup. x6 ladder theorem: its hypothesis is false as stated for discrete spectra; an
  approximate version rescues the result. Its "sharpness" numbers and the "n ≈ 11" crossover are not asymptotic.
- x5: one inequality chain repaired (conclusion ρ_cert ≥ 1/√2 stands); the "iff" region holds only for α ≤ 1.
- x3: only the middle piece sits on the threshold; the saving constant is (√2 − β)²·m.
- New hypothesis H6 [C]: target the weaker trigger directly — an unbalanced piece family with min cost below
  (E/√p)λ on every piece — since it decides the dichotomy without needing a faster algorithm.

### Review of Finding 5 (`review-pc.md`) — proofs sound, one claimed result fails [V]
- L1 (reduction): correct. H4 answered: the generic path of the whole input space must reject, so every component
  y = g_e divides one of its test numerators. The weakest-link worry does not apply.
- L2, L3 (N_g hard; cofactor hard): correct.
- L4 (local-method barrier): correct for ideals of small (polynomial) colength only.
- L6 (Span Conjecture): the implication is correct, but it is NOT a reduction [X]. For Ryser g the span of the g_e is
  2^n − 1 by elementary linear algebra, so the permanent bound plays no role and the conjecture just restates the gap
  in a stronger form. It is harder than the target. Drop it as a route.
- Degenerations: one implication in y2 was stated in reverse.
- P_ℂ ≠ PAR_ℂ and P_ℝ ≠ PAR_ℝ: correct; a one-line corollary of Bürgisser 2004 plus the border bound. Whether it was
  open before rests on y1's quotations (not re-checked).
- Lemma L (defect ≤ 1): correct. Overclaim removed: graph(per) ∉ NP_ℂ(nu) is proved only for defect ≤ 1 verifiers.
- Bürgisser's Oct 2026 conjecture (VNP ⊄ closure of VP ⇒ P_ℂ(nu) ≠ NP_ℂ(nu)) exists as cited (arXiv:2606.25121).
- Lead's updated assessment of target 2: the real gains are P_ℂ ≠ PAR_ℂ, Lemma L for defect ≤ 1, the cofactor-hardness
  lemma and the local-method barrier. Toward P_ℂ ≠ NP_ℂ itself we have only located the gap.
- Open test case suggested by the referee: is the cyclic norm of Φ = ∏_i (x_i + T^{2^{i−1}}) easy? Its roots span 2^n
  dimensions. Passed to pc1.

### w1 interim 1 (rank inequalities) [K + R, unreviewed]
- H3 confirmed: x7's lemma L1, rk(A|BCD) ≤ rk(AB|CD)·rk(AC|BD), is Cadney–Huber–Linden–Winter 2014, Thm 1
  (arXiv:1308.0539). x7's L2, rk(AD|BC) ≤ rk(AB|CD)·rk(AC|BD), was their open Hypothesis 1, proved by
  Song–Chen–Sun–Hu 2023 (arXiv:2105.07679, Thm 9). Both stated over ℂ; other fields being checked.
- The complete list of four-party linear rank inequalities is known (same papers).
- On K₄ they reduce to the triangle inequality c_k ≤ c_k′ + c_k″. With uniform weights every family has ρ ≥ 4/9,
  below the target √2/3 = 0.471, so K₄ is NOT excluded. With general weights only 1/3.
- Open: does c₁ ≤ c₂ + c₃ hold for single tensors on Δ₃? If so, ρ ≥ 2/3 on Δ₃ with uniform weights, which would
  kill the 1/√3 target there (not the 1/√2 prize) and leave K₄ as the only live three-merge instance.
- Lead's question back to w1: which bounds hold for the engine's actual (possibly non-uniform) accounting.

### pc1 status note (restricted-machine separations) [R claimed, unreviewed, notebook not yet on disk]
- Theorem A (elementary, no border bound): a polynomial with τ distinct powers of y is divisible by y − g_E for at
  most 2τ − 2 Ryser roots (Descartes' rule at a real specialisation). With the reduction L1: any tree deciding A_g
  whose generic-path tests have ≤ τ distinct y-powers needs ≥ (2^n − 1)/(2τ − 2) tests. Covers bounded y-degree and
  y-lacunary tests of any degree. So polynomial time forces tests with ≥ 2^n/poly distinct y-powers.
- Theorem B (uses the border bound): if Q = c(x)·N_g·H and H has at most h distinct y-roots, then
  L̄(per_n) ≤ O((h+1)·n³·L(Q)). So an easy multiple needs a cofactor with superpolynomially many distinct roots
  ("few false alarms" is impossible).
- Caveat pc1 could not remove: Ryser roots caught with non-uniform multiplicity give a weighted sum Σ μ_E g_E.
- Unified statement: for every easy multiple, the "trace germ" of the cofactor is border-hard.
- Referee's test case Φ = ∏(x_i + T^{2^{i−1}}): undecided. All low power sums of its roots are easy, so the border
  bound is blind to it. A sibling with matching-encoding weights has a hard cyclic norm.
- Lead's input on the caveat: with Glynn's form the weighted sum equals μ̂(0)·per + Σ_{a≠0} μ̂(a)·F_a, and
  μ̂(0) = Σ μ > 0 always, so per never cancels; the question is the contamination. Suggested a clean target that
  sidesteps it: no UNAMBIGUOUS polynomial-time BSS machine (each branch caught once) decides A_g.
- H5 status: looks true. Awaiting the notebook, then a referee.

### Idea agent status note (Newton-polygon route) [R claimed, unreviewed, file not yet on disk]
- Theorem (no border bound, every characteristic): in the "ΠΣ-sparse" model (each test a product of ≤ m powers of
  t-sparse polynomials, any degree), a tree deciding A_g has T·m·(t−1) ≥ 2^n − 1 tests on its generic path.
  Idea: weight the variables by powers of a parameter τ; root valuations of N_g·H contain those of N_g for every
  cofactor H, so the cofactor cannot help; the 2^n − 1 Ryser branches get distinct valuations; a sparse polynomial
  has few slopes. Multiplicity-blind.
- Extension claimed for cancellation-free tests of bounded alternation depth.
- Tightness gadget: a size-O(n) positive circuit with 2^n distinct root valuations, so no slope bound for general
  circuits; a depth hierarchy.
- Span Conjecture: false in every positive characteristic; in characteristic 0 it would imply the ℂ-Knapsack norm
  has no easy multiple. Confirms the referee: drop it. [X]
- Test case Φ: undecided; guess hard. Same facts as pc1.
- Lead's action: relayed the theorem to pc1 to verify and merge with Theorem A; asked whether the tropical argument
  can replace the trace in Theorem B and so remove the multiplicity caveat.
- New hypothesis H7 [C]: valuation (tropical) invariants are the right tool for restricted-model separations because
  they ignore both the cofactor and multiplicities; the obstacle is cancellation at high alternation depth.

### w1 interim 2 (three-merge line) [R/N, unreviewed]
- Fields: CHLW Thm 1 holds over every field (pure linear algebra). Song et al. Thm 9 is proved over ℂ only;
  180,913 tests over GF(2)/GF(3) found no violation [N].
- Accounting: the engine's real accounting is general weights q. On K₄ the rank LP then gives only ρ ≥ 1/3; the 4/9
  was a symmetric sub-class statement. The escaping vectors (4,4,0) are not realisable as a family (z1), so K₄
  remains open exactly at z1's "three-rank object".
- Δ₃: rank LP with all 156,960 four-party inequalities improves x7's factor 4 to 2. With uniform q: ρ ≥ 1/2 on Δ₃
  (flattening gave 4/9). General q running; expected 1/2 by symmetry. If confirmed, first unconditional three-merge
  floor at 1/2 on Δ₃ (over ℂ; field-free version being tested).
- SU(2) recoupling pieces on K₄: dead [X]. Channel projectors are related by Racah polynomials, giving a polynomial
  uncertainty principle (small support in one channel forces near-full rank in the other two).
- Lead's reading: both dead K₄ families (Weyl, SU(2)) are compact-group constructions killed by uncertainty
  principles. Appendix B is su(1,1) (non-compact; Meixner = its Clebsch–Gordan coefficients).
- H8 [C]: if three-wire fusion exists it comes from coupling three su(1,1) discrete-series representations
  (Tratnik-type multivariate Meixner). Passed to w1 as the first thing to test for Task 2.

### Idea agent, second note: `ideas-span.md` on disk with proofs [R claimed; referee launched]
- Theorem S: generic-path product = product of ≤ R polynomials with ≤ t monomials ⇒ R(t−1) ≥ 2^n − 1.
  Distinctness of the 2^n − 1 valuations now proved (base-n digits).
- Theorem 2T: first cancellation case. For a difference of two products of powers of sparse polynomials, the number
  of distinct root valuations is bounded independently of the exponents (non-archimedean Rolle lemma, residue
  characteristic 0). k terms: sketched, tower-type bound; conjectured polynomial.
- Theorems S′ and G: depth hierarchy for cancellation-free tests. Lower bound 2^{Ω(n/Δ)} at alternation depth Δ;
  exponential up to Δ = n^{1−ε}; the method provably stops at Δ = Θ(n/log n).
- Open (its Idea 7): does A_g have small cancellation-free tests at depth ≥ n/log n? ("tropical cofactor problem")
- Lead's action: launched an Opus referee (`review-sparse.md`) on Theorems S, 2T, S′, G and on pc1's A and B, with a
  prior-art search (Ben-Or, Meyer auf der Heide, Grigoriev–Vorobjov, Koiran et al., Cucker–Shub, Meer).

### pc1 note 2: notebook on disk; theorems merged [R claimed; with referee]
- pc1 verified the idea agent's Newton-polygon theorem and found a one-line distinctness proof (weights w_ij = 2^i
  off the diagonal, 0 on it; val g_E = Σ_{i∉E} 2^i).
- Merged Theorem A: sparsity in x is not needed. If every generic-path test numerator is a product of ≤ m
  polynomials, each with ≤ τ distinct powers of y (arbitrary coefficients, any degree, any multiplicities), then
  T·m·(τ−1) ≥ 2^n − 1. Over any field. Contains bounded y-degree, sparse tests, the ΠΣ-sparse model, y-lacunary tests.
- Theorem B′: "(h,h′)-tight" machines; quotable case: unambiguous machines with polynomially many false alarms.
  Unambiguity alone is not enough (lead's suggestion was too optimistic).
- Lead's partial-averaging idea for the multiplicity caveat: does not work (the Fourier mass stays on a coset of size
  2^n/|Γ|). Recorded as open problem O1.
- Theorem B cannot be re-proved tropically: slopes record presence of branches, never their sum.
- Question raised by pc1, relayed to the idea agent: can the gadget realise a slope set containing the one N_g
  forces? If yes, a barrier: no valuation-only argument proves the cofactor gap.
- Idea agent's final report: original problem not within reach; top items are the slope theorems (S, S′, G, 2T).
- H7 refined [C]: valuations settle restricted models but probably cannot settle the full gap (pending the gadget
  answer). H5 confirmed pending referee.

### pc1 final report (`pc1/notebook.md`, checks pass) [R claimed; with referee]
- Theorem A as in note 2; contains the idea agent's Theorem S with the same constant. Lemma A.1 (Descartes) kept for
  Knapsack.
- Theorem B: if Q has the Ryser roots with multiplicities μ_E and ≤ h other distinct y-roots, then
  L̄(Σ μ_E g_E) ≤ C(h+1)n³(L(Q)+n²). B′: no polynomial-time tree with polynomially many false alarms and uniform hit
  multiplicity off polynomially many branches. Mixed Theorem AB.
- Prop. σ: for every easy multiple, the degree-n germ of the cofactor's trace is border-hard (contains L3 and B).
- Partial norms: subcubes of dimension ≥ n^ε are border-hard (they project onto a smaller permanent). Arbitrary large
  subsets open.
- Test case Φ: undecided; the border bound is blind to it; a sibling with subset-sum weights is a border-hard
  cyclic norm.
- Failed: removing multiplicity weights (every method costs 2^n); tropical proof of B; root counting with y inside
  the base polynomials; implicit products; constant-free machines.
- Open statements carried forward: O1 (is every positively weighted Ryser sum border-hard?), O2 (what a
  polynomial-time machine must look like: a test that is not a short product of y-sparse polynomials,
  superpolynomially many spurious roots, a border-hard spurious-root trace), O3 (the test-case norm).

### w1 interim 3 (three-merge line) [R claimed, unreviewed]
- THEOREM claimed: ρ_Δ₃ ≥ 1/2 for every family and every weighting q, in characteristic 0. Human proof: one
  CHLW Thm 2 instance plus three instances of Song et al.'s inequality give 2h(R) ≤ Σ h(C_g) + Σ h(D_g); hence
  c_k ≤ 2(c_k′ + c_k″); with the pigeonhole piece, V ≥ 4.5λ. LP dual certificate checked symbolically. Field-free
  only 4/9 survives; no violation found over GF(2)/GF(3) in 79k tests [N]. Closes the "ρ < 1/2 on Δ₃ not ruled out"
  item from the engine3 notes.
- Lead's su(1,1) reading (H8) partly right, partly wrong: su(1,1) recoupling projectors also die (each energy shell
  is finite). Appendix B escapes because its pieces are boosts with a Gram pole, not channel projectors.
- No-go claimed: single-flavour three-wire fusion at 1/√3 is impossible in the whole multivariate
  generalised-Meixner class (Tratnik families lie inside x7's ansatz; at most d+1 wires on a d-mode bond).
- LIVE CANDIDATE [C]: a d = 2 bond with 2D wires (bivariate Meixner, multinomial weights) passes the constant-term
  conditions for three wires and has naive ρ ≈ 3^{−1/3} ≈ 0.693 < 1/√2 ≈ 0.707. Sufficiency untested. If real:
  α′ ≈ 0.528, #3-SAT in 2^{O(n/(log n)^{0.528})}. Consistent with all floors (1/2 unconditional, 1/√3 flat).
- Lead's worry: for two merges the same 2D-oscillator spectrum gave 0.794 because of the degree budget (x5/x6).
  Asked w1 what plays that role with three merges and to do the engine's real accounting before anything else.
- Z₃ interpolation on K₄: a sphere law capped exactly at the flat floor [X as an improvement].
- H9 [C]: the candidate dies to a three-merge version of the degree-budget/ladder argument. If it does not, it is a
  new record.

### Running (as of this entry)
- `review-link.md` (Opus referee): Findings 2 and 3.
- `review-pc.md` (Opus referee): Finding 5 and P_ℂ ≠ PAR_ℂ.
- `ideas-span.md` (Fable): try to refute the Span Conjecture; ranked attacks.
- `w1/` (Opus): rank lemma, three-wire fusion, recoupling pieces.
- `pc1/` (Fable): restricted-model separations; partial norms.
