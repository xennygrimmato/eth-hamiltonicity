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

### Idea agent: the valuation barrier (`ideas-span.md` §7) [R claimed; with referee]
- Answer to pc1's question: YES. A positive-coefficient polynomial of size O(n), in one x-variable and y, has root
  valuations (under pc1's weights) equal to all even integers in [0, 2^{n+1}), which contain those of N_g.
- Robust to: any single integral monomial substitution; polynomially many weight vectors at once.
- Not covered: all weight vectors simultaneously (containment of tropical varieties).
- BARRIER: no argument using root valuations for one, or polynomially many, monomial substitutions can prove that
  N_g has no easy multiple. H7 resolved: valuations settle restricted models only. Theorems S, A, S′, 2T stand; the
  barrier says their restrictions cannot be dropped.
- Lead's next assignment to the idea agent: for cancellation-free (positive) tests, tropicalisation is exact for all
  weights at once, so the barrier may not apply. Try to remove the depth restriction from Theorem S′ using
  monotone/tropical circuit lower bounds (Jerrum–Snir, Jukna). Deliver a theorem, a universal positive barrier, or a
  reduction to a named open problem.
- H10 [C]: no polynomial-size family of positive tests of any depth decides A_g (a "monotone" BSS separation).

### w1 verdict on the 0.693 candidate: DEAD [X] (H9 half right)
- It does not exist. In the single-denominator (Tratnik/GVZ) multivariate-Meixner class every pole wire is
  effectively one-dimensional: the pole condition forces a matrix of rank ≤ 1. So a bond with 2D wires cannot be
  built there. w1 withdrew the number.
- The degree budget would NOT have killed it (lead's guess H9 was wrong about the mechanism). The balanced formula is
  ρ = p^{α−1} (p wires fused per bond, α the level-count exponent); three merges beat 1/√2 iff α < 0.685. A genuine
  2D three-wire bond (α = 2/3) would give 0.693. What forbids it is the local bond algebra.
- The d = 2 bond with 1D wires passes the pole conditions but its shells are full rank: it loses for large energy.
- Conclusion for the line: within generating-function (hypergeometric, single-denominator) families no three-wire bond
  beats 1/√2.
- Remaining open door, stated precisely: a bond whose Gram identity has a pole of order ≥ 2 at X = 1 on wire spaces
  of dimension ≥ 2 — matrix-valued poles (determinantal generating functions) or non-Möbius families.
- Lead's last constructive suggestion (45-minute time-box): determinantal generating functions are the reproducing
  kernels of holomorphic discrete series of U(p,q) (matrix-argument Meixner/Laguerre; Howe duality). Asked w1 to redo
  the pole computation for the rank-2 case, then write the final report.
- H1 (the flat case holds; the engine's pieces are optimal) gains weight: every constructive family tried is dead for
  a structural reason.

### w1 final report (`w1/notebook.md`) [R claimed, unreviewed]
- No construction; no improvement on 2^{O(n/√log n)}.
- Theorem: ρ_Δ₃ ≥ 1/2 for every family and every q over characteristic-0 fields. Needs both CHLW Thm 2 and Song et
  al.'s inequality; field-free only 4/9. Factor 2 is the limit of four-party rank inequalities; c₁ ≤ c₂ + c₃ stays [C]
  (it would cap every spherical family at exactly 1/√2).
- K₄ under the real accounting: known rank inequalities give only 1/3; flat floor √2/3 unreached. Still open.
- Dead, with reasons: Weyl (Donoho–Stark); SU(2) and su(1,1) recoupling projectors (Racah-polynomial uncertainty);
  Z₃ interpolation (sphere law pinned at the flat floor on K₄); Tratnik/GVZ multivariate Meixner (pole wires are
  one-dimensional, Prop. A); determinantal / Hermitian-symmetric class (dimension ≥ 3 gives α ≥ 3/4, ρ ≥ 0.76;
  sketch only, matrix-pole algebra not checked symbolically).
- Remaining open case: a non-Möbius, non-determinantal bond family with a pole of order ≥ 2 and level-count exponent
  ≤ 0.685; on K₄, a sphere-law family avoiding the three corners.
- Lead's assessment of target 1: constructive side exhausted for every family anyone on the team can name. Outputs
  worth keeping: the Δ₃ ≥ 1/2 theorem, the refereed win-win link, the catalogue of no-gos. H1 (engine pieces
  optimal) is the working belief; proving it unconditionally = proving the flat case, which the toolkit cannot do (c1).
- Next for target 1 (proposal): referee w1; then write the paper "The ETH engine and the VP ≠ VNP dichotomy".

### Idea agent §8: the cancellation-free case — no theorem, one correction, one reduction [R claimed, no scripts]
- CORRECTION: Theorem S′ as stated ("+, × and positive constants") is vacuous. A positive polynomial is never
  divisible by y − g for positive g, and half the Ryser branches are positive; no positive test family decides A_g at
  any size, for a sign reason. Fix: state S′ for Newton-faithful circuits (no vertex of the Newton polytope cancels at
  a sum gate). Bound unchanged. Theorems S, 2T, G and the §7 barrier unaffected. Referee informed.
- H10 as posed is therefore trivially true and uninteresting. The real question (Newton-faithful tests, any depth)
  reduces to a tropical covering problem: a (min,+) circuit whose corner locus contains all hyperplanes θ = a(S)
  (the resonance arrangement). Proved lower bound only (1−o(1))·n² min gates.
- Why known monotone/tropical lower bounds do not apply: they bound circuits computing an exact support, while the
  cofactor adds arbitrary vertices; extension complexity is not inherited by Minkowski summands.
- Equivalent form: a small integer-weight ReLU network whose decision boundary contains all 2^n graphs.
- Conjecture H (smallest multi-parameter case): a size-s (min,+) circuit in three homogeneous variables contains at
  most poly(s) complete planes, no three sharing a line. Would give an exponential bound.
- Lead's assessment: the P_ℂ line has reached its frontier for this round. Deliverables pending the referee:
  merged Theorem A, Theorem B/B′, the two-term cancellation bound, the depth hierarchy (corrected model), the
  valuation barrier. Open: O1–O3, Problem TC, Conjecture H.

### Referee report on the P_ℂ restricted-machine results (`review-sparse.md`) — nothing broken [V]
- pc1's Theorem A: CORRECT, and the statement for a paper. Form: if every generic-path test can be written F_i/G_i
  with F_i a product of ≤ m polynomials each with ≤ τ powers of y, then T·m·(τ−1) ≥ 2^n − 1. Every characteristic.
  (The idea agent's Theorem S needed a "catching lemma" fix; A contains it.) Descartes version also correct.
- Non-archimedean Rolle lemma: correct (complete algebraically closed field, residue characteristic 0).
- Theorem 2T (two-term cancellation): correct with fixes; corrected bound ≤ 2m·t^{2m} + 4m(t−1) + 1. The k-term
  version is an unverified sketch and must not be claimed.
- Theorem S′ / Theorem G / hierarchy: correct with fixes (layering). NOTE: this verdict predates the idea agent's own
  correction that S′ is vacuous for literally positive tests on A_g; the referee has been sent the correction and
  resumed. Treat S′ as unsettled until its addendum arrives.
- §7 valuation barrier: correct. Precisely: rules out proofs using only y-Newton polygons of a multiple under
  polynomially many integral weightings. Does NOT rule out all-weights-at-once arguments, residue data of roots, or
  trace arguments. pc1's "B cannot be re-proved tropically" is a heuristic, not a theorem.
- pc1's Theorems B, B1, AB, Prop. σ: correct. Theorem B′: needs a fix — "unambiguous ⇒ multiplicity 1" fails when
  divisors vanish on branches; holds for division-free trees with each branch a simple zero of exactly one test.
- PRIOR ART: the gadget (r = 2) is Hrubeš–Yehudayoff, "Shadows of Newton polytopes" (CCC 2021) Thm 5.1, and the core
  of S′ is their Thm 5.4. Two-term valuation counts: Koiran–Portier–Rojas (arXiv:1309.0486) under a genericity
  condition; 2T is a residue-characteristic-0 analogue without it. Sparse-test separations over ℂ: no published
  statement found, but elementary.
- SIGNIFICANCE (referee): correct and unconditional, but the models are much weaker than P_ℂ, the cores of S′ and G
  are known, and only Theorem B/B′ uses the permanent bound. Suitable for a short note on restricted separations
  plus the barrier. Not progress on P_ℂ vs NP_ℂ itself, and a paper must say so.
- Lead's conclusion for target 2: frontier reached for this round. Reviewed deliverables: P_ℂ ≠ PAR_ℂ (Bürgisser +
  border bound), Lemma L (defect ≤ 1), cofactor-hardness and trace-germ statements, Theorem A, Theorem B (with the
  corrected B′), Theorem 2T, the valuation barrier.

### Referee addendum (`review-sparse.md` §12): the S′ correction and §8 [V]
- The idea agent's correction is right; the referee's first verdict on S′ is withdrawn. S′ for literally positive
  tests is vacuous on A_g. Nothing else depended on it.
- The "Newton-faithful" model is well defined and non-trivial; restated S′ holds: T·(1 + s/Δ)^Δ ≥ 2^n − 1; depth
  Θ(n/log n) is tight.
- §8 solid: Problem TC and its two consequences; the reduction to the resonance arrangement; r(n) ≥ (1−o(1))n² min
  gates (and counting cannot do better); the ReLU-network equivalence.
- §8 not justified: "Conjecture H ⇒ exponential bound" has a gap (Problem R only needs planes over the positive
  orthant, a wedge; H is about complete planes). The Euclid/Ostrowski construction is unverified.
- More prior art: the fold gadget is Telgarsky's sawtooth (COLT 2016).
- STATE OF TARGET 2: all agents finished. Reviewed results listed in the previous entry stand, with S′ in its
  Newton-faithful form. Open: O1–O3, Problem TC, a repaired Conjecture H.

### State at end of round (24 Nov, evening)
- Target 1 (engine / VP ≠ VNP link): link reviewed [V]; Δ₃ ≥ 1/2 theorem and three-wire no-gos unreviewed [R];
  no faster algorithm; one precisely stated open case.
- Target 2 (P_ℂ vs NP_ℂ): not proved, not within reach of these methods; restricted-machine separations and a
  valuation barrier reviewed [V].
- No agents running. Proposed next: referee w1; write the two papers.

### Running (as of this entry)
- none

## 26 Nov 2026

### Survey of the labs' repositories (lead)
- Anthropic `formal-math`: no change since 23 Nov (zeta23, 3sum-apsp, eth, vp-vnp).
- OpenAI `math`, 24 Nov: nine new manuscripts. Family 379, "Euclidean tensor geometry":
  - "Euclidean geometry in the asymptotic spectrum of tensors": over any field, tensor prices exist for sites in a
    real Hilbert space, a shared bit costing the distance. Lean. This reads as the FLAT HYPOTHESIS of Anthropic's
    VP ≠ VNP paper, proved. To be confirmed against the exact statement before we rely on it.
  - "The matrix multiplication exponent is nine fourths": ω = 9/4 EXACTLY over every field (matching lower bound;
    rank and border rank of ⟨n,n,n⟩ ≥ n^{9/4}; dual exponent 1/2; exact rectangular formula). Lean statement
    `square_exponent : formalOmega F 1 1 1 = 9/4` for division-free straight-line programs with formal correctness.
  - Permanent / Hamiltonian cycle: exp(c(log N)²/(log log N)²) gates (this bound not formalised).
  - VP ≠ VNP via grid state sums; Fourier transform N(log N)^{1/2+o(1)}; integer multiplication
    n(log n)^{1/2+o(1)}; an exponential sunflower bound.
  - Family 380: strongly polynomial linear programming (Smale's 9th problem); polynomial Hirsch disproved.
- Google DeepMind: nothing new found for November; latest is the Aug 2026 AlphaEvolve bound ω < 2.371177.
- Reddit is not reachable by the search tool; Hacker News and Latent Space carry the discussion. No expert reading
  of the 24 Nov manuscripts is public yet.

### Consequences (hypotheses, to be checked)
- User's new target, an n² matrix multiplication algorithm: if OpenAI's claim holds, impossible for arithmetic
  circuits over ANY field. What remains is non-algebraic computation over finite fields (word RAM, Boolean circuits,
  functional rather than formal correctness).
- H1 (flat case holds, engine's pieces optimal) would become a theorem via the reviewed win-win. The swap-splitting
  problem recommended on 24 Nov would be answered: the circle is the limit. Do not assert until the statement is
  checked.

### Running
- `research/mm/verify-nine-fourths.md` (Opus): build OpenAI's Lean proof, audit the statement, check consistency
  with known bounds, list what the theorem does not cover.
- `research/mm/ideas-n2.md` (Fable): map of open models for n² matrix multiplication; ranked targets; consequences
  for our notes.

### Change of plan (user, 26 Nov)
- Verifier stopped at the user's request; we take the 9/4 claim as given and work scrappily: try → feedback → update.
- Running now:
  - `research/mm/ideas-n2.md` (Fable): map of models where n² is still open; ranked targets.
  - `research/mm/lab/` (Opus, "lab"): fast experiments. E1 Boolean vs bilinear cost of 2×2 over F₂ (is 6 AND gates
    possible?); E2 word-RAM baselines; E3 integer packing; E4 lookup-table identities.
  - `research/mm/why-nine-fourths.md` (Fable): a geometric intuition for 9/4 (triangle perimeter 6 over shared-label
    rate 8/3 at a tripod), with a figure and tweet versions.
- H11 [C]: over F₂, computing the product as a function (non-bilinear circuits) can beat bilinear rank at some small
  size. E1 tests the smallest case. If no gap shows at any reachable size, the non-algebraic route is weaker than hoped.

### Idea agent, interim note 1 (reading of the OpenAI papers) [K, from the text; unverified by us]
- FLAT HYPOTHESIS CONFIRMED FROM THE STATEMENT: companion Theorem 1.1(2) gives, for every finite set S in a real
  Hilbert space, ONE spectral point whose wire metric is ‖u−v‖/W(S), over every field; the finite-dimensional case is
  in their Lean. That is our FH with equality. So, given OpenAI's result: H1 is a theorem, the reviewed win-win's
  flat floors are unconditional, the engine's two-merge pieces are optimal, and the swap-splitting question is
  answered (the circle is the limit). Exact list of our statements affected: pending in `research/mm/ideas-n2.md`.
- AUDIT FLAG: the 9/4 lower bound is not algebraic at its core. It rests on the paper's Theorem 2.2, a lower bound
  for trivalent tensor networks over a finite field computing "list distinctness", and the paper's own Prop. 2.3
  embeds Boolean circuits in such networks. At t = 1 this would be a superlinear Boolean circuit lower bound
  Ω(N(log N)^σ) for an explicit function in P — far past the 3.1n record and not advertised. Either the release's
  biggest unadvertised corollary or the first place to look for an error. We are NOT verifying (user's decision);
  recorded so that anyone reading our work knows the claim's weak point.
- CONSEQUENCE FOR THE TARGET: the same lemma may give Ω(n²√log n) for any Boolean circuit multiplying matrices over
  F₂. Honest target is therefore n²·polylog(n) bit operations over F₂, not n² flat.
- Functional algorithms over F₂ do not tensor (x² = x fails for matrices), so a small-size gap between Boolean and
  bilinear cost does not amplify by recursion. H11 downgraded: a gap at size 2 would be a curiosity unless a
  block-compatible mechanism is found.

### Lab note 1 (E2 baselines, first E1/E3 data) [N]
- Word-RAM baselines over F₂ (w = 64, exact word-operation counts): Four-Russians n = 512…4096 costs 0.43M, 2.9M,
  20.5M, 148M; local exponent 2.70 → 2.85, heading to 3 (it is n³/(w log n)). Bit-packed Strassen–Winograd: slope
  ≈ 2.82, not yet ahead at n = 4096. About 9 word operations per output bit at 4096, growing like n/(64 log n).
- Reading: every known word trick buys w·log n over n³ and nothing more. For n²·polylog the n-fold sharing has to come
  from structure, not parallelism.
- E1 first data point: 2×2 matrix times vector over F₂ has Boolean multiplicative complexity exactly 4 = its rank
  (3 AND gates certified impossible). No gap there. 2×2 × 2×2 at 6 AND gates: SAT still running.
- E3: 1-D Kronecker packing for 2×2 needs product length 11 > n³ = 8 (exact). n = 3 running.
- Lead's steer: use Mirwald–Schnorr (a quadratic Boolean form in 2k essential variables needs exactly k ANDs) on XOR
  combinations of outputs as a free lower bound; also compare TOTAL gate counts, since the 9/4 claim counts additions.

### "Why 9/4" agent, interim note [K from the papers + its own check; unreviewed]
- Dictionary: wire price per bit = distance d(i,j); matrix multiplication = triangle of three wires (perimeter Per);
  a rank decomposition = one three-way shared label with rate D; monotonicity gives ω ≥ Per/D.
- Write the three distances as a_i + a_j (tripod with arms a₁, a₂, a₃). Paper's "tripod principle" (Prop. 8.1): for
  every spectral point, D ≥ (a₁+a₂+a₃) − (1/a₁+1/a₂+1/a₃)^{-1}: hub-routing cost minus the parallel resistance of
  the arms. Unit arms: 3 − 1/3 = 8/3, Per = 6, ratio 9/4.
- By AM–HM the parallel resistance is at most (Σa)/9, so Per/D ≤ 2/(1 − 1/9) = 9/4. So 9/4 = 2 × 9/8: "2" is the flat
  value, "1/9 = (1/3)²" the best three-arm discount. Calibration on the unit tripod: D = 3 ⇔ ω = 2; D = 2 ⇔ ω = 3.
- The inequality D ≥ 8/3 is the algorithm side (October upper bound, polynomial multiplication). The 24 Nov claim is
  that equality is attained by some spectral point; its proof is by contradiction and gives no intuition.
- Agent's own check: the tripod formula is the Legendre dual of the rectangular formula
  ω = (xy+yz+zx)²/(4xyz); the boundary ω = x+y and α = 1/2 correspond to reciprocals adding (1/z = 1/x + 1/y).
- Discrepancy to reconcile: the agent says the paper proves only 1/2 ≤ α ≤ 2/3; OpenAI's Lean scope note states
  α = 1/2 and the exact rectangular formula as Lean theorems. Asked the agent to say which is claimed where.
- If ω = 9/4, Strassen's asymptotic rank conjecture for tight tensors is false.

### Lab note 2 (E3 packing closed) [N + R]
- Exact minimum 1-D monomial packing of ⟨n,n,n⟩: product length 11 at n = 2 and 41 at n = 3 (n³ = 8, 27). Stride
  packing needs ~2n³ slots, so with fast integer multiplication the total is n³·polylog, worse than Four-Russians.
- Obstruction: monomial packing into a commutative product is a triple-product embedding into an abelian group
  (Cohn–Umans forces length ≥ n³); any LINEAR packing is a restriction of polynomial multiplication, so it is a
  bilinear algorithm in disguise and needs length ≥ n^{9/4}/O(1) under the claim. Only loophole: non-linear read-out
  (carries, comparisons). E3 dropped. [X]
- The lead's Mirwald–Schnorr shortcut gives only 4 for 2×2 and 9 for 3×3: useless. [X]
- Lead's expectation: in the quadratic-Boolean model the 2×2 answer is 7 (Winograd 1971), and quadratic algorithms can
  never beat rank/2. A gap can only live in circuits with AND gates on higher-degree intermediates.
- New experiment E5: exhaustive sweep of tiny bilinear maps over F₂ (dimensions ≤ 3): does any have general Boolean
  multiplicative complexity below its quadratic complexity? One example = first positive sign; none = evidence against
  the non-algebraic route at the level of AND counts.

### Lab note 3 (E1 answered in the quadratic model) [N, exact]
- 2×2 matrix product over F₂, quadratic-Boolean model (ANDs of arbitrary affine forms in all 8 inputs, x² = x allowed):
  multiplicative complexity is exactly 7. Six refuted by exhaustive enumeration of alternating forms (57.3M class
  pairs; positive controls correct); seven found in 0.1 s. So x² = x buys nothing here. Matches Winograd.
- Literature: Mirwald–Schnorr prove quadratic circuits optimal only for 1- and 2-output quadratic maps. For ≥ 3
  outputs, whether higher-degree intermediates can save AND gates is OPEN (the "Boyar–Find question"). An Aug 2026
  paper (arXiv:2608.30238) settles one instance (4-term binary polynomial multiplication: 9, no gain).
- So the non-algebraic route, at the level of AND counts, is exactly an open question in the literature, with every
  settled instance saying "no gain". H11 further weakened.
- Next: E5 sweep of tiny bilinear maps (exact general complexity), then general 6-AND search for 2×2.

### "Why 9/4" write-up complete (`research/mm/why-nine-fourths.md`, `.svg`) [K + agent's own derivations; unreviewed]
- Core: 9/4 = 2 × 9/8; tripod inequality D ≥ Σa − 1/Σ(1/a); unit arms 8/3; AM–HM gives the cap.
- 8/3 in two lines: the polynomial-multiplication price is homogeneous of degree D; the "half rule" (three long×short
  blocks fit in 3h + a) gives ∂P/∂log b ≥ 4/3 at a = b; two inputs give 4/3 + 4/3.
- Equivalent form: D* = max over splits f of Σ a_i(1 − f_i²). "Parallel resistance" is partly mechanism (lever rule,
  optimal split), partly formula; no literal flow found.
- Legendre dual reproduces the rectangular formula exactly (checked on 200 random shapes).
- Paper vs Lean: the paper states only 1/2 ≤ α ≤ 2/3 and the max(...) bound; OpenAI's Lean scope note claims α = 1/2
  and the exact rectangular formula. The Lean claims more than the paper. Solution module not inspected.
- Figure rendered and checked by the lead. Tweet (279 chars) and three-tweet thread included.
- Caveats: barrier constants and history from memory; Parts II–IV of the lower-bound paper not read.

### User steer: anti-proofs welcome
- New executor `research/mm/anti/` (Opus): derive from OpenAI's network lower bound a precise theorem that Boolean
  circuits for n×n multiplication over F₂ need c·n²·(log n)^γ gates. Crux: the routing must be input-dependent.
- H12 [C]: given OpenAI's Theorem 2.2 / Lemma 4.1, flat n² is impossible even at the bit level, by a power of log n.

### Lead's assessment of the "why 9/4" picture (asked by the user): not convinced
- It explains ω ≥ 2 (flat: label = half the perimeter) and where 9/4 sits in the October ALGORITHM. It does not
  explain why nothing can beat it: the "tripod" is a change of variables, "parallel resistance" is the shape of one
  trick's optimum, and the Legendre-dual check is internal consistency, not outside evidence.
- A real "why" must come from the lower bound's mechanism (Parts II–IV of the paper, unread by us), or the picture
  must predict a number checkable on another tensor with a known exponent.
- Reasons to hold the claim itself loosely: refutes Strassen's asymptotic rank conjecture; implies an unadvertised
  superlinear Boolean circuit lower bound; Lean scope claims more than the paper.

### Idea agent final report (`research/mm/ideas-n2.md`, ~740 lines) [reading + own derivations; unreviewed]
- Algebraic n² is dead (given the release); the bound does not transfer to bits, except for bilinear and quadratic
  XOR–AND circuits where functional = formal. Functional algorithms do not recurse on blocks.
- Conditional impossibility: pin A to a permutation matrix → input-dependent routing → Ω(n²√log n) gates for any
  Boolean circuit multiplying matrices, over any semiring, IF some characteristic has "no ports" (a hypothesis the
  paper leaves open). The method caps at polylog factors: n^{2+ε} for bits is out of reach of it.
- A formal-versus-functional separation is already a theorem given the release: "x is exactly a Hamiltonian cycle" is
  easy as a Boolean function and superpolynomially hard as a formal polynomial over F₂.
- "n² theorems" available now from the exact rectangular formula: n×√n products in n^{2+o(1)}; fully sparse products
  in m^{4/3+o(1)}; Zwick APSP at n^{2.5}. ("Atlas", target T4.)
- Cleanest negative target: polynomial multiplication over F₂ needs Ω(n√log n) Boolean gates under no-ports, tight
  against the release's upper bound.
- Our notes, given the flat-hypothesis theorem: flat floors, ρ_× = 1/√2, "no SWAP splitting below Q^{√2}", the K₄
  floor all become theorems; H6 dead. Still open: attaining 1/√3, K₄, p ≥ 5 merges. New caveat: the 9/4 paper says
  flat prices are not extremal for the matrix-multiplication triangle (tripod prices beat them), so for ≥ 3 merges the
  true floor may be ABOVE the flat floor. Whether "contracting" is also true is not settled by this.
- Correction: Alman–Vassilevska Williams (min,+) exponent appears as 2.9995 in search, not the 2.99942 I wrote
  (unverified either way).
- Ranked: T1 impossibility-and-separation package (85% for the conditional form); T2 neutral public note on the hidden
  corollary; T4 atlas; T5 an actual n²·polylog algorithm over F₂ (< 1%); AND-count gap at 2×2 (5%).
- Lead's plan: anti executes T1/N6; lab does calibration + atlas + sweep; decide on T2 with the user.

### User: "try all of those; find a convincing story, easy even for high-school students"
- Resumed the why-9/4 agent (Fable): Part A read Parts II–IV for the lower bound's real mechanism (is 9/4 forced, or
  would the argument "prove" any current upper bound?); Part B test the picture on tensors with known exponents;
  Part C a jargon-free story with figures (`research/mm/story-nine-fourths.md`).
- New executor "note" (Opus): neutral two-page note on the hidden circuit corollary, with verbatim quotes, a Lean
  dependency-cone check by grep, and a risk list (`research/mm/note-circuit-corollary.md`).
- Running as before: anti (impossibility theorems), lab.

### Lab note 4: the atlas [N; uses the exact rectangular formula; balance equations transcribed, not re-derived]
- At the ideal exponent (same as if ω were 2): n × n^k × n products for k ≤ 1/2 (n²); Zwick / unweighted directed
  APSP at n^{2.5}; fully sparse products m^{4/3} (output size m) and m^{7/6} (output √m), ideal for every output size
  ≤ input size.
- Not ideal: n × n^{0.6} × n at 2.0167; n × n^{0.75} × n at 2.0833; n × n^{1.5} × n at 2.667 (ideal 2.5); α = 1/2
  (ideal 1); sparse with larger outputs slightly off; formulas that use only the square exponent (triangle detection
  m^{1.385}, k-clique 9t/4, bounded-difference (min,+) 2.625, determinant/rank n^{2.25}) not re-optimised with
  rectangular blocks, so only upper bounds on the true derived exponents.
- Lead's caveat: the "ideal" rows need only the UPPER bounds (October algorithms). The "not ideal" rows need the new
  lower bound and the exact formula, which the paper itself does not state (only the Lean notes do).

### Lab note 5: thin-product decomposition closed without computation [R]
- If AB = Σ_{t≤s} F_t·G_t with F_t of size n×√n and G_t of size √n×n, for ANY functions F_t, G_t of the inputs, then
  rank(AB) ≤ s·√n pointwise. A random product over F₂ has rank n − O(1), so s ≥ √n, which splitting the inner index
  achieves trivially. Cost √n · n^{2+o(1)} = n^{2.5}. The idea agent's one "positive" experiment for the user's
  literal wish (T5) cannot pass for any preprocessing. [X]
- Positive routes tried so far for n²·polylog over F₂: word tricks, packing, thin products. All closed with reasons.
