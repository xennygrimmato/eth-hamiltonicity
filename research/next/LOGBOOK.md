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

### Lab note 6: matrix multiplication over F₂ as a twisted convolution (set-up verified) [N]
- M_n(F₂) ≅ F_{2^n}[x; Frobenius]/(xⁿ − 1): a matrix is a linearised polynomial Σ a_i z^{2^i}, and the product is
  c_k = Σ_{i+j≡k} a_i · b_j^{2^i}. Checked for n = 2…8 on random pairs.
- Lead's reading: WITHOUT the twist b_j ↦ b_j^{2^i} this is an ordinary cyclic convolution over F_{2^n}, which costs
  n²·polylog bit operations by FFT. So matrix multiplication over F₂ = convolution + an index-dependent Frobenius
  twist, and in a normal basis the twist is a cyclic shift of coordinates (free wiring). The whole gap between
  n²·polylog and n^{9/4} sits in that twist.
- Known fast skew-polynomial multiplication is algebraic and bounded by the same exponent. No non-algebraic use of
  "Frobenius is free" found. Open as an idea, not as a result.

### Anti, step 1: the paper's network bounds quoted verbatim (`research/mm/anti/notebook.md` §1) [K]
- "Prop. 2.3" is ω ≥ 9/4 over finite fields; the circuit embedding is one sentence in its proof, for the sorting
  circuit only. The general embedding of Boolean circuits into trivalent networks is ours to prove (elementary).
- Network wires carry bits; field values live only in vertex tables.
- σ in Theorem 2.2 is not effective: any σ < 1/2 under "no ports"; an unspecified smaller σ > 0 under "ports". Which
  case holds is open and depends only on the characteristic. So the hidden corollary is Ω(N(log N)^σ) for some σ > 0.
- Lemma 4.1's proof uses only the marginal destination law and lets tables vary with the permutation; the paper itself
  pins tag inputs to a uniform permutation. This is the precedent for pinning A to a permutation matrix.
- Lean: Theorem 2.2 / Lemma 4.1 not found among the formalised statements in the sparse clone. If the network bound is
  not in the Lean cone of `square_exponent`, how does the Lean proof get the lower bound? The note agent is checking
  the import cone; this is now the most informative open fact.

### Anti, step 2: Corollary A proved from the paper's Theorem 2.2 [R, given the paper; unreviewed]
- Lemma E (ours): a fan-in-2 Boolean circuit with N inputs, s gates, m outputs becomes a trivalent network for the
  graph of its function, of volume ≤ 16s + 4N + 4m, over every field; exactly one internal assignment contributes.
- Corollary A: every fan-in-2 Boolean circuit (any basis) for list distinctness on N = 2w·2^w bits has more than
  N(w^σ − 4)/16 − 1 gates = Ω(N(log N)^σ), σ > 0 ineffective. Direct-sum version for up to 2^w blocks. Also for
  unambiguous and parity-nondeterministic circuits. Upper bound O(N log N) by a sorting network.
- So the gap for this function is (log N)^σ ≤ size/N ≤ log N.

### Why-9/4 agent, Parts A and B [reading + own checks; unreviewed]
- A BETTER PICTURE (Part B): with x = qr, y = rp, z = pq the rectangular formula is ω = (p+q+r)²/4 (or
  largest × rest when one of p, q, r exceeds half): the complete graph on p+q+r vertices grouped into three teams.
  Six people, one shared bit per pair (15 bits): making this from one broadcast label costs exactly 9 bits = the max
  cut 3|3 (Zhou, arXiv:2610.34273, two-sided). Pair them into three teams: exactly 16×16 matrix multiplication
  (4 bits per team pair). Cost ≤ 9 (inherited), ≥ 8 (best cut respecting teams). ω = 9/4 ⇔ still 9; ω = 2 ⇔ 8.
  So 9/4 is 9 bits over 4 bits. The resistor formula is this in bad coordinates and does not generalise to 4 arms.
  Lead: this convinces me; it becomes the spine of the story. Caveat to handle: "coins/broadcast" must not be read
  as probability (that would give 15); the 9 is a counting fact about adding up "all-agree" patterns with cancellation.
- MECHANISM OF THE LOWER BOUND (Part A): a dichotomy on whether a tensor family's cheapest "site" moves with a
  parameter. (a) If it moves: rank ≥ n^{9/4} directly (unconditional Theorem 7.1). (b) If nothing moves: gadget tensors
  become a resource for sorting below n(log n)², hence a universal bulk discount on any small network, which iterated
  beats the list-distinctness floor. ω < 9/4 is used in one place: to exclude (a).
- Tied to 9/4? Not vacuous: (a) outputs 9/4 unconditionally; if ω ≤ 2.2 were proved the paper would be wrong. But both
  directions lean on the same 2026 algorithm family; the agent cannot certify the match is more than
  self-consistency. First place to send a referee.
- Credibility loads: Theorem 2.2's two cases rest on companion results (one on the VP ≠ VNP-type paper); the
  unadvertised superlinear circuit bound; refutes Strassen's conjecture.
- Checks: reproduces K₄ (asymptotic rank 16), polynomial multiplication exponent 1, Strassen/Bini/Schönhage identities,
  all known ranks, pre-2026 rectangular bounds. None could have failed. Falsifiable predictions exist (small
  Coppersmith–Winograd tensors, S₃ group algebra, border rank of T₁₆ ≥ 512) but none is laptop-scale.

### Anti: the missing hypothesis follows from Weak ETH → a dichotomy [R in progress, given the papers]
- OpenAI's integer-multiplication paper, Theorem 7.1 (verbatim per anti): if characteristic zero admits "ports", then
  3-SAT on v variables is decidable in 2^{O(v^{1−δ})}·poly. So under variable-count Weak ETH, characteristic zero has
  no ports — exactly the hypothesis (H2) the impossibility argument needed.
- DICHOTOMY: either 3-SAT has a 2^{O(v^{1−δ})} algorithm, or every Boolean circuit multiplying n×n matrices (over F₂,
  Boolean, or (min,+)) needs Ω(n²√log n) gates. Same for polynomial and integer multiplication at Ω(n√log n), and that
  version uses only printed statements (no reading of Lemma 4.1's proof), because there the number of destinations
  equals the number of wires.
- Matrices need Lemma 4.1's entropy step (n destinations for n² wires). To be written with every dependency listed.
- Note: the current ETH refutation (2^{n/(log n)^{1/2+o(1)}}) is compatible with Weak ETH. H12 sharpened accordingly.

### Note agent: the network lower bound IS in OpenAI's Lean, inside the cone of the 9/4 theorem [K by grep; not built]
- Import chain traced: square_exponent → … → BatchDescent.hard → `manyList_full (F) [Field F] [Finite F]`:
  ∃ η > 0, eventually in w, for all t ≤ 2^{w^{1+η}}: any bit network (tables of bit-arity ≤ 3) computing t-fold list
  distinctness has size > t · (2w·2^w) · w^η. Hypotheses: finite field only. No ports / no-ports split at top level.
  The Lean route is a "descent + resists" diagonal argument, not visibly the paper's Lemma 4.1 (which the Lean cone
  does not appear to use). 592 modules in the cone; grep finds no sorry/admit/axiom.
- So the hidden superlinear circuit bound rests on a Lean-formalised statement (as read by us, not built). OpenAI's
  Lean has the pieces of the circuit embedding (used for a sorting seed) but states no general circuit corollary.
- Context found: the multiple-unicast network coding conjecture was refuted in Oct 2026 (arXiv:2610.20079 and others),
  so the older conditional lower bounds built on it have a false premise.
- Lead's idea passed to anti: reduce list distinctness to matrix multiplication (radix passes = data-dependent 0/1
  matrix times a record matrix) to get the matrix lower bound from the Lean statement directly, without Weak ETH or
  Lemma 4.1. May lose too many log factors; to be worked out.

### Story written (`research/mm/story-nine-fourths.md`, three figures) [exposition; unreviewed]
- Built on the six-people / three-teams picture, re-framed honestly as "matching switches" with simple pieces that are
  added and subtracted (no coins, no probability). Strassen's 7 worked so one block can be checked by hand.
- 9 = links crossing the 3|3 split of six people; 8 = best split that keeps teams of two whole; 16×16 multiplication
  has 4 links per team pair; exponent 8/4 = 2 versus 9/4. Claim in one sentence: teaming up never saves the ninth bit.
- Says plainly that there is no simple picture for the lower bound; gives the dichotomy and the parcel-routing floor;
  boxes for "what this picture hides" and "why experts will be cautious". Six-tweet thread included.
- Lead checked: Strassen formulas correct; all three figures render; counts 9 and 8 visible in figure 2.
- Technical note extended: limits of the tripod picture (§13), the mechanism (§14), the team-size formula and
  predictions (§15).

### User guidance and requests (26 Nov)
- "Anthropic's proofs are much more reliable; but read both labs' papers." Weighting adopted: Anthropic's VP ≠ VNP and
  ETH results are the firmer base; OpenAI's 24 Nov family (ω = 9/4, Euclidean prices, network lower bound) is taken as
  given for exploration but flagged wherever a result of ours depends on it. Anthropic has made no claim about ω.
- Visual explanation via an image-generation API: prompts for six panels prepared (using our own accurate diagrams
  as references). Blocked: the provided key authenticates but the account has no credits (HTTP 402 on every model).
- Network coding: the conjecture refuted in Oct 2026 is the Li–Li multiple-unicast conjecture for undirected networks
  (arXiv:2610.20079; independently 2610.09367 and 2610.10108). Unrefereed.

### Anti: the impossibility theorems written (`research/mm/anti/notebook.md` §3) [R, given OpenAI's papers; unreviewed]
- THEOREM S (shifts): under variable-count Weak ETH, polynomial multiplication over F₂, integer multiplication, and
  cyclic shift by an input amount each need Ω(n√log n) fan-in-2 Boolean gates. Uses ONLY printed statements of
  OpenAI's integer-multiplication paper (Thm 7.1, Lemma 8.2, the §7.1 price bound). Ours: the circuit embedding, a
  pinning lemma, an XOR fold turning a·x^t into a rotation, averaging over shifts. Dichotomy form stated.
  Tight for F₂[x]: OpenAI's upper bound n(log n)^α for every α > 1/2, so the log-exponent of Boolean polynomial
  multiplication over F₂ would be exactly 1/2 under Weak ETH. By-product, unconditional given their upper bound:
  cyclic shift by a binary amount in O(n(log n)^{1/2+ε}) gates, beating the barrel shifter.
- THEOREM M (matrices): Ω(n²√log n) gates for products over F₂, Boolean, (min,+), integers; also unitriangular inverse,
  transitive closure, squaring. Two versions: M1 = Lemma 4.1 as printed + some prime without ports; M2 = Weak ETH +
  Lemma 4.1 read for characteristic 0 (anti checked its proof uses no finiteness). Needs the lemma's entropy step
  because there are n destinations for n² wires. Sanity: permutation × matrix has O(n² log n) circuits.
- Lead's reduction idea (distinctness → matrix multiplication, to use the Lean statement directly): KILLED [X]. One-hot
  permutation matrices are too wasteful an encoding (N² cells for the hard narrow-record instances), and permutation
  products realise too few routings, so radix pipelines need Ω(n/log n) products. Mixed reductions not excluded.
- Corollary A now rests on the Lean statement: s > N(w^η − 2)/4 − 1, every finite field, no hypotheses.
- Constants differ between anti (÷4, ÷16) and the note (÷3): different size measures; to reconcile before publishing.

### Note on the circuit corollary: draft complete (`research/mm/note-circuit-corollary.md` + checks file)
- Quotes cross-checked against the LaTeX; the Lean statement `manyList_full` quoted; import chain to
  `square_exponent` given; search of the whole release finds no statement of the circuit consequence.
- Our lemma: a fan-in-2 circuit of size s gives a trivalent network with ≤ 3s + N + 2 vertices (size ≤ 3s + 2N + 2 in
  the Lean's measure). Corollary: s > N(w^η − 2)/3 − 1 for list distinctness; direct-sum and mod-p counting versions.
- Agent's confidence: ~95% that the reading and derivation are right given the statements; ~90% that the release does
  not already state it. Main risk: Theorem 2.2 / the Lean build being wrong, which the note says outright.
- Lead read the draft in full: neutral, accurate to what we know, three good questions for experts (the sharpest: a
  linear-size ⊕-circuit for distinctness would refute Theorem 2.2). Ready for the user's decision on posting.

### Anti final report (`research/mm/anti/notebook.md`) [R given OpenAI's release; unreviewed]
- Headline dichotomy as logged above; log-exponent 1/2 from the routing lemmas. Theorem S (shifts) rests only on
  printed statements; Theorem M (matrices) also on reading Lemma 4.1 in characteristic 0 (anti checked its proof uses
  no finiteness). Covers F₂, Boolean, (min,+), b-bit integers, rectangular, batches, unitriangular inverse, transitive
  closure, squaring. The method is capped at O(n² log n): it bounds the sub-problem "permutation × matrix".
- Ports case not covered. Prior art: bounded-coefficient Ω(n² log n) (Raz), 3n² bilinear over F₂ (Shpilka), 5/2·n²
  rank (Bläser), conditional bounds via the (now refuted) network coding conjecture. No superlinear bound for general
  Boolean circuits was known.

### User: "focus on more important results" — lead's choice of focus: THE PORTS QUESTION
- One open question in OpenAI's release decides both things the user cares about most:
  PORTS in characteristic 0 ⇒ 3-SAT in 2^{O(v^{1−δ})} (their integer-multiplication paper, Thm 7.1);
  NO PORTS ⇒ tight lower bounds with log-exponent 1/2 (our Theorems S and M become unconditional given the release).
- "Ports" = expanders with respect to the nonpositively curved spaces realised by tensor prices. This looks parallel to
  Anthropic's "contracting hypothesis" (a Poincaré-type inequality for prices on Mat_μ(F₂)); our c1/b2/w1 work is
  about exactly which metrics are prices. H13 [C]: ports and contracting are two forms of one question, and our
  notes on which metrics are prices are the right tools.
- H14 [C]: if every spectral space has Izeki–Nayatani invariant bounded below 1 (flats, trees, buildings, products),
  ordinary expanders are ports and the fast 3-SAT algorithm follows. Conversely Weak ETH forces a "wild" spectral
  space in characteristic 0.
- Actions: Fable strategist on `research/ports/ideas-ports.md` (statements, dictionary with Anthropic's paper and our
  notes, metric-geometry literature, ranked attacks). Lab told to wrap up the AND-count line and report.
- Parked: the public note (drafted, awaiting the user's decision); the story (done; image generation blocked on
  credits).

### Lab final report (`research/mm/lab/notebook.md`) [N, exact where stated]
- Every tested route to n²·polylog over F₂ closed with a reason: word tricks (factor w·log n only); packing (bilinear in
  disguise); thin-product decompositions (rank); twisted convolution (algebraic). No small case shows a gap between
  functional and bilinear/quadratic cost.
- 2×2 over F₂: quadratic-Boolean model exactly 7. Unrestricted model (gate reuse, higher-degree intermediates):
  5 refuted in 0.06 s by a new exact subspace search (`mc_span.c`, calibrated against Morse's published cases);
  6: 3 of 72 symmetry orbits refuted, 69 left (~1.8 h on 3 cores). Status 6 ≤ MC ≤ 7. No proof object.
- ⟨1,2,2⟩: exactly 4 = rank. ⟨1,2,3⟩: 5 or 6. Tiny-map sweep partial; no map with a gap.
- Atlas table recorded earlier. Lab's intuition: a non-algebraic win would need something non-linear AND recursive;
  no hint of one; the 5% prior for a 2×2 gap looks generous.
- Leftover cheap job: finish the 69 orbits (settles one instance of the Boyar–Find question). To be run unattended.

### Ports strategist, interim 1 (`research/ports/ideas-ports.md` §0, Part 1) [K quoted + D; unreviewed]
- Ports (OpenAI's Euclidean-geometry paper, Def. 11.1): one family of bounded-degree regular graphs and one constant γ
  with E_pairs d² ≤ γ·E_edges d² for every placement into every spectral space of the characteristic. Depends only on
  the characteristic.
- Finite certificate (their HC paper, Thm 4.2): ONE graph whose Poincaré constant over all spectral spaces is below
  c·log n/log(d+1) already gives ports.
- "Ports ⇒ 3-SAT" chain: Poincaré inequality → exact rerouting identities (Strassen duality) → iterated compression →
  contraction of any size-s network in 2^{s^{1−η}} → sparsified 3-SAT. δ not tracked in the papers.
- Lean (read, not built): ports defined; "ports in characteristic 0 ⇒ power-saving 3-SAT" formalised. Which
  characteristics have ports: stated nowhere.
- KEY (H13 confirmed in one direction): Anthropic's CONTRACTING hypothesis IMPLIES ports (their Thm F.6 gives a
  Poincaré constant far below the certificate threshold). Hence contracting ⇒ 3-SAT in 2^{v^{1−δ}} (char 0), and Weak
  ETH ⇒ contracting fails in characteristic 0.
- Lead's follow-up: with c1's reduction (contracting ⇔ √rank on Mat_μ(F₂) is not a price for some μ ≥ 3) this gives a
  finite test for a faster 3-SAT algorithm; asked for exact statements and review status.
- H15 [C]: "the metric √rank on 3×3 binary matrices is not a tensor price over ℚ" ⇒ 3-SAT in 2^{v^{1−δ}}.

### Ports strategist, interim 2 (`research/ports/ideas-ports.md` §2) [D from both labs' texts; with a referee now]
- THEOREM A: contracting over k ⇒ ports in the characteristic of k. Anthropic's Thm F.6 gives a Poincaré constant
  C₀(h−1) on an (h−1)-regular graph of order 2^{h(h−1)/2}; OpenAI's certificate threshold is ≥ h(h−1)/(20000(log₂h+4));
  the first is below the second for large h. Strategist read the certificate's proof line by line. Independent check:
  OpenAI's own Prop. 11.2 proof shows "no uniform gap ⇒ the Grassmann metric √(dim(U+V) − m) is spectral", and
  Mat_μ(F₂) is the big cell of that Grassmannian: the same inequality as contracting.
- THEOREM B (finite test): if √rank on Mat_μ(F₂) for some μ ≥ 2 (16 or 512 points), or the five-point set M5, is NOT a
  price over ℚ, then 3-SAT is in 2^{O(v^{1−δ})}. Under Weak ETH these building-type metrics ARE prices over ℚ.
  Caveat: the object is finite, the decision is not; only the algorithm side has a machine-checkable certificate
  (one cheaper cover).
- Cells: {contracting, no ports} impossible. OpenAI's unconditional permanent bound ≈ Anthropic's contracting-case
  bound. The ports algorithm is a piece family obeying all our flat floors; it wins by restoring bounded degree at
  constant cost so the √ trade iterates log-many times. Our floors do not bear on ports.
- No LP/SDP over known necessary conditions can exclude M5 or ρ₃ (they sit in a Euclidean building). Only a new
  tensor identity can.
- RE-BASING SKETCH: Anthropic's Thm J.4 alone may give, under contracting, fast 3-SAT with no OpenAI input.
- Lead's actions: executor "rebase" (Opus) to prove or refute contracting ⇒ fast 3-SAT from Anthropic's paper alone,
  with the corollary "Weak ETH ⇒ flat hypothesis in characteristic 0, independent of OpenAI"; referee (Opus) on
  Theorems A and B, attacking the class containment, the growing degree, and any tension with Anthropic's
  contracting-case lower bound.
- H16 [C]: contracting is false over ℚ (i.e. Weak ETH-type hardness wins), and the provable content is the
  implication "contracting ⇒ fast 3-SAT" on Anthropic's footing.

### Ports strategist, interim 3: metric geometry (`research/ports/ideas-ports.md` §3) [K + one new derivation, unreviewed]
- Literature: Kondo (first CAT(0) space with Izeki–Nayatani invariant 1); Mendel–Naor 2015 (classical expansion is
  neither necessary nor sufficient against Hadamard spaces; their zig-zag with Cesàro averages is what OpenAI's
  certificate implements); Izeki–Nayatani inequality; δ = 0 for trees and Hilbert space, ≤ 0.4122 for the SL₃(ℚ₂)
  building, ≤ 1/2 for cube complexes; nothing uniform in the rank.
- New (elementary, unreviewed): any CAT(0) space containing √rank on Mat_μ(F₂) has Izeki–Nayatani invariant
  ≥ 1 − 4/(μ−1). So buildings of GL_n(F₂((t))) have invariant → 1 as n grows, and the rank-one Cayley graph on
  Mat_μ(F₂) has nonlinear Poincaré constant ≈ μ ≈ 2 log n/log d against them — exactly the growth OpenAI's theorem
  says every graph has when there are no ports.
- H14 resolved: the Izeki–Nayatani route to ports is not independent. It works only if some √rank metric is not a
  price, and then Theorem A already gives ports. If all are prices, the spectral class has invariant 1.
- Missing for "contracting ⇔ ports": Q-build — is there a bounded-degree family that expands against the buildings of
  GL_n(F₂((t))) for all n at once? Not decidable from classical expansion. Anthropic's graphs sit at Θ(√log n) in
  both worlds and do not separate the cases.

### Ports strategist, interim 4: which spaces are spectral (`research/ports/ideas-ports.md` §4) [K + D, unreviewed]
- Known spectral: cuts, stars, trees, Hilbert spaces (OpenAI, non-constructive), their convex hulls and limits.
  Products not known. The 9/4 paper's tripod is a star metric; its non-flatness is in the label price.
- {Hilbert spaces, ℝ-trees} is closed under everything known, contains every known example, and HAS ports. So "no
  ports" needs a genuinely new spectral point; the current axioms cannot prove it.
- Weak ETH forces, in characteristic 0, prices realising buildings of unbounded rank (the √rank / Grassmann metrics).
  Neither lab constructs such a space.
- Reformulation: by Strassen duality, the best rate for converting EPR pairs on a supply graph into EPR pairs on demand
  pairs is the multicommodity-flow dual LP restricted to spectral metrics. Since prices are CAT(0), tensor coding
  strictly beats routing; on the Okamura–Seymour instance K_{2,3} the rate is > 3/4 and ≤ 1. Exact value open.
  Ports = full log n gain over routing on expanders; no ports = at most √ of that.
- Lead's idea passed on (H17 [C], speculative): the wild spectral point in characteristic 0 comes from ARITHMETIC —
  2-adic lattices as sites, elementary-divisor invariants as costs, realising the building of GL_n(ℚ₂). Characteristic
  p has no such valuation on its tensors, which would explain why Weak ETH constrains characteristic 0 only and would
  predict ports in characteristic p. Asked which axiom (monotonicity under all linear maps is the dangerous one) kills
  or permits it.
- State of evidence: everything KNOWN is on the "ports exist" side; Weak ETH says the truth in characteristic 0 is on
  the other side. One of: a new spectral point (then lower bounds), or no such point (then fast 3-SAT).

### Ports strategist, interim 5: attack routes (`research/ports/ideas-ports.md` §5) [plan]
- Route 0 (already running): referee Theorems A/B; re-base "contracting ⇒ fast 3-SAT" on Anthropic's Thm J.4.
- Route A (ports via rigidity): only live form is one new tensor identity showing some √rank metric or M5 is not a
  price. The LP/SDP I proposed is predetermined (those metrics satisfy every CAT(0)-valid constraint): do not run.
- Route B (no ports via a wild price): all construction steps missing. Best idea B1 (5%): do OpenAI's VALUED prices
  (9/4 paper §5–6) induce building metrics on lattice classes? If yes, contracting is false unconditionally.
  (Same direction as the lead's arithmetic idea H17.)
- Route C (characteristic p): nothing excludes ports in characteristic 2; consequence would be mod-2 counting of
  networks in 2^{s^{1−η}}; whether that contradicts a randomised Weak ETH needs an isolation lemma check (C1, 50%).
- Route D: no intermediate algorithm from weaker expansion (the certificate is a dichotomy with no middle regime).
  Proposed D1 (25%): an "engine gap" theorem — any rewriting algorithm of the engine's type beating log-exponent 1/2
  implies ports, hence 2^{n^{1−δ}}.
- Route E: E3 compute the Okamura–Seymour tensor rate ("tensor coding always attains the cut bound" would imply
  contracting, hence fast 3-SAT).

### Rebase executor, task 1 (Anthropic's contracting case read precisely) [K quoted; D]
- Anthropic's §2.4: "Steps 1 to 4 prove, with no circuit and no permanent, that every computation of a nondeterministic
  program with weighted runs can be cut into short pieces, which a fast program lists." So the first half of the
  contracting case is UNCONDITIONAL on circuits: F.6, G.2, H.2, J.2–J.4, K.4–K.6. Only K.3 and K.7 use the assumed
  permanent circuit.
- Thm J.4 (under contracting): some program of size ≤ v^H cuts (τ, s) into (v^H, v^{H−32}) with ≤ τv²/v^H pieces in
  ≤ τ/v^24 steps. Model: nondeterministic programs on binary trees; the Lean statement is existential.
- GAP found in the strategist's sketch: used as a black box, J.4's step bounds make run-enumeration worse than brute
  force for 3-SAT. Proposed fix from the printed proof of J.3: the cutting program makes only ~τ/v^235 guesses, the
  rest of its steps being deterministic. With that, the executor says the theorem goes through; details pending.
- Open points for the lead to watch: existential (non-uniform?) statement; the guess-count reading is from a proof,
  not a stated theorem.

## 26 Nov (late): ports round 1 closes; three results on the table

**Strategist final (ideas-ports.md, Parts 1–6 + addendum).** Odds [C]: no ports in char 0 93%; contracting true 2%.
- My H17 (2-adic lattices as the wild spectral point) is **dead in its naive form [X]**: spectral points are invariant
  under invertible local maps, GL_n(ℚ) is transitive on lattices, so no lattice-relative invariant exists. No asymmetry
  between characteristics follows either (EG Lemma 2.3; F_p((t)) is valued). A family-based form survives as B1′ (3–5%).
- K_{2,3} threshold: the five-point set W₅ in tripod × ℝ (h = ℓ/3) has supply/demand ratio √(9/10) ≈ 0.9487 < 1.
  A tensor protocol on K_{2,3} with rate > 0.9487 would show W₅ is not spectral; with an unproved "hull lemma" that
  would give contracting. Flow gives ≥ 3/4, cuts give ≤ 1.

**Rebase final (rebase/notebook.md): Theorem R [R, unreviewed].** Contracting over a field of characteristic 0 ⇒
3-SAT in 2^{O(n^{1−δ})}, δ < 187/(5H+187), using Anthropic §§F–J + sparsification + Nullstellensatz only.
- The strategist's black-box use of J.4 fails (step count ≥ s·v²⁴ ≥ brute force). Repair = **Lemma 1**: the composed
  lister makes ≤ τ/v²³⁵ guesses. Lemma 1 is read from the printed proof of J.3; it is in no statement and not in Lean.
- Corollary: Weak ETH ⇒ ¬contracting ⇒ flat (thm_alt) over every char-0 field, independent of OpenAI's EG paper.
- Weak points: Lemma 1; uniformity (Lean thm_cut is ∃ G only); paper is not human-checked.

**Referee interim on Theorems A/B: Theorem A correct with small fixes.** Containment OA-spectral ⊆ AN-prices goes
the right way; F.6's C₀ is independent of h; HC 4.2 is a single-graph certificate so growing degree is harmless.
Lean caveat: `exists_logarithmic_placement` has an extra `scalar` hypothesis (satisfiable; lines are prices).
Correction to B(iii): Weak ETH gives AN-prices, not Strassen spectral points.

**Hypotheses.**
- H17 [X] (see above).
- H18 [C]: Lemma 1 survives adversarial review. If it does, "Anthropic's contracting case contradicts Weak ETH" is a
  theorem resting on one lab's Lean-backed statements plus one proof-reading.
- H19 [C]: no K_{2,3} tensor protocol beats 0.9487 (Weak ETH + hull lemma predicts this).

**Working protocol change (user).** Fast parallel compiled code (Rust/C++ with Python bindings), reusable; Lean
skeletons for each hypothesis to see where it breaks. Lean is not installed in this container; elan/Mathlib cache
hosts are reachable. 4 cores, 15 GB; the 6-gate search is reniced to 19.

**Launching.** (1) `tools/tensorlab` Rust+PyO3 library and the E3 K_{2,3} computation. (2) Lean skeletons: Theorem A
quantifier line-up, Theorem R arithmetic, W₅. (3) Adversarial referee on Lemma 1 / Theorem R.

## 26 Nov (late, 2): two hard subproblems assigned to stronger thinkers (user request)

- **Hull lemma / is W₅ spectral** (high effort): does failure of contracting force a tripod × segment configuration
  with W₅'s distances inside a price space? Is tripod × ℝ spectral outright? Output: `research/ports/hull/notes.md`.
  This is what would make the K_{2,3} computation decisive; without it a protocol above 0.9487 only refutes product
  closure.
- **C1 + D1** (medium effort): (C1) does ports/contracting in characteristic p refute a randomised Weak ETH, via
  isolation with variable overhead small enough for the power-saving regime? (D1) an "engine gap" theorem: engine-type
  algorithms run at n/√log n or jump to n^{1−δ}. Output: `research/ports/c1d1/notes.md`.
- Lean toolchain is up (Lean 4.36.0 + prebuilt Mathlib) in `research/ports/lean`; scaffold committed (6c5e38d).
- Running in total: library/E3 executor, Lean executor, referee on Theorem R, referee on Theorems A/B, the two above,
  and the 6-gate search (niced).

## 26 Nov (late, 3): referee final on Theorems A/B — Theorem A stands [V]

Report: `research/ports/review-theoremAB.md`. The referee could not break "contracting over k ⇒ ports in char k" (85%).
- Fixes to carry into any write-up: (1) Lean `exists_logarithmic_placement` has the extra hypothesis `scalar`
  (satisfiable: finite subsets of a line are prices, AN C.3); (2) with the Lean constant the arithmetic condition is
  h/(log₂h + 4) > 40000·C₀ after loop padding; (3) Theorem B(iii): Weak ETH gives Anthropic prices, not Strassen
  spectral points; (4) "one cheaper cover" → "a family of covers with exponential saving"; (5) the cell "ports
  algorithm is a piece family obeying flat floors" is heuristic; (6) bound comparison differs by log log in the
  exponent and in circuit model.
- Numerical check [N]: spectral gap of the walk on U_h, h = 3..7: gap·(h−1) = 0.586, 0.291, 0.200, 0.156, 0.132,
  consistent with gap ~ 1/h as F.6 needs for real-valued placements. A 1/h² gap would have refuted contracting.
- LP/SDP no-go holds for metric-only CAT(0)-valid inequalities; two classes are NOT covered: the crossing inequality
  B.3 (validity in all CAT(0) spaces only conjectured) and constraints on non-wire tensors. → possible later probe.
- Weakest link is imported: AN F.6, OA HC 4.2, and for 3-SAT the OA chain HC 13.1 → IM 7.1 — which is exactly what
  Theorem R (rebase) would remove, if Lemma 1 survives its own referee.

## 26 Nov (late, 4): referee interim on Theorem R — Lemma 1 holds after small fixes

- Paper text supports the guess count: J.3 proof l.3130–3143 ("All of this is deterministic except for the guesses";
  plan ≤ τΛ/v²⁵⁶ steps; cut packets kΛ·τΛ/v³⁰⁰). Exponents 256 and 300 are the paper's (Table 2); 235/236 are ours.
- The referee went to Anthropic's Lean: the one-cut program is `dealProg` = `dealF`; its only guess constructs are
  `pickB` and `bitsB`; the s-dependent phases (`wordB`, `partStep`) contain no guess; `compC` adds none.
- Robust: even the coarse bound from the J.3 *statement* gives ≈ τ/v¹⁹¹, i.e. ρ = H/(H+143). Exponents
  ρ = H/(H+187), δ < 187/(5H+187) recomputed and confirmed.
- Fixes: a power of Λ; "every run" → prune the run tree at g guesses and t steps.
- **New weakest point: uniformity.** Lean takes the plan structure from `thm_tree` (Nonempty) and pieces from
  `prop_pieces`; their specs include sum identities that cannot be checked by an algorithm. Unless those witnesses are
  explicit constructions, Theorem R gives 3-SAT with poly-size advice (contradicting non-uniform Weak ETH), not a
  uniform algorithm.
- H18 status: Lemma 1 [V, interim]. H20 [C]: the witnesses of `thm_tree`/`prop_pieces` are constructible in poly(v)
  time (needed for the uniform statement).
- Action: asked the Lean executor to scope a machine-checked guess count against Anthropic's Lean (define guess count
  on their program syntax; additivity under `compC`; bound for `dealProg`).

## 26 Nov (late, 5): referee final on Theorem R — survives with fixes [V]; uniformity open

Report: `research/ports/review-theoremR.md`.
- **Proved and reviewed (non-uniform form):** contracting over a char-0 field ⇒ 3-SAT ∈ DTIME(2^{n^{1−δ}})/poly,
  δ < 187/(5H+187) ≈ 0.121 at H = 272. Contradicts non-uniform Weak ETH. Uses Anthropic §§F–J only.
- **Uniform form: gap, plausible.** `thm_onecut` builds G from witnesses `TT` (from `thm_tree`, via `prop_pieces`) and
  `pc` that Lean only shows to exist, and whose specs include uncheckable sum identities. Paper prose says the
  constructions are explicit (l.2781–2785, l.3135–3136). Not verified in the Lean proofs. → audit launched.
- Guess count recomputed against Lean: ≤ 2rΛ³(4Λ²)^r·τ/v²³⁶ ≤ τ/v²³⁵. Any total τ/v^{48+g} gives ρ = H/(H+g).
- 3-SAT encoding, char 0, Nullstellensatz: correct. ψ need not be injective; constant table is non-explicit but
  n-independent.
- No clash with K.6. Contracting is used only through the laws (G.2).
- Stronger consequence than the notebook states: subexponential *counting* for nondeterministic linear time.
- Corollary 2 (engine optimality under Weak ETH) NOT checked; depends on review-link and the flat-floor theorem.
- Recipe for a Lean check: `guesses` field on the run record of `Ev`; guess-aware `DoesG`; `CutDG` = `CutD` + guess
  bound threaded through `thm_onecut_program` (g = nS·X + mm·bd·ub), `thm_cut_compose` (g₁ + P₁·g₂), `thm_cut`.

**State of the headline.** "Anthropic's contracting case contradicts (non-uniform) Weak ETH" now has two independent
routes, each refereed once: Theorem A (via OpenAI HC 4.2 + IM 7.1) and Theorem R (Anthropic only).
**Launching:** uniformity audit of `thm_tree`/`prop_pieces`; first draft of the note.

## 26 Nov (late, 6): C1 interim — isolation is free in the power-saving regime [D]

From the char-p agent (`research/ports/c1d1/notes.md`):
- Claim [D]: ports or contracting in characteristic p ⇒ one-sided-error randomised 3-SAT in 2^{O(v^{1−δ})}, same δ.
- Mechanism: both mod-p counters accept more than 3-CNF (HC 13.1: any closed bit network; Theorem R: any weighted
  nondeterministic program), so a hash circuit attaches parsimoniously. Toeplitz hash h(x) = T_a x + b is pairwise
  independent and is polynomial multiplication over F₂: circuit size O(v log v loglog v), below the v^{1+4α} leaf
  volume sparsification already creates. Success 3/(16v) per trial (ordinary Valiant–Vazirani).
- CIKP as a black box is fatal here (2^{Θ(εn)} repetitions). The power-saving regime tolerates v ↦ v^{1+o(1)} but needs
  success ≥ 2^{−v^{1−δ}}.
- Derandomisation: free non-uniformly (Adleman); uniformly under Impagliazzo–Wigderson; no unconditional route.
- Effect on anti's Theorem M (F₂): would follow from one hypothesis, randomised one-sided Weak ETH.
- Caveat it found: the sunflower sparsification printed in IM §7 is not disjoint, so "#3-SAT mod p" (and exact
  counting in char 0) needs count-preserving sparsification. Decision does not.
- **My check, sent back:** the Theorem R encoding has sum 2^e·#SAT; in characteristic 2 this vanishes for e ≥ 1, so
  the Anthropic route may fail exactly at p = 2 — the case Theorem M needs. Asked for the source of 2^e and the same
  check on the OpenAI route. H21 [C]: the encoding can be made exactly parsimonious (e = 0).
- 6-gate search: shard 0 of 3 done, no circuit in its orbits.

## 26 Nov (late, 7): hull lemma claimed TRUE [D] — K_{2,3} becomes a real test

From the hull agent (`research/ports/hull/notes.md`), re-derived twice by it, not yet refereed:
- N5 := {0, I, e11, e21+e22, e12+e22} ⊂ Mat_2(F₂) under √rank is √(graph metric of K_{2,3}):
  |0 I| = |t_i t_j| = √2, |0 t_i| = |I t_i| = 1. **I checked the ten ranks by hand: correct.**
- Each quadrilateral (0, t_i, I, t_j) has sides 1 and diagonals √2 = equality in the CAT(0) quadrilateral inequality,
  hence a flat square (AN C.4(b),(f) + filling as in D.2 Step 8). The three squares share the diagonal [0, I]; their
  union is the diamond {|x|+|σ| ≤ 1/√2} ⊂ tripod × ℝ, which contains W₅.
- So: ¬contracting over k ⇒ ρ₃ a price ⇒ ρ₂ ⊇ N5 a price ⇒ W₅ a price ⇒ **f*(K_{2,3}; k) ≤ 3/√10 ≈ 0.94868.**
- Falsifiable form: an asymptotic K_{2,3} protocol over ℚ with rate > 3/√10 ⇒ contracting over ℚ ⇒ ports ⇒ fast 3-SAT.
- My reading of the soft spot: "W₅ ⊂ convex hull of N5 in the price space ⇒ W₅ is a price" (do interior points of
  the price space pull back to prices? the agent cites AN Prop. C.3). To be refereed.
- H19 sharpened: under Weak ETH (even non-uniform, via Theorem R), no K_{2,3} tensor protocol over ℚ beats 3/√10.
  Open: is f* = 3/√10 exactly under ¬contracting (needs R ≥ 3/√10 on all five-point CAT(0) sets)?
- Sent to the library executor: certify f_Q; scan small supply/demand instances on 5 parties for the largest gap
  between the N5/W₅ bound and the cut bound; protocol search on those. Sent to the Lean executor: rank table, the
  equality case, the tripod × ℝ model, and an explicit hypothesis structure for the rigidity step.

## 26 Nov (late, 8): Theorem A skeleton in Lean [L, conditional]; f_Q computed [N]

**Lean (`research/ports/lean/PortsLean/ThmA.lean`, `ThmAArith.lean`).** `theorem_A : Contracting → PortZero`,
sorry-free; I rebuilt it myself (18256 jobs, success) and read the statement. Hypotheses are explicit arguments, no
axioms: F6Statement (copy of AN `thm_poincare`, quantifier order ∃u ∃C₀ ∀l ∀price), LogPlacementStatement (copy of OA
`exists_logarithmic_placement` incl. `large`, `scalar`, threshold s/(10000(e+3))), ContainStatement (OA target ⇒ AN
price, one direction), LineStatement (line placements are AN prices; used only for `scalar`), |U_h| = 2^{h(h−1)/2},
generators are involutions. What this does and does not show: the *deduction* and the arithmetic are machine-checked;
the four imported statements are copies, not the labs' own Lean objects.
- Break found: the referee's condition h/(log₂h+4) > 40000·C₀ is not sufficient for the Lean form; OA's `large`
  (10000(e+3) ≤ h(h−1)/2) is separate (counterexample C₀ = 0). Proved sufficient: 40000(C₀+1)(e+3) ≤ h.
- Field bookkeeping sits inside ContainStatement (needs K = ℚ or ℚ̄); undischarged.

**E3 (`tools/tensorlab`, `research/ports/e3/notebook.md`).** Library builds (Rust + rayon; metric/opt/models; 8 tests).
- f_Q = 0.9446059737… (triangles + 30 Reshetnyak quadruple inequalities), root of 58x³−14x²−29x−9; **below 3/√10**.
  The minimiser is argued not CAT(0) (double equality ⇒ parallelogram, fails). So four-point inequalities alone do
  not prove R ≥ 3/√10; the rigidity case or five-point conditions are needed. Sent to the hull agent.
- Triangles only: 0.75 (flow). Triangles + Euler: 0.893.
- Products of two trees: minimum exactly 3/√10 at W₅. Single tree or Euclidean: exactly 1 (strategist's 1.078 wrong).
- [R] No exact single-shot K_{2,3} restriction at equal bond dimension over any field. Border/asymptotic open.
- H22 [C]: min of R over five-point CAT(0) sets = 3/√10, so f*(K_{2,3}) = 3/√10 exactly under ¬contracting…
  (only if W₅-type sets are the extremal prices; upper bound side is the hull lemma).

## 26 Nov (late, 9): uniformity audit interim — Theorem R looks uniform [D]

- `prop_pieces` (Paper/Pieces.lean:765–801) and `thm_tree` → `exists_thinTrees` (Paper/Tree.lean:1468–1512) build
  their witnesses as structure literals; the uncheckable `value` fields are theorems for any spec-satisfying inputs.
- Remaining choices are finite with decidable specs (subgroup chain, host maps, route words, embedding, bijection,
  move order, bounded law choice, SLP conversion): poly(v) directly; blind search ≤ 2^{O(v^{2Cp+1})} ≪ 2^{v^H}.
- Nothing depends on the input z (CutD quantifies ∀z after G).
- Non-explicit only: n-independent constants (laws, universal automaton, finitely many group evaluators).
- Caveat: "any spec-satisfying choice works" is a parametricity argument at the meta level, not a Lean theorem.
- H20: supported [D]. Tentative statement of Theorem R: uniform algorithm with a non-explicit constant table.

## 26 Nov (late, 10): the p = 2 normalisation hole was real, and is fixed [D]

- Rebase's encoding guesses all 2^{⌈log n⌉} leaves of the balanced tree; the padding leaves are free guesses, giving
  sum = 2^e·#SAT. **As written, rebase Cor. 1′ fails in characteristic 2** unless n is a power of two (fine for odd p).
- Fix for all p: the checker rejects unless every padding leaf is 0. Then runs ↔ assignments bijectively, e = 0.
  No other factor found (Def. J.1 is an exact identity; ½ appears only in the flat case, Prop. E.1). The agent did not
  re-read §§G–J line by line for hidden divisions.
- OpenAI route: no normalisation factor (IM 7.1 contracts to exactly #SAT; HC 13.1 uses prime-field constants).
- Theorem M over F₂ depends on the OpenAI route at p = 2 (HC 13.1 + isolation) + randomised Weak ETH; Theorem R is
  not on its dependency list. H21: confirmed [D].

## 26 Nov (late, 11): c1d1 final — C1 positive [D]; D1 gives a gap theorem with a corrected threshold [D]

Notes: `research/ports/c1d1/notes.md`. Unrefereed, nothing run.
- **C1-OA [D]:** ports in characteristic p ⇒ randomised one-sided 3-SAT in 2^{O(v^{1−δ})}, same δ as IM 7.1.
  **C1-AN [D]:** same from contracting in characteristic p (with the padding fix), δ < 187/(5H+187).
- **Lemma C4 [R, classical]:** power-saving #3-SAT mod p, or Unique-3-SAT, ⇒ randomised power-saving 3-SAT.
  So rWETH ⇒ UWETH ⇒ ⊕_pWETH for all p.
- Theorems S: WETH (unchanged). **Theorem M1 over F₂: one hypothesis now suffices — rWETH** (or nuWETH, UWETH,
  ⊕₂WETH with disjoint sparsification, or WETH + Impagliazzo–Wigderson). Depends on MM Lemma 4.1 + HC 13.1 at p = 2.
- **Theorem D [D] (engine gap):** a (p, β, 𝒞)-tower engine with certified e_L ≤ (log K_L)^{−α′}, α′ > ½·log_β p,
  forces ¬flat ⇒ contracting ⇒ power-saving 3-SAT. For Anthropic's engine type the threshold is α′ > 1/2.
- Dead [X]: (i) the sharp form "2^{o(n/√log n)} ⇒ ¬flat": sub-constant deficits can accumulate up to (log n)^{o(1)};
  Anthropic's flat hypothesis has no rate. (ii) "beating 1/2 forces ¬flat" for all engines: with three non-product
  merges the floor is 1/√3 and the threshold is ½·log₂3 ≈ 0.79; engines in (1/2, 0.79] are not excluded.
  (iii) network-rewriting via MM Lemma 4.1 (one topology per family, not per term). (iv) CIKP as a black box.
- If EG 1.2 holds, Theorem D's hypothesis is vacuous; what remains is the Anthropic-only dichotomy.
- My earlier leaning ("D1 would be the most quotable consequence") is downgraded: true but with a grey zone and
  vacuous under OpenAI's theorem. C1 is the real gain.
- Queue: referee on C1.4/S4 (launched); Lean for Toeplitz + isolation lemmas (launched); S3 (Δ₃ placements in
  Mat_μ(F₂) vs 3√3, compiled) after the K_{2,3} protocol search; S5 (Majdoddin Thm 4.13 with floor 1/√2) later.

## 26 Nov (late, 12): uniformity audit final; hull proof written; five-point CAT(0) test

- **Uniformity audit final (`research/ports/review-uniformity.md`): Theorem R is uniform** [V by audit, one reader,
  nothing built]. Constant table is n-independent and non-explicit. Contracting enters only via `exists_laws`.
  A Lean-checked uniform form needs a mechanical refactoring (choices → parameters); watch for proofs that unfold a
  specific enumeration.
- **Hull lemma: complete proof in `research/ports/hull/notes.md` §1.** Inputs: AN Def. A.4, Prop. C.3 (price space),
  C.4(a),(f). The step "ρ₃ is a price when contracting fails" is D.2 Steps 1–7 / Remark D.3, not a named Lean theorem.
  Referee launched.
- The hull agent confirmed the executor's no-single-shot theorem.
- **f_CAT5:** five points embed in a CAT(0) space iff all weighted box inequalities hold (Toyoda 2020; quoted from
  memory, executor to confirm). Coarse grid gives 0.94679 < 3/√10. If the true minimum stays below, there is a
  five-point CAT(0) set better than W₅ — but the hull lemma only certifies W₅-type points as prices, so H22 would be
  false while the bound 3/√10 under ¬contracting stands. Executor asked to compute it by cutting planes.
- Launched: referee on C1 (isolation in characteristic p); Lean project `research/ports/lean-c1` for Toeplitz
  pairwise independence and the isolation bound.

## 26 Nov (late, 13): Theorem R arithmetic in Lean [L, conditional]

`research/ports/lean/PortsLean/ThmR.lean`: 10 theorems, sorry-free, standard axioms. Nothing breaks.
- Cleaner parameters: v := ⌈τ^{1/(H+187)}⌉, τ′ := v^{H+235}; all J.4 constraints hold exactly. τ′ ≤ v^{2H} needs only
  H ≥ 235.
- Cost 2^g(t + P·2^{v^H}·v^H) ≤ 2^{(2H+241)v^H}, exponent ≤ (2H+241)·2^H·τ^{H/(H+187)}. Piece brute force and run
  enumeration are balanced (both 2^{v^H}); 187 = 235 − 48.
- δ: α* = 187/(5H+187), balance identity proved; for each δ < α* an admissible α exists (needs H > 112.2).
- Unstated side conditions found: v₀ must grow with C_cut ((lg v)^{2C_cut} ≤ v); α < 1/4.
- Lemma 1 arithmetic proved from per-cut bounds. The per-cut guess count itself is still read from the J.3 proof.
- Cost model assumed the guess bound on every run; the referee's pruning fix needs it on accepting runs only. Asked
  the executor to restate accordingly.

## 26 Nov (late, 14): referee interim on C1 — items 1–4 correct

- HC 13.1 as printed has no 3-CNF hypothesis; needs a closed bit network, volume = tensors + wires, degree ≤ s^{1/20}.
  XOR/AND/equality/pin tables allowed; fan-out via equality trees keeps degree ≤ 3. Wording fix: in characteristic p
  the constants lie in a fixed finite extension F_{p^r} (prime field for prime-field choices); same count mod p.
- Parsimony: with a fixed, x ↦ T_a x is linear, so the multiplication circuit is an XOR-only straight-line program of
  size O(n log n loglog n), no divisions, every wire a function of x.
- Toeplitz pairwise independence for every k ≥ 1 (indices 0..n+k−2); VV ≥ 3/16 on q ∈ [1/4, 1/2]; 16v rounds give
  success ≥ 1 − e^{−3}, one-sided.
- Leaves are tested separately; sound and complete.
- Pending: item 5 (hidden divisions in AN §§G–J), 6 (C4), 7 (Theorem M1 dependency list), 8 (Theorem D).
