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

## 26 Nov (late, 15): pruned evaluator in Lean; Anthropic's run semantics; build scoping

- `PortsLean/PrunedTree.lean` [L]: pruning at g guesses / t steps gives ≤ 2^g leaves by construction; pruned sum =
  true sum if every accepting leaf has depth ≤ g and cost ≤ t. Arithmetic of Theorem R unchanged.
- Anthropic's Lean semantics (read, not built): `Ev θ F x l` lists only accepting runs and its derivability encodes
  "all runs halt"; `Does` and `CutD` bound cost on accepting runs only. So a guess-aware `DoesG` should bound guesses
  on accepting runs — matching the pruned evaluator.
- vp-vnp: 324 files / 72.9k lines, Lean v4.33.1, Mathlib pinned. Guess-relevant closure: 61 files / 13.6k lines.
  `Paper.Cuts` closure: 261 files / 60.7k lines. 46 GB free.
- Decision: build the 61-file closure and define the guess count against the real definitions (EvG / DoesG,
  guess-freeness of deterministic combinators, costs of pickB and bitsB, additivity under compC), then estimate the
  rest. Top priority for the Lean executor.

## 26 Nov (late, 16): three reviews in; K_{2,3} rate pinned numerically; note draft; one permission block

**Hull lemma: passed review [V]** (`research/ports/review-hull.md`). For any field k: ¬contracting over k ⇒ N5 a price
⇒ every finite subset of the diamond (incl. W₅) a price ⇒ every restriction protocol on K_{2,3} over k has rate
≤ 3/√10 (border protocols included over infinite fields). "ρ₃ is a price when contracting fails" is the Lean theorem
`thm_alt_rank_price` (Paper/Alternative.lean:706). Edits requested: add the missing rate-bound section; any char-0
field, not just ℚ.

**f_CAT5 = 3/√10 [N]** (tensorlab; Toyoda's theorem confirmed from arXiv:1907.09074v2, Thm 1.3). 1000/1000 multistarts;
minimiser W₅; active constraints = three box inequalities at t = s = 1/2 with multiplier 2√10; no triangle active.
Products of 2 and 3 trees and the Heawood cone agree. The f_Q minimiser violates box inequalities.
- So, numerically: **f*(K_{2,3}) ≥ 3/√10 unconditionally** (Strassen duality + prices are CAT(0)), and
  **= 3/√10 whenever contracting fails**. A global proof is missing. My three-line idea (CN at the midpoint of u₁u₂ +
  triangle through it) is refuted numerically (ratio ≈ 0.81) [X]. Hull agent is on the proof.
- [R] demand (2,2,2,1) at bond dimension 2 is impossible even as a border restriction.

**C1: passed review [V]** (`research/ports/review-c1.md`). C1-OA, Lemma C4, Cor. C5 hold; C1-AN holds with the
padding fix, conditional on Theorem R. No hidden divisions in AN §§G–J (App. M: only ½ in Prop. E.1). Corrections:
"same formula for δ" (η depends on the characteristic); Theorem M1's list = rWETH (or nuWETH/UWETH/⊕₂WETH with disjoint
branching), HC 13.1, IM §7, MM Lemma 4.1, our Lemmas E and P — and the B₂-circuit bounds need only *some* prime
without ports; p = 2 only for part (a). The earlier Theorem R review wrongly passed Cor. 1′ (#3-SAT mod p). Theorem D's
averaging is right (needs E_C ≥ 1 stated); the win-win it relies on was not re-checked here.

**Note draft** `research/ports/note-contracting-eth.md` (≈7,300 words): Theorems R (uniform by audit), A, B,
Corollary 1, dependency tables. I rebuilt all four Lean files (18260 jobs, success; no sorry). Needs a v2 with the
refereed C1 and hull results.

**Permission block.** The Lean executor fetched the Mathlib cache for Anthropic's pin but its `lake build` of
Anthropic's sources was denied by the permission classifier, twice. Not retried. Fallback in progress: guess count on
a faithful copied fragment of NS1/Machine.lean. Finding: `Gives`/`Does` do not imply guess-freeness, so every guess
bound must be re-derived syntax-directedly. → ask the user whether to permit the real build.

## 26 Nov (late, 17): Toeplitz pairwise independence in Lean [L]

`research/ports/lean-c1/IsoLean/Toeplitz.lean`: `hash_pairwise_F2` — for x ≠ y the number of (a, b) with h(x) = s and
h(y) = t, times 4^k, equals 2^{(n+k−1)+k}; `hash_pairwise_F2'` gives the count as 2^{n−1}. Indexing as in the notes,
(T_a)_{j,i} = a_{n−1+j−i}, a ∈ F^{n+k−1}. Surjectivity of a ↦ T_a z for z ≠ 0 holds over any field. No sorry (per the
executor; I have not rebuilt this project). The notes' statement is correct. Next: the isolation bound.

## 26 Nov (late, 18): isolation bound in Lean [L]

`research/ports/lean-c1/IsoLean/Isolation.lean` (per the executor; not rebuilt by me): for a finite family with uniform
marginals and pairwise independence at the target y₀, M²·#U ≥ |H|·(NM − N² + N); if M ≤ 4N ≤ 3M then 16·#U ≥ 3|H|.
So the constant is 3/16 on the wider window [M/4, 3M/4]; the notes' window [M/4, M/2] is a corollary.
Break found: the marginal condition does not follow from the pairwise one when |S| = 1 and must be assumed separately
(Toeplitz with a uniform offset b has it). Notes' Lemma C3 is correct as stated. Next: composition with Toeplitz.

## 26 Nov (late, 19): guess count on a verbatim fragment of Anthropic's machine model [L, fragment]

`research/ports/lean/PortsLean/ANFragment/`: `Machine.lean` = Anthropic's NS1/Machine.lean copied verbatim (typechecks
unchanged on our Mathlib); `Defs.lean` = verbatim definitions of app, listT, foldB, foldF, appF, pickB, pickF, stepC,
compC; `Guess.lean` = our overlay. I rebuilt the project (18266 jobs, success, no sorry) and read the statements.
- `EvG` mirrors `Ev` with a guess count; `EvG.toEv` projects to `Ev` (so EvG lists are the accepting runs).
- `GB θ F x g`: every accepting run uses ≤ g guesses. Combinator lemmas: quote/id/fail 0, guess 1, sequencing adds,
  ite = guard + max of branches. `pickB_guesses`: ≤ number of options. `foldB/foldF/appF` lemmas.
- `compC_guesses`: guesses(compC G G′) ≤ g + Σ_pieces g′ — the additive form Lemma 1 uses.
- Not done: `bitsB` (needs ~150 more lines of copied definitions); the lifting Ev → ∃ EvG.
- Finding: `Gives`/`Does` do not imply guess-freeness (e.g. `ite guess id fail`); every bound must be syntax-directed.
- Estimate for the rest, both needing the real build: dealProg ≤ s-free part of dealB ≈ 1.5–3k lines, 2–5 focused
  days; threading through thm_cut ≈ 1–2 weeks (needs the 261-file closure). Blocked on build permission (user asked).
- Limitation to state wherever this is cited: it is a copy, checked against a different Mathlib version than theirs.

## 26 Nov (late, 20): isolation composed with the Toeplitz hash in Lean [L]

`research/ports/lean-c1/IsoLean/Compose.lean` (per the executor; not rebuilt by me): `exists_good_k` — for n ≥ 1 and
nonempty S ⊆ F₂ⁿ some k ∈ [2, n+1] isolates with probability ≥ 3/16; `avg_succProb` — with k uniform, ≥ 3/(16n).
Break found: the notes' range {2..n+1} is empty at n = 0; assume n ≥ 1 (harmless). Next: Tseitin parsimony.
So the probabilistic core of C1 (hash + isolation + choice of k) is machine-checked; the reduction itself
(attaching the circuit to the counting network) is not.

## 26 Nov (late, 21): 6-gate search finished — MC(2×2 over F₂) = 7 [N]

All 72 first-gate orbits are refuted for k = 6 (3 earlier, 69 in the background run; every log line "none"). So no
XOR/AND circuit with 6 AND gates computes the 2×2 matrix product over F₂; with Strassen's 7 the unrestricted
multiplicative complexity is exactly 7. Trust base: `research/mm/lab/mc_span.c`, the orbit computation, the pruning
rules, a 128-bit memo hash. No proof object. Novelty not checked (Winograd's 7 is for a different model: non-scalar
multiplications in arithmetic straight-line programs; here intermediate polynomials may have any degree and x² = x).
Possible follow-ups, low priority against the ports work: an independent re-implementation in tensorlab with a
different pruning order; a literature check; a SAT/DRAT certificate.

## 26 Nov (late, 22): isolation Lean project complete and rebuilt by me [L]

`research/ports/lean-c1/IsoLean/` (592 lines; `lake build` 18260 jobs, success; no sorry/axiom/native_decide — I
rebuilt it and read the main statements):
- `Toeplitz.lean`: `toeplitz_surjective` (any field), `hash_uniform`, `hash_pairwise`, `hash_pairwise_F2'`
  (count = 2^{n−1}).
- `Isolation.lean`: `isolation_exact`, `isolation` (M ≤ 4N ≤ 3M ⇒ 16·#U ≥ 3|H|), `isolation_notes_window`.
- `Compose.lean`: `exists_good_k`, `avg_succProb` (≥ 3/(16n) for n ≥ 1).
- `Tseitin.lean`: `Circuit.consistentEquiv` (consistent wire assignments ≃ inputs), `card_tseitin`,
  `gateClauses_iff` (axiom-free).
Discrepancies with the notes: marginal uniformity must be assumed separately; n ≥ 1.
Machine-checked now: the probabilistic and combinatorial core of C1 / Lemma C4. Not machine-checked: the link to
either lab's counting theorem, and the multiplication-circuit size bound.

## 26 Nov (late, 23): towards a proof that the five-point minimum is 3/√10

From the hull agent (interim 3):
- My route (i) and its projection variant are refuted [X] (tree-like sets; e.g. u₁ = v₁, u₂ = v₂, v₃ the apex).
- **Book reduction [R, unreviewed]:** for five points in a CAT(0) space, glue the three Euclidean comparison triangles
  (u₁,u₂,v_i) along [u₁,u₂]. By AN C.4(a) and the triangle inequality the v–v distances only increase, the others
  are unchanged, so R(Y) ≥ R(book). The minimum is attained on books of three flat triangles (7 parameters). Uses
  only C.4(a), so it holds for all AN prices. [N] minimum over books = 3/√10 at W₅.
- **Calibration [D]:** bounding each |u_k v_i| below by its projection on a chosen unit vector makes all length terms
  cancel and leaves one scalar inequality in three angles:
  (I) Σ_{i<j} cos((θ_i−θ_j)/2)·√(1+9 sin²((θ_i+θ_j)/2)) ≥ 3 on [−π/2, π/2]³; equivalently, for z_i on the half-ellipse
  x² + y²/10 = 1, x ≥ 0: |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. Equality only at θ = 0 (= W₅). [N] on a 121³ grid.
  An end-of-spine variant (geodesic through an end of the spine) remains to be checked.
- **Dependency chain settled [D]:** f* = min over Strassen's spectrum (exact, Strassen 1988); each such point is an AN
  spectral point, so the lower bound needs Strassen + AN C.4(a) + the five-point inequality — nothing from OpenAI.
  The upper bound holds for every AN price. So the larger AN class costs nothing here.
- H22 status: reduced to inequality (I) + the end-of-spine variant.
- Launched: `tools/ivcert`, a Rust interval branch-and-bound certifier with a certified-convexity test near equality
  points and an independent certificate checker; first jobs are (I) and the variant. Sent the hull agent a
  reformulation: with φ_k the half-sums, (I) reads Σ_k cos(φ_i − φ_j)·g(φ_k) ≥ 3, g(φ) = √(1+9 sin²φ).

**If (I) is proved: Theorem K (unconditional).** f*(K_{2,3}; k) ≥ 3/√10 over every field. And with the hull lemma:
f*(K_{2,3}; k) = 3/√10 whenever contracting fails over k; in characteristic 0, f* > 3/√10 ⇒ fast 3-SAT.

## 26 Nov (late, 24): W₅ and hull checks in Lean [L]

`research/ports/lean/PortsLean/W5.lean`, `Hull.lean` (per the executor, sorry-free; not yet rebuilt by me):
- W₅: √(9/10)(6ℓ+2h) ≤ 6√(ℓ²+h²) (it is 4(ℓ−3h)² ≥ 0), equality iff h = ℓ/3; all 125 triangle inequalities; not in
  the cut cone (Σ_S d − Σ_T d ≥ 0 on all 32 cut metrics, violated by W₅).
- Flow bound 3Σ_T d ≤ 4Σ_S d for every metric (rate ≥ 3/4); cut {v₁} gives ratio 1.
- Hull: the ten ranks of N5 over ZMod 2 by explicit factorisations and determinants; equality in the quadrilateral
  inequality for each (0, t_i, I, t_j); the tripod × ℝ model realises N5 and contains W₅(ℓ, ℓ/3) for ℓ ≤ 1/√2;
  glue lemma: ρ₂ a price ⇒ any five diamond points are a price, given a `HullHyps` structure.
- What Lean cannot see: Lemma H itself (solid squares from C.4(f), uniqueness, gluing) — Mathlib has no CAT(0) theory.
- Break found and fixed: Lemma H must assume a complete space with midpoints (CN), not only the quadrilateral
  inequality — N5 as a bare five-point space satisfies the inequality and contains no diamond, so the weaker
  skeleton was false/vacuous. The informal proof uses the price space (complete CAT(0)), so it is unaffected.
- Confirmed: "points of the price space are prices" is not a gap; `prop_space` says the whole metric is a price.

## 26 Nov (late, 25): first Lean executor finished; whole project rebuilt by me [L]

`research/ports/lean/` — 10 files, 2089 lines, `lake build` 18272 jobs success, no sorry/axiom/native_decide (my
rebuild). Contents: ThmA(+Arith) (contracting ⇒ ports, conditional on copied statements); ThmR + PrunedTree (exponent
bookkeeping and pruned evaluator); ANFragment (guess count on a verbatim copy of Anthropic's machine file;
additivity under composition); W5, Hull (five-point geometry, rank table, glue from explicit hypotheses);
NineFourths (the algebra behind 9/4: AM–HM, perimeter ≤ 9/4, (xy+yz+zx)²/(4xyz) = (p+q+r)²/4 after substitution, and
that S²/(4xyz) solves the rectangular formula). Executor's notes: `research/ports/lean/NOTES.md`.
Numbers worth keeping: OpenAI's `large` alone needs h ≥ 491; both conditions need h ≥ 480 300 at C₀ = 1.
Open Lean items: `bitsB`, dealProg, thm_cut threading (need Anthropic's build — permission pending with the user);
Lemma H (needs CAT(0) theory absent from Mathlib); the field identification inside `ContainStatement`.

## 26 Nov (late, 26): inequality (I) certified by interval arithmetic [N, rigorous]

`tools/ivcert` (Rust + rayon): own outward-rounded intervals (TwoSum/fma error sign), Taylor sin/cos with Lagrange
remainder and a rigorous π enclosure, no libm; leaf tests = natural extension, mean-value form, Taylor-2, certified
convexity (interval Hessian PD via Gershgorin after congruence or interval Cholesky); deterministic certificate and a
separate checker `ivcheck`. 14 tests (true claims, false claims refused with exact counterexamples, tampered
certificates rejected).
- (I): F(θ) ≥ 3 on [−π/2, π/2]³. 1014 leaves without symmetry, 401 with; < 1 s. The box [−π/32, π/32]³ closes by
  convexity with F(0) = 3, ∇F(0) = 0 exact; elsewhere bound ≥ 3.00072. **I built the tool and ran `ivcheck` on both
  certificates myself: VERIFIED.** Certificates: `tools/ivcert/certificates/hull3{,-nosym}.cert`.
- Sanity: constant 2 in place of 9 is refuted (F(π/4, −π/4, 0) = 2.808); constant 8 does not close (equality at the
  corner (π/2, π/2, −π/2)).
- Trust base: the Rust interval code and the checker. Not Lean.
- Remaining for the lower bound: the end-of-spine variant (spec not yet written by the hull agent), and a referee
  pass on the book reduction and calibration.

## 26 Nov (late, 27): hull interim 4 — one six-variable inequality covers all cases; P2 assessed negative

- Notes rewritten (`research/ports/hull/notes.md`): §3.1 book reduction, §3.2 calibration (Prop. 3.2 [R]), §3.3 spec,
  §4 P2. Referee edits applied.
- **(CL\*)**: for ψ ∈ [−π/2, π/2]⁶, Φ(ψ) = Σ_i cos μ_i √(1+9 sin²δ_i) − 3 + (3/2)Σ_pairs |sin ψ_ij + sin ψ_ji| ≥ 0.
  Prop. 3.2: in every book Σ_S − κΣ_T ≥ (D/√10)Φ(ψ). (I) is the slice ψ_ji = −ψ_ij. No realisability constraint used.
  Equality at ψ = 0 (non-smooth) and at six cube corners (collinear configurations; true ratio 1 there).
  [N] 3000 local searches + 2·10⁶ random points: no violation; chain checked on 20 000 random books.
  No analytic reduction of (CL\*) to (I); a six-variable certificate is needed → sent to the ivcert executor with a
  plan for the non-smooth point (sign-split; Φ ≥ F(θ) − 3 + (3/2 − L)Σ|ε| with certified L) and the corners.
- **P2 negative [R/D]:** tripod × ℝ is a price space over k iff N5 is a price iff W₅ is. Given the five-point theorem,
  "tripod × ℝ is spectral" ⇔ "no asymptotic K_{2,3} protocol beats 3/√10" — a tensor lower bound, not something a
  known functional gives: every explicit spectral point has an ℓ₁ wire metric (R ≥ 1), geometric means are not
  subadditive, one-point extension gives only minimal distance vectors. So N5 a price is known only from
  ¬contracting; the only refutation is a protocol above 3/√10, which certifies contracting.
- Launched: referee on the book reduction, calibration and the chain to tensors (asked specifically whether CAT(0)
  is asserted for the price d or its square root — the place I think an error could hide).

## 26 Nov (late, 28): hull agent final; next hard subproblem assigned

**Hull agent final** (`research/ports/hull/notes.md`, §0–§7).
- [R, refereed] Lemma H; H1; H2 (¬contracting ⇒ N5, W₅ prices); H3 (N5 a price ⇔ every finite subset of
  tripod × ℝ a price); rate bound f* ≤ R(d) for every AN price d.
- [R, being refereed] book reduction; calibration Prop. 3.2. [N, rigorous] (I). [N] (CL\*) — certificate pending.
- [D] W₅ a price ⇒ N5 a price (needs flat-rhombus rigidity); a second forced tripod (tripod × tripod × segment);
  (m-pod) × segment for m ≤ 2^r+1 via Mat₂(F_{2^r}); K_{2,m} gives R = 2m/√(m²(m−1)²+4). [C] uniqueness of W₅.
- Falsifiable statement: under Weak ETH, over every characteristic-0 field, no asymptotic restriction protocol on
  K_{2,3} (exact or border) has rate above 3/√10, and rates up to it are attained.
- Dead [X]: single hub; projection relaxation; unweighted quadruple inequalities; ℓ₂-product symmetrisation;
  per-quadrilateral inequality; an "ellipse lemma" and concavity of the book perimeter; chord and quadratic
  templates for (I); reaching W₅ from matrix vertices alone (no collinear triples).
- Its advice: aim the protocol search below 0.9487 first (existence guaranteed asymptotically). Forwarded.

**New hard subproblem (high effort): is the middle cell {¬contracting, ports} empty?** I.e. ports ⇒ contracting, so
the two labs' hypotheses coincide. Reformulation I gave: for every bounded-degree graph find a placement into
Mat_μ(F₂) (or the price space it generates) with bounded-rank gradient and unbounded typical rank distance.
My seed observations [C]: diagonal (Hamming/ℓ₁/Hilbert) placements can never work on expanders; Cayley graphs of
groups generated by transvections work via f(g) = π(g); a general graph is a Schreier graph of a free group but
equivariance ties the representation to the permutation module, where generators are not low-rank. Class caveat:
¬contracting gives Anthropic prices, ports is over OpenAI's spectral spaces → work with "AN-ports".
H23 [C]: AN-ports ⇔ contracting. Output: `research/ports/middle/notes.md`.

## 26 Nov (late, 29): protocol search interim — nothing above 3/4 at reachable sizes; the test is weaker than hoped

From the tensorlab executor (`research/ports/e3/notebook.md`). Library: 15 unit + 2 integration tests, Python wheel
builds; ALS over ℝ/ℂ, Levenberg–Marquardt, border ALS, F₂ SAT encoder, cut prechecks.
- [R] Single-shot rate 1 is impossible for every bond dimension and field; the same argument kills every instance
  whose v-cuts are all tight with d_uu ≥ 2. [R] Bond 2 with all three v–v wires of dimension 2 is impossible even as
  a border restriction over ℂ (border rank ≤ 4 < 7).
- Numerics (relative residual): 2 → (2,2,2,2): floor √(5/8); 3 → (2,2,2,2) (rate 0.63): 5.7·10⁻³ with growing norms,
  border-like, unverified; **4 → (3,3,3,3) (rate 0.792, the positive control): 0.64, no sign of a protocol.**
- Border ALS as implemented is unreliable (reaches 10⁻² on a provably impossible case); only the dense check counts.
- Instance scan (9.8M supply/demand patterns on 5 parties): N5 is ℓ₁-embeddable, so no instance on these five
  parties can refute "N5 is a price" — hub parties are needed. For W₅ the largest gap is K_{2,3} itself (1.054).
- Size limit of the dense code: wire dimension ≤ 6. The smallest single-shot uniform rate above 3/√10 is 10 → 9.
**Assessment.** The search cannot currently reach rates above 0.9487, and it has not found even the protocols above
3/4 that must exist asymptotically. So a null result here says nothing about contracting. The K_{2,3} statement is
valuable as a theorem and a prediction; as an experiment it needs either structured constructions (from the crossing
identity) or a contraction scheme that avoids the dense environment. H19 remains untested.

## 26 Nov (late, 30): referee interim on the five-point theorem — items 1, 2, 4 pass

- Book reduction: fine. C.4(a) (l.1667–1669) is a statement inside a CAT(0) space; the notes pass to a price space via
  C.3 first; only the triangle inequality in that space is then used, so no book-geometry claim is needed.
- Calibration Prop. 3.2: re-derived line by line, every identity checks; 200k random books (incl. degenerate ones),
  no violation; W₅ gives equality.
- **No normalisation mismatch** (the point I worried about): the price is d_φ itself, with φ(⟨q⟩_uv) = q^{d_φ}
  (l.1069–1074, Def. A.4); CN is stated for the price with squared prices (l.417, l.1446). Strassen spectral points
  are AN spectral points. Every field is covered.
- Minor: the infimum of R over Strassen's spectrum may not be attained (not closed under scaling); affects only an
  "iff" in notes §4.2, not f* ≥ 3/√10.
- So the lower bound now rests on (CL\*) alone. Certificate and the referee's own violation search still running.

## 26 Nov (late, 31): (CL\*) certified on the full cube — the five-point theorem is computer-assisted [N, rigorous]

From the ivcert executor; **I re-ran `tools/ivcert/run_proofs.sh` and every certificate passes `ivcheck`**; I also
read `src/problems/clstar.rs` and checked the covering argument and the corner lemma by hand.
- Substitution σ = sin ψ makes (CL\*) algebraic on the exact box [−1,1]⁶:
  Φ(σ) = ½Σ_i √((c_ij+c_ik)² + 10(σ_ij−σ_ik)²) − 3 + (3/2)Σ_pairs|σ_ij+σ_ji|, c = √(1−σ²). No trig, no π.
  (Identity checked: cos²μ(1+9 sin²δ) = ¼[(c_ij+c_ik)² + 10(σ_ij−σ_ik)²].)
- Three pieces cover the cube:
  1. central cube |σ|∞ ≤ 1/2: coordinates a = (σ_ij−σ_ji)/2, e = (σ_ij+σ_ji)/2; eight orthant problems `clnear`,
     smooth, closed at the equality point 0 by a "gain test" (a-block Hessian PD, linear gain in e); ~10k leaves each.
  2. six corner regions {sσ_jk ≥ 15/16, sσ_kj ≥ 15/16}: analytic lemma, Φ ≥ ½(√d₁+√d₂) − (3/2)(d₁+d₂) ≥ 0 for
     d ≤ 1/16 (needs d ≤ 1/9). Checked by hand.
  3. the rest: `clstar`, 92k leaves with symmetry (S₃ × ±1), 529k without; both verify.
  The checker re-tests that every excluded leaf lies in piece 1 or 2.
- Total ≈ 35 s on 4 cores. Refutes the constant 2 in place of 9 with exact counterexamples.
- Certificates (13 MB) are regenerated by the script, not committed; sha256 printed by it.
- Trust base: the Rust interval/AD code and checker; the corner lemma; the substitution. Not Lean.

**Theorem K [computer-assisted; referee interim positive on the reduction and calibration].**
For every field k: f*(K_{2,3}; k) ≥ 3/√10. If contracting fails over k, f*(K_{2,3}; k) = 3/√10. Over a field of
characteristic 0, a protocol of rate > 3/√10 implies contracting, hence 3-SAT in 2^{O(n^{1−δ})}.
H22: established modulo the trust base above and the referee's final report.
Launching: a short separate note on Theorem K; v2 of the contracting/Weak ETH note.

## 26 Nov (late, 32): five-point theorem passes review [V]; independent checker launched

Referee final (`research/ports/review-fivepoint.md`): no gap, fatal or repairable. Book reduction, Prop. 3.2 (re-derived;
200k random books, min slack +1.5·10⁻⁵), equality cases, chain to tensors (price = d_φ itself; every field; AN Thm A.6
gives the duality without Strassen), certificate glue (substitution exact; covering complete; corner lemma right;
symmetry pruning sound; referee re-ran `ivcheck` on all ten (CL\*) certificates).
Weakest points, in the referee's order: (1) `ivcheck` shares the Rust encoding, interval library and leaf tests with
the prover; (2) the corner lemma and the covering sit outside the checker — write them into the notes verbatim;
(3) "min" over Strassen's spectrum should be "inf" (not closed under F ↦ F^a); (4) cosmetic.
Referee's own numerics on (CL\*): 2·10⁷ random points, 800 local searches, 2 DE runs — no negative value; zeros only at
the origin and the six corners.
→ Launched `tools/ivcheck2`: an independent second checker in a different arithmetic stack (Arb via python-flint or
MPFI), forbidden from reading ivcert's arithmetic; verifies coverage from the box list, re-proves every leaf, and
handles the equality point by its own argument.
Theorem K status: [V] by one referee + interval certificate; trust base as listed in the review.

## 26 Nov (late, 33): note on Theorem K written

`research/ports/note-k23-rate.md` (≈7,800 words): statement, Strassen duality for this instance, upper bound (hull
lemma), lower bound (book reduction, full calibration, (CL\*) with the covering argument and corner lemma written
out), consequences, small exact facts, status table, open problems. All referee fixes applied.
Writer's own checks: `ivcheck` on all 12 certificates; an independent Python test of Prop. 3.2 on 20 000 books (the
subgradient choice at hubs on the spine matters — stated in the note); Hessian Q = (3/4)Id + (5/4)J by hand.
Choices it made that I accept: item 1 uses thm_cn packaged as Prop. C.3 and then C.4(a) (not C.4(a) alone); item 3
split by uniform vs non-uniform Weak ETH; border protocols claimed only for approximation degree 2^{o(n)}; "inf" over
Strassen's spectrum, "min" over AN prices; protocol search scope stated as supply dimension ≤ 4 (the notebook has no
logs at 5–6, contrary to what I told it).
Inconsistencies it found in our sources, to tidy: hull notes status rows still call (CL\*) numerical; Lemma H's
condition; "min"/"some point" wording; the e3 notebook mentions runs "still in progress" that are not listed;
`HullHyps.prop_space` in Hull.lean adds `QuadIneq` to Anthropic's conclusion (harmless, follows from C.4(b)).
I edited one sentence that could read as a literature claim ("earlier known" → "an earlier step of this project").
Novelty against the literature on entanglement/tensor network coding has NOT been checked.

## 26 Nov (late, 34): main note v2 written

`research/ports/note-contracting-eth.md` v2 (≈8,000 words, "Changes in v2" at the end).
- New §5 on characteristic p (C1-OA, C1-AN with the padding fix, Lemma C4, Cor. C5, hypotheses table); new
  Corollary 1′ (under rWETH or nuWETH no characteristic has ports and contracting fails over every field) — composed
  from refereed steps, not refereed as a statement.
- Lean status rewritten for both projects; exact coverage of lean-c1 stated.
- §3.6 = final uniformity audit. One paragraph each for K_{2,3} and Theorem M1 with the corrected dependency list.
- I corrected the K_{2,3} paragraph: my brief had said "independent checker"; the checker shares code with the prover.
Inconsistencies the writer found, to keep in mind:
- `ThmR.lean` checks Λ² per cut while the referee's count is Λ³ (follows by Λ ↦ Λ^{3/2}; stated in the note).
- **480 300 is where OpenAI's two conditions first hold together at C₀ = 1, checked directly — not where our sufficient
  condition 40000(C₀+1)(e+3) ≤ h holds (that needs much larger h).** My earlier summary conflated the two.
- `ThmR.lean`'s header still cites H ≥ 272 where 235 and 113 suffice.
- The earlier Theorem R review listed a J.3 hypothesis (4 lg τ′ ≤ (lg v)²) as a check for R(a); it is internal to
  J.4's proof. Replaced by J.4's own condition.
- The writer could not see `review-fivepoint.md` (it was written while the writer worked); I checked it exists and
  fixed the paragraph by hand.
Weakened in v2: J.3 paraphrased not quoted in full; exact #3-SAT in characteristic 0 via disjoint sparsification is an
unrefereed combination; the UWETH variant rests on the referee accepting it in the M1 list.

## 26 Nov (late, 35): tensorlab executor final; second checker warm-up verifies

**tensorlab final** (`tools/tensorlab`, `research/ports/e3/notebook.md`). Reusable pieces: constraint families with an
exact box oracle; multistart + KKT polish; tree-product and graph-cone model searches; generic-wire ALS/LM; cut
tables; F₂ SAT encoder; Python wheel. 15 unit + 2 integration tests.
- Protocol runs (single-shot): 2 → 2 floor √(5/8); 4 → 3 residual 0.644 (ℝ), 0.640 (ℂ); 5 → 4 residual 0.806;
  3 → (2,2,2,2) border-like, unverified. Non-uniform demand vectors beyond routing: residual ≥ 0.47.
  Not tried: several supply copies, bond ≥ 6, a structured crossing-identity ansatz.
- f_Q stays [N] (Gröbner certificate did not finish).
- Note updated to state the actual scope (single-shot, uniform dimension 2–5).
**ivcheck2 warm-up:** the three-angle inequality is verified independently with Arb (python-flint 0.9.0), own interval
layer and gradients, no ivcert code: coverage structural + exact-rational volume; 344 leaves by natural extension,
654 after extra bisection, 16 inside its own convexity region [−1/8,1/8]³ (Sylvester minors). Six-variable runs
started. It also corrected my garbled description of the equality corners (vertex i both −s, other four +s).
**Next hard subproblem (medium effort):** an explicit protocol on K_{2,3} beating routing — existence is now a
theorem, a construction is not known; it would be the positive control for any search above 3/√10.

## 26 Nov (late, 36): (CL\*) verified by an independent second checker [N, rigorous ×2]

`tools/ivcheck2` (Arb via python-flint 0.9.0, own endpoint-interval layer, nothing from ivcert), per its executor:
- `clstar` no-symmetry certificate: 528 970 leaves; coverage structural + exact volume; 94 excluded leaves all inside
  the excluded regions by exact comparison (64 central, 30 corner); 520 956 by natural extension, 6 852 by mean-value
  form, 1 068 after extra bisection (max 5 levels); 21 s on 4 cores.
- All eight `clnear` certificates verified (about 2 000–2 400 leaves each needed extra bisection, max 7 levels).
- Origin by its own lemma on [−1/8,1/8]⁶ in (a,e): g(a) = V(a,0) has g(0) = 3, is even, interval Hessian PD (Sylvester,
  minor ≥ 1.76); sup|∂V/∂e_k| ≤ 2.063 < 3; so Φ ≥ (g − 3) + Σ(3 − L_k)|e_k| ≥ 0.
- Mutation test (Φ − 0.001 with the lemma off) fails 898 leaves, as it should.
- No discrepancy with the first checker. Corner-face confirmation and README pending; I will re-run it myself when
  it is final, then update the two notes (they still say "second checker in progress").

## 26 Nov (late, 37): second checker final; I re-ran both checkers on regenerated certificates

- `tools/ivcheck2` final (README, `run_all.sh`). I regenerated all certificates with the current prover code
  (`tools/ivcert/run_proofs.sh`, exit 0; sha256 unchanged from the first run) and ran `tools/ivcheck2/run_all.sh`:
  **OVERALL: VERIFIED** for the three-angle certificate, the eight `clnear` certificates and the no-symmetry `clstar`
  certificate (528 970 leaves: 520 956 natural extension, 6 852 mean-value, 1 068 after extra bisection; 94 excluded:
  64 central, 30 corner). Twelve corner faces proved. Corner lemma h(d) ≥ 0 on [0, 1/16].
- Both notes updated: the K_{2,3} note now describes the second checker and what the two implementations still share
  (box lists, problem statement, hand steps); the main note's pointer paragraph says "verified by two checkers".
- Remaining trust items for Theorem K: Anthropic's thm_cn / C.3 / C.4(a) (their Lean, not built by us); the hand
  steps (substitution, covering, corner lemma — referee-checked, corner lemma also re-derived by the second
  checker's author); the book reduction and calibration (one referee + two independent numerical tests).

## 26 Nov (late, 38): middle cell interim 1 — a spectral threshold; my H23 looks false by this route

From the middle-cell agent (`research/ports/middle/notes.md`, being written):
- **Kernel lemma [R]:** K(a,b) = 2^{−rank(a−b)} is positive semidefinite on Mat_μ(F₂) (it is Pr_x[(a−b)x = 0]). Hence for
  every regular graph with second eigenvalue λ and every placement f: E_edges 2^{−rk} ≤ λ + (1−λ)·E_pairs 2^{−rk}.
  So a spreading placement with edge rank ≤ r needs r ≥ log₂(1/λ): good expanders resist low-rank-gradient
  placements. Sharp: Cay(Mat_μ, rank ≤ r) has λ ≈ 2^{−r}. (I checked the PSD claim: the kernel is an average of
  indicators of {ax = bx}.)
- **Explicit expanders that are not ports if contracting fails [R]:** Cay(SL₃(F₂[x]/(p)), elementary generators),
  property (T) quotients, 12-regular; placement g ↦ g·W₀ in a Grassmannian gives ratio ≥ (3/16)·log₂ n, the maximal
  order. Grassmann metrics are pull-backs of scaled ρ_μ. Numerics on SL₂(F_{2^k}), k ≤ 6: ratio 3.0 … 10.5.
- **Direct form [R]:** a graph with Poincaré constant γ against AN prices and a placement with mean edge rank e and a
  fraction π of full-rank pairs with γe < πμ gives contracting at (μ, s² = γe/π), without D.2.
- **Reformulation:** [¬contracting ∧ AN-ports] ⇒ (GE): some bounded-degree family satisfies the rank-Poincaré
  inequality for all placements into all Mat_μ(F₂). So ¬(GE) ⇒ (AN-ports ⇔ contracting).
- **Agent's belief: (GE) is TRUE** (random regular graphs; evidence: the threshold lemma, a dimension count, small-set
  profile) — so the metrics ρ_μ alone will not empty the middle cell. Not proved beyond a low-energy regime.
- Class caveat stands: the literal cell also contains "ρ_μ is an AN price but not Strassen-spectral".
H23 [C → doubtful]: AN-ports ⇔ contracting is not reachable through ρ_μ if (GE) holds. New question H24 [C]: (GE) —
random regular graphs are expanders against the rank metric on all Mat_μ(F₂). Itself a clean metric-geometry
statement (expanders against buildings of unbounded rank).

## 26 Nov (late, 39): an explicit protocol family at rate 6/(4+√10) ≈ 0.8377 > 3/4 [D]

From the protocol agent (`research/ports/protocol/notes.md`, being written); unrefereed.
- **Construction.** Split the u₁u₂ demand into three equal parts, pair each with one wire v_iv_j, apply Anthropic's
  crossing identity (Prop. B.2) to each pair with log-dimensions (1/3, 1): the pair is a sum of Θ+1 terms Ψ_N whose
  log-ranks across the two crossing cuts satisfy r² + r′² ≤ 2(P²+Q²). By Lemma A.3, with hubs at real parties, each
  term is a restriction of a three-wire network through u₁ or through u₂. The trivial rank bound is exactly routing,
  so any rank saving beats 3/4. Over K blocks, choose the network per block adaptively (time-sharing); a zero-sum
  game / LP gives the rate. Worst type is all-middle; optimal mixture is a cyclic orientation.
- **Rate 6/(4+√10) = 0.83772.** Dual check [N]: the minimum of R over five-point metrics satisfying triangles + all
  instances of Prop. B.3 with all eight points among the five parties is the same 0.83772. So this is exactly what
  the crossing identity with real hubs gives; reaching 3/√10 needs virtual hubs and recursion (the rest of thm_cn).
- **Why small searches fail [N, exact mod p]:** computed Ψ_N for dimensions (2,2), (3,3), (5,5), (4,8): the middle terms
  have full rank across both cuts at these sizes. Break-even near wire dimension ~10⁴; a usable gain only at wire
  dimension ≳ 10¹². So the single-shot searches at dimension ≤ 5 could not have found anything, and a direct
  numerical test of H19 (nothing above 3/√10) is out of reach by many orders of magnitude.
- To do when the notes are complete: referee; record in the K_{2,3} note (open problem 1 becomes "explicit family at
  0.8377 [D]; gap to 0.9487 open").

## 26 Nov (late, 40): middle-cell agent final; experiments, referee and Lean launched

Final report in `research/ports/middle/notes.md`. Unrefereed.
- **Bottom line:** "ports ⇒ contracting" is equivalent (given all that ¬contracting provides) to ¬(GE), where
  (GE): some bounded-degree family of unbounded order satisfies E_pairs rk ≤ γ·E_edges rk for all placements into all
  Mat_μ(F₂). The agent puts (GE) at ≈60% true; if true, wire metrics cannot unify the two hypotheses and a proof
  would need tensors beyond wire metrics.
- [R] Theorem M0 (direct, quantitative route from a graph + placement to contracting at μ; only D.2 Step 1).
- [R] Kernel lemma (2^{−k·rk} PSD) and threshold: a spreading placement of gradient r needs r ≥ log₂(1/λ₂); LPS graphs
  of degree ≥ 18 admit no 1-Lipschitz spreading placement; for cubic graphs the protected window is empty.
  Barrier: subcritical percolation kernels have the same positivity, so positivity alone cannot prove (GE).
- [R] Theorem M2: Cay(SL₃(F₂[x]/(p))) with the Grassmannian placement has ratio ≥ (3/8)log₂ n − 5; mechanism is
  Lubotzky–Zelmanov's failure of dimension expansion over finite fields (arXiv:0804.0481, checked by the agent).
  So the standard property-(T) expanders in characteristic 2 are maximally bad against buildings of growing rank.
- Rank cone: CUT_n ⊆ 𝒦_n^{rk} ⊆ MET_n, 𝒦_5^{rk} = MET_5. Equivalent forms: subspaces, lattices, linear colourings,
  low-rank coboundaries; for Cayley graphs a "rank-metric Kazhdan property over F₂".
- Weak annealing on small cubic graphs: non-commutative gains of a few per cent only (K_{3,3}: 7/6 vs 1).
- Ten dead routes recorded (§7).
- The 3% prior on the middle cell as the true state is unchanged; what changed is provability.
**Launched:** (1) `rankplace` module in tensorlab (bit-packed F₂ matrices, parallel annealing, graph generators,
controls) running E-M1/E-M3/E-M4; (2) one agent refereeing §2/§4/§5.2 and formalising the kernel lemma and the
spectral inequality in Lean (`PortsLean/RankKernel.lean`).
H24 (GE): open; computation will say whether β_ρ/β_cut grows on generic expanders.

## 26 Nov (late, 41): protocol agent final; referee interim on the middle-cell notes

**Protocol agent final** (`research/ports/protocol/notes.md` + six scripts). Unrefereed → referee launched.
- Explicit asymptotic family at rate 6/(4+√10) ≈ 0.83772 [D]; a coarser fully finite version at 0.83132.
- The tensor statement from App. B: two crossing wires are a sum of Θ+1 integer tensors Ψ_N with log-ranks
  r² + r′² ≤ 2(p²+q²); a cover, not a restriction; the midpoint statement (CN) appears only in the limit (C.2, C.1).
- Level 1 (hubs at real parties, no nesting) is exactly 0.83772: the game value and the dual (triangles + all
  instances of B.3 on five parties) agree [N]. Anything higher needs nesting. One nesting step, heuristic: ≈ 0.854.
- **Sizes (corrects its interim):** with proved rank bounds the first instance above 3/4 has demand wires ≈ 2¹²⁸ per
  block (rate 0.7529 as K → ∞); possibly 2⁵⁰–2⁶⁰ if true ranks are smaller. At ≤ 5×5 the middle terms have full rank
  [R, exact mod p]. So no dense check of any instance above 3/4 is possible.
- Reformulation: a two-term crossing decomposition is SWAP = X + Y with small operator-Schmidt rank(X) and small
  rank(Y); for d = 2 it is δδ − δδ = εε, which gives no asymptotic gain.
- Dead [X]: level 1 without adaptivity; gain on a single 4-cycle; midpoint of u₁u₂ as the only virtual point;
  matrix-multiplication/laser route on the v-side (my suggestion): the triangle alone at rate 1 is routing, all gain
  is in the coupling with u₁u₂.
- It flagged a wrong sentence in the K_{2,3} note ("products of spectral points add their metrics"); fixed.
- My main worry, given to the referee: turning a SUM of restrictions with term-dependent local maps into ONE
  restriction — who knows the term index, what it costs on the supply, and whether rank bounds apply to what is
  actually sent.

**Referee interim on middle-cell notes: kernel lemma, Prop. S and Theorem M0 correct.** Prop. S holds with the signed
second eigenvalue and is exactly tight on Cay(Mat_μ(F₂), rank one) for μ = 2, 3. M0: D.2 Step 1 is unconditional; the
averaging uses transitivity of the affine group on pairs of given difference rank. Bookkeeping: one table row tags
an equivalence [R] whose ⇐ direction is Theorem A ([D]/refereed separately). Numerics on SL₃(F₄): E_edges = 0.5,
E_pairs = 2.292, λ₂ = 0.80.

## 26 Nov (late, 42): kernel lemma and the spectral inequality in Lean [L]; rebuilt by me

`research/ports/lean/PortsLean/RankKernel.lean` (project now 11 files; `lake build` 18274 jobs, success; no sorry):
- `card_ker_mul_two_pow_rank`: #{x : c·x = 0}·2^{rank c} = 2ⁿ over ZMod 2.
- `rankKernel_psd`, `rankKernel_pow_psd`: Σ w_i w_j 2^{−k·rank(a_i−a_j)} ≥ 0, via the explicit feature map
  φ_a(x,y) = 2^{−n/2}·1[a x = y] and product features for powers.
- `spectral_ineq`: for A with unit row and column sums (symmetry not needed) and the quadratic-form gap hypothesis
  ⟨g, A g⟩ ≤ λ⟨g, g⟩ on mean-zero g, and a feature-map kernel with unit diagonal:
  N⁻¹ΣA_uv K_uv ≤ λ + (1−λ)·N⁻²ΣK_uv (ordered pairs incl. u = v) — the notes' normalisation, with signed λ.
- `propS_rank`, `propS_rank_pow`: Proposition S for any f : V → Matrix (Fin m) (Fin n) (ZMod 2).
Not formalised: that the second eigenvalue of a symmetric A gives the quadratic-form hypothesis (Courant–Fischer);
it is a hypothesis of the theorem.

## 26 Nov (late, 43): middle-cell notes pass review, with tagging and wording fixes [V]

`research/ports/review-middle.md`. No fatal gap; every [R] statement checked holds with its constants.
- Fixes: (1) "¬(GE) ⇒ (AN-ports ⇔ contracting)" is tagged [R] but its ⇐ direction is Theorem A; the OA version of M0
  and C_OA ⇒ P_OA rest on OpenAI text the referee could not check. (2) The LPS degree-≥18 claim follows from 4.2(c),
  not (a) ((a) at r = 1 needs p ≥ 62); "the window is empty for cubic graphs" is literally false (e < 0.085).
  (3) "Edge ranks ≤ 1" is in Grassmann units; as F₂-rank placements the edge ranks are ≈ 2 log₂ n — the ratio is
  scale-free so the bound stands.
- Theorem M2 confirmed with independent code: SL₃(F₄) exact (n = 60 480): E_edges = 0.5, E_pairs = 2.2917, λ₂ = 0.8005;
  SL₃(F₈ … F₆₄) sampled: E_pairs = 2.91, 5.18, 5.88, 8.16 against the claimed 2, 5, 5, 8. Ratio ≥ 6j − 2 is nearly tight.
- M0, monotonicity, kernel lemma, Prop. S (exactly tight on Cay(Mat_μ(F₂), rank one)), 4.2(a),(b),(c),(e): correct.
Status of the middle-cell results: Theorem M0, kernel lemma + Prop. S ([L] too), Theorem M2 — [V] by one referee.
(GE) remains open; experiments running.

## 26 Nov (late, 44): referee interim on the protocol — my main worry is answered

- Sum → single restriction: correct. The cover index is the whole word in B^{3K}, held coherently by all five parties
  as a GHZ index: T = (⊗_p Σ_w A_{p,w} ⊗ e_w*)(S^{⊗n′} ⊗ GHZ_M). A five-party GHZ₂ is a restriction of a spanning tree
  of four binary wires, hence of S; cost ⌈3K log₂ B⌉ extra copies of S — O(1) per block against Θ(κ√n₀): negligible
  for fixed B as n₀ → ∞.
- Ranks are used term by term on bucket tensors (rank ≤ sum of bounds), each with its own hub network; the rank of a
  product across a cut is never needed. Time-sharing is a tensor product over blocks: legitimate.
- The matrix reading in the agent's script matches Anthropic's Lean `matM` exactly.
- Independent LP: all-middle = (4+√10)/6; bucketed values for B = 2, 4, 8, 16: 1.20291, 1.20188, 1.19860, 1.19643.
  **So a rate ≥ 0.8358 is backed by finitely many (float) LPs; the limit 0.83772 rests on a numerical claim** (the game
  maximum over term types is at all-middle; referee's 17³ grid + 40 local searches agree).
- Full report to follow.

## 26 Nov (late, 45): explicit protocol passes review, with one correction [V]

`research/ports/review-protocol.md`: no fatal gap. Correction: what is proved is rate ≥ 1/n*(B) for each finite bucket
count B (n*(2) = 1.2029076 → 0.83132; n*(16) = 1.19643 → 0.8358), from floating-point LPs; the limit 6/(4+√10) holds
only if the game maximum over term types is at all-middle ([N]; the value is neither convex nor concave in the ranks).
- Crossing identity matches Lean `prop_identity`/`matM`, integer, every field; A.3 with hubs at real parties fine;
  GHZ index and time-sharing fine; all lower-order terms accounted.
- Class sizes confirmed (log₂ D₁ = 42.555, log₂ D₂ = 127.807; rate 0.75291); "first above 3/4" is the first point of a
  one-parameter scan, with a 0.4% margin resting on float LPs.
- Not refereed: notes §3.3 (nesting heuristics), §4.
K_{2,3} note updated: scope bullet, status-table row and open problem 1 now describe the family and its status.
Follow-up launched: exact rational certificates for the bucket games (finite check: for each of the B³ types a
rational mixture with all six edge loads below a rational bound, with rank bounds rounded up).

## 26 Nov (late, 46): exact certificates for the protocol game; I ran the verifier

`research/ports/protocol/certificates/` (cert_B{2,4,8,16}.json, `verify.py`: 153 lines, only fractions/json/math).
I ran `verify.py` on all four: OK. Exact maximum loads: n*(2) ≤ 1.2029076090 (rate ≥ 0.83131904), n*(4) ≤ 1.2018754980,
n*(8) ≤ 1.1986027020, n*(16) ≤ 1.1964314390 (rate ≥ 0.83581889). Worst type is the middle bucket each time.
Square roots replaced by rational upper bounds (checked by squaring); rounding up is sound because loads are monotone
in the rank bounds. The two LP implementations agree per type (difference 4·10⁻¹⁰ = the rounding). The certificates
use the more restrictive routing model.
So "an explicit asymptotic protocol family on K_{2,3} with rate ≥ 0.8358 > 3/4" rests on: AN Prop. B.2 and Lemma A.3
(their Lean, not built by us), the construction (one referee), and exact arithmetic for the game. K_{2,3} note updated.
Pending from the same executor: dual for B = 2, B = 32/64, a Lean version.

## 26 Nov (late, 47): certificates executor final; Lean certificate for the two-bucket game [L]; all re-run by me

- Certificates for B = 2, 4, 8, 16, 32 (`research/ports/protocol/certificates/`): best c₃₂ = 1.195153569, **rate ≥ 0.83671**.
  I ran `verify.py` on B = 2 and B = 32 (32 768 types): OK; and `verify_dual_B2.py`: n*(2) ≥ 1.2029076080.
  So 1.2029076080 ≤ n*(2) ≤ 1.2029076090.
- New closed form [D, symbolic check by the executor]: n*(2) = 29/27 + 11√10/270, a root of 270x² − 580x + 307; worst type
  is the acyclic one; the optimal mixture has α = 7/18 − √10/90, γ = 5/9 − 13√10/90.
- Sequence (float, with the order-12 symmetry): n*(8…128) = 1.1986027, 1.1964314, 1.1951536, 1.1944556, 1.1940901; gap to
  (4+√10)/6 ≈ 0.048/B; extrapolation 1.193725. Worst type is always the bucket next to the middle, acyclic orientation;
  the cyclic version has value exactly (4+√10)/6. Consistent with the conjectured limit 6/(4+√10); still [N].
- Lean: `PortsLean/ProtocolCert.lean`, theorem `n_star_two_le` — every type in {0,1}³ has a well-formed certificate
  entry with all six edge loads ≤ c = 1.20292 < 4/3, and √(10/9) ≤ ρ̂. Proved by `decide +kernel` on rationals (kernel
  evaluation; no `native_decide`, no sorry — the one grep hit is the header comment saying so). I rebuilt the project:
  18276 jobs, success. It certifies the game arithmetic only, not the tensor construction.
- Lean project now has 12 files.

## 26 Nov (late, 48): rank-placement experiments interim — the search is too weak to decide anything yet

From the `rankplace` executor (module in `tools/tensorlab`; 26 Rust tests + Python smoke pass).
- Structured controls reproduce the notes: SL₂(F₈) ratio 3.738; SL₃(F₄) (n = 60 480) ratio 4.583.
- E-M4 done: λ₂(SL₃(F₄)) = 0.8005; λ₂(SL₃(F₈)), n = 16 482 816, = 0.8773 (Lanczos). Both far above the notes' bound 0.5.
- **Calibration is poor.** On SL₃(F₄) random-start chains reach 1.11 and cut-start chains 2.54, against 4.58 for the
  structured placement. On Cay(Mat₃(F₂), rank one) the identity gives 2.23, β_cut = 1.53, search from scratch ≤ 1.79.
  The annealer recovers the identity from a 90%-randomised start: it refines structure but does not nucleate it.
- Heawood: 27/14 = 1.929 at μ = 3 (notes had 1.75; β_cut 1.714) — a Fano-plane linear structure.
- Random graphs, n ≤ 512: best found always equals β_cut. **Given the calibration, this is weak evidence for (GE):**
  the search would also miss structured placements if they existed. The earlier β_cut heuristic was too weak and has
  been strengthened; E-M1 is being rerun.
- What would make the experiment informative: a search that nucleates linear structure (e.g. placements parametrised
  by F₂-linear maps / module structures, or algebraic ansätze), or exact small cases (which rays of MET₆/MET₇ are rank
  metrics).

## 26 Nov (late, 49): first certifier final; everything re-run with its final code

`tools/ivcert` final (`research/ports/ivcert-notes.md`; README; 18 tests). With the final binary I re-ran
`run_proofs.sh`: all 12 certificates VERIFIED, no FAIL leaves, sha256 unchanged (so the later source edits for the
book problem did not alter the (I)/(CL\*) certificates); `cargo test --release`: 10 + 8 tests pass.
- Stretch goal NOT reached: a direct interval certificate for the book claim (6 parameters, homogeneous
  compactification, a new hull-convexity leaf for the ill-conditioned minimum at W₅). Stopped after 58.7M nodes with
  0 failures — not a certificate. Bottleneck: v_j near the spine line. The book claim follows anyway from
  reduction + calibration + (CL\*); numerically re-confirmed (600 L-BFGS-B starts, DE, basin hopping: min 3/√10 at W₅,
  next local minima 0.9519, 0.9613).
- K_{2,3} note updated with the final protocol figures: exact certificates to B = 32 (rate ≥ 0.83671), dual for B = 2,
  Lean for B = 2.
Agents still running: the rank-placement experiments only.

## 26 Nov (late, 50): E-M1 done — no growing excess over cuts on random graphs, with a weak search

- Random d-regular graphs (d = 3, 4, 6; n = 16 … 512; μ = 2 … 6; 1M iterations × 8 chains): β_found/β_cut ∈ [1.000, 1.031];
  excess > 0.5% only at n ≤ 64; ≤ 0.14% for n ≥ 128. LPS X^{5,13}, X^{5,17}, PSL₂(13), SL₂(F₈) with random generators:
  1.000. Cycles and tori: exactly β_cut.
- Earlier apparent excesses of 6–17% were artefacts of a weak cut baseline (cuts S_xy = {v : yᵀf(v)x = 1} read off the
  placements beat it); fixed.
- Controls: structured placements reproduce the notes; on SL₂(F₁₆) the structured ratio 6.63 is below β_cut ≥ 8.84 (cuts
  win at that size); on SL₃(F₄) structured 4.58 vs β_cut ∈ [2.52, 5.01].
- Calibration unchanged: from random or cut starts the search does not find the structured placements (2.54 vs 4.58;
  1.79 vs 2.23). So the null result is evidence only against placements reachable by local search from cuts.
- E-M2: 6 of 7 orbits of extreme rays of MET₆ are rank metrics at μ = 2; the seventh (with a distance 3) not found for
  μ ≤ 8. E-M3 running.
(GE) remains open; my reading: no evidence against it, weak evidence for it.

## 26 Nov (late, 51): rank-placement executor final

`research/ports/middle/experiments.md`; module `tools/tensorlab/src/rankplace/` (bit-packed F₂ matrices, rank ≈ 5 ns;
graph and group generators incl. LPS; Lanczos; parallel annealer; kernel-inequality checks; nine Python functions;
26 unit tests). An independent plain-Python checker agrees with six saved placements to 10⁻⁹.
- E-M1 (51 random graphs + named families): excess over the best cut ≤ 3.1%, > 0.5% only at n ≤ 32; ≤ 0.14% at n ≥ 128.
- E-M3 (edge rank ≤ r): for d ≥ 8 every placement found has E_pairs ≈ r; for d = 3, 4 the spread rises to 1.3–1.5·r at
  r = 4 — consistent with a threshold near r ≈ log₂ d, in a narrow window (μ = 8).
- E-M4: λ₂ = 0.8005 (n = 60 480), 0.8773 and 0.8798 (n = 16 482 816); all above the notes' bounds.
- E-M2: 7 orbits of extreme rays of MET₆ found (281 rays; the executor recalls 296 from the literature — a 15-ray gap,
  unresolved); 6 orbits are rank metrics at μ = 2 (incl. K_{3,3}); the seventh (90 rays, contains a distance 3) not
  found for μ ≤ 8, not excluded by the kernel test: open.
- Small graphs with real non-commutative gain: Heawood 27/14 vs 1.714 (above 1/(1−λ₂) = 1.892), K_{3,3} 1.167,
  Pappus ≈ 1.05, McGee 1.029, Tutte–Coxeter 1.017.
- On SL₃(F₄) the structured placement's excess over cuts is ≤ 1.55 and not certified > 1 (β_cut ∈ [2.96, 5.01]); on the
  SL₂ controls cuts beat the structured placements.
- Calibration as before: the search repairs structure but does not nucleate it.
- Caveats: β_cut for n > 32 is a lower bound; machine was heavily shared.
- Three 6 MB regenerable placement files are git-ignored; smaller ones and logs are committed.
All agents have now finished. Nothing is running.

## 26 Nov (late, 52): overview written; literature check and a generalisation launched

- `research/ports/README.md`: one-page overview of the seven results with status tags, the two notes, the tools and
  the known weak points.
- Launched: (1) literature and novelty check with web search, for the two notes, the 7-AND-gate result and the
  rank-metric expander question (output `research/ports/literature-check.md`); (2) high-effort theory agent on
  K_{2,m} for all m and on which networks have a "pinned" rate (output `research/ports/k2m/notes.md`).
- Still pending with the user: permission to build Anthropic's Lean here; whether/where to post.

## 26 Nov (late, 53): literature and novelty check

`research/ports/literature-check.md` (web search worked; primary sources read). No prior public statement of the two
main results found; no retraction or correction by either lab.
- **A. Contracting ⇒ fast 3-SAT.** Not stated publicly (blogs and comments, HN, MathOverflow, alphaXiv, issues on both
  labs' repositories checked). Anthropic's paper never mentions SAT or ETH. **Overlap to cite:** OpenAI's EG §11.1
  proves the mechanism of Theorem A under another hypothesis (Lemma 11.3: a uniform contracting gap on the
  F₂-Grassmannian from a largest flat dimension; Prop. 11.2: gap ⇒ ports). So Theorem A is partly anticipated;
  Theorem R looks new. Context to add: both labs' October refutations of classical ETH are compatible with Weak ETH;
  arXiv:2610.41622 (October-type algorithms cannot reach 2^{n^{1−c}}).
- **B. K_{2,3}.** The instance is the Okamura–Seymour example; classical network coding also achieves only 3/4 there
  (Harvey–Kleinberg–Lehman 2006, Thm 27). No study of it for tensor restriction/SLOCC/LOCC found; constants 3/√10 and
  6/(4+√10) not found. Different resource model from classical coding and from LOCC — phrase comparisons carefully.
- **C. 7 AND gates.** The cited 2026 paper on Mul_n exists and says what we wrote. A public machine-generated register
  already claims MC ≥ 6 and calls 6 vs 7 open. So our "≥ 6" is not new; **MC = 7 appears new**, and rests on an
  unverified search → independent recheck launched.
- **D. Expanders.** Lubotzky–Zelmanov attribution verified. Whether one bounded-degree family is an expander against
  all Hadamard spaces is open (three references). For each fixed Euclidean building every expander works, with a
  dimension-dependent constant (Naor–Silberman); unbounded rank is the gap, where Theorem M2 sits. Kernel lemma and
  Prop. S are standard.
- **E. Toyoda.** Theorem confirmed; our reference had the wrong title; fails at six points (so K_{2,m}, m ≥ 4, cannot
  use the box inequalities).
- **Exposure:** the project's GitHub repository is public and indexed, and `research/ports/` has been pushed there all
  day under the standing instruction to keep the public repository updated. So these drafts are already publicly
  readable, though unannounced. My earlier phrasing "nothing has been posted" was imprecise; told the user.
Launched: a writer applying the check's edits to both notes, the overview and the middle-cell notes; an independent
executor re-verifying the 7-AND-gate claim with a different method and, if possible, a proof object
(`tools/mc222/`).

## 26 Nov (late, 54): Theorem K extends to K_{2,m} for every m, with no new certificate [R given (CL\*), unreviewed]

From the K_{2,m} agent (`research/ports/k2m/notes.md`, being written):
- **Weighted five-point theorem:** for 0 < w ≤ 1 every five-point CAT(0) set has Σ_S ≥ 3/√(9+w²)·(Σ_vv + w|u₁u₂|). Proof:
  Prop. 3.2 with κ(w) = 3/√(9+w²); the bracket becomes (κw/3)·Φ_w with Φ_w ≥ Φ₁ termwise for w ≤ 1, so (CL\*) suffices.
- **Averaging over the C(m,3) triples of pages** reduces K_{2,m} at weight w to K_{2,3} at weight w′ = 6w/(m(m−1)).
  I re-did the count: each v in C(m−1,2) triples, each v-pair in m−2, u₁u₂ in all; it gives
  Σ_S ≥ R_m(w)(Σ_vv + wD), **R_m(w) = 2m/√(m²(m−1)²+4w²)**, for 0 < w ≤ m(m−1)/6 (includes w = 1). Formula confirmed.
  Values at w = 1: m = 3: 0.9487 (routing 0.75); m = 4: 0.6576 (0.5714); m = 5: 0.4975 (0.4545); m = 8: 0.2855 (0.2759).
- **Upper bound under ¬contracting:** q+1 rank-one idempotents of Mat₂(F_q), q = 2^r (a cyclic derangement of the
  projective line), pushed to Mat_{2r}(F₂) with ranks scaling by r (machine-checked r ≤ 5); m ≤ 2^k+1 is maximal for
  apex rank 2k. Lemma H is pairwise, so it goes through: f*(K_{2,m}; w) ≤ R_m(w), with equality for w ≤ m(m−1)/6.
- [X] The direct m-page calibration is FALSE for m ≥ 4 (a collinear book gives a negative bracket); averaging avoids it.
- [N] Weighted family: book minimum = min(R_m(w), best cut m/(w+⌊m²/4⌋)); for m = 3 the switch is at w = 5/4. If the
  single inequality 13Σ_S ≥ 12Σ_vv + 15D on five CAT(0) points is certified, then f*(K_{2,3}; w) = 3/(2+w) = the cut
  bound **unconditionally** for w ≥ 5/4. Spec to follow → certificate job.

## 26 Nov (late, 55): literature-check edits applied to both notes, the overview and the middle-cell notes

- Main note: new "Prior work and novelty" paragraph (Theorem A partly anticipated by OpenAI's EG Lemma 11.3 + Prop. 11.2;
  Theorem R and Corollary 1 not previously stated to our knowledge, search of 26 Nov; Lean Zulip and Mastodon not
  searched); ETH context (both labs' October results compatible with Weak ETH; Stearns–Hunt equivalence as stated in
  IM; arXiv:2610.41622, known from an excerpt only, relation not analysed further); OpenAI's history file says a
  working group is reviewing its ETH paper.
- K_{2,3} note: instance named (Okamura–Seymour); classical network coding gives 3/4 there (HKL 2006, Thm 27) —
  phrased as a comparison across different resource models; "not LOCC, not a coding improvement" bullet; EG Thm 4.3 as
  an independent source for the CAT(0) input; Toyoda reference fixed; five-point limit references; ≈20 references added.
- Middle-cell notes: kernel lemma and Prop. S tagged standard; status of the Hadamard-expander problem; unbounded rank
  as the gap.
- Lab notebook (7 AND gates): literature status added by me.
- The writer hedged wherever the check had only seen an abstract or snippet; several of the check's suggested
  sentences were reworded (list in its report).

## 26 Nov (late, 56): (CL\*) has a six-line analytic proof — I checked it by hand [R]

From the K_{2,m} agent. For σ ∈ [−1,1]⁶, 0 < w ≤ 1, K = 1+9/w²: Φ_w ≥ 0. Proof: with m = max|σ|, V = Σ_i|σ_ij−σ_ik|,
E = Σ|σ_ij+σ_ji|: (1) hexagon identity 2σ₁₂ = (σ₁₂−σ₁₃)+(σ₁₃+σ₃₁)−(σ₃₁−σ₃₂)−(σ₃₂+σ₂₃)+(σ₂₃−σ₂₁)+(σ₂₁+σ₁₂) ⇒ V+E ≥ 2m;
(2) c ≥ √(1−m²); (3) Cauchy–Schwarz with sin χ = 3m/√(9+w²): Φ_w + 3 ≥ 3cos χ√(1−m²) + (3m/(2w))(V+E) ≥ 3(1−m²) + 3m²/w ≥ 3.
**My check:** expanded the identity (it is 2σ₁₂; brackets are the three vertex differences and three pair sums);
√K·sin χ = 3m/w; (3/(2w))E ≥ (3m/(2w))E since m ≤ 1; cos χ = √(1−9m²/(9+w²)) ≥ √(1−m²). Correct.
Consequences: the interval certificates (two checkers) become independent confirmation rather than the proof;
Theorem K.1 and the K_{2,m} bounds are computer-free given AN C.3/C.4(a) + Strassen + the calibration; the
three-angle inequality holds with constant 8 in place of 9 (sharp, [N]). The uniform-m argument cannot reach w > 1
[X] (bracket negative at the corners); a refined calibration for 1 < w ≤ 5/4 is open.
Launched: Lean formalisation (`PortsLean/CLStar.lean`): weighted inequality, K = 9 version, algebraic form of (I),
and the K_{2,m} averaging arithmetic.
Lesson for the log: the hard-looking six-variable inequality fell to one identity once the weighted family was
considered — generalising (to K_{2,m}) exposed the structure, as I had hoped when assigning P3.

## 26 Nov (late, 57): the six-variable inequality is in Lean (per the executor; rebuild pending)

`PortsLean/CLStar.lean`: `clstar_weighted` (0 < w ≤ 1, K = 1+9/w²) and `clstar` (w = 1, K = 10), no sorry. The informal proof
is correct. Simplification found: the Cauchy–Schwarz direction (a, b) = (√(1−m²), m) works and needs only K ≥ 9/w²; so
the K = 9 version follows, and K = 9 is sharp (Φ = √K − 3 at σ = (1, −1, −1, −1, 1, 1)). Targets 3–5 in progress; I will
rebuild when it is done.

## 26 Nov (late, 58): independent recheck of the 7-AND-gate claim — second implementation agrees [N ×2]

`tools/mc222` (written without reading `mc_span.c`), per its executor:
- Method 1: exact Rust search over the chain of spaces S_j = span{1, x, g₁..g_j}; failed states memoised by their exact
  canonical RREF basis (no hashing). Symmetry generators checked by computer; 72 plane orbits for the first gate, sizes
  summing to 10 795 — the same orbit count as the first search, obtained independently.
- Validation, each found circuit re-checked by a separate script on all inputs: F₄ mult (2 none / 3 found), 2-term
  polynomial product (2 / 3), ⟨2,2,1⟩ (3 / 4), 3-term polynomial product (5 / 6), matrix product k = 5 none (with and
  without orbit reduction), k = 7 found with Strassen's first products fixed.
- **Matrix product k = 6: all 72 orbits "none" in 6.6 min (3.5M states).** The first search took hours; this one is
  both exact (no hash collisions) and far faster.
- Method 2: its own SAT encoding with CaDiCaL agrees on all small cases; the k = 6 run with LRAT proof checking is
  in progress — that would give a proof object.
Status of MC(⟨2,2,2⟩ over F₂) = 7: two independent exact searches agree; proof object pending.

## 26 Nov (late, 59): K_{2,m} notes ready (§§0–4); referee launched

`research/ports/k2m/notes.md`: Lemma P (q+1 rank-one idempotents of Mat₂(F_q), q = 2^r: t₀, t_∞, t₁, t_a = [a+1 1; a²+a a];
pairwise differences invertible; rank over F₂ scales by r; machine-checked r ≤ 6, m ≤ 65), Lemma P′ (maximality
m ≤ 2^k+1), Lemma H_m, Theorem A (upper bound under ¬contracting for every w > 0), Proposition C (weighted calibration
written out), Theorem D (the analytic inequality), Theorem 5_w, Theorem B (averaging), Theorem K_m with routing value
2m/(m(m−1)+2w) and cut bound min(2/(m−1), m/(⌊m²/4⌋+w)). Corrected [X]: the direct m-page inequality is false for every
even m ≥ 4, and for odd m ≥ 5 at large w.
My spot check: t_a has trace 1 and determinant 0 in characteristic 2, so it is a rank-one idempotent.
Question I put to the referee: since the five-point theorem applies to any five points of a CAT(0) space, the m-page
book may not be needed at all for the averaging; and whether Strassen duality is stated correctly for a weighted
(non-integer) demand.

## 26 Nov (late, 60): the six-variable inequality, the three-angle inequality and the K_{2,m} averaging in Lean [L]

`research/ports/lean/PortsLean/CLStar.lean` (15 theorems; I rebuilt the project: 18278 jobs, success; no sorry):
- `clstar_gen`: Φ(K, t) ≥ 0 on [−1,1]⁶ whenever t² ≤ K and t ≥ 3 (t = coefficient 3/w of the pair sums ×2/… as defined in
  the file); `clstar_weighted` (0 < w ≤ 1, K = 1+9/w²); `clstar` (K = 10); `clstar_weighted_sharp` (any K ≥ 9/w²);
  `clstar_K9`; `clstar_K_lt9_fails` (K < 9 fails at σ = (1,−1,−1,−1,1,1)) — so 9 is sharp.
- `three_angle_alg`, `three_angle` (trigonometric form with any constant c ≥ 8), `three_angle_I` (c = 9),
  `three_angle_corner` (sharpness at the corner).
- `k2m_average`, `R_eq`, `k2m_rate`: the averaging over triples and the identity R = (2/(m−1))·κ(w′).
Now machine-checked: (CL\*) and (I) themselves. Still by hand/referee: the book reduction, the calibration
(Prop. 3.2 / Prop. C), the hull lemma's CAT(0) rigidity, the idempotent family.
Lean project: 14 files.

## 26 Nov (late, 61): referee interim on K_{2,m} — main items correct

- Lemma P: correct (referee's own GF(2^r) code, r ≤ 5; exactly q+1 members; exhaustive search in Mat₂(F_q), q = 2, 4, 8
  finds at most q+1 such points). r = 1 handled by μ = max(2r, 3) with a ↦ diag(a, 0).
- Lemma H_m / Theorem A: correct; every step involves one page or one pair of pages. Optimum correct for all w > 0.
- Prop. C: correct; 200k random three-page books at five weights, minimum slack +3·10⁻⁷; bracket equals (κw/3)·D·Φ_w to
  3·10⁻¹⁴; Lean `clstar_weighted` is exactly the inequality used.
- Theorem B: correct; **the m-page book is not needed** — Theorem 5_{w′} applies directly to five-point subsets (my
  question). Book minimisation for m = 3–6 reproduces R_m(w) to 10⁻¹⁶.
- Minor: the table row m = 6 is wrong (R₆(1) = 12/√904 = 0.399114, checked by me, not 0.399557); the duality for
  non-integer w needs an explicit rational-w plus monotonicity/continuity step (exposition, not a gap).
- Items 2, 6, 7 pending.

## 26 Nov (late, 62): Theorem K_m passes review [V]

`research/ports/review-k2m.md`: no fatal gap. For m ≥ 3: f*(K_{2,m}; w) ≥ R_m(w) = 2m/√(m²(m−1)²+4w²) over every field for
0 < w ≤ m(m−1)/6, and ≤ R_m(w) for every w > 0 when contracting fails. Same imported statements as the m = 3 theorem.
- Fixes: weighted duality needs the rational-w + monotonicity/continuity lines; table row m = 6; "can be taken" in the
  degenerate counterexample; a stale line in `lean/NOTES.md`.
- Confirmed with the referee's own code: Lemma P (r ≤ 5, exhaustive maximality for q = 2, 4, 8), Lemma P′ (largest family
  in Mat₄(F₂) is exactly 5; not used in the theorem), calibration on 200k books, flow LPs (2m/(m(m−1)+2w), m = 3–6), all
  cuts by brute force, the counterexample to the direct m-page calibration (bracket −0.658 at m = 4, w = 1 while the
  true left side is +2.03).
Launched: a writer turning the K_{2,3} note into a K_{2,m} note (analytic proof primary and in Lean; interval
certificates as confirmation; explicit-protocol section). Sent the referee's fixes to the K_{2,m} agent.

## 26 Nov (late, 63): the 7-AND-gate claim now has checked proof objects [N‑rig]

`tools/mc222`, per its executor (my own re-run pending its final report):
- (A) exact Rust search: none for all 72 first-gate orbits, 6.6 min.
- (B) own CNF encoding, CaDiCaL 2.1.3: all 1080 cubes (72 orbits × 15 helper-position pairs) UNSAT; every LRAT proof
  VERIFIED by `lrat-check`; 0.33 h solver CPU, 0.08 h checking, 5.41 GB of proofs (not kept; sha256 and sizes of each
  CNF and proof recorded; one cube re-run gives bit-identical hashes).
- The 7-AND case is found by both methods; circuits pass a separate checker on all 256 inputs.
Together with the first search: three implementations, two methods, one with machine-checked UNSAT proofs.
Remaining trust: the encoding and the symmetry/cube-splitting lemmas (written in the README), the LRAT checker.
MC(⟨2,2,2⟩ over F₂) = 7 in the XOR-free model.

## 26 Nov (late, 64): mc222 final; my own full re-run started

`tools/mc222` final (README with the statement, model, lemma proofs, trust base; `run_all.sh`).
- (A) Rust exact search (810 lines, no dependencies, full keys, no hashing): k = 6 none for all 72 orbits, 3 546 906
  states. (B) truth-table CNF over all 256 inputs with RREF normal forms; 1080 cubes = 72 orbits × 15 positions of the
  two "helper" gates (lemma H, proved in the README); all UNSAT under CaDiCaL rel-2.1.3; every LRAT proof VERIFIED by
  `lrat-check` (drat-trim 2e3b2dc). Without cubes one root did not finish in 275 s.
- Orbits computed twice (Rust and Python): the same 72 representatives. State counts are orbit-invariant (6 orbits
  checked).
- Validation table: F₄ mult 3; 2-term product 3; 3-term product 6; ⟨2,2,1⟩ 4; matrix product k = 5 none (also without
  orbit reduction); k = 7 found by both.
- Shared between the methods: the model and three short lemmas (normal form, count of missing target dimensions,
  symmetry). (A) without orbit reduction at k = 6 not run (~150× longer).
- Do not use the CaDiCaL development head (prints a partial model).
I started `run_all.sh` myself in the background (using the executor's pinned solver/checker builds).

## 26 Nov (late, 65): a claimed UNCONDITIONAL exact rate (Theorem E) [R, unreviewed] — referee and certifier launched

From the K_{2,m} agent (`research/ports/k2m/notes.md` §§5–9; referee fixes to §§0–4 applied).
- **Theorem E:** for five points of a CAT(0) space and every w ≥ w₁ = 1.91345 (λ = 3/(2+w) ≤ λ₁ = 0.766588, the real root of
  4λ³ − 8λ² + 9λ − 4): Σ_S ≥ (3/(2+w))(Σ_vv + wD). Hence **f*(K_{2,3}(w); k) = 3/(2+w) exactly for all w ≥ w₁, every field,
  no hypothesis** (w = 2: tensor rate 3/4 against routing 3/5), and f*(K_{2,4}(w)) = 4/(4+w) for w ≥ 2w₁.
  Upper bound = flattening rank across the cut {u₁, v₁} (crossing supply u₁v₂, u₁v₃, u₂v₁; demand v₁v₂, v₁v₃, u₁u₂).
  Proof: a refined calibration (uses ρ_i ≥ 0), sign cases, two one-vertex lemmas. 3·10⁵-point numerical check.
- Lemma R: the refined bracket is ≥ 0 outside a "hard region" for a wider parameter range. Certificate specs:
  S(9/10) (no zeros in the domain, numerical minimum +0.0627) would lower the threshold to 4/3; (CL\*\*₀) at λ = 12/13,
  η = 15/13 (only zero at the origin) would give 13Σ_S ≥ 12Σ_vv + 15D and the exact rate for all w ≥ 5/4.
- P2: "pinned" networks; Prop. T [R]: K_{2,m} with an r-regular demand graph having a fractional triangle decomposition
  is pinned at 2m/√(m²r²+4w²) (octahedron demand on K_{2,6}: 6/13 < 0.498273 < 1/2); Conjecture P [C]: every two-apex
  network is pinned. K_{3,3}: flow 3/4, cut 1, f_CAT(0) ≥ 3/√10 [R], numerics running.
Why it matters if it survives: this would be an exact tensor rate, strictly above routing, with no reference to
contracting or ETH — unconditional given only "prices are CAT(0)" and Strassen.
H25 [C]: f*(K_{2,3}(w)) = 3/(2+w) for all w ≥ 5/4, and = 3/√(9+w²)-type value below (the latter only under ¬contracting).
Launched: referee on §§5–7; an executor certifying S(9/10) and (CL\*\*₀) with ivcert and ivcheck2.

## 26 Nov (late, 66): the K_{2,3} note is now a K_{2,m} note

`research/ports/note-k23-rate.md` revised in place (≈10,500 words). New title: "Tensor rates of the networks K_{2,m}: …".
- Item 1 is no longer computer-assisted: Theorem D is given in full with its Lean names; sharp constants 9 (six-variable
  form) and 8 (three-angle form); the interval material is a compressed "independent confirmation" section.
- Weighted demand throughout (duality with the rational-w fix, weighted calibration, Theorem 5_w for w ≤ 1).
- K_{2,m}: Lemma P with explicit matrices, Lemma H_m, the optimal configuration, averaging applied directly to
  five-point subsets, routing/cut values, corrected table, the failed direct m-page calibration as a remark.
- New section on the explicit protocol family (certificates to B = 32; closed form for n*(2); limit numerical).
- **New and NOT refereed:** a uniqueness proof (zeros of Φ₁ are σ = 0 and the six corners; corners are tree metrics with
  R ≥ 1; so equality forces W₅). My quick check of its first step: equality in Theorem D's chain forces m ∈ {0, 1}, and at
  m = 1 the dropped cosine terms force all c = 0 — consistent. Still needs a referee before being relied on.
- Not yet in the note: Theorem E (unconditional exact rate at heavy weights) — under review.
- Stale lines the writer found in `lean/NOTES.md` and `k2m/notes.md` (status rows) — to tidy.

## 26 Nov (late, 67): I re-ran the full 7-AND-gate verification — reproduces exactly

`tools/mc222/run_all.sh` (with the executor's pinned CaDiCaL 2.1.3 and lrat-check builds), exit 0:
- all validation cases as reported (both methods; every found circuit re-checked on all inputs);
- Python orbit computation: 72 orbits, sizes summing to 10 795;
- exact search, k = 6: 72/72 roots, found = false, 3 547 604 states, 462 s (state count differs slightly from the
  executor's run because memoisation order depends on thread scheduling);
- SAT: 1080 cubes needed, 1080 verified UNSAT with checked LRAT proofs; solver 0.59 h CPU, checking 0.13 h; 5.41 GB;
- **all 1080 CNF hashes and all 1080 LRAT proof hashes are identical to the executor's record.**
Lab notebook updated. Status: MC(⟨2,2,2⟩ over F₂) = 7 [N‑rig]: three implementations, two methods, proof objects
reproducible bit for bit. Trust: the CNF encoding and four short lemmas in the README, `lrat-check`.

## 26 Nov (late, 68): referee interim on Theorem E — proof checks line by line; no violation

- Cut bound: all 15 bipartitions recounted; {u₁, v₁} is crossed by 3 supply wires and 2 + w of demand; minimum cut for
  w ≥ 1; crosses the W₅-type value at w = 5/4 exactly. Flow LP: 3/(3+w) (0.6 at w = 2). K_{2,4}: cut {u₁, v₁, v₂} gives
  4/(4+w), minimum for w ≥ 2.
- Prop. C′ (refined calibration) re-derived: lengths cancel; only ρ_i ≥ 0 is dropped, with the right sign. 60k random
  books with the referee's own code (86% with a hub at a spine end): true value − bound ≥ +10⁻⁴; adversarial search
  finds the gap tight (−2·10⁻¹⁵), never negative.
- Br′ ≥ 0 on the cut line: the one-vertex lemmas, the sign cases and the cubic are correct (λ₁ = 0.7665884,
  w₁ = 1.9134429). Numerically the bracket's minimum is 0 for λ up to 12/13 and −0.0373 at λ = 0.93 (at σ = 0): so the
  bracket holds up to 12/13 (w = 5/4) and λ₁ is only where the hand proof stops.
- Five-point minimum over three-page books equals the cut value for w = 2, 1.92, 1.5, 1.3, 1.26, 1.25 and is negative
  below (−0.015 at 1.24, at W₅). Threshold 5/4 consistent.
- Spec domain minima match the notes (+0.1619, +0.1035, +0.0627 at λ = 0.8, 6/7, 0.9).
Theorem E: [V, interim]. H25 (threshold 5/4): supported numerically by two independent codes; certificates pending.

## 26 Nov (late, 69): first refined certificate proved by ivcert (independent check still running)

From the certificate executor:
- **S(9/10):** 10·Br′(σ; 9/10, 6/5) ≥ 0 on all of 𝓕′₁, split into 16 closed pieces (v₃ curved or linear × 8 sign patterns of
  the pair sums) on each of which the function is smooth; a box is discarded only if a defining inequality is
  certainly violated on the whole box. 22.5M leaves, ≈270 MB (git-ignored), ≈1000 s under contention. Verified by
  `ivcheck`; `ivcheck2` still running → not yet confirmed independently.
- ivcert changes: new problem file `k2m.rs`; a new hook `point_in_domain` in the branch-and-bound core (a box centre
  with f < c counts as a counterexample only if it is certainly inside the piece). Default true, so existing problems
  should be unaffected — **I will re-run the earlier certificates to confirm their hashes.**
- **(CL\*\*₀):** the eight near-origin certificates are proved and verified. The gain test failed next to the origin
  (cross terms cancel the linear gain); fix: substitute e_k = s_k t_k², which turns the kink into a smooth strict
  minimum closed by convexity leaves; constants scaled by 13 to be exact floats. Far pieces running.
- Reduction check: 140k points outside all symmetric images of 𝓕′₁ give min Br′ = +0.0034 (λ = 9/10), +0.0032 (12/13),
  consistent with Lemma R.

## 26 Nov (late, 70): K_{2,m} agent final

`research/ports/k2m/notes.md` (§§0–9, 895 lines). §§0–4 refereed; §§5–7 under review (interim positive on Theorem E).
New in the final report beyond what is already logged:
- Instances with three distinct values (routing, CAT(0), cut): K_{2,5} with pentagon demand: 5/6, 5/√26 = 0.98058, 1
  (optimum W₇); an asymmetric five-point instance: 0.8, 0.965136, 1 (books and the five-point criterion agree; the
  earlier W₅ value 0.973 for it was not optimal); K_{2,3} plus a u₁u₂ supply wire of capacity ½: 7/8, 0.98675, 1.
- In 48 perturbed K_{2,3}/K_{2,4} instances the CAT(0) minimum equals the cut (in 14 the cut is strictly above the flow):
  three distinct values seem to need near-symmetric data.
- K_{3,3}: flow 3/4, cut 1; f_CAT(0) ≥ 3/√10 [R]; no configuration below 1 found (240 local minima at 1.0607) →
  conjecture Σ_cross ≥ Σ_within for 3+3 CAT(0) points, i.e. f*(K_{3,3}) = 1 unconditionally [C].
- Conjecture W [C]: the CAT(0) minimum for K_{2,m}(w) is min(R_m(w), m/(⌊m²/4⌋+w)); switch points 5/4, 5/2, 16/3 for
  m = 3, 4, 5. Conjecture P [C]: optimal books have their hubs on the spine (138 random instances).
- Unconditional chord bound in the open range, e.g. f*(K_{2,3}(5/4)) ≥ 0.8908 against the conjectured 12/13.
- Dead [X]: (CL\*)-type relaxation beyond w = 1; convexity to reach arc points; per-quadrilateral inequalities; the
  one-vertex lemmas beyond λ₁; triangle-inequality proofs of (I); lifting to Y × ℝ; ℓ₂-product closure of hulls.
- Its next steps: referee Theorem E (running), certificates (running), then Lean for the one-vertex lemmas and
  Prop. C′; prove Conjecture P; decide K_{3,3}.

## 26 Nov (late, 71): second refined certificate proved by ivcert (independent check running for both)

- **(CL\*\*₀):** 13·Br′(σ; 12/13, 15/13) ≥ 0 on 𝓕′₁: 16 far pieces + 8 near-origin orthants; the eight "curved" far pieces
  exclude the central cube [−R, R]⁶, R = (181/256)², which the orthant certificates cover; the "linear" case never meets
  that cube. ≈58M leaves, ≈680 MB (950 MB for both jobs; git-ignored), ≈1350 s. Verified by `ivcheck`.
- `ivcheck2` (independent): 6 of 16 certificates of S(9/10) verified so far; estimated 1.5–2 h more for everything.
- If both independent checks pass and the referee's final report holds: f*(K_{2,3}(w)) = 3/(2+w) for all w ≥ 5/4,
  unconditionally — the full cut regime, H25.

## 26 Nov (late, 72): S(9/10) verified by both checkers — after a bug in the second checker was found and fixed

- **S(9/10) fully certified:** ivcert, `ivcheck` and `ivcheck2` accept all 16 certificates; a coverage script confirms the 16
  pieces cover 𝓕′₁. ivcheck2: 23.3M leaves; 12.45M excluded leaves re-confirmed outside the piece by its own constraint
  test; 10.85M closed (9.18M natural extension, 1.31M mean-value, 367k after bisection); 1400 s.
- **Bug found by the mutation test, in the new ivcheck2 code for this problem:** in the mean-value form the value was
  scaled by the constant M but the gradient was not, so a shifted (false) statement was "verified" near the origin.
  Fixed; a new self-test (enclosures must contain point values on random boxes) catches the old bug (2209 failures)
  and passes now. All quoted results are re-runs after the fix; the earlier "6 verified" message is void.
- Lessons: (1) mutation tests earn their keep; (2) for these two new problems the same executor wrote both the Rust
  encoding and the Arb encoding, so the "independent checker" is independent in arithmetic and method but not in
  authorship — weaker than for (CL\*), where a different agent wrote the second checker. To state in any write-up.
  (3) I must confirm the fix did not touch the code path used for the original (CL\*) verification (that problem has
  no M scaling) — re-run both original suites when the executor is done.
- (CL\*\*₀): ivcheck2 running (~62M leaves, ~1 h).

## 26 Nov (late, 73): Theorem E passes review [V] — an unconditional exact rate

`research/ports/review-thmE.md`: no gap, no numerical violation; all recomputation with the referee's own code.
**f*(K_{2,3}(w); k) = 3/(2+w) for every w ≥ w₁ = 1.9134429 and f*(K_{2,4}(w); k) = 4/(4+w) for every w ≥ 2w₁, over every field,
with no hypothesis.** Routing gives 3/(3+w) and 4/(6+w). (At w = 2: 3/4 against 3/5.)
- Cut bound over all 15 bipartitions: min(1, 3/(2+w), 3/w) = 3/(2+w) for w ≥ 1; crosses the W₅ value exactly at 5/4.
- Prop. C′ re-derived; the only dropped term is ρ_i(a_ix + b_ix − λP_i) ≥ 0. 60k random books, weights 1.1–2.
- Br′ ≥ 0 for λ ≤ λ₁ checked line by line; numerically the bracket's minimum is 0 up to λ = 12/13 and negative beyond.
- Equality set is larger than stated: the whole family of line metrics (v_i = u₁, v_j = u₂, v_k on [u₁u₂]).
- Specs: S(λ₂) gives every w ≥ (3 − 2λ₂)/λ₂ by convexity (4/3 for λ₂ = 9/10); (CL\*\*₀) gives 13Σ_S ≥ 12Σ_vv + 15D.
- Prop. T, its octahedron instance and the book principle: correct. Minor: non-regular demand graphs need a different
  constant (not used); "minimum" → "infimum" in Prop. B; one recorded margin missed σ = 0 (+0.0158 not +0.0163 at 0.92).
Combined with the certificates: threshold 4/3 now has two checkers (same author for both encodings); threshold 5/4
awaits the second checker.

## 26 Nov (late, 74): (CL\*\*₀) verified by both checkers

All 24 certificates (62.1M leaves) accepted by ivcert, `ivcheck` and `ivcheck2`; the coverage script confirms they cover
𝓕′₁ including the central cube via the eight near-origin orthants. ivcheck2 closed 1 412 leaves by its own origin lemma
on [−1/16, 1/16]⁶; 3771 s. Write-up: `research/ports/ivcert-notes.md` §5.
With the refereed Theorem E, Lemma R and the convexity argument: **f*(K_{2,3}(w)) = 3/(2+w) for all w ≥ 5/4** and
**f*(K_{2,4}(w)) = 4/(4+w) for all w ≥ 5/2**, unconditionally, modulo: the two certificates (both checkers by one author),
Lemma R (referee checked the implications, see review-thmE §6), and the imported CAT(0) theorem.
To do when the executor hands back: re-run the original (CL\*) suites to confirm the tool changes left them intact;
then add the cut-regime theorem to the note.

## 26 Nov (late, 75): certificate executor final; original suites re-run and intact

- Final report on S(9/10) and (CL\*\*₀): 40 certificates (23.3M + 62.1M leaves, 950 MB, git-ignored), all accepted by
  `ivcheck` and `ivcheck2`; coverage script passes; mutation tests reject shifted statements; `run_k2.sh` in both tools.
  Independence caveat (same author for both encodings; they agree to 2·10⁻¹⁴ at random points) stated in the write-up
  (`research/ports/ivcert-notes.md` §5). Not checked there: Lemma R and Prop. C′ (the referee did), and the margin.
- **My re-run after the tool changes:** `tools/ivcert/run_proofs.sh` → 12 certificates VERIFIED, sha256 unchanged from
  the first run (three spot hashes compared); `cargo test`: 10 + 9 pass; `tools/ivcheck2/run_all.sh` → OVERALL VERIFIED for
  the three-angle certificate, the eight central certificates and the main six-variable certificate; twelve corner
  faces proved. So the new hook in the prover core and the checker fix did not disturb the (CL\*) verification.
- I have not re-run the 40 new certificates myself (about 1.5 h of machine time); their status is "two checkers, one
  author, run by the executor".
State of the cut regime: f*(K_{2,3}(w)) = 3/(2+w) — w ≥ 1.913: hand proof, refereed; w ≥ 5/4: adds two certificates.
Launching a writer to add the cut-regime theorem to the note and the overview.

## 26 Nov (late, 76): cut-regime theorem added to the note; overview updated

`research/ports/note-k23-rate.md` (≈12,800 words; title now ends "… and the exact rate 3/(2+w) in the cut regime"):
new item 5 in the main theorem with levels (a) w ≥ 1.913 (hand proof, refereed), (b) w ≥ 4/3 (+ certificate),
(c) w ≥ 5/4 (+ second certificate); new §4.4 with the refined calibration, Br′, the one-vertex lemmas, sign cases, the
cubic, Lemma R, the certificates with the same-author caveat and the fixed checker bug; new §4.5 on pinned networks
(Props. B and T refereed; three-value instances numerical; Conjectures W, P, K_{3,3}); the interval section for (CL\*)
cut to one paragraph. `README.md`: rows for the cut regime and the 7-AND-gate result; code table; weak points.
Writer's own additions, which I checked:
- K_{3,3}: f* ≥ (3λ+η)/4 from summing the five-point inequality over the six K_{2,3} sub-instances — I re-did the count
  (each cross wire lies in 2 of the 3 sub-instances per side): 0.975 at level (b), 51/52 at level (c). Correct.
- Level-(c) chord values for 1 < w < 5/4 — I recomputed 0.9383 at w = 1.1 from the chord between (κ(1), κ(1)) and
  (12/13, 15/13). Correct. (The valid set of (λ, η) is an intersection of half-planes, hence convex.)
- "Below 5/4 the cut value is not reached by CAT(0) geometry" is provable, not numerical: W₅(w) has ratio
  3/√(9+w²) < 3/(2+w) exactly when w < 5/4. My brief was wrong to call it numerical.
- Equality in Theorem E stated as "holds on the family of line metrics", not as a characterisation.
Stale status rows remain in `k2m/notes.md` (its author has finished): Theorem E is refereed; cut-pinned range is 5/4.

## 26 Nov (late, 77): next step — the calibration in Lean

All earlier agents have finished. The stated weakest point of Theorem K's lower bound is the book reduction and the
calibration (refereed, numerically tested, not in Lean). Launched a Lean executor with the target: from one explicit
hypothesis — the comparison inequality dist(v_i, c(t))² ≤ (1−t/D)|v_iu₁|² + (t/D)|v_iu₂|² − t(D−t) that Anthropic's
Lemma C.4(a) provides — derive the weighted five-point inequality in Lean, using `clstar_weighted`. Staged: (1) the
calibration given exit data; (2) existence of minimisers and optimality relations; (3) passage from the metric data
to planar data. If it succeeds, the lower bound of Theorem K_m is machine-checked down to a single imported
statement (plus Strassen duality, which is not formalised).
Open decisions for the user (unchanged): building Anthropic's Lean here; whether to keep pushing drafts to the public
repository; whether/where to announce.

## 26 Nov (late, 78): the calibration is in Lean (stage 1; per the executor, rebuild pending)

`PortsLean/FivePoint/Calibration.lean`, theorem `book_calibration` (w > 0): given the six exit sines with |s| ≤ 1, the bounds
Z_ij ≤ ρ_i√(1−s_ij²) + (a_i − y_ij)s_ij + ρ_j√(1−s_ji²) + (a_j − y_ij)s_ji, and the first-order condition in the combined form
(D/2)|s_ij + s_ji| ≤ (y_ij − D/2)(s_ij + s_ji), it concludes
κ(Z₁₂+Z₁₃+Z₂₃+wD) + (κw/3)·D·Φ(1+9/w², 3/w)(s) ≤ Σ_i√(ρ_i²+a_i²) + Σ_i√(ρ_i²+(a_i−D)²), κ = 3/√(9+w²).
No sign conditions on ρ, a, D needed. Calibrating vectors are algebraic (no trigonometry); only |p|, |q| ≤ 1 is used,
which also covers the degenerate case. No discrepancy with the note's §3.2. Stages 2 (minimisers and optimality) and
3 (metric reduction) in progress.

## 26 Nov (late, 79): stage 2 of the Lean calibration (hubs and first-order conditions)

`PortsLean/FivePoint/Hub.lean`, `hub_exists` (ρ_i, ρ_j ≥ 0, D ≥ 0): there are y ∈ [0, D] and s_i, s_j ∈ [−1, 1] with
√(ρ_i²+(a_i−y)²) = ρ_i√(1−s_i²) + (a_i−y)s_i (same for j) and (D/2)|s_i+s_j| ≤ (y − D/2)(s_i+s_j). The hub is a minimiser on
[0, D]; one-sided optimality is proved without derivatives, from f(y+h) ≤ f(y) − σh + h²/(2f(y)). Spine case handled by
choosing σ_i = −σ_j (minimality not needed there), as the note says. No discrepancy with the note. Stage 3 (metric
reduction from the comparison hypothesis) in progress. Per the executor; rebuild pending.

## 26 Nov (late, 80): the five-point theorem is machine-checked from one hypothesis [L]; rebuilt by me

`research/ports/lean/PortsLean/FivePoint.lean` (+ `FivePoint/Calibration.lean`, `FivePoint/Hub.lean`; 526 lines). I rebuilt the
project (18284 jobs, success; no sorry) and read the statements.
- `CMP u1 u2 c v`: ∀ t ∈ [0, D], dist(v, c t)² ≤ (1 − t/D)·dist(v,u₁)² + (t/D)·dist(v,u₂)² − t(D − t), D = dist(u₁,u₂).
- **`five_point_weighted`**: in any pseudometric space, 0 < w ≤ 1, five points and c with CMP for v₁, v₂, v₃:
  3/√(9+w²)·(|v₁v₂| + |v₂v₃| + |v₁v₃| + w·|u₁u₂|) ≤ Σ_{k,i}|u_kv_i|. D = 0 handled inside without CMP.
- `five_point` (w = 1); `cmp_inner` (CMP holds in every real inner product space — the hypothesis is satisfiable);
  `five_point_inner`; **`k2m_five_point`** (K_{2,m} form with R_m(w)).
- No step of the informal proof failed; no sign conditions on the planar coordinates needed; optimality conditions
  proved without derivatives.
So Theorem 5_w and Theorem B are in Lean modulo CMP (our transcription of AN Lemma C.4(a), not linked to their Lean).
Not formalised: Strassen duality; "prices satisfy CMP" (imported); Lemma H_m; Theorem E's refined calibration.
Note §8 and the overview updated accordingly. Lean project: 17 files.

## 26 Nov (late, 81): Lean executor final on the five-point theorem

All four stages done (statements in `research/ports/lean/NOTES.md`, FivePoint section). Findings:
1. A remark in MY brief was false: "any subgradient choice in [−1,1] works" for points on the spine. The proof needs
   σ_ij = −σ_ji (or 0 when both vanish), exactly as the note says; the careless choice σ = 0 produces violations.
2. The calibration needs no angles: with P = c_ij + c_ik, Q = σ_ij + σ_ik, M = (κw/6)√(P² + K(σ_ij − σ_ik)²), take
   q = (κP/2 + z, κQ/2 − M), p = κ(P, Q) − q with Pz = QM; only |p|, |q| ≤ 1 is needed, which also covers P = 0 (both exit
   vectors vertical), a degenerate case the note does not mention.
3. The three-case optimality condition is one inequality: (D/2)|ε| ≤ (y − D/2)ε.
4. No derivatives needed for optimality; no hidden hypotheses; D = 0, ρ_i = 0, h_i(t_ij) = 0, A_i = 0 all covered.
Nothing is running now. Open with the user: public repository policy for drafts; building Anthropic's Lean;
announcement.

## 27 Nov: paper on the 7-AND-gate result commissioned (user request)

User asked for a paper in the manner of the two labs' recent papers, written by a subagent, with little machine-writing
filler. I read "our proof" as the result just discussed (2×2 over F₂ needs 7 AND gates); the other two results already
have draft notes. Told the user there is no Lean proof of this result — the paper must say "computer-verified with
checked LRAT proofs", not "formalised".
Writer brief: LaTeX in `research/mm/paper-mc222/` (main.tex, refs.bib, PDF if a TeX engine can be installed — none is
present); model, theorem, why Winograd's bound does not apply, lemmas with proofs re-derived, both computations with
exact figures, trust base, provenance statement, open questions; author line left as a placeholder; no model names;
a CHECKS.md listing what was re-derived and which references were verified. A referee pass will follow.
Also for the record: I could not open GitHub pages from this container (403 from the proxy), so the public link given
for the tweet is unverified from here.

## 27 Nov: posts for X drafted (`research/ports/posts-x.md`)

By a subagent, after web research. Found the "claudish-to-english" plugin (github.com/gvzdv/claudish-to-english; its
rules are the rewrite prompts in rewrite.sh / md-core.sh) plus a companion style reference; and guidance on research
posts on X (result must fit above the ~280-character fold; links in the first reply or last thread post; state review
status; no hype, emoji or hashtags). For each of the three tweetable results: a long post, a 4–6 post thread (all
≤ 280 weighted characters), image alt text and a reply post with links pinned to commit 8039282. Nothing was posted.
Softenings it made, all correct: no "2^(n^0.88)" (δ ≈ 0.121 only at the smallest allowed value of Anthropic's constant
H, which is not explicit) — my morning summary to the user stated 0.88 too flatly; "flat holds under weak ETH" is not
news by itself since OpenAI claims flat outright — what result 2 adds is that contracting fails; the refereed form of
Theorem R uses advice; "no assumptions" for the weighted rate still uses Anthropic's CAT(0) lemma.

## 27 Nov: paper on the 7-AND-gate result drafted; referee and a small extension launched

`research/mm/paper-mc222/` (main.tex, refs.bib, main.pdf — 10 pages; CHECKS.md). TeX Live installed via apt. I read the
first three pages: abstract states the theorem and says plainly that nothing is formalised in a proof assistant;
Strassen's seven products over F₂ checked by me against the standard identities; a section on why homogenisation does
not transfer the classical bound (x₁x₂·x₁x₂ = x₁x₂), without claiming that Boolean circuits ever beat quadratic ones.
Writer's findings, acted on:
- The committed exact-search log came from an earlier build (cache of failed states kept across roots): 3,546,906
  states vs 3,547,604 with the committed code. Replaced `tools/mc222/results/exact_k6_orbits.log` by the log of my
  re-run and corrected three figures in the README (commit c3b3a73); the paper's repository link now pins that commit.
- README lemma H, step 5 silently used S_{i−1} ⊆ W_i; the paper normalises first. README's N1 lacked one argument.
- Added by the writer: "the first gate is a helper" (why 720 of the 1080 cubes are trivial); a short proof that F₄
  multiplication has value 3.
Launched: (1) an adversarial referee on the paper (lemmas, faithfulness of the encoding incl. a toy problem the
authors did not tune on, regenerating cubes, prior work — in particular whether a general theorem already implies
the result, prose); (2) an executor to settle ⟨1,2,3⟩ at k = 5 with the same tooling (MC ∈ {5, 6}); a 5-gate circuit
there would be a Boolean circuit beating bilinear rank.

## 27 Nov: Lean proof of the 7-AND-gate theorem scoped; ⟨1,2,3⟩ interim

- User asked whether the theorem can be proved in Lean. Answer given: not kernel-checked (5.4 GB of LRAT), but
  plausibly via `bv_decide` (Lean's verified LRAT checker; extra axiom `Lean.ofReduceBool`), with the model and the
  reduction lemmas in Lean so that the encoder, the external checker and the hand lemmas no longer need to be trusted.
  Launched a prototype in `research/mm/lean-mc222/`: statement + Strassen upper bound; one cube end to end with
  timings (the feasibility verdict); small validation cases as complete theorems; then the lemmas; estimate.
- ⟨1,2,3⟩ (eight inputs, three outputs), interim from the executor: exact search finds no 5-gate circuit (51 orbits
  under GL₂ × GL₃ of order 1008, generators checked on truth tables; 2,829,011 states; 199 s); k = 4 refuted too.
  Points to MC = 6 = bilinear rank. SAT + LRAT over 51 × 10 cubes pending.

## 27 Nov: back to 3-SAT itself (user: "lets make progress on 3-SAT")

Honest position: we have no result on SAT itself. Yesterday's 3-SAT statement is conditional on a case nobody expects.
The one concrete unconditional opening is the exponent of log n: known algorithms give 2^{O(n/(log n)^{1/2})}; D1 showed
that under flatness an engine with p merges and node growth β is capped at exponent ½·log_β p, so designs with more
merges than their growth pays for (three non-product merges: up to ½·log₂3 ≈ 0.79) are not excluded.
My framing of the question, as a duality problem:
- H26 [C]: the true floor of a multi-merge piece is the maximum over ALL prices, not only Euclidean ones. If
  contracting fails, building-type prices (√rank on Mat_μ(F₂), tripod × ℝ) are available and may raise the floor above
  1/√p — then more merges cannot help in the world everyone believes in, and 1/2 is a barrier for the whole method
  (a theorem worth having: "no rewriting engine beats (log n)^{1/2} unless contracting holds").
- H27 [C]: if the floor is NOT raised, duality (AN Thm A.6) should give covers attaining it, at least
  non-constructively; whether that yields an algorithm depends on finding pieces by search or on an explicit
  "three-way crossing identity" (terms with log-ranks on a sphere across three cuts).
Launched: (1) a high-effort theory agent on exactly this (P1: which designs have p > β honestly; P2: the true floor;
P3: attainment; P4: the barrier if negative) → `research/sat3/notes.md`; (2) an executor computing floors for K₄ and Δ₃
over Euclidean configurations, matrix placements and tree products with a new tensorlab module (spec S3 of c1d1) →
`research/sat3/s3-experiments.md`.
Still running from before: referee on the 7-AND-gate paper; ⟨1,2,3⟩ executor; Lean prototype for the 7-AND-gate theorem.

## 27 Nov: MC(⟨1,2,3⟩ over F₂) = 6 [N‑rig, per the executor; my check pending]

Both methods: (A) exact search, 51/51 orbits under GL₂ × GL₃, no 5-gate circuit, 2,829,011 states, 199 s; (B) SAT, all
510 cubes (51 orbits × 10 helper pairs) UNSAT, every LRAT proof verified; 146 s solver, 54 s checking, 1.14 GB.
k = 4 UNSAT in both; a 6-gate circuit found and verified on all 256 inputs. Orbits agree between Rust and Python.
The executor says the old 2×2 results still reproduce — I will confirm by re-running the 2×2 hashes after it is done,
since it edited the shared generator and search program.
So in both small formats settled so far (⟨2,2,2⟩: 7; ⟨1,2,3⟩: 6; also ⟨2,2,1⟩: 4) the unrestricted Boolean
multiplicative complexity equals the bilinear rank over F₂. No example of a Boolean circuit beating bilinear rank.

## 27 Nov: Lean route for the 7-AND-gate theorem — stage 1 done, feasibility looks good

`research/mm/lean-mc222/` (per the executor; my rebuild pending).
- `MC222/Statement.lean`: functions F₂⁸ → F₂ as `Fin 8 → ZMod 2 → ZMod 2`-valued maps; inputs x_k; targets c_ij;
  S g j = span of 1, the inputs and the first j gates; `IsCircuit g := ∀ i, ∃ u ∈ S g i, ∃ v ∈ S g i, g i = u * v`;
  `Computes`; `HasCircuit k`; `MC := sInf {k | HasCircuit k}`. Target: `HasCircuit 7 ∧ ¬ HasCircuit 6`.
- `MC222/Upper.lean`: `hasCircuit_seven` proved (Strassen), standard axioms only.
- Feasibility preview: one cube as a single `bv_decide` goal over `BitVec 256` truth tables and `BitVec 16` selectors
  takes 11–20 s, LRAT check < 2 s; a satisfiable control returns a counterexample. All 360 non-trivial cubes are
  building. So the finite part looks feasible inside Lean; what remains is the reduction lemmas in Lean (normal form,
  helper count, orbits) linking `¬ HasCircuit 6` to the cube statements.

## 27 Nov: ⟨1,2,3⟩ executor final; my checks on the shared tooling

- Final report: MC(⟨1,2,3⟩ over F₂) = 6. Symmetry group of order 1008 (GL₂ on the middle index, GL₃ on columns; no
  transposition), checked in Rust (generators) and Python (all 1008 elements); 51 orbits of first-gate planes; with
  k − 3 helpers: 10 cubes per root at k = 5. k = 5: exact search none (2,829,011 states); 510 cubes UNSAT with verified
  LRAT (1.14 GB, largest 16.5 MB). k = 4: none / UNSAT (also without orbits). k = 6: circuits found and verified.
  A truncated proof is rejected by the checker. New files only add an `mm123` branch; `run_mm123.sh` reproduces in ≈ 11.5 min.
- **My check that the 2×2 results are untouched by the edits to the shared files:** regenerated all 1080 formulas for
  ⟨2,2,2⟩, k = 6 with the modified `gen_cnf.py` — all 1080 sha256 match `results/sat_k6_results.tsv`; rebuilt the search
  program and re-ran ⟨2,2,2⟩, k = 5 with and without orbit reduction — same verdicts and the same 10,975 states.
- Started my own full run of `run_mm123.sh` in the background.
- The paper still lists ⟨1,2,3⟩ as open; to be updated together with the referee's revisions.

## 27 Nov: floors of multi-merge pieces — first numbers; tree products raise the Δ₃ floor [N]

From the executor (`research/sat3/s3-experiments.md`). Value = (Σ_m b_m⁺)/p per merge, larger = higher floor.
- Two-merge crossing: Euclid √2; products tree × flat, tree × tree: exactly √2, never more; single tree and √rank on
  Mat_μ(F₂) (exhaustive μ = 2, 3; annealed to 6): exactly 1.0. The matrix VERTEX sets are weak because √rk is the square
  root of a metric (far legs carry no information) — c1d1's spec S3 was wrong to expect them to reproduce the flat
  value. The relevant non-Euclidean prices are hull configurations (tree × flat).
- K₄ with three matchings (flat 2√2, ρ = 0.4714): nothing tried beats flat.
- **Δ₃ (flat 3√3 = 5.196, ρ = 0.5774): tripod × tripod gives 5.4641 = 2 + 2√3 (ρ = 0.6071); tripod × ℝ⁴ gives 5.4798
  (ρ = 0.6089).** Verified by an independent evaluation on explicit finite configurations.
So H26 is confirmed in kind for Δ₃: non-Euclidean CAT(0) configurations raise the floor above 1/√3. Open: whether these
configurations are prices when contracting fails (m-pod × ℝ is; tripod × ℝ^k, k ≥ 2, and tripod × tripod are not
proved), how high the supremum goes, and whether the raised floor still beats two merges once the node growth β is
counted. K₄ is not raised by anything tried. Sent to the theory agent with three questions (β; the supremum over
proven prices; K₄ versus Δ₃).

## 27 Nov: 3-SAT theory interim 1 — the route is not dead by counting; the floor of 3-nets is the whole question

From the theory agent (`research/sat3/notes.md`):
- Exponent α′ = log_β(1/ρ*), ρ* the true level value, β the node growth. D1's cap ½·log_β p holds only for fully crossing,
  "balanced" configurations (balance = vanishing cross terms; that is what gives the flat value E/√p).
- Product designs all give 1/2: g × g grid with rows + columns (p = 2, β = 2); d-dimensional grids with hyperplane merges
  (p = d, β = d); with line merges (p = d, β = d/(d−1), unbalanced, flat value √((d−1)/d)) — again exactly 1/2.
- **p-nets do have more merges than their growth pays for:** AG(2,g) with p of its g+1 parallel classes (p − 2 MOLS; any
  Latin square for p = 3): K′ = g², K = g, so β = 2 for every p; balanced; flat floor → 1/√p. Window for α′: up to 0.79
  (p = 3), 1 (p = 4), polynomial saving for p = g + 1. Smallest instances: K₄ with 3 matchings (g = 2), Δ₃, full AG(2,3).
- [R] In every CAT(0) space, for a quadrilateral o, w, o′, w′: d(m_ow, m_o′w′)² + d(m_ow′, m_o′w)² ≤ ½(d(o,o′)² + d(w,w′)²).
  Consequences: (1) for two merges the price-method value is ≤ E/√2 for every price, unconditionally (recovers the
  crossing bound without App. B); (2) K₄'s floor is exactly the flat one; (3) on a full p-net level every price is
  capped at E/√2·(1+o(1)), so the true floor of a 3-net lies in [1/√3, 1/√2]; (4) for p ≥ 3 an excess term
  (pairwise variance minus true variance of the p hubs of a node) vanishes in flats and is positive in trees.
- Exponents (mine): ρ = 1/√3 → 0.792; ρ = 0.6071 → 0.720; ρ = 0.6089 → 0.716; ρ = 1/√2 → 0.5. So even the raised floor
  found numerically for Δ₃ leaves room above 1/2; the route dies only if the supremum over admissible prices reaches
  1/√2.
- Relevant spaces when contracting fails: hulls Π_j (m_j-pod) × ℝⁿ (block-diagonal embedding; the product-of-hulls step
  is [D]).
H26 refined: for 3-nets, sup over hull prices ∈ [0.609, 0.707]; H28 [C]: the supremum is strictly below 1/√2 for some
p-net. If H28 holds and floors are attained (H27), 3-SAT counting improves to 2^{n/(log n)^α}, α > 1/2.
Forwarded the corrected spec to the executor (stop matrix-vertex runs and K₄; nets AG(2,3), AG(2,4), AG(2,5); general
trees; growth with the number of factors; a run without the far-leg ansatz).

## 27 Nov: 3-SAT theory interim 2 — on Δ₃ the floor under ¬contracting is in [2/3, 1/√2]; asymptotics open

From the theory agent:
- [D, wants a referee] **Every finite subset of every finite ℓ₂-product Π_j (m_j-pod × ℝ) is a price when contracting
  fails** (block-diagonal embedding with additive rank; "segment filling" from AN C.4(f) with an arbitrary factor Z;
  gluing as in Lemma H_m; induction over factors). So tripod², tripod⁹, tripod × ℝ^k are prices in that world. General
  trees with two branch points: not proved.
- [R] One-tree reduction on Δ₃: sup over all ℓ₂-products of trees = (1/p)√(E·Γ), Γ = sup over one tree of S/D̄.
- **Δ₃: the product of nine node-tripods gives exactly 6 per merge, ρ = 2/3** (Γ = 36; cap for every price 9/√2 = 6.364,
  Γ ≤ 40.5). So under ¬contracting the Δ₃ three-merge floor is in [0.6667, 0.7071]; exponent ≤ log₂(3/2) = 0.585 on Δ₃.
  Mechanism: (avg b)² ≤ E·(E/p + Σ_n deg(n)·X(n)), X(n) = pairwise variance minus true variance of the p hubs at node n;
  X = 0 in flats and for p = 2; node-tripods make X > 0 with equality in the chain.
- K₄ is not a design for the tower (K = 2 cannot be iterated); its floor is settled for every price; it remains a pure
  attainment question.
- **Asymptotics decide the route:** a tower needs nets of order g → ∞. The node-tripod family gives √((g+p−2)/(gp)) per
  merge on generic edges: 2/3 at g = p = 3, → 1/√p as g → ∞. So the constructed obstruction vanishes for large g;
  whether cleverer trees keep the floor above 1/√3 (or push it to 1/√2) as g → ∞ is open.
Status of H28: on the smallest net the floor is at least 2/3 (exponent at most 0.585 there); asymptotically nothing
yet excludes 1/√3 (exponent 0.79). Three cheap runs sent to the executor: check of the nine-tripod value; Γ over
general trees on Δ₃; Γ for full 3-net levels on AG(2,g), g = 3, 4, 5, 7.
Next, once numbers are in: referee the product-of-hulls statement; then the attainment question (H27) becomes the
main problem.
