# Next steps (recorded 3 Nov 2026)

Deferred by decision on 3 Nov 2026; to be picked up after the quantum note and the crossover note are out.

## 1. Barrier paper: "What the ETH refutations do not give"

**Goal.** One paper consolidating the negative results, with every claimed theorem machine-checked in Lean
(claim policy, top-level README) and everything else labelled informal.

**Material (all in `research/permanent/` unless noted):**
- Rate tightness. Anthropic's engine: the per-level saving ρ = 1/√2 is tight for graded two-order pieces
  (`rho-lower-bound.md`, spread lemma; `sparse-fock.md`: sparse algebras reduce to the same tensor problem).
  Recursions of Anthropic's shape are capped at α′ ≤ 1 (`clique-evaluation.md` §4.3). OpenAI's Engine I: the √Q
  parity bound is tight in its template (`parity-barrier.md`, Thms 1–2; Thm 2 uses the ARV structure theorem).
- The dense permanent. Local networks need Θ(n log n) shared bits (`permanent-attack.md`, `barrier.md` Thm 6.1,
  `vertex-local-bound.md` Thm 3.1 for trees), entropy and algebra-rank obstructions (`wild-ideas.md` F1/F2),
  mod-p obstruction (`perm-mod-p.md`), what the m-independence mechanism needs (`anthropic-m-independence.md`).
- The Tutte plane (`research/tutte-plane.md`). The engine reaches exactly the integer hyperbolas
  (x−1)(y−1) = q and the line y = 1; everywhere else a vertex-local network needs (1−o(1))·n log n bits
  (cut rank Bell(b) of [q^{|P∨Q|}]). Tight: Θ(n log n) by interpolation.
- Unifying statement to aim for: every remaining wall reduces to an engine with rate o(1/log K) outside
  Anthropic's framework.

**Already in Lean** (`lean/EthFollowup/Barriers/`, 39 theorems, standard axioms): cut/rank bound, row-cut rank
C(n,k), the Model-R bound U ≥ n·log₂(n/s) with the rank step as hypothesis, triangular rank bound, spread
lemma (abstract form), algebra-rank bound C(n,n/2), per ≡ 0 mod p for low rank, colouring barrier.

**To do:**
1. Independent referee pass on `tutte-plane.md` (barrier theorem, realisability by subcubic gadgets, rank of
   [q^{|P∨Q|}] via Lindström; the Catalan rank on y = 1 is only conjectured beyond b = 7) and on the
   rate-tightness proofs.
2. Formalise the key new theorems in Lean: the Tutte cut-rank barrier (partition-lattice ranks), the
   vertex-local tree bound with the rank step proved, the α′ ≤ 1 cap. Anything not formalised is labelled
   "written proof, not claimed".
3. Close the two open loopholes of the Tutte barrier or state them: sums over many different clusterings;
   skeletons that depend on private edges.
4. Literature: items flagged in `tutte-plane.md` as checked only at abstract level or from memory
   (DHMTW Thm 1.4 general-hyperbola section, Brand–Dell–Roth, FLS/Lovász, Noble, treewidth bounds).
5. Write the paper (amsart), run the citation audit as for the HC paper, submit to Hexagon.

## 2. Theorem S: a sparsification lower bound in the clause width

**Statement** (`research/sat-width.md`): there is a k-CNF such that any cover by 2^{εn} CNFs of width ≤ k′ on the
same variables has an output with log₂(m/n) ≥ k(1−ε) − log₂(k(k′·log₂2n + 2)) − 3. Hence sparsification with
clause density poly(k/ε) is impossible once k ≳ 4c·loglog n. No prior lower bound on the k-dependence was
found (Santhanam–Srinivasan treat unbounded width; Calabro's thesis §5.1 leaves density O(2^k) open).

**To do:**
1. Independent referee pass (Shearer, union bound, reverse-Markov step; the model of "cover").
2. Literature check beyond the two sources above (2012–2026 work on sparsification limits).
3. Lean: needs Shearer's inequality, which Mathlib lacks (the earlier estimate was well over 800 lines).
   Decide: formalise, or publish as a written proof labelled not machine-checked.
4. Either a standalone short note or a section of the barrier paper.
