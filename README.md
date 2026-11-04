# Hamiltonian cycles after the ETH refutations

Follow-up work to the claimed refutations of the Exponential Time Hypothesis by OpenAI
([openai/math](https://github.com/openai/math)) and Anthropic
([anthropics/formal-math](https://github.com/anthropics/formal-math), folder `eth`). Both were posted
on 26 Oct 2026 and are still under expert review. All results are for sparse graphs (|E| = O(n)),
asymptotic only, and conditional on those refutations.

**Paper (PDF):** [`docs/exact-hc-paper.pdf`](docs/exact-hc-paper.pdf), LaTeX source in `paper/`.

| | Result | Status |
|---|---|---|
| R1 | Parity of the number of Hamiltonian cycles, deterministically, in subexponential time. Randomized decision. Directed versions. | **Machine-checked in Lean** on top of both labs' Lean proofs, which we rebuilt and re-checked from source (`lean/`, `lean-bridge/`, `lean-bridge-anthropic/`). Only the standard axioms are used. |
| R2 | **Exact, deterministic counting of Hamiltonian cycles in subexponential time:** for every δ > 0, `2^{δn}` when \|E\| ≤ Dn (the paper also proves the single-algorithm rate `2^{O(max(m,n)/√log n)}`). Gives deterministic decision, search (output a Hamiltonian cycle) and Hamiltonian paths — **machine-checked** (`decision_TM`, `search_TM`, `hamPaths_*_TM` and `_rate` versions, `Corollaries.lean`, `Paths.lean`). | **Formally verified in Lean, end to end** (both bounds): `EthFollowup.ExactHC.theorem1` — for every δ > 0 and D, a Turing machine outputs #HC(G) in binary within ⌊C·2^{δn}⌋ steps on every graph with \|E\| ≤ D·n — built on Anthropic's Lean proof, standard axioms only, and re-checked by a fresh `leanchecker` kernel replay of the whole dependency closure (`lean-bridge-anthropic/`). The sharper rate is `EthFollowup.ExactHC.theorem2`: one Turing machine outputs #HC(G) within ⌊C·2^{C(m+n)/√log₂(n+2)}⌋ steps for every graph G with m edges, i.e. `2^{O(n/√log n)}` when m = O(n). Same axioms; a fresh `leanchecker` replay of its full closure also passed. Written proof: [`research/exact-hc-theorem.md`](research/exact-hc-theorem.md). Independent AI referee: sound. **Not yet reviewed by human experts.** |
| R2w | **Sparse TSP, exact, deterministic, in `2^{δn}·poly(W)` for every δ > 0** on graphs with \|E\| ≤ Dn and integer weights ≤ W (so subexponential for all W = 2^{o(n)}); the output also gives the number of tours of every weight and the number of optimal tours. | **Formally verified in Lean, end to end**: `EthFollowup.ExactHC.theoremTSP` and `theoremTSP_decode` (`lean-bridge-anthropic/bridge/EthFollowup/ExactHC/TSP.lean`), standard axioms only, and a fresh `leanchecker` replay of its full closure passed. Does **not** cover dense/metric TSP (Held–Karp's 2^n stands there) or weights 2^{Θ(n)}; see `research/tsp-theorem.md`. |
| R2d | **Exact #HC in 2^{O(n log d̄/√log n)} for average degree d̄** (so also max degree Δ): subexponential whenever log d̄ = o(√log n), far beyond the bounded-density regime of R2. Neighbouring blobs share the *rank* of their set of used crossing edges instead of one label per edge. | **Formally verified in Lean** (`theorem3`: one machine, ⌊C·2^{C·n·log₂(2m/n+2)/√log₂(n+2)}⌋ steps on every graph; `theorem3_maxdeg` with log₂(Δ+2)), standard axioms only; files `Unrank`, `PairCode`, `VertexBalanced`, `RankNetwork`, `RankProcs`, `DegTableProc`, `RankWordProcs`, `Theorem3`, `DPackage`. Written proof `research/hc-degree-theorem.md`; independent AI referee: sound. Dense graphs (d̄ ≈ n) still not covered. |
| R3 | **Directed HC and ATSP, machine-checked:** exact #DHC of sparse digraphs in 2^{δn} (`theoremDHC`) and in 2^{O((m+n)/√log n)} for all digraphs (`theoremDHC_rate`); ATSP with weights ≤ W in 2^{δn}·poly(W), with the count of tours of every weight, the optimum and the number of optimal tours (`theoremATSP`, `theoremATSP_decode`). Proved by vertex splitting onto the verified undirected machines (`VertexSplit.lean`, `DirectedTheorems.lean`); the directed matrix-tree / blob layer is also formalised (`Directed*.lean`). *Conjectured, not claimed:* graphic TSP, Steiner tree, FVS, forests / Tutte T(x,1), longest path, k-leaf spanning trees, ATSP in explicit-rate form. | Machine-checked rows: standard axioms only. Everything in the conjectured list: identities checked numerically only (`research/exact-extensions.md`, `research/meta-theorem.md`, `research/tsp-theorem.md`). |
| R4 | **Exact counting of Eulerian circuits** (Kotzig's transition systems, i.e. closed Euler trails up to rotation and reversal; #P-complete, Brightwell–Winkler 2005): for every δ > 0 and Δ, a machine counting them on graphs of maximum degree ≤ Δ in time (n+2)^C·2^{δm} (2^{δm} when G has no isolated vertex), and one machine for all graphs in (n+2)^C·2^{C·m·log₂(Δ+2)/√log₂(m+2)}, assuming Anthropic's #3-SAT theorem. Reduction: #HC of the line graph of the double subdivision (Kotzig; the bijection is classical, the subexponential count and its verification are new). | **Formally verified in Lean** (`theoremEuler`, `theoremEuler_noIso`, `theoremEuler_rate`; `lean-bridge-anthropic/bridge/EthFollowup/ExactHC/EulerTheorems.lean`, pure part `lean/EthFollowup/ExactHC/EulerSplit.lean`), standard axioms only, fresh `leanchecker` replay of the closure of `EthFollowup.ExactHC.EulerTheorems` passed (4 Nov 2026). The Mathlib-walk bridge is not formalised; `eulerCircuitsAll` is the formal object. |
| Q | **Exact quantum circuit amplitudes** in 2^{O(G/√log G)} (G two-qubit gates, any connectivity, Clifford+T): one Turing machine outputs ⟨y\|C\|x⟩ exactly as (a₀+a₁ω+a₂ω²+a₃ω³)/√2^k. | **Formally verified in Lean** (`amplitude_TM`, `amplitude_TM_rate`, `amplitude_TM_rate'`; `lean/EthFollowup/Quantum/`, `lean-bridge-anthropic/bridge/EthFollowup/Quantum/`), standard axioms, fresh `leanchecker` replays passed. Note: `docs/quantum-note.pdf` (polynomial-space variant and marginals/sampling corollaries: written proof only, not claimed). |
| C | **Machine-checked superlinear circuit lower bound:** some language in E^NP has no Boolean circuits of size ε·n·√log n for infinitely many n (full binary basis), assuming Anthropic's #3-SAT theorem. The statement is OpenAI's Corollary 1.4 (preprint revised 25 Oct 2026, proved on paper there); what is ours is the machine-checked proof on Anthropic's development, which strengthens the O(n) bound Anthropic formalised. | **Formally verified in Lean** (`enp_not_size_n_sqrt_log`, `lean-bridge-anthropic/bridge/EthFollowup/Circuits/`) on Anthropic's CircuitLowerBound module, standard axioms, fresh `leanchecker` replay passed. Note: `docs/circuit-note.pdf`. |
| F | **Deterministic factoring in time 2^{O(n/√log n)}** (independent second proof): one finite-alphabet Mathlib Turing machine outputs Nat.minFac N within ⌊C·2^{C·n/√log₂(n+2)}⌋₊ steps for every N (n = bit length), assuming Anthropic's #3-SAT theorem; hence Rudich–Rousseau's `SqrtLogLogConjecture` in their verbatim definitions. An earlier Lean proof of the same statement exists (github.com/1337isnot1337/integer-factoring, 30 Oct 2026; Shunia hexagon:2610.00711 on paper); ours uses a different network (2D Schönhage–Strassen over ℤ/(2^J+1)). | **Formally verified in Lean** (`EthFollowup.Factoring.minFac_TM_rate`, `EthFollowup.Factoring.sqrtLogLog`, `RR.Factoring.subexponentialRate`; `lean-bridge-anthropic/bridge/EthFollowup/Factoring/Final.lean`, pure parts in `lean/EthFollowup/Factoring/`), standard axioms only, fresh `leanchecker` replay of the closure of `EthFollowup.Factoring.Final` passed (4 Nov 2026). Paper: `docs/factoring-note.pdf`. |
| N1 | **Class numbers of imaginary quadratic fields in time \|D\|^{o(1)}**: one finite-alphabet Mathlib Turing machine outputs the number of reduced forms of discriminant −N (Gauss's form class number, Cox's conventions) within ⌊C·2^{C·n/√log₂(n+2)}⌋₊ steps, n the bit length of N, assuming Anthropic's #3-SAT theorem; for fundamental discriminants this is the number of primitive reduced forms. Previous unconditional deterministic bound \|D\|^{1/2+o(1)} (\|D\|^{1/5+ε} under GRH). The equality with the ideal class number (Dirichlet–Dedekind) is classical and not formalised; real quadratic fields are not covered. | **Formally verified in Lean** (`EthFollowup.ModP.hForm_TM_rate`, `hFormPrim_TM_rate`; `lean-bridge-anthropic/bridge/EthFollowup/ModP/Final.lean`), standard axioms only, fresh `leanchecker` replay of the closure of `EthFollowup.ModP.Final` passed (4 Nov 2026). Paper: `docs/classnumber-note.pdf`. |
| N2 | **Square roots modulo any m and the least quadratic non-residue modulo a prime, in time 2^{O(n/√log n)}**: the least y < m with y² ≡ a (mod m), or m if none, for every m and a; and the least non-residue for every prime p (previous unconditional deterministic bound p^{1/(4√e)+o(1)} via Burgess 1957), assuming Anthropic's #3-SAT theorem. | **Formally verified in Lean** (`EthFollowup.ModP.sqrtMod_TM_rate`, `lqnr_TM_rate`), same file, axioms and replay as N1. |
| N3 | **Exact divisor sums Σ_{m≤x} τ(m), Σ_{m≤x} σ(m) and the Gauss circle count #{a²+b² ≤ x} in time x^{o(1)}**, assuming Anthropic's #3-SAT theorem (previously about x^{1/3}). | **Formally verified in Lean** (`EthFollowup.ModP.divisorSum_TM_rate`, `sigmaSum_TM_rate`, `circle_TM_rate`), same file, axioms and replay as N1. |
| P1 | **The parity of the prime-counting function in time x^{o(1)}**: one finite-alphabet Mathlib Turing machine outputs π(x) mod 2 within ⌊C·2^{C·n/√log₂(n+2)}⌋₊ steps (n the bit length of x), and another outputs the parity of the number of primes in any interval [A, B], assuming Anthropic's #3-SAT theorem. Previously x^{1/2−c} for intervals of length ≤ x^{1/2+c} (Tao–Croot–Helfgott 2012) and x^{1/2+o(1)} for π(x) itself (Lagarias–Odlyzko). Key lemma: chains d₁² | n, d₂² | d₁, … counted mod 2 give [n squarefree]. Does not give prime finding or the exact π(x). | **Formally verified in Lean** (`EthFollowup.Primes.piParity_TM_rate`, `piIntervalParity_TM_rate`; lemmas `chainCount_mod_two`, `primeParity` in `lean/EthFollowup/Primes/ChainParity.lean`; leveled network library in `lean-bridge-anthropic/bridge/EthFollowup/Primes/`), standard axioms only, fresh `leanchecker` replay of the closure of `EthFollowup.Primes.Final` passed (4 Nov 2026). Paper: `docs/parity-note.pdf`. |
| B | **Barrier study (the dense permanent).** Informal research notes giving evidence that the engine does not reach dense counting problems (Anthropic's rate tight for its family of "pieces", every known permanent network needs Θ(n log n) shared bits, row-local lower bounds). | **Machine-checked core lemmas** (`lean/EthFollowup/Barriers/`, 38 theorems, standard axioms): cut/rank bound, row-cut rank = C(n,k) for the permanent (barrier.md Lemma 3.2) and the abstract Model-R bound U ≥ n·log₂(n/s) (Thm 6.1, with the rank step as hypothesis), triangular rank bound (parity-barrier Thm 1), spread lemma (rho-lower-bound Thm 3.3, abstract form), derandomization bound t_p ≤ log₂#S (derandomization.md Thm 1), algebra-rank bound C(n,n/2) (wild-ideas F2), per ≡ 0 mod p for low rank, colouring barrier (paper Prop. on colourings, graph level: `colouring_barrier_graph`), and the turn-labelling lower bound `Kstar.theoremL` (`KstarLower.lean`: on the degree-3 crossing grid H_t every good k-bit turn labelling has t < 2^(20k+10), so k* ≥ (log₂ t − 10)/20; research/kstar.md Theorem L). Also `Decorrelated.rankSum_ge` (`DecorrelatedRank.lean`: any decomposition F⊗F = Σ T_t over two rectangles, with arbitrary coupling terms, has D² ≤ Σ_t min(rank_row T_t, rank_col T_t), so correlated decompositions of two rectangles cannot beat ρ = 1/2; research/engine2-decorrelated.md Theorem 1), the iterated-product tree bound `IterProd.BTree.cost_ge_entropy` (`IterProdTree.lean`: any binary multiplication tree with leaf sizes ℓᵢ has cost ≥ Σ ℓᵢ log₂(W/ℓᵢ), = n log₂ k for equal sizes; the link from network size to tree cost is on paper, research/iterated-product.md) and the cut rank of the product indicator `IterProd.rank_prodMat_pow` (`IterProdCutRank.lean`), `Grid33.rankSum_ge` (`DecorrelatedGrid33.lean`: on the full 3×3 grid level, N⁸ ≤ Σ_t min(rank_rowcut, rank_colcut), with the general lossy-flattening lemma `Lossy.rank_contr_le`; N⁹, which would make ρ = 1/2 optimal, is open and every flattening argument provably stops at N⁸, research/engine2-decorrelated.md §8), and `Grid32.rankSum_ge` (`DecorrelatedGrid32.lean`: the same for three rectangles on one column pair, N³ ≤ Σ_t min(rank_rowcut, rank_colcut); Theorem 4). Everything else in `research/permanent/` is informal and **not claimed**. |

**Published:** the Hamiltonian-cycle paper is on Hexagon as [hexagon:2610.00672v1](https://hexagonmath.org/abs/2610.00672v1).

**Claim policy.** We claim as theorems only statements that are machine-checked in Lean (standard axioms, fresh `leanchecker` replay). Anything else in this repository — rows marked *conjectured* or *not claimed* above, the extensions section of the paper, and every statement in `research/` that is not tagged [Lean] — is an informal note, not a claim. All theorems stated in the paper are machine-checked. Audit (29 Oct 2026): `lean-bridge-anthropic/bridge/EthFollowup/ExactHC/AuditAll.lean` prints the axioms of all 27 theorems built on Anthropic's development (incl. the quantum amplitude and circuit lower bound theorems) and `lean/EthFollowup/Axioms.lean` + `AxiomsExtended.lean` those of 60 further theorems — every one exactly `[propext, Classical.choice, Quot.sound]` — and fresh `leanchecker --fresh` replays of `EthFollowup.ExactHC.AuditAll` (Anthropic's toolchain) and `EthFollowup.AxiomsExtended` (repo toolchain) both passed.

Work done by Vaibhav Tulsyan with AI assistance (Claude Code). The Lean proofs were written by AI agents and reviewed by an AI coordinator; they are machine-checked, but no human has yet verified that the formal statements match the printed theorems. The results are corollaries of the claimed ETH refutations and stand or fall with them. See the paper's *Limitations* section.

---

# lean-code

Research notes and Lean artifacts building on OpenAI's claimed refutation of the Exponential Time
Hypothesis (openai/math, 26 Oct 2026). Branch `eth-followup`.

## Contents

- `findings.md` — the research memo. Task 1 (how the hidden constants depend on the clause width
  `k`, and for which `k = k(n)` the method survives) is the gatekeeper; Tasks 2–6 cover easy
  corollaries, proof complexity, the √log n barrier, the circuit-lower-bound moonshot, and
  neighbouring problems. Every claim is tagged `[Lean]`, `[Paper]`, or `[Mine]`.
- `hamiltonicity.md` — new result: Hamiltonian Cycle on sparse graphs in subexponential time
  (parity deterministically, decision with randomness), via Cut&Count plus the OpenAI counter.
- `lean/` — a Lean 4 project pinned to the same Lean toolchain (`v4.34.1`) and Mathlib commit
  (`d13f23b7`) as openai/math.
  - `EthFollowup/Comparator.lean` — verbatim copy of openai/math's comparator statement
    (`lean/ComparatorChallenges/SubexponentialSAT.lean`, commit `7ef5c0cc`), with the `sorry`'d
    theorem turned into the proposition `ExactCountAndSatStatement`.
  - `EthFollowup/IndependentSet.lean` — encodings of a graph as a 2-CNF, proofs that satisfying
    assignments biject with independent sets / vertex covers, and the derived subexponential
    counting theorems (conditional on the upstream theorem, passed as a hypothesis).
  - `EthFollowup/CNFKit.lean` — generic local-constraint → CNF encoding and count-preserving
    relabelling.
  - `EthFollowup/HamiltonianParity.lean` — the Cut&Count CNF, the identity
    `#cutCNF ≡ #HamiltonianCycles (mod 2)`, and the derived subexponential parity machine.
  - `EthFollowup/HamiltonianAllGraphs.lean` — the same for every graph (counter encoding, width 5).
  - `EthFollowup/HamiltonianIsolation.lean` — the count restricted by any edge CNF (for isolation-based
    decision).
  - `EthFollowup/IsolationLemma.lean` — the Calabro–Impagliazzo–Kabanets–Paturi isolation lemma
    for arbitrary finite sets, in counting form.
  - `EthFollowup/HamiltonianDecision.lean` — randomized decision of Hamiltonicity: soundness,
    completeness with an explicit success fraction, and the machine.
  - `EthFollowup/IsolationAnalysis.lean`, `EthFollowup/HamiltonianDecisionFraction.lean` — the
    analytic estimate: success probability `exp(−δ|E|)` for every `δ > 0`.
  - `EthFollowup/HashCNF.lean`, `EthFollowup/DirectedHamiltonianDecision.lean` — generic hash CNFs
    and the directed decision procedure.
  - `EthFollowup/DirectedHamiltonianParity.lean` — the same for directed Hamiltonian cycles.
  - `EthFollowup/Examples.lean` — evaluated sanity checks (not in the default build).
  - `EthFollowup/Axioms.lean` — `#print axioms` audit.

- `lean-bridge/` — builds openai/math's own Lean proof from source (`setup.sh` fetches it at the
  pinned commit) and instantiates the conditional theorems above with `exact_count_and_sat`,
  making them unconditional (`bridge/EthFollowup/Unconditional.lean`). **Built and checked;**
  see *Independent verification* below.

## Building

```
cd lean
lake exe cache get   # Mathlib oleans
lake build
```

```
cd lean-bridge
./setup.sh           # sparse-fetch openai/math at 7ef5c0cc into ./OAI
lake exe cache get
lake build           # ≈11.5k jobs; see notes below
```

## Independent verification (27 Oct 2026)

I built openai/math's Lean development from source at commit `7ef5c0cc` (Lean `v4.34.1`, Mathlib
`d13f23b7`), target `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final`, and then the bridge on
top of it.

* **Upstream build:** `Build completed successfully (11492 jobs)`, with no errors. The fetched
  `OAI/` tree has no occurrence of `sorry`. `#print axioms` (upstream `Final.lean`, lines
  197–201) reports exactly `[propext, Classical.choice, Quot.sound]` for
  `exact_count_and_sat`, `exact_count_eth`, `sat_polynomial_space`, `original_sat_main` and
  `compiled_exact_count_and_sat`. That means no `sorryAx`, no `Lean.ofReduceBool`
  (`native_decide`), and no custom axioms.
* **Statement check:** the upstream `exact_count_and_sat` statement is textually identical to
  the body of `ExactCountAndSatStatement` (the comparator challenge).
  `bridge/EthFollowup/Comparator.lean` restates it over the upstream definitions and proves it
  with `exact exact_count_and_sat k hk`.
* **Bridge build:** `Build completed successfully (11507 jobs)`. `#print axioms` reports only
  `[propext, Classical.choice, Quot.sound]` for `indepSet_count_subexponential_unconditional`,
  `hamParity_allGraphs_unconditional`, `hamParity_unconditional`, `dirHamParity_unconditional`,
  `hamIso_unconditional`, `hamDecision_unconditional` and `dirHamDecision_unconditional`. Their
  types are closed statements with no ETH hypothesis left; `#check` confirms this.
* **Kernel replay:** `leanchecker EthFollowup.Unconditional
  OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final` exits 0.
  `leanchecker --fresh EthFollowup.Unconditional` re-checks every declaration in the full import
  closure (Mathlib, the upstream `OAI` tree and the bridge) in a fresh kernel environment. It also
  exits 0.

Notes for reproducing on a small machine (4 cores, 15 GB RAM, about 40 GB of disk):

* Lake has no job limit, and two modules, `SqrtLogSpace.HighQueryLoop` and
  `SqrtLogSpace.HighQueryTraversal`, were killed for running out of memory (exit 137) when built
  alongside others. Building each one alone (`lake build +<module>`) and then rerunning the full
  build works.
* Lake writes a 6 MB `*.setup.json` file per module under `.lake/build/ir` (about 15 GB in
  total). These are regenerated on every compile and can be deleted once a module is built.
* One proof (`IndependentSet.lean`) had to be rewritten for the bridge. Upstream `SAT.lean`
  carries extra `@[simp]` lemmas (`Literal.eval_eq_true`, …) that the vendored comparator copy
  lacks, and they changed the simp normal form. The new proof goes through `CNF.eval_iff` and
  builds in both settings.

