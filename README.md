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
| R2 | **Exact, deterministic counting of Hamiltonian cycles in subexponential time:** for every δ > 0, `2^{δn}` when \|E\| ≤ Dn (the paper also proves the single-algorithm rate `2^{O(max(m,n)/√log n)}`). Gives deterministic existence and search. | **Formally verified in Lean, end to end** (the subexponential bound): `EthFollowup.ExactHC.theorem1` — for every δ > 0 and D, a Turing machine outputs #HC(G) in binary within ⌊C·2^{δn}⌋ steps on every graph with \|E\| ≤ D·n — built on Anthropic's Lean proof, standard axioms only (`lean-bridge-anthropic/`). The sharper `2^{O(n/√log n)}` rate is proved in the paper; its Lean formalisation is in progress. Written proof: [`research/exact-hc-theorem.md`](research/exact-hc-theorem.md). Independent AI referee: sound. **Not yet reviewed by human experts.** |
| R3 | The same template gives directed HC, TSP with poly weights, Steiner tree, FVS, forests / Tutte T(x,1), longest path, k-leaf spanning trees, and others. | Conditional on R2. Checked numerically (`research/exact-extensions.md`, `research/meta-theorem.md`). |

Work done by Vaibhav Tulsyan with AI assistance (Claude Code). The Lean parts are machine-checked.

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

