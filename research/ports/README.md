# The ports question: what was found on 26 November 2026

This folder studies one question raised by the two machine-assisted papers of November 2026: Anthropic's "VP ≠ VNP over
every field" (dichotomy: *flat* or *contracting*) and OpenAI's release of 24 November (hypothesis: *ports*).

**Everything here is machine-generated and has not been read by a human mathematician.** Both source papers are
machine-generated and not human-refereed. We have not built either lab's Lean development. Read every claim with its
status tag.

Status tags: **[L]** proved in our Lean (compiles, no `sorry`); **[V]** passed one adversarial review by a separate
agent; **[N]** computed; **[N‑rig]** rigorous computation with a checkable certificate; **[D]** derived, not reviewed;
**[C]** conjecture; **[X]** dead.

## Results

| # | Statement | Status | Where |
|---|---|---|---|
| 1 | **Theorem R.** If the contracting hypothesis holds over a field of characteristic 0, then 3-SAT is decidable in time 2^{O(n^{1−δ})}, δ < 187/(5H+187). Uses Anthropic's paper only. | [V] in the form with polynomial advice; uniform by an audit of the Lean proof terms (one reader); exponent arithmetic [L] | `rebase/notebook.md`, `review-theoremR.md`, `review-uniformity.md`, `lean/PortsLean/ThmR.lean` |
| 2 | **Theorem A.** Contracting over k ⇒ ports in the characteristic of k (⇒ fast 3-SAT in characteristic 0 by OpenAI's theorem). | [V]; the deduction is [L] conditional on four statements copied from the labs' Lean | `ideas-ports.md`, `review-theoremAB.md`, `lean/PortsLean/ThmA.lean` |
| 3 | **Corollary.** Under the weak exponential-time hypothesis, contracting fails and the flat hypothesis holds over every field of characteristic 0. | follows from 1 or 2 | `note-contracting-eth.md` |
| 4 | **Characteristic p.** Ports or contracting in characteristic p ⇒ randomised one-sided 3-SAT in 2^{O(v^{1−δ})}. | [V]; hash and isolation lemmas [L] | `c1d1/notes.md`, `review-c1.md`, `lean-c1/` |
| 5 | **Theorem K.** On the network K_{2,3} the asymptotic tensor (restriction) rate is ≥ 3/√10 ≈ 0.9487 over every field (routing: 3/4), and equals 3/√10 whenever contracting fails. | [V]; one six-variable inequality [N‑rig], verified by two checkers in different arithmetic libraries | `note-k23-rate.md`, `hull/notes.md`, `review-hull.md`, `review-fivepoint.md`, `../../tools/ivcert`, `../../tools/ivcheck2` |
| 6 | **Explicit protocols.** An explicit asymptotic protocol family on K_{2,3} with rate ≥ 0.8367 (limit 6/(4+√10) ≈ 0.8377 under one numerical claim). Smallest instances have wire dimension ≈ 2¹²⁸. | [V]; game bound exact ([N‑rig]); two-bucket case [L] | `protocol/notes.md`, `review-protocol.md`, `protocol/certificates/` |
| 7 | **Ports vs contracting.** "Ports ⇒ contracting" (for Anthropic's class of prices) holds iff a statement (GE) about bounded-degree graphs and matrices over F₂ fails. Kernel lemma: 2^{−rank(a−b)} is positive semidefinite, with a spectral threshold. Cayley graphs of SL₃(F₂[x]/(p)) are not port families if contracting fails. | reduction and lemmas [V]; kernel lemma and spectral inequality [L]; (GE) itself open [C] | `middle/notes.md`, `review-middle.md`, `lean/PortsLean/RankKernel.lean`, `middle/experiments.md` |

Not claimed anywhere: that contracting holds or fails; that ports holds or fails; any unconditional algorithm or lower
bound for SAT.

## Two draft notes

- `note-contracting-eth.md` — results 1–4, with dependency tables.
- `note-k23-rate.md` — results 5–6, self-contained.

Neither has been posted. `literature-check.md` (if present) records a novelty check.

## Code

| Tool | What it is | Checks |
|---|---|---|
| `lean/` (12 files) and `lean-c1/` (4 files) | Lean 4.36 + Mathlib projects | `lake build` succeeds; no `sorry`, no added axioms |
| `../../tools/ivcert` | Rust interval branch-and-bound with certificates and a checker | `run_proofs.sh` |
| `../../tools/ivcheck2` | Independent checker (Python + Arb) | `run_all.sh` |
| `../../tools/tensorlab` | Rust library with Python bindings: metric optimisation, model spaces, restriction search, rank placements over F₂ | `cargo test` |
| `protocol/certificates/verify.py` | Exact-fraction verifier for the protocol game | `python3 verify.py cert_B*.json` |

## Known weak points

1. Theorem R's guess-count lemma is read from the printed proof of Anthropic's Thm J.3 and from their Lean source; it
   is machine-checked only on a verbatim copy of their machine model (`lean/PortsLean/ANFragment/`), not against their
   built development.
2. Theorem A's 3-SAT conclusion depends on OpenAI's unreviewed chain (HC 13.1 → IM 7.1).
3. Theorem K's lower bound depends on Anthropic's CAT(0) theorem for prices (their Lean, not built by us) and on a
   hand-checked reduction and calibration (one referee, two numerical tests).
4. The numerical searches for protocols and for rank placements are weak; their null results carry little weight
   (see `e3/notebook.md`, `middle/experiments.md`).
5. Novelty has not been established for any item.

Dated working log: `../next/LOGBOOK.md`.
