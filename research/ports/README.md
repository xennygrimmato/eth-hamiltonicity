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
| 5 | **Theorem K.** On the network K_{2,3} the asymptotic tensor (restriction) rate is ≥ 3/√10 ≈ 0.9487 over every field (routing: 3/4), and equals 3/√10 whenever contracting fails. The instance is the Okamura–Seymour example, where classical network coding also gives only 3/4 (Harvey–Kleinberg–Lehman 2006, Thm 27); the models differ (tensor restriction vs classical coding). | [V]; its six-variable inequality (CL\*) is now proved by hand (Theorem D) and in Lean [L]; the interval certificates [N‑rig] are a confirmation only. Extends to K_{2,m} with a weight w on u₁u₂ (Theorem K_m) | `note-k23-rate.md`, `hull/notes.md`, `k2m/notes.md`, `review-hull.md`, `review-fivepoint.md`, `review-k2m.md`, `lean/PortsLean/CLStar.lean`, `../../tools/ivcert`, `../../tools/ivcheck2` |
| 6 | **Explicit protocols.** An explicit asymptotic protocol family on K_{2,3} with rate ≥ 0.8367 (limit 6/(4+√10) ≈ 0.8377 under one numerical claim). Smallest instances have wire dimension ≈ 2¹²⁸. | [V]; game bound exact ([N‑rig]); two-bucket case [L] | `protocol/notes.md`, `review-protocol.md`, `protocol/certificates/` |
| 7 | **Ports vs contracting.** "Ports ⇒ contracting" (for Anthropic's class of prices) holds iff a statement (GE) about bounded-degree graphs and matrices over F₂ fails. Kernel lemma: 2^{−rank(a−b)} is positive semidefinite, with a spectral threshold. Cayley graphs of SL₃(F₂[x]/(p)) are not port families if contracting fails. | reduction and lemmas [V]; kernel lemma and spectral inequality [L]; (GE) itself open [C] | `middle/notes.md`, `review-middle.md`, `lean/PortsLean/RankKernel.lean`, `middle/experiments.md` |
| 8 | **Cut regime (Theorem E).** With weight w on the u₁u₂ demand, f*(K_{2,3}(w)) = 3/(2+w) = the cut bound over every field, unconditionally (no hypothesis on contracting), for w ≥ w₀; likewise f*(K_{2,4}(w)) = 4/(4+w) for w ≥ 2w₀. Routing: 3/(3+w). Example w = 2: 3/4 against 3/5. For 1 < w < 5/4 only bounds are known | three levels: (a) w₀ = 1.9134 (root of 4λ³−8λ²+9λ−4 via λ = 3/(2+w)): hand proof, [V]; (b) w₀ = 4/3: (a) + one interval certificate S(9/10) [N‑rig]; (c) w₀ = 5/4: + certificate (CL\*\*₀), i.e. 13Σ_S ≥ 12Σ_vv + 15D [N‑rig]. Certificates checked by two checkers, but both encodings written by one author; implications [V] | `note-k23-rate.md` §4.4, `k2m/notes.md` §5, `review-thmE.md`, `ivcert-notes.md` §5 |
| 9 | **Multiplicative complexity 7.** Over F₂, the 2×2 matrix product needs exactly 7 AND gates in XOR-AND circuits (Strassen's 7 is optimal). | [N‑rig]: two independent methods (exact search; SAT with 1080 cubes, every LRAT proof checked by `lrat-check`), re-run independently by the project lead with identical hashes. The lower bound 6 was already public; exactly 7 appears new | `../../tools/mc222/README.md` |

Not claimed anywhere: that contracting holds or fails; that ports holds or fails; any unconditional algorithm or lower
bound for SAT.

## Two draft notes

- `note-contracting-eth.md` — results 1–4, with dependency tables.
- `note-k23-rate.md` — results 5, 6 and 8, self-contained.

Neither has been posted. `literature-check.md` records the literature and novelty check of 26 November 2026.

## Code

| Tool | What it is | Checks |
|---|---|---|
| `lean/` (14 files) and `lean-c1/` (4 files) | Lean 4.36 + Mathlib projects | `lake build` succeeds; no `sorry`, no added axioms |
| `../../tools/ivcert` | Rust interval branch-and-bound with certificates and a checker | `run_proofs.sh`; `run_k2.sh all` (result 8, ≈ 40 min) |
| `../../tools/ivcheck2` | Independent checker (Python + Arb) | `run_all.sh`; `run_k2.sh` (result 8, ≈ 90 min) |
| `../../tools/mc222` | Exact circuit search (Rust) and SAT + LRAT pipeline for result 9 | `run_all.sh` |
| `../../tools/tensorlab` | Rust library with Python bindings: metric optimisation, model spaces, restriction search, rank placements over F₂ | `cargo test` |
| `protocol/certificates/verify.py` | Exact-fraction verifier for the protocol game | `python3 verify.py cert_B*.json` |

## Known weak points

1. Theorem R's guess-count lemma is read from the printed proof of Anthropic's Thm J.3 and from their Lean source; it
   is machine-checked only on a verbatim copy of their machine model (`lean/PortsLean/ANFragment/`), not against their
   built development.
2. Theorem A's 3-SAT conclusion depends on OpenAI's unreviewed chain (HC 13.1 → IM 7.1).
3. Theorem K's lower bound depends on Anthropic's CAT(0) theorem for prices (their Lean, not built by us; OpenAI's EG
   Thm 4.3 is an independent alternative source) and on
   Strassen duality (not formalised). The reduction and calibration are now in Lean (`lean/PortsLean/FivePoint.lean`:
   the weighted five-point inequality from one comparison hypothesis, which is our transcription of their Lemma C.4(a)).
4. Result 8 at levels (b), (c) rests on interval certificates whose two encodings (prover side and Arb checker) were
   written by the same author; a bug in the checker's new code was found by a mutation test and fixed before the
   reported runs. The certificates are not refereed. Level (a) is hand-proved and refereed, but not in Lean. Like
   Theorem K, all levels use Anthropic's CAT(0) theorem for prices.
5. The numerical searches for protocols and for rank placements are weak; their null results carry little weight
   (see `e3/notebook.md`, `middle/experiments.md`).
6. Novelty (`literature-check.md`, 26 Nov 2026): Theorem R, Corollary 1, Theorem K, 3/√10, 6/(4+√10) and M2 not found before.
   Partly anticipated: Theorem A (OpenAI EG §11.1, Grassmannian gap ⇒ ports). Standard: Lemma K, Prop. S; K_{2,3} is Okamura–Seymour.

Dated working log: `../next/LOGBOOK.md`.
