# Submitting to Hexagon (hexagonmath.org): guide and form answers

Source of the rules: hexagonmath.org/about and the public submission schema
(hexagonmath.org/api/v1/openapi.json, `SubmissionMetadata`), read on 30 Oct 2026.

## What Hexagon requires (summary)
- Sign in with an ORCID iD. The submitter must be one of the contributors. AI systems cannot be
  contributors (tools are listed separately).
- Upload **TeX source** (ZIP ≤ 100 MiB). Choose exactly one main `.tex` file. The source must compile
  without error (automated screening + a human moderator during the beta, ~48 h on weekdays).
- **No code in the submission** (Lean included). Formalizations may be linked only on allowlisted hosts
  (Mathlib, Palomar, Prove2.me, Tau Ceti); our Lean lives on GitHub, so it is cited inside the paper
  instead and the "formalizations" field stays empty.
- New accounts: **one deposit per UTC day**. Plan: HC paper on day 1, quantum note on day 2.
- Declarations you make as submitter (these are yours to decide — see "Your decisions" below):
  correctness believed, of interest to the community, good-faith citations, rights to distribute,
  how much a human has checked and understood, and the text origin.
- Licence options: CC BY 4.0, CC BY-SA 4.0, CC0 1.0.
- Optional: supplementary AI-use material (prompts, transcripts). Optional: arXiv id of the same work.

## Paper 1 — Hamiltonian cycles (upload `submission/hexagon/hexagon-hc-paper.zip`, main file `main.tex`)
- **Title** (≤ 240 chars): Counting Hamiltonian cycles in sparse graphs in subexponential time, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-hc.txt`.
- **Primary subject:** cs.DS. **Cross-lists:** cs.CC, math.CO, cs.LO.
- **MSC2020** (≤ 5, all checked against Hexagon's catalogue): 68Q25, 05C45, 05C30, 68W40, 03B35.
- **Tags** (≤ 12): Hamiltonian cycle; exact counting; Exponential Time Hypothesis; matrix-tree theorem;
  Grassmann algebra; Cut&Count; travelling salesman problem; Lean 4; formal verification; fine-grained complexity.
- **Tools used:** Claude (Anthropic), via Claude Code (you may add the model names shown in your session);
  Lean 4 with Mathlib; Python (exact-arithmetic checks); TeX Live.
- **Formalizations:** none (GitHub is not an allowlisted host; the repository is cited in the paper).
- **arXiv id:** none (unless you post there too).

## Paper 2 — Quantum circuits (upload `submission/hexagon/hexagon-quantum-note.zip`, main file `main.tex`)
- **Title:** Exact amplitudes of sparse quantum circuits in subexponential time, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-quantum.txt`.
- **Primary subject:** quant-ph. **Cross-lists:** cs.CC, cs.DS.
- **MSC2020:** 81P68, 68Q12, 68Q25, 68Q17, 03B35.
- **Tags:** quantum circuit simulation; strong simulation; Clifford+T; quantum supremacy; fine-grained
  complexity; Exponential Time Hypothesis; tensor networks; Lean 4; formal verification.
- **Tools / formalizations / arXiv:** as for paper 1.

## Your decisions (the form asks you to declare these; I have not filled them in for you)
1. **Human understanding** — `all` / `some` / `none`: "whether all, some, or none of the contribution
   has been checked and understood by a human at submission time." Choosing `some` requires a
   provenance statement; a draft is in `provenance.txt` (edit it to be true for you). Note: Lean
   machine-checking is not human understanding; the honest answer depends on what you yourself have
   read and understood.
2. **Text origin** (`authorshipMode`) — primarily AI-generated / mixed / primarily human-written. The
   text of both papers was drafted by Claude in sessions you directed; "primarily AI-generated" is the
   accurate description unless you have rewritten parts. This is a text-origin declaration, not a claim
   that an AI is an author.
3. **Correctness / community interest / citations / rights** — four confirmations. Basis you can rely
   on: every theorem claimed is machine-checked in Lean (standard axioms, fresh kernel replays), an
   independent AI referee pass, exact numerical checks, and a citation audit
   (`research/citation-audit.md`). Everything rests on the labs' claimed ETH refutations, which the
   papers state plainly.
4. **Licence** — I suggest CC BY 4.0 (the usual choice for arXiv-style preprints).
5. **Supplementary AI-use material** — optional; you could attach this session's transcript if you
   want maximal transparency.

## Files in this folder
- `hexagon-hc-paper.zip`, `hexagon-quantum-note.zip` — TeX source packages (`main.tex`, `refs.bib`,
  prebuilt `main.bbl`); each compiles from an empty directory with two `pdflatex` runs. They are
  snapshots of `paper/` and `quantum-note/`; rebuild them if those change.
- `abstract-hc.txt`, `abstract-quantum.txt` — abstracts for the form (TeX math kept, paper macros expanded).
- `provenance.txt` — a DRAFT provenance statement; edit it so every sentence is true for you.
