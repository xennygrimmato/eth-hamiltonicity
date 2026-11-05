# Hexagon submission 2: circuit note

Files in this folder: `hexagon-circuit-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 10 pages).

> Modest contribution (a machine check of a stated bound). Earlier copies of this ZIP claimed the bound was new: do not use them.

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-circuit-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **10 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
A machine-checked proof of superlinear circuit lower bounds for E^NP, assuming the new #SAT algorithms
```

**Abstract** — paste the full contents of `abstract.txt` (1918 characters, under the 1920 limit).

**Primary subject:** `cs.CC`

**Cross-lists:** `cs.LO`

**MSC2020** (all checked against Hexagon's catalogue on 4 Nov 2026):

- `68Q17` — Computational difficulty of problems
- `68Q15` — Complexity classes
- `68Q25` — Analysis of algorithms and problem complexity
- `03B35` — Mechanization of proofs and logical operations

**Tags** (6, limit 12):

- circuit lower bounds
- E^NP
- Exponential Time Hypothesis
- Williams' algorithmic method
- Lean 4
- formal verification

**Tools used:**

- Claude (Anthropic), via Claude Code
- Lean 4 with Mathlib
- TeX Live

**Formalizations:** leave empty (GitHub is not an allowlisted host; the repository and commit are cited in the paper).

**arXiv id:** leave empty.

## Declarations

- **Human understanding:** `all`, `some` or `none`. If `some`, paste `provenance.txt` (no placeholders; read its third sentence once, it describes what you reviewed).
- **Text origin:** "primarily AI-generated" (drafted by Claude in sessions you directed).
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see what is claimed below.
- **Licence:** CC BY 4.0 (suggested).
- **Supplementary AI-use material:** optional; may be skipped.

## What the paper claims (so your declarations match)

- The bound itself is OpenAI's Corollary 1.4 (preprint revised 25 Oct 2026, proved on paper). The paper says so and claims only the machine-checked proof.
- Machine-checked: the first part of Theorem 1.1 (enp_not_size_n_sqrt_log). The second part and the OpenAI corollary are proved on paper only.
- Related work (rebuilt 5 Nov 2026) cites Wu and Wang, arXiv:2611.02560 (2 Nov 2026), who extend OpenAI's bound to larger gate bases on paper. Nothing there contradicts the note; the abstract now says "nothing more from counting for binary gates", since their extension uses counting.

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no long (page-splitting) tables.
- Compiles from a fresh unzip with `pdflatex -halt-on-error`: 0 errors, no undefined references.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with a commit; no placeholders.
