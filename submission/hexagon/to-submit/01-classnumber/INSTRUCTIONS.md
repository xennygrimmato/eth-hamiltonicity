# Hexagon submission 1: classnumber note

Files in this folder: `hexagon-classnumber-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 11 pages).

> Strongest new number-theory result. Priority check against OpenAI, Anthropic, Bhattacharjee and Nguyen: no conflict.

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-classnumber-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **11 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
Class numbers, square roots and quadratic non-residues in time $2^{O(n/\sqrt{\log n})}$, assuming the new #SAT algorithms
```

**Abstract** — paste the full contents of `abstract.txt` (1893 characters, under the 1920 limit).

**Primary subject:** `math.NT`

**Cross-lists:** `cs.CC`, `cs.DS`, `cs.LO`

**MSC2020** (all checked against Hexagon's catalogue on 4 Nov 2026):

- `11R29` — Class numbers, class groups, discriminants
- `11Y16` — Number-theoretic algorithms; complexity
- `11Y40` — Algebraic number theory computations
- `11A15` — Power residues, reciprocity
- `68V20` — Formalization of mathematics in connection with theorem provers

**Tags** (11, limit 12):

- class number
- binary quadratic forms
- quadratic non-residue
- Burgess bound
- square roots modulo m
- divisor sum
- Gauss circle problem
- #SAT
- Exponential Time Hypothesis
- Lean 4
- formal verification

**Tools used:**

- Claude (Anthropic), via Claude Code
- Lean 4 with Mathlib
- TeX Live
- Python (small numeric checks)

**Formalizations:** leave empty (GitHub is not an allowlisted host; the repository and commit are cited in the paper).

**arXiv id:** leave empty.

## Declarations

- **Human understanding:** `all`, `some` or `none`. If `some`, paste `provenance.txt` (no placeholders; read its third sentence once, it describes what you reviewed).
- **Text origin:** "primarily AI-generated" (drafted by Claude in sessions you directed).
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see what is claimed below.
- **Licence:** CC BY 4.0 (suggested).
- **Supplementary AI-use material:** optional; may be skipped.

## What the paper claims (so your declarations match)

- Machine-checked in Lean (fresh kernel replay passed): the number of reduced forms of discriminant -N, the least square root modulo any m, the least quadratic non-residue modulo a prime, exact divisor sums and the Gauss circle count, each in time 2^{O(n/sqrt log n)}.
- Not formalised: the equality of the form class number with the ideal class number (classical, cited). Real quadratic fields are not covered.

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no long (page-splitting) tables.
- Compiles from a fresh unzip with `pdflatex -halt-on-error`: 0 errors, no undefined references.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with a commit; no placeholders.
