# Hexagon submission 5: factoring note

Files in this folder: `hexagon-factoring-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 10 pages).

> Lower priority: independent confirmation of a known result.

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-factoring-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **10 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
An independent machine-checked proof of deterministic factoring in time $2^{O(n/\sqrt{\log n})}$, via the new #SAT algorithms
```

**Abstract** — paste the full contents of `abstract.txt` (1903 characters, under the 1920 limit).

**Primary subject:** `cs.CC`

**Cross-lists:** `cs.DS`, `math.NT`, `cs.LO`

**MSC2020** (all checked against Hexagon's catalogue on 4 Nov 2026):

- `11Y05` — Factorization
- `68Q25` — Analysis of algorithms and problem complexity
- `68W40` — Analysis of algorithms
- `68V20` — Formalization of mathematics in connection with theorem provers
- `03B35` — Mechanization of proofs and logical operations

**Tags** (10, limit 12):

- integer factorization
- deterministic factoring
- Schonhage-Strassen
- fast Fourier transform
- #SAT
- Exponential Time Hypothesis
- fine-grained complexity
- Lean 4
- formal verification
- Mathlib

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

- A second machine-checked proof (fresh kernel replay passed). The first Lean proof is github.com/1337isnot1337/integer-factoring (30 Oct 2026); the paper claims no priority.

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no long (page-splitting) tables.
- Compiles from a fresh unzip with `pdflatex -halt-on-error`: 0 errors, no undefined references.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with a commit; no placeholders.
