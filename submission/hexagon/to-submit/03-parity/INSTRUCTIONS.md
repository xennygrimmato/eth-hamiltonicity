# Hexagon submission 3: parity note

Files in this folder: `hexagon-parity-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 9 pages).

> Strongest new result of the queue.

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-parity-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **9 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
The parity of the prime-counting function in time $x^{o(1)}$, assuming the new #SAT algorithms
```

**Abstract** — paste the full contents of `abstract.txt` (1722 characters, under the 1920 limit).

**Primary subject:** `math.NT`

**Cross-lists:** `cs.CC`, `cs.DS`, `cs.LO`

**MSC2020** (all checked against Hexagon's catalogue on 4 Nov 2026):

- `11N05` — Distribution of primes
- `11Y16` — Number-theoretic algorithms; complexity
- `11A25` — Arithmetic functions; related numbers; inversion formulas
- `68Q25` — Analysis of algorithms and problem complexity
- `68V20` — Formalization of mathematics in connection with theorem provers

**Tags** (11, limit 12):

- prime-counting function
- parity of pi(x)
- Polymath4
- deterministic prime finding
- squarefree numbers
- Mobius function
- divisor chains
- #SAT
- Exponential Time Hypothesis
- Lean 4
- formal verification

**Tools used:**

- Claude (Anthropic), via Claude Code
- Lean 4 with Mathlib
- TeX Live
- Python (exact numeric checks)

**Formalizations:** leave empty (GitHub is not an allowlisted host; the repository and commit are cited in the paper).

**arXiv id:** leave empty.

## Declarations

- **Human understanding:** `all`, `some` or `none`. If `some`, paste `provenance.txt` (no placeholders; read its third sentence once, it describes what you reviewed).
- **Text origin:** "primarily AI-generated" (drafted by Claude in sessions you directed).
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see what is claimed below.
- **Licence:** CC BY 4.0 (suggested).
- **Supplementary AI-use material:** optional; may be skipped.

## What the paper claims (so your declarations match)

- Machine-checked (fresh kernel replay passed): pi(x) mod 2 and the parity of the number of primes in any interval, in time 2^{O(n/sqrt log n)}; the chain lemma; the one-count identity; the product-tree lower bound.
- Proved on paper only: the adversary proposition, the link from networks to the tree model, the mod-k remark. It does NOT give deterministic prime finding or the exact pi(x).

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no long (page-splitting) tables.
- Compiles from a fresh unzip with `pdflatex -halt-on-error`: 0 errors, no undefined references.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with a commit; no placeholders.
