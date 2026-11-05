# Hexagon submission 10: representation-number note

Files in this folder: `hexagon-repnum-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 13 pages).

> New content: representation numbers of every fixed positive-definite form, and Tunnell's test, in time n^{o(1)}; the L-value, twist and Sha consequences are on paper only.

## Before uploading

Nothing to do for the upload itself. The paper cites the repository at commit `3e181e7`, which contains all seven Lean
modules (`lean-bridge-anthropic/bridge/EthFollowup/ModP/`: RepQF, SlpDesc, RepDesc, CntPad, RepPoly, RepPkg, FinalRep);
they are unchanged at the current HEAD `b7b7352`.

One sentence of the paper was corrected for this package and is not yet committed: the Limitations section still said
the fresh replay of `EthFollowup.ModP.FinalRep` was pending, contradicting the formal-development section; it now says
it passed on 5 November 2026. The ZIP and `preview.pdf` contain the corrected text; `repnum-note/main.tex` and
`repnum-note/main.pdf` carry the same change in the working tree.

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-repnum-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **13 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
Representation numbers of quadratic forms and Tunnell's congruent-number test in time $n^{o(1)}$, assuming the new #SAT algorithms
```

**Abstract** — paste the full contents of `abstract.txt` (1916 characters, under the 1920 limit).

**Primary subject:** `math.NT`

**Cross-lists:** `cs.CC`, `cs.DS`, `cs.LO`

**MSC2020** (all five checked against Hexagon's catalogue, https://hexagonmath.org/api/v1/msc?q=CODE, on 5 Nov 2026):

- `11E25` — Sums of squares and representations by other particular quadratic forms
- `11G05` — Elliptic curves over global fields
- `11G40` — L-functions of varieties over global fields; Birch-Swinnerton-Dyer conjecture
- `11Y16` — Number-theoretic algorithms; complexity
- `68V20` — Formalization of mathematics in connection with theorem provers

(The form allows five. `11E20` — General ternary and quaternary quadratic forms; forms of more than two variables — is also
valid and can replace `11G05` if you prefer. `11Y40` — Algebraic number theory computations — is valid but fits less well.)

**Tags** (12, limit 12):

- representation numbers
- positive-definite quadratic forms
- ternary quadratic forms
- congruent number problem
- Tunnell's theorem
- central L-values
- Waldspurger's theorem
- Tate-Shafarevich group
- #SAT
- Exponential Time Hypothesis
- Lean 4
- formal verification

**Tools used:**

- Claude (Anthropic), via Claude Code
- Lean 4 with Mathlib
- TeX Live
- PARI/GP and Python (numerical checks)

**Formalizations:** leave empty (GitHub is not an allowlisted host; the repository and commit are cited in the paper).

**arXiv id:** leave empty.

## Declarations

- **Human understanding:** `all`, `some` or `none`. If `some`, paste `provenance.txt` (no placeholders; read its third sentence once, it describes what you reviewed).
- **Text origin:** "primarily AI-generated" (drafted by Claude in sessions you directed).
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see what is claimed below.
- **Licence:** CC BY 4.0 (suggested).
- **Supplementary AI-use material:** optional; may be skipped.

## What the paper claims (so your declarations match)

- Machine-checked in Lean (`EthFollowup.ModP.repNum_TM_rate`, `diagRep_TM_rate`, `tunnell_TM_rate` in `EthFollowup.ModP.FinalRep`;
  axioms propext, Classical.choice, Quot.sound only; fresh `leanchecker` replay passed 5 Nov 2026): a finite-alphabet Mathlib
  Turing machine outputs r_A(n) for each fixed positive-definite integer matrix A of any dimension, the count for diagonal forms,
  and Tunnell's test bit, within ⌊C·2^{C·L/√log₂(L+2)}⌋ steps, L the bit length of n. This rests on Anthropic's Lean development
  of its claimed ETH refutation, which is under review.
- Proved on paper only: exact L(E_n,1) for squarefree n via Tunnell's Theorem 3; central values of imaginary quadratic twists of a
  fixed curve of squarefree conductor via Böcherer–Schulze-Pillot; the reduction of forms with odd cross coefficients by doubling;
  the comparisons with earlier bounds. Deciding congruence in analytic rank ≥ 2 needs BSD.
- Conditional on an unrefereed result: |Sha(E_n)| in analytic rank 0 assumes OpenAI's catalogue entry 002 (full BSD).
- Checked numerically only (PARI/GP 2.17.2 and Python, not part of any proof): Tunnell's L-value formula for the 183 squarefree
  n ≤ 300, the Sha formula for the 73 with L(E_n,1) ≠ 0, Gross's formula for 11a, Gauss's formula for r_3(n).
- Not claimed: anything practical (the constants are astronomical and the machines use exponential space); binary forms, even
  rank and one-class genera were already within reach.

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no `longtable`.
- Compiles from a fresh unzip with `pdflatex -interaction=nonstopmode -halt-on-error` (3 passes): 0 errors, no undefined
  references, 13 pages. One overfull vbox of 1.02pt on page 1 (invisible; left as is).
- ZIP built with `zip -X -D -j`, containing only `main.tex`.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with commit `3e181e7`
  (`3e181e776a38ada042c0c3318c0d66cc2ccf498b`), which contains the Lean files; current HEAD `b7b7352`; no placeholders.
