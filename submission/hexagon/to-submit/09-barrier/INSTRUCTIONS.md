# Hexagon submission 9: barrier note

Files in this folder: `hexagon-barrier-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 24 pages).

> Repositioned after Majdoddin (arXiv:2610.41622, 30 Oct) and Dias–Lima (arXiv:2611.00517, 31 Oct). The product-term rate caps are credited to them (and to Anthropic's Appendix H) as parallel and stronger; what the paper claims as new is the correlated (non-product) decompositions, the walls for the problems beyond SAT, and the Lean development.

## Before uploading

Nothing to do. The paper cites the repository at commit `946c499`, which contains the Lean files and the repaired
research notes (covering proof, K = Θ(n^{1/9}) cap, re-run script).

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-barrier-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **24 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
What the ETH refutations do not give: barriers for the counting engines, with machine-checked lemmas
```

**Abstract** — paste the full contents of `abstract.txt` (1906 characters, under the 1920 limit).

**Primary subject:** `cs.CC`

**Cross-lists:** `cs.DS`, `cs.LO`, `math.CO`

**MSC2020** (all five checked against Hexagon's catalogue, https://hexagonmath.org/api/v1/msc?q=CODE, on 5 Nov 2026):

- `68Q17` — Computational difficulty of problems (lower bounds, completeness, difficulty of approximation, etc.)
- `68Q25` — Analysis of algorithms and problem complexity
- `68W30` — Symbolic computation and algebraic computation
- `15A69` — Multilinear algebra, tensor calculus
- `05C31` — Graph polynomials

(The form allows five. `68V20` — Formalization of mathematics in connection with theorem provers — is also valid and can replace `68W30` if you prefer.)

**Tags** (12, limit 12):

- engine barrier problem
- Exponential Time Hypothesis
- #SAT
- tensor networks
- correlated decompositions
- cut rank
- flattening rank
- permanent
- Tutte polynomial
- lower bounds for restricted models
- Lean 4
- formal verification

**Tools used:**

- Claude (Anthropic), via Claude Code
- Lean 4 with Mathlib
- TeX Live
- Python (exact rank tables, integer programs, the covering check)

**Formalizations:** leave empty (GitHub is not an allowlisted host; the repository and commit are cited in the paper).

**arXiv id:** leave empty.

## Declarations

- **Human understanding:** `all`, `some` or `none`. If `some`, paste `provenance.txt` (no placeholders; read its third sentence once, it describes what you reviewed).
- **Text origin:** "primarily AI-generated" (drafted by Claude in sessions you directed).
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see what is claimed below.
- **Licence:** CC BY 4.0 (suggested).
- **Supplementary AI-use material:** optional; may be skipped.

## What the paper claims (so your declarations match)

- Machine-checked in Lean (45 cited theorems, 16 modules of `lean/EthFollowup/Barriers`, axioms propext, Classical.choice, Quot.sound only): the cut lemma; the permanent's row-cut rank C(n,k) and the Model-R summation; the algebra dimension bound C(n,n/2); per A = 0 for low rank in characteristic p; the rank form of rho >= 1/2 for pieces; the spread inequality; the correlated rank sums N^2, N^3, N^8 (two rectangles, 3x2 grid, 3x3 level); the triangular rank bound for OpenAI's M0-template; the colouring barrier n <= q+4; the turn-labelling bound; the residue-support duality; the product-tree and product-indicator bounds.
- Proved on paper only: the step from a network to a factorised matrix and from cost to rank; the engine exponent; Model V; the Tutte barrier; the graded two-order bound; the grouping caps, including the covering bound (proof repaired in this version: rectangles meeting three blocks are reclassified); rho >= 3/8 on full levels and the limit of flattening certificates; the template corollaries (modulo Arora–Rao–Vazirani); the meta-barrier and the conditional cap (now with K = Θ(n^{1/9})).
- Credited, not claimed: rho >= 1/2 for pieces is Anthropic's Appendix H observation, generalised by Majdoddin; Majdoddin's 1/log2 K for grid algorithms with product terms is sharper than our two-grouping cap. Conjectured, not claimed: N^9 on the 3x3 level; the Catalan rank on y = 1.
- Nothing is about all algorithms: every barrier is for a named model.

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no `longtable` (all tables are `tabular`).
- Compiles from a fresh unzip with `pdflatex -interaction=nonstopmode -halt-on-error` (3 passes): 0 errors, no undefined references, no overfull boxes, 24 pages.
- ZIP built with `zip -X -D`, containing only `main.tex`.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with commit `d7c41181c625f19d4799f3bac4a068562685d7e8`; no placeholders.
