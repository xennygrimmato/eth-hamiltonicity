# Hexagon submission 4: survey note

Files in this folder: `hexagon-survey-note.zip` (upload this), `abstract.txt` (paste), `provenance.txt` (paste if you choose "some"), `preview.pdf` (what the compiled paper should look like, 16 pages).

## Steps

1. Go to https://hexagonmath.org and sign in with your ORCID iD.
2. Click **Submit a work**. New accounts may deposit once per UTC day; check the queue in `../README.md`.
3. **Upload** `hexagon-survey-note.zip`. When asked for the main file, choose `main.tex`.
4. **Preview**: wait for the compile preview. It should show **16 pages**. If it reports an error, send Claude a screenshot.
5. Fill in the form fields below, in order.
6. **Contributors**: yourself only. AI systems are listed under tools, not as contributors.
7. **Declarations** (your decisions; see the section below).
8. **Submit**. Moderation usually takes about 48 hours on weekdays.

## Form fields

**Title**

```
What survives the ETH refutations? A map of fine-grained hypotheses and conditional lower bounds
```

**Abstract** — paste the full contents of `abstract.txt` (1913 characters, under the 1920 limit).

**Primary subject:** `cs.CC`

**Cross-lists:** `cs.DS`

**MSC2020** (all checked against Hexagon's catalogue on 4 Nov 2026):

- `68Q17` — Computational difficulty of problems
- `68Q25` — Analysis of algorithms and problem complexity
- `68Q15` — Complexity classes

**Tags** (6, limit 12):

- Exponential Time Hypothesis
- SETH
- fine-grained complexity
- conditional lower bounds
- parameterized complexity
- survey

**Tools used:**

- Claude (Anthropic), via Claude Code
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

- A survey: 34 hypotheses and 27 conditional theorems classified. Nothing is claimed as machine-checked except where it cites our Lean theorems.
- Review fixes: priority credit to OpenAI and Bhattacharjee; rows B16, B17, B23 corrected; long tables replaced by lists for Hexagon.
- Rebuilt 5 Nov 2026 after the novelty audit: new row A34 (sparse Max-SAT hypotheses, refuted; credited to Li and Majdoddin); SH = Almost-ETH (MIT Hardness Group); Wu-Wang FVS/forests/Steiner (under OpenAI Thm D.1) in B16/B17; 3SUM/APSP noted as claimed refuted independently (Alman-Vassilevska Williams); a related-work map of follow-ups (Li, MIT, Majdoddin, Szeider, Dias-Lima, Wu-Wang, O'Donnell, Kominers, Vega, OpenAI 003/142); our own works cited by Hexagon ID (2611.00088, 2611.00090, 2611.00115, 2611.00116).

## Package checks done

- Single `main.tex`, bibliography inlined, no `anc/`, no code, no long (page-splitting) tables.
- Compiles from a fresh unzip with `pdflatex -halt-on-error`: 0 errors, no undefined references.
- GitHub repository https://github.com/xennygrimmato/eth-hamiltonicity cited with a commit; no placeholders.
