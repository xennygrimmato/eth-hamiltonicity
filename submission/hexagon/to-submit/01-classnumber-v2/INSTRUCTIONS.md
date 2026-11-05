# Hexagon revision: classnumber note v2 (record hexagon:2611.00115)

This is a **new version of your published record 2611.00115**, not a new submission. Do **not** use "Submit a work":
that would create a second record with a new identifier. After publication the record shows v2 as current and v1
as superseded (as on https://hexagonmath.org/2611.00073v2).

Files in this folder:

- `hexagon-classnumber-note-v2.zip`: upload this. It holds one file, `main.tex` (bibliography inlined).
- `abstract.txt`: paste into the abstract field (1913 characters, under the 1920 limit).
- `provenance.txt`: paste as the provenance statement if you keep human understanding at `some`.
- `preview.pdf`: what the compiled paper should look like (**12 pages**; v1 had 11).

## Why v2

A novelty audit (`research/novelty-audit-2026-11-05.md`) found that two entries in OpenAI's catalogue predate v1:
003, "The quasi-Riemann hypothesis" (preprint dated 30 September 2026), and 142, "Deterministic polynomial
factorization over prime fields" (preprint dated 4 October 2026). Together they give deterministic polynomial time for
the least quadratic non-residue and for square roots modulo a prime. v1 said that Burgess is the best unconditional
bound and that polynomial time needs GRH. v2 corrects this and leads with class numbers and lattice-point counts.

## Steps

1. Sign in at https://hexagonmath.org with your ORCID iD.
2. Open your account page, https://hexagonmath.org/account, and find the record **2611.00115**. Click **Submit revised
   version**. If the button is not on the account page, open https://hexagonmath.org/2611.00115 while signed in and
   look there (see "What I could and could not check" below).
3. The button opens a new draft for the same record. **Upload** `hexagon-classnumber-note-v2.zip`. When asked for the
   main file, choose `main.tex`.
4. **Preview**: run the compile preview. It should show **12 pages** with no errors. If it fails, send Claude a
   screenshot or the preview log.
5. Fill in the metadata. Fields marked "changed" differ from v1; keep the rest as in v1.
6. **Comments** (changed): the comments field starts blank in a revision. Paste the text in the next section.
7. **Declarations**: the same choices as in v1 (see below). Re-read the provenance statement: it now has sentences on
   v2.
8. **Submit**. The new version goes through moderation like a new deposit.

## Comments (paste into the comments / changes field)

```
v2 corrects v1's statements about quadratic non-residues and square roots, which were out of date. OpenAI's catalogue (https://github.com/openai/math, CONTENTS.md) already contained entry 003, "The quasi-Riemann hypothesis" (preprint dated 30 September 2026), and entry 142, "Deterministic polynomial factorization over prime fields" (preprint dated 4 October 2026). Corollary 1.2 of 003 bounds the least quadratic non-residue modulo p by C(log p)^A and gives square roots modulo p in deterministic polynomial time; 142 gives them too; and the least square root modulo a composite m also follows, on paper, from deterministic factoring with Hensel lifting and the Chinese remainder theorem. The note is retitled to lead with class numbers and lattice-point counts. The Lean theorems for square roots and non-residues are unchanged and are now presented as an independent machine-checked route, not as the best bounds. Adds citations to Frei-Sofos-Widmer (arXiv:2610.18491) and Vega (hexagon:2611.00086) and reports a repeated novelty search. No Lean theorem, statement or proof changed. 12 pages (v1: 11).
```

(1105 characters; the field allows 2000.)

## Form fields

**Title** (changed):

```
Class numbers and lattice-point counts in time $2^{O(n/\sqrt{\log n})}$, assuming the new #SAT algorithms
```

**Abstract** (changed): paste the full contents of `abstract.txt`.

**Primary subject:** `math.NT` (unchanged). **Cross-lists:** `cs.CC`, `cs.DS`, `cs.LO` (unchanged).

**MSC2020** (five codes; checked against Hexagon's catalogue on 5 Nov 2026). Suggested change: replace `11A15` by
`11P21`, since the headline now includes lattice-point counts. Keeping v1's codes is also fine.

- `11R29`: Class numbers, class groups, discriminants
- `11Y16`: Number-theoretic algorithms; complexity
- `11Y40`: Algebraic number theory computations
- `11P21`: Lattice points in specified regions (new; replaces `11A15` Power residues, reciprocity)
- `68V20`: Formalization of mathematics in connection with theorem provers

**Tags** (changed; 11, limit 12). "Burgess bound" is removed and "lattice points" is added:

- class number
- binary quadratic forms
- divisor sum
- Gauss circle problem
- lattice points
- square roots modulo m
- quadratic non-residue
- #SAT
- Exponential Time Hypothesis
- Lean 4
- formal verification

**Tools used** (unchanged): Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (small numeric
checks).

**Formalizations:** leave empty. These links are record-level and do not change with a version.

**arXiv id:** leave empty. Hexagon ignores this field on revisions.

## Declarations

- **Human understanding:** your decision, as in v1 (`some` in v1). If `some`, paste `provenance.txt`. It has no
  placeholders. Its third sentence says what you reviewed for v1. If you did not review the v2 changes, it still reads
  correctly, because the new sentences say that Claude drafted them.
- **Text origin:** "primarily AI-generated", as in v1.
- **Four confirmations** (correctness, community interest, good-faith citations, rights): see the claims below.
- **Licence:** CC BY 4.0, as in v1.

## What v2 claims (so your declarations match)

- Machine-checked in Lean (unchanged from v1): the number of reduced forms of discriminant -N, the least square root
  modulo any m, the least quadratic non-residue modulo a prime, exact divisor and sigma sums, and the Gauss circle
  count, each in time 2^{O(n/sqrt log n)}.
- New in v2, on paper only: credit to Corollary 1.2 of OpenAI 003 (least non-residue at most C(log p)^A, square roots
  modulo p in polynomial time), and the route to the least square root modulo composite m by factoring, Hensel lifting and
  the Chinese remainder theorem.
- Not new bounds: the square-root and non-residue theorems. Modulo a prime, polynomial time follows from OpenAI 003 and
  142.

## What I could and could not check

- Hexagon's API (https://hexagonmath.org/api/v1/openapi.json, v1.13.0-beta) has no separate "new version" call.
  The site's "Submit revised version" button (component `RevisionButton` in the site's JavaScript) calls
  `POST /api/v1/submissions/{draftId}/revise`. The OpenAPI text describes that call as "after moderator-requested
  changes", with a 409 error "The submission is not awaiting changes". Other published records do have author-made v2s
  with comments (for example 2611.00073v2, "Fixed ten references..."), so revising a published record works. I could
  not see the signed-in pages, so I could not confirm where the button sits or whether it opens for a published
  record.
- If no "Submit revised version" button appears for 2611.00115, or the call returns "The submission is not awaiting
  changes", do not submit a new work. Email admin@hexagonmath.org and ask how to deposit version 2 of 2611.00115.
- Whether a revision counts against the one-deposit-per-UTC-day limit is not documented. Compile previews have their
  own per-day cap and never use up a submission slot.

## Package checks done

- The ZIP was built with `zip -X -D` and holds only `main.tex`: no `anc/`, no `.bib` or `.bbl`, no code, no
  `longtable`.
- From a fresh unzip, three passes of `pdflatex -interaction=nonstopmode -halt-on-error` give 0 errors, no undefined
  references or citations, no overfull boxes and **12 pages**.
- The repository https://github.com/xennygrimmato/eth-hamiltonicity is cited with commit `b9ea3f1`. No placeholders.
- Lean theorem names and the quoted Lean statements are byte-identical to v1.
