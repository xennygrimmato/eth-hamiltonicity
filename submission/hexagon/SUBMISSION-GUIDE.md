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
- **Tools:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (numeric checks).
- **Formalizations / arXiv id:** leave empty.
- Status: READY (revised 4 Nov 2026, 15 pp, house style, single main.tex, repository and commit cited). Machine-checked: Theorem 1.1
  only (`amplitude_TM_rate'`, `amplitude_TM_rate`, `amplitude_TM`); everything else is labelled proved on paper only. The remark
  after Theorem 1.1 was corrected (its sufficient condition on L was too weak); the theorem itself is unchanged.
  Bhattacharjee hexagon:2610.00594 Thm 5.3 is now cited as a near route to the polynomial-space variant (not claimed).

## Your decisions (the form asks you to declare these; I have not filled them in for you)
1. **Human understanding** — `all` / `some` / `none`: "whether all, some, or none of the contribution
   has been checked and understood by a human at submission time." Choosing `some` requires a
   provenance statement; use `provenance.txt` as is (it has no placeholders; its one sentence about what you reviewed is
   written to be true of this project, read it once). Note: Lean
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
- `provenance.txt` — the provenance statement, ready to paste as is (no placeholders).

## Paper 3 — Crossover note (upload `hexagon-crossover-note.zip`, main file `main.tex`)
- **Title:** When do the new #SAT algorithms beat brute force? Crossover points of the proven bounds behind the ETH refutations
- **Abstract:** paste `abstract-crossover.txt`.
- **Primary subject:** cs.CC. **Cross-lists:** cs.DS.
- **MSC2020:** 68Q25, 68W40, 68Q17.
- **Tags:** Exponential Time Hypothesis; model counting; fine-grained complexity; explicit constants; galactic algorithms; crossover point.
- **Tools:** Claude (Anthropic), via Claude Code; Python with mpmath; TeX Live.
- **Formalizations / arXiv id:** leave empty.
- Status: READY (revised 4 Nov 2026, 11 pp, house style, repository and commit 2798867 cited). Nothing in this note is
  machine-checked: the crossover numbers are computations, not theorems. Six errors found in review were fixed, including two
  table rows recomputed after a floor/ceiling fix in the script; the headline numbers in the abstract are unchanged.

## Packaging lesson (from the HC upload)
Hexagon rejected ZIPs containing `anc/` scripts and/or separate `.bib`/`.bbl` files with "file type not accepted",
and accepted a ZIP with a single `main.tex` (bibliography inlined from the `.bbl`). All three packages here use that
form; the papers cite the scripts in the repository instead.

## Paper 4 — Circuit lower bound note (upload `hexagon-circuit-note.zip`, main file `main.tex`)
- **Title:** A machine-checked proof of superlinear circuit lower bounds for E^NP, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-circuit.txt`.
- **Primary subject:** cs.CC. **Cross-lists:** cs.LO.
- **MSC2020:** 68Q17, 68Q15, 68Q25, 03B35 (all checked against Hexagon's catalogue).
- **Tags:** circuit lower bounds; E^NP; Exponential Time Hypothesis; Williams' algorithmic method; Lean 4; formal verification.
- **Tools:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live.
- **Formalizations / arXiv id:** leave empty.
- PRIORITY: the bound itself is OpenAI's Corollary 1.4 (preprint revised 25 Oct 2026, proved on paper there); the note now says so
  and claims only the machine-checked proof. Earlier versions of this ZIP claimed the bound was new; do not use them.
- Status: READY (revised 4 Nov 2026, 10 pp, house style, repository and commit 9e5dfc8 cited). What is machine-checked: the
  first part of Theorem 1.1 as `enp_not_size_n_sqrt_log` (Anthropic's language L0, ε = 1/(4608(qG+1)), fresh leanchecker
  replay passed); the second part (any ε with 36aCε < 1) and the OpenAI corollary are proved on paper only.

## Paper 5 — Survey note (upload `hexagon-survey-note.zip`, main file `main.tex`)
- **Title:** as in survey-note/main.tex ("What survives the ETH refutations? …").
- **Abstract:** paste `abstract-survey.txt`.
- **Primary subject:** cs.CC. **Cross-lists:** cs.DS.
- **MSC2020:** 68Q17, 68Q25, 68Q15.
- **Tags:** Exponential Time Hypothesis; SETH; fine-grained complexity; conditional lower bounds; parameterized complexity; survey.
- Nothing in this note is claimed as machine-checked except where it cites our Lean theorems.
- **Tools:** Claude (Anthropic), via Claude Code; TeX Live. **Formalizations / arXiv id:** leave empty.
- Status: READY (revised 4 Nov 2026, 14 pp, house style, repository linked). Review fixes: priority credits to OpenAI
  (CNF-SETH observation, counting corollaries, circuit bound) and Bhattacharjee (Vertex Cover, sparse Max-Cut); rows B16, B17
  and B23 corrected; the two long tables are now lists (Hexagon's TeX rejects page-splitting tables).

## HC paper v2 candidate (4 Nov 2026)
`hexagon-hc-paper-texonly.zip` (single `main.tex`, bibliography inlined) is now a **v2 candidate** for the
existing record hexagon:2610.00672 (v1 is published). Upload it via **"Revise"** on that record, not as a new
submission. Changes from v1: two citation sentences only, to Bhattacharjee (hexagon:2610.00594, independent
white-box weighted route, in the Tutte subsection of the Extensions) and de Brito (hexagon:2610.00692, rank floor
for Theorem-B-shaped pieces, in the open problem on the exponent). Abstract unchanged (`abstract-hc.txt`).

## Paper 6 — Factoring note (upload `hexagon-factoring-note.zip`, main file `main.tex`)
Status: READY. The fresh kernel replay of the whole proof passed on 4 Nov 2026 (README row "F").

**Form answers**
- **Title:** An independent machine-checked proof of deterministic factoring in time $2^{O(n/\sqrt{\log n})}$, via the new #SAT algorithms
- **Abstract:** paste `abstract-factoring.txt` (1905 characters, under the 1920 limit).
- **Primary subject:** cs.CC. **Cross-lists:** cs.DS, math.NT, cs.LO.
- **MSC2020** (all five checked against Hexagon's catalogue, `api/v1/msc`, on 4 Nov 2026): 11Y05 (Factorization),
  68Q25 (Analysis of algorithms and problem complexity), 68W40 (Analysis of algorithms), 68V20 (Formalization of
  mathematics in connection with theorem provers), 03B35 (Mechanization of proofs and logical operations).
- **Tags:** integer factorization; deterministic factoring; Schönhage–Strassen; fast Fourier transform; #SAT;
  Exponential Time Hypothesis; fine-grained complexity; Lean 4; formal verification; Mathlib.
- **Tools used:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (small numeric checks).
- **Formalizations:** none (GitHub is not an allowlisted host; the repository and commit are cited in the paper).
- **arXiv id:** none.
- **Related works to be aware of** (cited in the paper; you do not need to enter them in the form): Rudich–Rousseau
  hexagon:2610.00600, Shunia hexagon:2610.00711, and the earlier Lean proof in github.com/1337isnot1337/integer-factoring.
  The paper claims no priority; it presents an independent second proof.

**Your decisions** (as for the other papers; see "Your decisions" above): human understanding (`all`/`some`/`none`,
with `provenance.txt`, ready to paste, if `some`), text origin (the text was drafted by Claude in sessions you directed), the four
confirmations, licence (suggested CC BY 4.0).

**Exact steps**
1. Go to hexagonmath.org and sign in with your ORCID iD.
2. Click "Submit a work". Remember the one-deposit-per-UTC-day rule: if you already deposited today, wait for the next UTC day.
3. Upload `submission/hexagon/hexagon-factoring-note.zip`. When asked for the main file, choose `main.tex`.
4. Wait for the automatic compile preview. It should show 10 pages. If it reports an error, send me a screenshot.
5. Fill in title, abstract, subject, cross-lists, MSC codes and tags from the list above. Leave "Formalizations" and "arXiv id" empty.
6. Add yourself as the contributor. List Claude and Lean under tools, not as contributors.
7. Make your declarations (human understanding, text origin, the four confirmations, licence).
8. Submit. A moderator reviews it, usually within about 48 hours on weekdays.

## Paper 7 — Eulerian circuits note (upload `hexagon-euler-note.zip`, main file `main.tex`)
Status: proof final (fresh leanchecker replay of `EthFollowup.ExactHC.EulerTheorems` passed 4 Nov 2026; README row R4).
Status: READY (4 Nov 2026). Paper 8 pp in `euler-note/main.tex`, PDF in `docs/euler-note.pdf`; the ZIP compiles cleanly from a fresh unzip.

**Form answers**
- **Title:** Counting Eulerian circuits in subexponential time, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-euler.txt`.
- **Primary subject:** cs.DS. **Cross-lists:** cs.CC, math.CO, cs.LO.
- **MSC2020** (all five checked against Hexagon's catalogue, `api/v1/msc`, on 4 Nov 2026): 05C45 (Eulerian and Hamiltonian
  graphs), 05C30 (Enumeration in graph theory), 68Q25 (Analysis of algorithms and problem complexity), 68Q17 (Computational
  difficulty of problems), 68V20 (Formalization of mathematics in connection with theorem provers).
- **Tags:** Eulerian circuits; Euler tours; exact counting; #P-completeness; transition systems; Hamiltonian cycle; line graph;
  Exponential Time Hypothesis; #SAT; Lean 4; formal verification.
- **Tools used:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (brute-force checks).
- **Formalizations:** none (GitHub is not an allowlisted host; the repository and commit are cited in the paper).
- **arXiv id:** none.

**What is claimed and what is not** (as the paper states): the theorems count Kotzig's transition systems with connected
transition graph (= closed Euler trails up to rotation and reversal); the bridge to Mathlib's `Walk.IsEulerian` is not
formalised; the time bounds carry a factor (n+2)^C for reading the n²-bit adjacency matrix (dropped when no vertex is
isolated). The reduction (line graph of the double subdivision) is classical; the subexponential exact count and its
verification are new to our knowledge.

**Exact steps:** as for Paper 6 (sign in with ORCID → Submit a work → upload the ZIP, main file `main.tex` → check the
compile preview → fill the fields above → contributor = you, Claude and Lean under tools → declarations → submit).

## Paper 8 — Class numbers, square roots, non-residues (upload `hexagon-classnumber-note.zip`, main file `main.tex`)
Status: SUBMITTED as hexagon:2611.00115v1. A v2 correction is READY in `to-submit/01-classnumber-v2/` (see its INSTRUCTIONS.md).
v1 status was: READY (4 Nov 2026). Fresh leanchecker replay of `EthFollowup.ModP.Final` passed (README rows N1–N3).
Paper 11 pp in `classnumber-note/main.tex`, PDF in `docs/classnumber-note.pdf`; the ZIP compiles cleanly from a fresh unzip.

**Form answers**
- **Title:** Class numbers, square roots and quadratic non-residues in time $2^{O(n/\sqrt{\log n})}$, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-classnumber.txt` (1895 characters).
- **Primary subject:** math.NT. **Cross-lists:** cs.CC, cs.DS, cs.LO.
- **MSC2020** (all five checked against Hexagon's catalogue, `api/v1/msc`, 4 Nov 2026): 11R29 (Class numbers, class groups,
  discriminants), 11Y16 (Number-theoretic algorithms; complexity), 11Y40 (Algebraic number theory computations),
  11A15 (Power residues, reciprocity), 68V20 (Formalization of mathematics in connection with theorem provers).
- **Tags:** class number; binary quadratic forms; quadratic non-residue; Burgess bound; square roots modulo m; divisor sum;
  Gauss circle problem; #SAT; Exponential Time Hypothesis; Lean 4; formal verification.
- **Tools used:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (small numeric checks).
- **Formalizations:** none (GitHub is not an allowlisted host; the repository and commit are cited in the paper).
- **arXiv id:** none.

**What is claimed and what is not** (as the paper states): Lean proves the number of reduced forms of discriminant −N
(Gauss's form class number, with Cox's reduction conventions); its equality with the ideal class number of ℚ(√D) is
classical and not in Mathlib; for fundamental discriminants every reduced form is primitive (`hFormPrim_TM_rate`);
real quadratic fields are not covered. Square roots are the least root modulo any m (output m when none);
the least non-residue theorem has a primality hypothesis, with a weaker clause for composite inputs.

**Exact steps:** as for Paper 6.


## Submitted (record)
- 2610.00672 HC paper (v1, earlier)
- 4 Nov 2026: Eulerian circuits note (Paper 7); quantum note (Paper 2, fixed ZIP without the long table).

## Paper 9 — Parity of the prime-counting function (upload `hexagon-parity-note.zip`, main file `main.tex`)
Status: READY (4 Nov 2026). Fresh leanchecker replay of `EthFollowup.Primes.Final` passed (README row P1). 9 pp, no long tables,
compiles from a fresh unzip with -halt-on-error.

**Form answers**
- **Title:** The parity of the prime-counting function in time $x^{o(1)}$, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-parity.txt` (1723 characters).
- **Primary subject:** math.NT. **Cross-lists:** cs.CC, cs.DS, cs.LO.
- **MSC2020** (all five checked against Hexagon's catalogue, 4 Nov 2026): 11N05 (Distribution of primes), 11Y16
  (Number-theoretic algorithms; complexity), 11A25 (Arithmetic functions; related numbers; inversion formulas), 68Q25 (Analysis
  of algorithms and problem complexity), 68V20 (Formalization of mathematics in connection with theorem provers).
- **Tags:** prime-counting function; parity of pi(x); Polymath4; deterministic prime finding; squarefree numbers; Möbius function;
  divisor chains; #SAT; Exponential Time Hypothesis; Lean 4; formal verification.
- **Tools used:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (exact numeric checks).
- **Formalizations / arXiv id:** leave empty.

**What is claimed and what is not** (as the paper states): machine-checked are π(x) mod 2 and the interval parity in
2^{O(n/√log n)}, the chain lemma and the one-count identity, and the product-tree lower bound; the adversary proposition, the
link from networks to the tree model and the mod-k remark are proved on paper only. It does NOT give deterministic prime finding
or the exact π(x).

**Exact steps:** as for Paper 6.

## Paper 10 — Roots of fixed-degree polynomials modulo any integer (upload `hexagon-roots-note.zip`, main file `main.tex`)
Status: SHELVED (5 Nov 2026). Do not upload. The fresh leanchecker replay passed, but OpenAI catalogue entry 142
(deterministic polynomial factorization over F_p, 4 Oct 2026) already gives roots mod p in polynomial time; see
`research/novelty-audit-2026-11-05.md`.

**Form answers**
- **Title:** Roots of fixed-degree polynomials modulo any integer in time $2^{O(n/\sqrt{\log n})}$, assuming the new #SAT algorithms
- **Abstract:** paste `abstract-roots.txt` (1731 characters).
- **Primary subject:** math.NT. **Cross-lists:** cs.CC, cs.DS, cs.LO.
- **MSC2020** (checked against Hexagon's catalogue, 5 Nov 2026): 11T06 (Polynomials over finite fields), 11Y16 (Number-theoretic
  algorithms; complexity), 13P05 (Polynomials, factorization in commutative rings), 68Q25 (Analysis of algorithms and problem
  complexity), 68V20 (Formalization of mathematics in connection with theorem provers).
- **Tags:** root finding; polynomials over finite fields; deterministic factoring of polynomials; Berlekamp; Horner's rule;
  #SAT; Exponential Time Hypothesis; Lean 4; formal verification.
- **Tools used:** Claude (Anthropic), via Claude Code; Lean 4 with Mathlib; TeX Live; Python (small numeric checks).
- **Formalizations / arXiv id:** leave empty.

**What is claimed and what is not** (as the paper states): machine-checked, for each fixed degree d ≥ 1: the least root modulo
any m, the least root above a bound, and the number of roots, in time 2^{O_d(n/√log n)}; the constant C_d is not tracked and the
theorem is per fixed d. Proved on paper only: factoring of degree-≤d polynomials over F_p via Berlekamp's reduction. Classical,
not claimed: the root count and irreducibility tests are polynomial-time; degree 2 reduces to square roots (Burgess gives
p^{0.152} there). Not covered: F_q with q = p^k.

**Exact steps:** as for Paper 6.
