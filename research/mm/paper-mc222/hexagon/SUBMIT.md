# Depositing the 7-AND-gate paper on Hexagon (hexagonmath.org)

This folder holds everything needed for the deposit: a script that builds the upload files,
the abstract, and the form values. The reproduction guide for readers is `../REPRODUCE.md`.

Field names in `code` are those of Hexagon's submission API (`/api/v1/submissions`, schema
`SubmissionMetadata`, version 1.13.0-beta, read on 26 Nov 2026). The labels on the web form may
differ.

## 1. Decisions only the submitter can make

| item | what to decide | prepared value |
|---|---|---|
| Author line | Hexagon requires at least one human contributor, and the submitter must be one of them. The paper's `\author{[author]}` is a placeholder. | filled in by the build script from `AUTHOR` |
| Sign-in | Deposits need an ORCID-authenticated browser session (or a scoped API credential, §5). | — |
| `humanUnderstanding` | "all", "some" or "none" of the contribution checked and understood by a human. The paper says: "No person has checked the proofs or the code." | `none`. Choose `some` only if you have read and understood at least the statement: Definition 2.1 and Theorem 1.1 of the paper, or `research/mm/lean-mc222/MC222/Statement.lean` and `Main.lean` (about 80 lines). Then add one sentence to `provenance` saying what you read. `some` requires a provenance statement; one is prepared. |
| `authorshipMode` | Text origin: primarily AI-generated, mixed, or primarily human. | `no-human-author-claimed` (primarily AI-generated) |
| `correctnessConfirmed`, `communityInterestConfirmed`, `citationsConfirmed`, `rightsConfirmed` | Your attestations. The form requires all four to be true for the final submission. | left `false` in `metadata.json`; tick them yourself |
| `license` | CC BY 4.0, CC BY-SA 4.0 or CC0 1.0. | CC BY 4.0 |
| Tools (`aiSystems`) | Which tools to declare. | Claude Code, Lean 4.36.0, Mathlib v4.36.0, CaDiCaL 2.1.3, lrat-check. Add the model names if the form asks for them. |
| Repository | The paper and the comments link `https://github.com/xennygrimmato/math` at a fixed commit. | Check that the repository is public before submitting. |

## 2. Build the upload files

From the repository root (needs `python3`, `zip`, `unzip`, `pdflatex` with a standard TeX Live,
and `pdfinfo`):

```
cd research/mm/paper-mc222/hexagon
AUTHOR="First Last" ORCID="0000-0000-0000-0000" ./build_package.sh
```

Optional: `AFFIL="Institution"` adds an affiliation line under the name. The script writes
`dist/` (git-ignored):

| file | upload as (`kind`) | contents |
|---|---|---|
| `mc222-source.zip` | `source-archive`; main file `main.tex` | `main.tex` with the author line filled in, `refs.bib`, `main.bbl`, and `anc/`: the eight Python scripts of the SAT pipeline and the five recorded result files (`.tsv`, `.log`). Hexagon's `anc/` accepts only `.json .jsonl .csv .tsv .yaml .yml .log .py` and a few computer-algebra formats, at most 4 MiB per text file; the script checks both. |
| `mc222-formal.zip` | `formal-artifact` (optional) | the Lean project sources, the Rust search and the run scripts. Hexagon keeps formal artifacts but does not publish or execute them; the public copy is the repository. |
| `main.pdf` | not uploaded | compiled from `mc222-source.zip` exactly as packed (two `pdflatex` passes with the shipped `.bbl`), for comparison with Hexagon's preview |
| `metadata.json` | not uploaded | the form values below with author, ORCID, commit and page count filled in |
| `abstract.txt` | paste into the abstract field | the paper's abstract, TeX math kept |

Open `dist/main.pdf` and check page 1 (title, author line) and the appendix (reproduction
checklist, pinned commit).

## 3. Form values

Copy them from `dist/metadata.json`. In summary:

* `title`: The multiplicative complexity of $2\times 2$ matrix multiplication over $\mathbb{F}_2$ is seven
* `abstract`: `dist/abstract.txt` (1616 characters; limit 8000)
* `subject`: `cs.CC`; `crossListSubjects`: `math.CO`, `cs.DM`, `cs.LO`
* `mscCodes`: `68Q06` (circuits as models of computation; circuit complexity), `68Q17` (lower
  bounds), `68V05` (computer-assisted proofs by exhaustion), `68V15` (theorem proving), `94C11`
  (switching theory). All five were checked against Hexagon's MSC2020 catalogue as assignable.
* `tags`: multiplicative complexity, matrix multiplication, Strassen's algorithm, Boolean
  circuits, XOR-AND circuits, SAT solving, LRAT proofs, Lean 4, bv_decide
* `comments`: page count and links to the code, the per-cube records, the Lean proof and
  `REPRODUCE.md` at the pinned commit
* `provenance`: prepared text: what was produced by AI systems, what is machine-checked (LRAT
  proofs; the Lean theorem and its axioms), what is proved on paper only, and that all runs were on
  one machine. Edit the first sentence if it does not describe your role.
* `formalizations`: empty. Hexagon accepts only Mathlib, Palomar, Prove2.me and Tau Ceti links
  there, not GitHub. The Lean proof is cited in the paper, in `comments` and in `provenance`.
  Registering the Lean proof on Palomar would allow a formalization link later
  (`PUT /api/v1/works/{identifier}/formalizations`).
* `license`: CC BY 4.0

## 4. Deposit through the web form

1. Go to hexagonmath.org and sign in with ORCID.
2. Start a new deposit and enter the metadata of §3, with your answers to §1.
3. Upload `dist/mc222-source.zip` as the source archive. Expand it and choose `main.tex` as the
   main file (`anc/` cannot hold the main file).
4. Optionally upload `dist/mc222-formal.zip` as a formal artifact.
5. Run the preview and compare the preview PDF with `dist/main.pdf`, in particular page 1, the
   tables and the verbatim blocks in Section 8 and the appendix. The source check
   (`preview/check`) is advisory.
6. Tick the four confirmations only if you can make them.
7. Submit. Submitting reserves a permanent identifier, which is never reused, and queues source
   screening; the record becomes public after screening. A published deposit can later be revised
   or withdrawn, but not deleted.

After publication: record the Hexagon identifier in `research/next/LOGBOOK.md` and in the README
of `research/ports/` (row 9), and update the X draft in `research/ports/posts-x.md`, whose other
posts still link an older commit under the old repository name.

## 5. Deposit through the API (alternative)

The API needs a bearer credential with scope `submissions:write`, issued from the Hexagon
account. The sequence is:

1. `POST /api/v1/submissions` with header `Idempotency-Key: <uuid>` and the body of
   `dist/metadata.json` (the four confirmations set by you). Returns a draft id.
2. `POST /api/v1/submissions/{draftId}/uploads` with `kind: "source-archive"`, file name,
   relative path, content type `application/zip` and size; then `PUT …/uploads/{uploadId}/parts/{n}`
   for each part and `POST …/uploads/{uploadId}/complete`.
3. `POST …/uploads/{uploadId}/expand`, then `POST …/uploads/{uploadId}/entry-point` with
   `{"relativePath": "main.tex"}`.
4. `POST /api/v1/submissions/{draftId}/preview`, then read `…/preview`, `…/preview/log` and
   `…/preview/pdf`.
5. `POST /api/v1/submissions/{draftId}/commit` reserves the identifier. Only this step is
   irreversible.

Steps 1–4 can be repeated and checked; step 5 should be taken only after the preview PDF has been
read.
