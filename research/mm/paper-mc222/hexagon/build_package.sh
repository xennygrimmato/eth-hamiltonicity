#!/usr/bin/env bash
# Build the files for a Hexagon (hexagonmath.org) deposit of the MC(2x2 over F2) = 7 paper.
#
# Usage:  AUTHOR="First Last" ORCID="0000-0000-0000-0000" ./build_package.sh
#         (optional: AFFIL="Affiliation" adds a line under the name; ORCID only fills metadata.json)
#
# Writes, in hexagon/dist/ (git-ignored):
#   mc222-source.zip       upload as "source-archive"; main file main.tex. Contains main.tex (with the
#                          author line filled in), refs.bib, main.bbl, and anc/ with the Python half of
#                          the computation and the recorded results (only extensions Hexagon accepts).
#   mc222-formal.zip       optional, upload as "formal-artifact" (kept by Hexagon, not public): the Lean
#                          project sources and the Rust search, for archival next to the paper.
#   main.pdf               the PDF compiled from mc222-source.zip exactly as packed (a local check).
#   abstract.txt, metadata.json   copies of the form values, with the author filled in.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PAPER="$(dirname "$HERE")"
ROOT="$(cd "$PAPER/../../.." && pwd)"
: "${AUTHOR:?set AUTHOR=\"Your Name\" (it replaces the author line of main.tex)}"
DIST="$HERE/dist"; rm -rf "$DIST"; mkdir -p "$DIST"
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT

# --- source archive
mkdir -p "$W/src/anc/results"
python3 - "$PAPER/main.tex" "$W/src/main.tex" "$AUTHOR" "${AFFIL:-}" <<'PY'
import sys
src, dst, author, affil = sys.argv[1:5]
s = open(src, encoding="utf-8").read()
import re
line = author if not affil else author + r"\\ " + affil
s, n = re.subn(r"\\author\{[^}]*\}", lambda _: r"\author{" + line + "}", s, count=1)
assert n == 1, "no \\author line in main.tex"
open(dst, "w", encoding="utf-8").write(s)
PY
cp "$PAPER/refs.bib" "$PAPER/main.bbl" "$W/src/"
M="$ROOT/tools/mc222"
for f in gen_cnf.py orbits.py orbits_mm123.py run_sat.py run_sat_mm123.py summarize_sat.py verify_circuit.py compare_results.py; do
  cp "$M/$f" "$W/src/anc/"
done
cp "$M"/results/*.tsv "$M"/results/*.log "$W/src/anc/results/"
# Hexagon: anc/ accepts .json .jsonl .csv .tsv .yaml .yml .log .py (and a few CAS formats); 4 MiB per text file
bad=$(cd "$W/src/anc" && find . -type f ! -name '*.py' ! -name '*.tsv' ! -name '*.log')
[ -z "$bad" ] || { echo "unsupported files in anc/: $bad"; exit 1; }
big=$(find "$W/src" -type f -size +4M)
[ -z "$big" ] || { echo "files over 4 MiB: $big"; exit 1; }
(cd "$W/src" && zip -qrX "$DIST/mc222-source.zip" main.tex refs.bib main.bbl anc)

# --- compile exactly what was packed (pdflatex twice, using the shipped .bbl; no bibtex)
mkdir -p "$W/build" && (cd "$W/build" && unzip -q "$DIST/mc222-source.zip" \
  && pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null \
  && pdflatex -interaction=nonstopmode -halt-on-error main.tex > pass2.log) \
  || { echo "compile failed; see $W/build/main.log"; trap - EXIT; exit 1; }
if grep -q "undefined\|Rerun to get" "$W/build/pass2.log"; then echo "warning: undefined references or rerun needed"; fi
cp "$W/build/main.pdf" "$DIST/main.pdf"

# --- formal artifacts (optional upload)
L="$ROOT/research/mm/lean-mc222"
(cd "$ROOT" && zip -qrX "$DIST/mc222-formal.zip" \
   research/mm/lean-mc222/MC222 research/mm/lean-mc222/MC222.lean research/mm/lean-mc222/lakefile.toml \
   research/mm/lean-mc222/lean-toolchain research/mm/lean-mc222/lake-manifest.json \
   research/mm/lean-mc222/CheckAxioms.lean research/mm/lean-mc222/check_axioms.sh \
   research/mm/lean-mc222/NOTES.md research/mm/lean-mc222/scripts \
   tools/mc222/src tools/mc222/Cargo.toml tools/mc222/Cargo.lock tools/mc222/README.md \
   tools/mc222/run_all.sh tools/mc222/run_mm123.sh tools/mc222/plane_orbits.txt tools/mc222/plane_orbits_mm123.txt \
   research/mm/paper-mc222/REPRODUCE.md -x '*/.lake/*')

# --- form values
pages=$(pdfinfo "$DIST/main.pdf" 2>/dev/null | awk '/^Pages/{print $2}')
python3 - "$HERE/metadata.json" "$DIST/metadata.json" "$AUTHOR" "${ORCID:-@ORCID@}" "$HERE/abstract.txt" "$PAPER/main.tex" "${pages:-?}" <<'PY'
import json, re, sys
src, dst, author, orcid, abstract, tex, pages = sys.argv[1:8]
commit = re.search(r"\\newcommand\{\\commit\}\{([0-9a-f]{40})\}", open(tex, encoding="utf-8").read()).group(1)
t = open(src, encoding="utf-8").read()
t = t.replace("@AUTHOR@", author).replace("@ORCID@", orcid).replace("@COMMIT@", commit).replace("@PAGES@", pages)
m = json.loads(t)
m["abstract"] = open(abstract, encoding="utf-8").read().strip()
json.dump(m, open(dst, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("metadata: commit", commit, "| orcid", orcid)
PY
cp "$HERE/abstract.txt" "$DIST/abstract.txt"
echo "built in $DIST:"; ls -l "$DIST" | awk 'NR>1{print "  " $5 "\t" $9}'
echo "main.pdf: ${pages:-?} pages; check the author line on page 1 before uploading"
