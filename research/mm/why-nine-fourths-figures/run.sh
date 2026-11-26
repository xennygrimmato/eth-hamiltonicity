#!/usr/bin/env bash
# Generate all pages. Usage: GEMINI_API_KEY=... ./run.sh
# Page 1 is generated first and passed to the other pages as a style reference.
set -euo pipefail
cd "$(dirname "$0")"; mkdir -p out
[ -s out/1-why.png ] || python3 gen.py prompts/1-why.txt out/1-why.png
for p in prompts/[2-9]-*.txt; do
  n=$(basename "$p" .txt)
  [ -s "out/$n.png" ] || python3 gen.py "$p" "out/$n.png" out/1-why.png &
done
wait
ls -la out
