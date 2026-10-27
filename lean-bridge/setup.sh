#!/usr/bin/env bash
# Fetch openai/math's SubexponentialSAT Lean sources at the pinned commit into ./OAI.
set -euo pipefail
cd "$(dirname "$0")"
REV=7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
tmp=$(mktemp -d)
git -C "$tmp" init -q
git -C "$tmp" remote add origin https://github.com/openai/math.git
git -C "$tmp" sparse-checkout init --cone
git -C "$tmp" sparse-checkout set lean/OAI/Algorithms/SubexponentialSAT
git -C "$tmp" fetch --depth 1 origin "$REV"
git -C "$tmp" checkout -q FETCH_HEAD
rm -rf OAI && mkdir -p OAI/Algorithms
cp -r "$tmp/lean/OAI/Algorithms/SubexponentialSAT" OAI/Algorithms/
cp "$tmp/LICENSE" OAI/LICENSE-openai-math 2>/dev/null || true
rm -rf "$tmp"
echo "Fetched $(find OAI -name '*.lean' | wc -l) files. Next: lake exe cache get && lake build"
