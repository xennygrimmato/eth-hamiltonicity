#!/bin/sh
# Usage: ./setup.sh /path/to/prime-algorithm   (Ni's repository, release v0.1-verified)
set -e
NI="$1"; HERE="$(cd "$(dirname "$0")" && pwd)"; ANTH=/home/user/anth-build/.lake
mkdir -p "$HERE/ni" "$HERE/build"
cp -r "$NI/formal/bridge/EthFollowup" "$NI/formal/unified/PrimeAlgorithm" \
      "$NI/formal/independent/PrimeIndependent" "$HERE/ni/"
# Upstream EthFollowup oleans (read-only symlinks): one package root per search-path entry.
(cd "$ANTH/build/lib/lean" && find EthFollowup -type f) | while read f; do
  t="$HERE/build/$f"; [ -e "$t" ] || { mkdir -p "$(dirname "$t")"; ln -s "$ANTH/build/lib/lean/$f" "$t"; }
done
LP="$HERE/build:$ANTH/build/lib/lean"
for p in mathlib batteries aesop Qq proofwidgets plausible LeanSearchClient importGraph Cli; do
  LP="$LP:$ANTH/packages/$p/.lake/build/lib/lean"; done
echo "$LP" > "$HERE/scripts/leanpath"
