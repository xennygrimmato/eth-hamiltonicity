#!/usr/bin/env bash
# Build Anthropic's ETH proof (anthropics/formal-math, folder eth) at a pinned commit and our bridge
# on top of it. Usage: ./setup.sh WORKDIR   (WORKDIR gets a copy of eth/ plus the bridge).
set -euo pipefail
REV=16a5ce41304fcdaea4e0be7c132e1c361dc26da5
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:-$HERE/work}
tmp=$(mktemp -d)
git -C "$tmp" init -q && git -C "$tmp" remote add origin https://github.com/anthropics/formal-math.git
git -C "$tmp" sparse-checkout init --cone && git -C "$tmp" sparse-checkout set eth
git -C "$tmp" fetch --depth 1 origin "$REV" && git -C "$tmp" checkout -q FETCH_HEAD
mkdir -p "$W" && cp -r "$tmp/eth/." "$W/" && rm -rf "$tmp"
mkdir -p "$W/bridge/EthFollowup"
for f in "$HERE"/bridge/EthFollowup/*.lean; do cp -L "$f" "$W/bridge/EthFollowup/"; done
cat "$HERE/lakefile.bridge.toml" >> "$W/lakefile.toml"
cd "$W" && lake exe cache get && lake build && lake build EthFollowupBridge
