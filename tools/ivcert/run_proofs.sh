#!/usr/bin/env bash
# Regenerate and independently check all certificates of the hull notes (§3.3).
set -euo pipefail
cd "$(dirname "$0")"
cargo build --release -q
mkdir -p certs
B=./target/release
$B/ivcert hull3 --out certs/hull3.cert | sed -n 3,4p
$B/ivcert hull3 --no-symmetry --out certs/hull3-nosym.cert | sed -n 3,4p
for s in +++ ++- +-+ +-- -++ -+- --+ ---; do
  $B/ivcert "clnear:rho=0.5:s=$s" --max-depth 50 --out "certs/clnear_rho0.5_s$s.cert" | sed -n 3,4p
done
$B/ivcert clstar:rho=0.5 --max-depth 50 --out certs/clstar_rho0.5.cert | sed -n 3,4p
$B/ivcert clstar:rho=0.5 --max-depth 50 --no-symmetry --out certs/clstar_rho0.5_nosym.cert | sed -n 3,4p
for f in certs/*.cert; do echo "== $f"; $B/ivcheck "$f" | sed -n 1p; done
sha256sum certs/*.cert
