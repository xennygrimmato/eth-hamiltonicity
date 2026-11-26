#!/usr/bin/env bash
# Certificates for the K_{2,3} refined bracket on the hard region F'_1 (research/ports/k2m/notes.md §5.4):
#   job s910 : S(9/10),  Br'(sigma; 9/10, 6/5)   >= 0 on F'_1   (16 pieces: case c|l x eps-sign pattern s)
#   job cl0  : (CL**_0), Br'(sigma; 12/13, 15/13) >= 0 on F'_1   (16 far pieces, central cube [-R,R]^6, R = (181/256)^2, of the
#              case-c pieces covered by 8 k2near orthant certificates; case l misses the central cube)
# usage: ./run_k2.sh [s910|cl0|all]   (certificates go to certs/k2/, which is git-ignored)
set -euo pipefail
cd "$(dirname "$0")"
cargo build --release -q
mkdir -p certs/k2
B=./target/release
JOB=${1:-all}
SIGNS="+++ ++- +-+ +-- -++ -+- --+ ---"
run() { # name file
  echo "== $1  ($(date +%T))"
  $B/ivcert "$1" --max-depth 60 --out "$2" | sed -n 3,5p
  $B/ivcheck "$2" | sed -n 1p
}
if [[ $JOB == s910 || $JOB == all ]]; then
  for c in c l; do for s in $SIGNS; do
    run "k2far:lam=9/10:eta=6/5:case=$c:s=$s" "certs/k2/s910_${c}_s$s.cert"
  done; done
fi
if [[ $JOB == cl0 || $JOB == all ]]; then
  for s in $SIGNS; do
    run "k2near:lam=12/13:eta=15/13:case=c:s=$s:t=0.70703125" "certs/k2/cl0_near_s$s.cert"
  done
  for s in $SIGNS; do
    run "k2far:lam=12/13:eta=15/13:case=c:s=$s:rho=0.4998931884765625" "certs/k2/cl0_c_s$s.cert"
    run "k2far:lam=12/13:eta=15/13:case=l:s=$s" "certs/k2/cl0_l_s$s.cert"
  done
fi
sha256sum certs/k2/*.cert
