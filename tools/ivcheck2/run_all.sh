#!/usr/bin/env bash
# Independent re-check of the ivcert certificates (see README.md). Needs: python3, python-flint, sympy.
set -euo pipefail
cd "$(dirname "$0")"
C=${CERTS:-../ivcert/certs}
J=${JOBS:-4}
mkdir -p results
python3 selftest.py | tee results/selftest.log
python3 check.py --jobs "$J" --json results/hull3.json "$C/hull3-nosym.cert" | tee results/hull3.log
python3 check.py --jobs "$J" --json results/clnear.json "$C"/clnear_rho0.5_s*.cert | tee results/clnear.log
python3 check.py --jobs "$J" --json results/clstar_nosym.json "$C/clstar_rho0.5_nosym.cert" | tee results/clstar_nosym.log
python3 corner.py "$J" | tee results/corner.log
sha256sum "$C/hull3-nosym.cert" "$C"/clnear_rho0.5_s*.cert "$C/clstar_rho0.5_nosym.cert" | tee results/sha256.txt
