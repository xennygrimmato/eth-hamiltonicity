#!/usr/bin/env bash
# Reproduce everything: validation cases, the exact Rust search for k=6, and the
# proof-producing SAT run (CaDiCaL + LRAT, checked by lrat-check) for k=6.
# Usage: ./run_all.sh [ext_dir]   (ext_dir: where CaDiCaL / drat-trim are cloned and built)
set -euo pipefail
cd "$(dirname "$0")"
EXT=${1:-$PWD/ext}
mkdir -p out out/sat "$EXT"

# --- external tools, pinned
if [ ! -x "$EXT/cadical-2.1.3/build/cadical" ]; then
  git clone -q --depth 1 --branch rel-2.1.3 https://github.com/arminbiere/cadical "$EXT/cadical-2.1.3"
  (cd "$EXT/cadical-2.1.3" && ./configure >/dev/null && make -j4 >/dev/null)
fi
if [ ! -x "$EXT/drat-trim/lrat-check" ]; then
  git clone -q https://github.com/marijnheule/drat-trim "$EXT/drat-trim"
  (cd "$EXT/drat-trim" && git checkout -q 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 && make >/dev/null 2>&1)
fi
CAD=$EXT/cadical-2.1.3/build/cadical
CHK=$EXT/drat-trim/lrat-check

cargo build --release
B=target/release/mc222

echo "== validation, exact search (circuits re-checked by verify_circuit.py)"
for c in "f4 2" "f4 3" "polymul2 2" "polymul2 3" "mm221 3" "mm221 4" "polymul3 5" "polymul3 6" "mm222 5"; do
  set -- $c
  $B $1 $2 --out out/circuit_$1_$2.txt | grep -E "RESULT|FOUND"
  [ -f out/circuit_$1_$2.txt ] && python3 verify_circuit.py out/circuit_$1_$2.txt
done
$B mm222 5 --no-orbits | grep RESULT
$B mm222 7 --prefix "9,144;12,16" --out out/circuit_mm222_7_p2.txt | grep FOUND
python3 verify_circuit.py out/circuit_mm222_7_p2.txt

echo "== validation, SAT encoding (models decoded and re-checked)"
sat() { # args for gen_cnf.py
  python3 gen_cnf.py "$@" > out/sat/v.cnf
  r=$($CAD -q out/sat/v.cnf > out/sat/v.out; head -1 out/sat/v.out)
  echo "$* : $r"
  if [ "$r" = "s SATISFIABLE" ]; then
    python3 gen_cnf.py "$@" --decode out/sat/v.out > out/sat/v_circ.txt
    python3 verify_circuit.py out/sat/v_circ.txt
  fi
}
sat f4 2; sat f4 3; sat polymul2 2; sat polymul2 3; sat mm221 3; sat mm221 4
sat polymul3 5; sat polymul3 6
sat mm222 7 --helpers 0,1,2          # 7-AND circuit found from scratch inside the cube
sat mm222 5 --root 1,2

echo "== orbit representatives (Python, independent of the Rust orbit code)"
python3 orbits.py

echo "== k=6, exact search over the 72 first-gate orbits"
$B mm222 6 --threads 4 --out out/circuit_mm222_6.txt > out/mm222_k6_orbits.log
tail -2 out/mm222_k6_orbits.log

echo "== k=6, SAT + LRAT over 72 x 15 cubes"
python3 run_sat.py "$CAD" "$CHK" 3 6 > out/run_sat_k6.log
python3 summarize_sat.py out/sat_k6/results.tsv
