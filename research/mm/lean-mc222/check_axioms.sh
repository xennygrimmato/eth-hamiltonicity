#!/usr/bin/env bash
# After `lake build`: print the axioms of the main theorem and check that the list is the
# expected one: the three standard axioms, and one auxiliary axiom per bv_decide / native_decide
# call (360 cubes, 3 bv_decide lemmas, 2 native_decide checks), and no sorryAx.
# Usage: ./check_axioms.sh
set -euo pipefail
cd "$(dirname "$0")"
out=$(lake env lean CheckAxioms.lean 2>&1)
echo "$out" | head -3
list=$(echo "$out" | tr ',[]' '\n\n\n' | sed 's/^ *//' | grep -v '^$')
fail=0
check() { if [ "$2" = "$3" ]; then echo "ok   $1: $2"; else echo "FAIL $1: got $2, expected $3"; fail=1; fi; }
check "statement" "$(echo "$out" | grep -c '^MC222.mc_eq_seven : MC222.MC = 7$' || true)" 1
check "upper bound uses only standard axioms" \
  "$(echo "$out" | grep -c "'MC222.hasCircuit_seven' depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)" 1
main=$(echo "$out" | sed -n "/'MC222.mc_eq_seven' depends on axioms/,\$p")
mlist=$(echo "$main" | sed "s/.*depends on axioms://" | tr ',[]' '\n\n\n' | sed 's/^ *//' | grep -v '^$')
check "sorryAx absent" "$(echo "$mlist" | grep -c '^sorryAx$' || true)" 0
check "standard axioms" "$(echo "$mlist" | grep -cx 'propext\|Classical.choice\|Quot.sound' || true)" 3
check "compiled-evaluation axioms" "$(echo "$mlist" | grep -c '\._native\.' || true)" 365
check "  of which cubes" "$(echo "$mlist" | grep -c '^\(MC222\.\)\?cube_[0-9]*_[0-9]*\._native\.bv_decide\.' || true)" 360
check "  of which native_decide" "$(echo "$mlist" | grep -c '\._native\.native_decide\.' || true)" 2
check "other axioms" "$(echo "$mlist" | grep -vcx 'propext\|Classical.choice\|Quot.sound\|.*\._native\..*' || true)" 0
if [ $fail = 0 ]; then echo "AXIOM CHECK PASSED"; else echo "AXIOM CHECK FAILED"; exit 1; fi
