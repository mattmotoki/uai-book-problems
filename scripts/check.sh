#!/usr/bin/env bash
# Build our library, then audit axioms. Exit 0 only when every listed theorem uses
# the three standard axioms (propext, Classical.choice, Quot.sound) and nothing else.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
if grep -rnE '^\s*(axiom|sorry)\b|\bsorry\b|\badmit\b' HutterPrizes --include=*.lean | grep -v Audit.lean; then
  echo "check: sorry, admit or axiom in HutterPrizes/" >&2; exit 1
fi
nice -n 10 lake build HutterPrizes
out=$(lake env lean HutterPrizes/Audit.lean 2>&1)
echo "$out"
flat=$(echo "$out" | tr '\n' ' ' | sed 's/  */ /g')
bad=$(echo "$flat" | grep -oE "depends on axioms: \[[^]]*\]" | tr -d '[]' | sed 's/depends on axioms: //' \
  | tr ',' '\n' | sed 's/ //g' | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' | sort -u || true)
if echo "$out" | grep -qE "(^|: )error:|sorryAx" || [ -n "$bad" ]; then
  echo "check: FAIL. Extra axioms or errors: $bad" >&2; exit 1
fi
echo "check: PASS"
