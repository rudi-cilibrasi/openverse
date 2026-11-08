#!/usr/bin/env bash
# Differential fuzzing of floats (#127): random Verse programs of float
# arithmetic, NaN and infinities, conversions, comparisons and ToString
# (scripts/gen-floats.py), run by the Lean reference interpreter and by
# cverse; both must print exactly what Python's IEEE doubles give under
# Verse's rules (the generator's expected output).
#   usage: scripts/fuzz-floats.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-200}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0
for ((s=first; s<first+n; s++)); do
  python3 -I "$root/scripts/gen-floats.py" "$s" "$tmp/p.verse" "$tmp/want.out"
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2>&1; le=$?
  ok=1
  if [[ $le -ne 0 ]] || ! cmp -s "$tmp/l.out" "$tmp/want.out"; then ok=0
  elif [[ ! -s "$tmp/p.vbc" ]]; then ok=0
  else
    timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>&1; ce=$?
    if [[ $ce -ne 0 ]] || ! cmp -s "$tmp/c.out" "$tmp/want.out"; then ok=0; fi
  fi
  if [[ $ok -eq 0 ]]; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-floats-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-floats-$s.verse)"
  fi
done
echo "fuzz-floats: $n programs from seed $first, $bad bad"
[[ $bad -eq 0 ]]
