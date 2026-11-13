#!/usr/bin/env bash
# Model fuzzing of = and <> (Verse's equality, Value.veq): random Verse programs
# (scripts/gen-equality.py) compare values of many types with the empty value at
# every depth, directly, inside arrays, options, tuples, maps and one struct's
# instances, through generic functions, as map keys and as searched elements. The
# Lean reference interpreter and cverse must both print what the generator's model
# of the Book of Verse's equality expects.
#   usage: scripts/fuzz-equality.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0; cmps=0
for ((s = first; s < first + n; s++)); do
  python3 -I "$root/scripts/gen-equality.py" "$s" > "$tmp/p.verse"
  python3 -I "$root/scripts/gen-equality.py" "$s" --expected > "$tmp/want"
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  if [[ $le -ne 0 ]] || ! cmp -s "$tmp/l.out" "$tmp/want"; then
    bad=$((bad+1)); echo "MISMATCH seed $s (Lean exit $le)"
    diff "$tmp/want" "$tmp/l.out" | head -5; head -3 "$tmp/l.err"; continue
  fi
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  if [[ $ce -ne 0 ]] || ! cmp -s "$tmp/c.out" "$tmp/want"; then
    bad=$((bad+1)); echo "MISMATCH seed $s (C exit $ce)"; diff "$tmp/want" "$tmp/c.out" | head -5; continue
  fi
  cmps=$((cmps + $(wc -l < "$tmp/want")))
done
echo "fuzz-equality: $n programs from seed $first, $cmps comparisons, $bad mismatches"
[[ $bad -eq 0 ]]
