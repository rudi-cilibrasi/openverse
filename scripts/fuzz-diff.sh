#!/usr/bin/env bash
# Differential fuzzing: random Verse Core programs (OpenVerse/Core/Gen.lean) run by the
# Lean reference interpreter and by the C runtime must give byte-identical stdout,
# stderr and exit codes.   usage: scripts/fuzz-diff.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-500}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0; skipped=0
for ((s = first; s < first + n; s++)); do
  timeout 60 "$ov" gen "$s" >"$tmp/l.out" 2>"$tmp/l.err"; le=$?
  if [[ $le -eq 3 || $le -eq 124 ]]; then skipped=$((skipped+1)); continue; fi
  "$ov" gen "$s" --emit "$tmp/p.vbc"
  timeout 60 "$cv" "$tmp/p.vbc" >"$tmp/c.out" 2>"$tmp/c.err"; ce=$?
  if [[ $le -ne $ce ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    echo "MISMATCH seed $s: lean exit $le, C exit $ce"
    diff <(cat "$tmp/l.out" "$tmp/l.err") <(cat "$tmp/c.out" "$tmp/c.err") | head -10
    bad=$((bad+1))
  fi
done
echo "fuzz-diff: $n programs from seed $first, $bad mismatches, $skipped skipped (Lean ran out of fuel)"
[[ $bad -eq 0 ]]
