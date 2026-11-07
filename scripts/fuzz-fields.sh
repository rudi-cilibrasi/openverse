#!/usr/bin/env bash
# Differential fuzzing of the C runtime's heap reclamation (#50): random Verse
# programs whose objects hold arrays in fields, written across calls, failure
# contexts, <decides> callees, for filters and recursion (scripts/gen-fields.py
# for odd seeds, scripts/gen-fields2.py for even ones), run by the Lean
# reference interpreter and by cverse; stdout and exit codes must agree.
#   usage: scripts/fuzz-fields.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0; mm=0
for ((s=first; s<first+n; s++)); do
  gen="$root/scripts/gen-fields.py"; (( s % 2 == 0 )) && gen="$root/scripts/gen-fields2.py"
  python3 -I "$gen" "$s" > "$tmp/p.verse"
  timeout 60 "$ov" run "$tmp/p.verse" > "$tmp/l.out" 2>/dev/null; le=$?
  if [[ $le -ne 0 ]] || ! "$ov" emit "$tmp/p.verse" -o "$tmp/p.vbc" 2>/dev/null; then bad=$((bad+1)); continue; fi
  ran=$((ran+1))
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    mm=$((mm+1)); cp "$tmp/p.verse" "$root/fuzz-fields-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-fields-$s.verse)"
  fi
done
echo "fuzz-fields: $n programs from seed $first, $ran run, $bad not runnable, $mm mismatches"
[[ $mm -eq 0 ]]
