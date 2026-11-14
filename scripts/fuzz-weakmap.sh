#!/usr/bin/env bash
# Model fuzzing of weak maps (docs/research/weak-map.md): random Verse programs
# (scripts/gen-weakmap.py) give a local, a module-scoped and a class field's
# weak map, each beside an ordinary map, one stream of writes, `+=`, whole
# replacements, calls and failure contexts, nested and in `for`s, and print
# every lookup after each statement. The Lean reference interpreter, cverse and
# the generator's model of the maps must give the same output, so a weak map
# agrees with its map on every lookup.
#   usage: scripts/fuzz-weakmap.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; mm=0; genbad=0
for ((s=first; s<first+n; s++)); do
  if ! python3 -I "$root/scripts/gen-weakmap.py" "$s" "$tmp/p.verse" "$tmp/model.out"; then
    genbad=$((genbad+1)); echo "GENERATOR FAILED seed $s"; continue
  fi
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2>"$tmp/l.err"; le=$?
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  ran=$((ran+1))
  if [[ $le -ne 0 || $ce -ne 0 ]] || ! cmp -s "$tmp/l.out" "$tmp/model.out" || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    mm=$((mm+1)); cp "$tmp/p.verse" "$root/fuzz-weakmap-$s.verse"
    echo "MISMATCH seed $s (Lean exit $le, C exit $ce; saved fuzz-weakmap-$s.verse)"
    head -3 "$tmp/l.err"
  fi
done
echo "fuzz-weakmap: $n programs from seed $first, $ran run, $mm mismatches, $genbad generator failures"
[[ $mm -eq 0 && $genbad -eq 0 ]]
