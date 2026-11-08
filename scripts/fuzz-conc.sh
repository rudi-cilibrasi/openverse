#!/usr/bin/env bash
# Differential fuzzing of the concurrency lowering (#156): random programs
# (scripts/gen-conc.py) with suspends functions, generic functions using
# branch, rush, race, sync and spawn, refined dispatch of suspends and
# immediate methods, spawned dispatches, nested spawns, defers and
# cancellation, run by the Lean reference interpreter and by cverse. Stdout
# and exit codes must agree, and no program may hit an internal error or be
# refused (the generator writes valid programs).
#   usage: scripts/fuzz-conc.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0
for ((s=first; s<first+n; s++)); do
  python3 -I "$root/scripts/gen-conc.py" "$s" > "$tmp/p.verse"
  timeout 60 "$ov" run "$tmp/p.verse" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  if [[ $le -ne 0 ]]; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-$s.verse"
    echo "REFUSED or INTERNAL seed $s (exit $le, saved fuzz-conc-$s.verse): $(head -c 200 "$tmp/l.err")"
    continue
  fi
  "$ov" emit "$tmp/p.verse" -o "$tmp/p.vbc" 2>/dev/null || { bad=$((bad+1)); echo "EMIT FAILED seed $s"; continue; }
  ran=$((ran+1))
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-conc-$s.verse)"
  fi
done
echo "fuzz-conc: $n programs from seed $first, $ran run in both, $bad bad"
[[ $bad -eq 0 ]]
