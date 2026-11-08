#!/usr/bin/env bash
# Differential fuzzing of the front end's class features: random Verse programs
# (scripts/gen-classes.py) with class hierarchies, interfaces, overrides and
# (super:), constructor functions and their overloads, qualified (i:)M
# implementations, parametric classes, overloaded functions and defer, run by
# the Lean reference interpreter and by cverse. Stdout and exit codes must
# agree, and no program may hit an internal error (a lowering that fails
# Prog.checkTypes), be refused (the generator writes valid programs), or run
# unreachable code (it writes no Err()).
#   usage: scripts/fuzz-classes.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0
for ((s=first; s<first+n; s++)); do
  python3 -I "$root/scripts/gen-classes.py" "$s" > "$tmp/p.verse"
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  # (the generator writes no Err(), so a user error is unreachable code run:
  # a lowering bug; other runtime errors are compared with C)
  if [[ $le -ne 0 && $le -ne 3 && $le -ne 2 ]] || grep -q "error: user" "$tmp/l.err"; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-classes-$s.verse"
    echo "REFUSED or INTERNAL seed $s (exit $le, saved fuzz-classes-$s.verse): $(head -c 200 "$tmp/l.err")"
    continue
  fi
  [[ -s "$tmp/p.vbc" ]] || { bad=$((bad+1)); echo "EMIT FAILED seed $s"; continue; }
  ran=$((ran+1))
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-classes-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-classes-$s.verse)"
  fi
done
echo "fuzz-classes: $n programs from seed $first, $ran run in both, $bad bad"
[[ $bad -eq 0 ]]
