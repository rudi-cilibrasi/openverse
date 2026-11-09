#!/usr/bin/env bash
# Model-based fuzzing of the scheduler (#156, #244): random concurrent
# programs from an independent scheduler model (scripts/models/sched_gen*.py,
# from the review of #249), each predicting the output and exit, run with
# copies at small closed types (the default) and with generic roots only
# (OPENVERSE_GENERIC_ROOTS=1). In each mode Lean must match the model and C
# must match Lean; no program may hit an internal error.
#   usage: scripts/fuzz-model-sched.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-40}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
gens=(sched_gen sched_gen2)
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0
for ((s=first; s<first+n; s++)); do
  g="${gens[$((s % ${#gens[@]}))]}"
  python3 -I "$root/scripts/models/$g.py" "$s" "$tmp" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED $g seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  v="$tmp/g$s.verse"; e="$tmp/g$s.expected"
  save() { cp "$v" "$root/fuzz-model-sched-$s.verse"; cp "$e" "$root/fuzz-model-sched-$s.expected"; }
  for mode in plain gr; do
    if [[ $mode == gr ]]; then export OPENVERSE_GENERIC_ROOTS=1; else unset OPENVERSE_GENERIC_ROOTS; fi
    rm -f "$tmp/$mode.vbc"
    timeout 60 "$ov" run "$v" --emit "$tmp/$mode.vbc" > "$tmp/$mode.l.out" 2> "$tmp/$mode.l.err"; le=$?
    if [[ $le -gt 2 ]]; then
      bad=$((bad+1)); save; echo "LEAN EXIT $le ($mode) $g seed $s (saved fuzz-model-sched-$s.verse): $(head -c 200 "$tmp/$mode.l.err")"; continue
    fi
    { cat "$tmp/$mode.l.out"; echo "exit=$le"; } > "$tmp/$mode.l.full"
    if ! cmp -s "$tmp/$mode.l.full" "$e"; then
      bad=$((bad+1)); save; echo "MODEL MISMATCH ($mode) $g seed $s (saved fuzz-model-sched-$s.verse)"; continue
    fi
    ran=$((ran+1))
    timeout 60 "$cv" "$tmp/$mode.vbc" > "$tmp/$mode.c.out" 2> /dev/null; ce=$?
    if [[ $ce -ne $le ]] || ! cmp -s "$tmp/$mode.l.out" "$tmp/$mode.c.out"; then
      bad=$((bad+1)); save; echo "C MISMATCH ($mode) $g seed $s (C exit $ce, saved fuzz-model-sched-$s.verse)"
    fi
  done
  unset OPENVERSE_GENERIC_ROOTS
done
echo "fuzz-model-sched: $n programs from seed $first, $ran runs as the model says, $bad bad"
[[ $bad -eq 0 ]]
