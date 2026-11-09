#!/usr/bin/env bash
# Model-based fuzzing of the scheduler (#156, #244): random concurrent
# programs from an independent scheduler model (scripts/models/sched_gen*.py,
# from the review of #249), each predicting the output and exit. Lean must
# match the model and C must match Lean; no program may hit an internal
# error.
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
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$v" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  if [[ $le -gt 2 ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le $g seed $s (saved fuzz-model-sched-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  { cat "$tmp/l.out"; echo "exit=$le"; } > "$tmp/l.full"
  if ! cmp -s "$tmp/l.full" "$e"; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH $g seed $s (saved fuzz-model-sched-$s.verse)"; continue
  fi
  ran=$((ran+1))
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> /dev/null; ce=$?
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); save; echo "C MISMATCH $g seed $s (C exit $ce, saved fuzz-model-sched-$s.verse)"
  fi
done
echo "fuzz-model-sched: $n programs from seed $first, $ran runs as the model says, $bad bad"
[[ $bad -eq 0 ]]
