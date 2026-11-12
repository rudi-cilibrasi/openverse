#!/usr/bin/env bash
# Model-based fuzzing of FIFO event resumption (#513, `--event-fifo`):
# random programs whose tasks (spawned ones, branches, Main, tasks spawned
# in a task's first run, the arms of a sync or race) wait on events and
# signal them, some in chains, from the model scripts/models/event_fifo.py,
# which predicts the output: each Signal's waiters go on in the order they
# began to wait. Lean must match the model, and C must match Lean; no
# program may hit an internal error.
#   usage: scripts/fuzz-model-fifo.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; bad=0
for ((s=first; s<first+n; s++)); do
  save() { cp "$tmp/p.verse" "$root/fuzz-model-fifo-$s.verse"; cp "$tmp/p.exp" "$root/fuzz-model-fifo-$s.expected"; }
  python3 -I "$root/scripts/models/event_fifo.py" "$s" "$tmp/p.exp" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  rm -f "$tmp/p.vbc"
  timeout 120 "$ov" run "$tmp/p.verse" --event-fifo --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  if [[ $le != 0 ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le seed $s (saved fuzz-model-fifo-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH seed $s (saved fuzz-model-fifo-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>&1; ce=$?
  if [[ $ce != 0 ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); save; echo "C DIFFERS seed $s (exit $ce, saved fuzz-model-fifo-$s.verse)"; continue
  fi
  ok=$((ok+1))
done
echo "fuzz-model-fifo: $n programs from seed $first, $ok ran as the model says, $bad bad"
(( bad == 0 ))
