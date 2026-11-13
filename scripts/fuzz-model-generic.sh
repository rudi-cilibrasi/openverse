#!/usr/bin/env bash
# Model-based fuzzing of generic functions with several values (#235, #282): random
# programs from an independent model (scripts/models/generic_mv.py, from the review of
# #282) that call such functions on all three paths (inlined, taken lazily, computed at
# the call), at several types, from for, first-success and <decides> consumers, generic
# ones too, with arguments that print or choose. The model predicts each program's output,
# or the diagnostics it may be refused with. On a random stream of its own, a program
# also has type parameters with upper bounds (#502). Lean must match the model, and C must match
# Lean. No program may hit an internal error. Programs expected to run are skipped if
# they run out of fuel (exit 3).
#   usage: scripts/fuzz-model-generic.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; ref=0; fuel=0; slow=0; bad=0; bounded=0
declare -A paths
for ((s=first; s<first+n; s++)); do
  save() { cp "$tmp/p.verse" "$root/fuzz-model-generic-$s.verse"; cp "$tmp/p.expected" "$root/fuzz-model-generic-$s.expected"; }
  python3 -I "$root/scripts/models/generic_mv.py" "$s" "$tmp" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  for p in $(sed -n 's/^paths=\([^ ]*\).*/\1/p' "$tmp/p.meta" | tr , ' '); do paths[$p]=$(( ${paths[$p]:-0} + 1 )); done
  grep -q ' bounds=yes' "$tmp/p.meta" && bounded=$((bounded+1))
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?; sed -i -E '/^[^ ]*:[0-9]+:[0-9]+: warning: /d' "$tmp/l.err"
  if [[ $(tail -n 1 "$tmp/p.expected") == exit=4 ]]; then
    if [[ $le -eq 4 && ! -s "$tmp/l.out" ]] &&
        ! grep -qi internal "$tmp/l.err" &&
        grep -qF -f <(sed '$d' "$tmp/p.expected") "$tmp/l.err"; then
      ref=$((ref+1)); continue
    fi
    bad=$((bad+1)); save
    echo "EXPECTED REFUSAL seed $s (Lean exit $le, saved fuzz-model-generic-$s.verse and .expected): $(head -c 200 "$tmp/l.err")"
    continue
  fi
  if [[ $le -eq 3 ]]; then fuel=$((fuel+1)); continue; fi
  # (Lean timed out: the reference interpreter is far slower than C on some long backtracking
  # programs, 78 s against 0.1 s at mv seed 20767547; run --emit wrote the bytecode before
  # interpreting, so C is checked against the model alone)
  if [[ $le -eq 124 && -s "$tmp/p.vbc" ]]; then
    (ulimit -v 4000000; timeout 60 "$cv" "$tmp/p.vbc") > "$tmp/c.out" 2> /dev/null; ce=$?
    { cat "$tmp/c.out"; echo "exit=$ce"; } > "$tmp/c.full"
    if cmp -s "$tmp/c.full" "$tmp/p.expected"; then
      slow=$((slow+1)); echo "slow in Lean: seed $s (C matches the model)"; continue
    fi
    bad=$((bad+1)); save; echo "LEAN TIMEOUT seed $s, and C (exit $ce) differs from the model (saved fuzz-model-generic-$s.verse)"; continue
  fi
  { cat "$tmp/l.out"; echo "exit=$le"; } > "$tmp/l.full"
  if grep -qi "internal" "$tmp/l.err" || ! cmp -s "$tmp/l.full" "$tmp/p.expected"; then
    bad=$((bad+1)); save
    echo "MODEL MISMATCH seed $s (Lean exit $le, saved fuzz-model-generic-$s.verse): $(head -c 200 "$tmp/l.err") [$(cat "$tmp/p.meta")]"
    continue
  fi
  [[ -s "$tmp/p.vbc" ]] || { bad=$((bad+1)); save; echo "NO BYTECODE seed $s"; continue; }
  (ulimit -v 4000000; timeout 60 "$cv" "$tmp/p.vbc") > "$tmp/c.out" 2> /dev/null; ce=$?
  ran=$((ran+1))
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); save; echo "C MISMATCH seed $s (C exit $ce, saved fuzz-model-generic-$s.verse)"
  fi
done
echo "fuzz-model-generic: $n programs from seed $first ($bounded with upper bounds, #502), $ran ran in both, $ref refused as the model says, $fuel out of fuel, $slow slow in Lean (C matches the model), $bad bad (paths: inlined ${paths[inlined]:-0}, lazy ${paths[lazy]:-0}, eager ${paths[eager]:-0})"
[[ $bad -eq 0 ]]
