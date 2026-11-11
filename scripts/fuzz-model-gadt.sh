#!/usr/bin/env bash
# Model-based fuzzing of classes that fix, repeat, relate or hide type
# arguments (GADTs, #209): random programs from six independent models
# (scripts/models/gadt_*.py, from the reviews of #236, #242, #243 and #250,
# with the clauses after a cast from #277 and named arguments with defaults of no
# type of their own through opening dispatches from #317, and covariant <suspends>
# overrides through them from #324, also spawned on a value of the class itself from
# #321, and through a class between that redeclares it narrower from #337; interfaces that
# give a parent interface other type arguments from #344, their defaults from #347, also in
# classes giving composite arguments from #355),
# each predicting the program's output, or the message of the refusal it
# expects. Each seed uses one model in turn. Lean must match the model, and C
# must match Lean; no program may hit an internal error.
#   usage: scripts/fuzz-model-gadt.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
gens=(gadt_rel gadt_rel2 gadt_exist gadt_refine gadt_open gadt_bounds)
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; ref=0; bad=0
for ((s=first; s<first+n; s++)); do
  g="${gens[$((s % ${#gens[@]}))]}"
  save() { cp "$tmp/p.verse" "$root/fuzz-model-gadt-$s.verse"; cp "$tmp/p.exp" "$root/fuzz-model-gadt-$s.expected"; }
  python3 -I "$root/scripts/models/$g.py" "$s" "$tmp/p.exp" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED $g seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  rm -f "$tmp/p.vbc"
  timeout 120 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  want=$(head -1 "$tmp/p.exp" | sed 's/exit=//')
  if [[ $want == 4 ]]; then
    msg=$(sed -n 2p "$tmp/p.exp")
    if [[ $le == 4 ]] && grep -qF "$msg" "$tmp/l.err" && ! grep -q "internal" "$tmp/l.err"; then ref=$((ref+1)); continue; fi
    bad=$((bad+1)); save; echo "EXPECTED REFUSAL $g seed $s (exit $le, saved fuzz-model-gadt-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if [[ $le != "$want" ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le $g seed $s (saved fuzz-model-gadt-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH $g seed $s (saved fuzz-model-gadt-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
  if [[ $ce != "$want" ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    bad=$((bad+1)); save; echo "C MISMATCH $g seed $s (C exit $ce, saved fuzz-model-gadt-$s.verse)"; continue
  fi
  ok=$((ok+1))
done
echo "fuzz-model-gadt: $n programs from seed $first, $ok ran as the model says, $ref refused as it says, $bad bad"
[[ $bad -eq 0 ]]
