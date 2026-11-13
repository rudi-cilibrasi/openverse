#!/usr/bin/env bash
# Model-based fuzzing of function values of functions with named parameters
# (#503): random programs from scripts/models/named_fn_values.py, a model of
# docs/research/named-function-values.md that predicts each program's output
# (written order, defaults once at the call in declaration order and scope,
# bound receivers' live fields and overrides, rollback), or the message of
# the refusal it expects. Lean must match the model, and C must match Lean;
# no program may hit an internal error.
# With --tuples, the programs come from scripts/models/tuple_params.py, a
# model of docs/research/tuple-parameters.md (destructured tuple parameters),
# on a stream of their own.
#   usage: scripts/fuzz-model-named-values.sh [COUNT [FIRST_SEED [--tuples]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
model=named_fn_values; stem=fuzz-model-named-values
if [[ "${3:-}" == --tuples ]]; then model=tuple_params; stem=fuzz-model-tuple-params; fi
ov="${OV:-$root/.lake/build/bin/openverse}"; cv="${CV:-$root/runtime/build/cverse}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; ref=0; bad=0
for ((s=first; s<first+n; s++)); do
  save() { cp "$tmp/p.verse" "$root/$stem-$s.verse"; cp "$tmp/p.exp" "$root/$stem-$s.expected"; }
  python3 -I "$root/scripts/models/$model.py" "$s" "$tmp/p.exp" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  rm -f "$tmp/p.vbc"
  timeout 120 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?; sed -i -E '/^[^ ]*:[0-9]+:[0-9]+: warning: /d' "$tmp/l.err"
  want=$(head -1 "$tmp/p.exp" | sed 's/exit=//')
  if [[ $want == 4 ]]; then
    msg=$(sed -n 2p "$tmp/p.exp")
    if [[ $le == 4 ]] && grep -qF "$msg" "$tmp/l.err" && ! grep -q "internal" "$tmp/l.err" && [[ ! -e $tmp/p.vbc ]]; then
      ref=$((ref+1)); continue
    fi
    bad=$((bad+1)); save; echo "EXPECTED REFUSAL seed $s (exit $le, saved $stem-$s.verse): $(head -c 300 "$tmp/l.err")"; continue
  fi
  if [[ $le != "$want" ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le seed $s (saved $stem-$s.verse): $(head -c 300 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH seed $s (saved $stem-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
  if [[ $ce != "$want" ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    bad=$((bad+1)); save; echo "C MISMATCH seed $s (C exit $ce, saved $stem-$s.verse)"; continue
  fi
  ok=$((ok+1))
done
echo "$stem: $n programs from seed $first, $ok ran as the model says, $ref refused as it says, $bad bad"
[[ $bad -eq 0 ]]
