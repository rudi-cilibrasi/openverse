#!/usr/bin/env bash
# Model-based fuzzing of the variance of parametric classes (Book of Verse
# ch. 10, "Instantiation and Identity"; docs/research/variance.md): random
# classes whose members use their type parameter at random polarities, a
# subclass that adds members and overrides, and a conversion of an instance
# at one type argument to another (scripts/models/variance.py). The model
# predicts the Book's verdict and openverse's (Verse Core types a reference
# by its object's own class, so a conversion needs every concrete class of
# the source to allow it by its fields); accepted programs print what it
# predicts, refused ones say what it expects. Lean must match the model, C
# must match Lean, and no program may hit an internal error: a variance the
# front end allows that Verse Core does not would be one (Prog.checkTypes).
#   usage: scripts/fuzz-model-variance.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-150}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; ref=0; bad=0
for ((s=first; s<first+n; s++)); do
  save() { cp "$tmp/p.verse" "$root/fuzz-model-variance-$s.verse"; cp "$tmp/p.exp" "$root/fuzz-model-variance-$s.expected"; }
  python3 -I "$root/scripts/models/variance.py" "$s" "$tmp/p.exp" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  rm -f "$tmp/p.vbc"
  timeout 120 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  sed -i -E '/^[^ ]*:[0-9]+:[0-9]+: warning: /d' "$tmp/l.err"
  want=$(head -1 "$tmp/p.exp" | sed 's/exit=//')
  if grep -q "internal" "$tmp/l.err"; then
    bad=$((bad+1)); save; echo "INTERNAL seed $s (saved fuzz-model-variance-$s.verse): $(head -c 300 "$tmp/l.err")"; continue
  fi
  if [[ $want == 4 ]]; then
    msg=$(sed -n 2p "$tmp/p.exp")
    if [[ $le == 4 ]] && grep -qF -- "$msg" "$tmp/l.err"; then ref=$((ref+1)); continue; fi
    bad=$((bad+1)); save; echo "EXPECTED REFUSAL seed $s (exit $le, saved fuzz-model-variance-$s.verse): $(head -c 300 "$tmp/l.err")"; continue
  fi
  if [[ $le != "$want" ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le seed $s (saved fuzz-model-variance-$s.verse): $(head -c 300 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH seed $s (saved fuzz-model-variance-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
  if [[ $ce != "$want" ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    bad=$((bad+1)); save; echo "C MISMATCH seed $s (C exit $ce, saved fuzz-model-variance-$s.verse)"; continue
  fi
  ok=$((ok+1))
done
echo "fuzz-model-variance: $n seeds from seed $first; $ok ran as the model says, $ref refused as it says, $bad bad"
[[ $bad -eq 0 ]]
