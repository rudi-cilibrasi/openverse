#!/usr/bin/env bash
# Model-based fuzzing of choice and functions with several values (#208,
# #235): random programs from an independent model (scripts/models/mv.py,
# from the reviews of #239, #245, #267, #275, #279, #287, #296, #302, #305, #307, #310, #312, #318, #328, #338 and #342, and #283's return frames and choice points in sequence), in four modes by seed: plain choices,
# choices in if branches (bif), functions with several values (mv), and
# recursive ones (rec). Lean must match the model's output and exit, and C
# must match Lean; no program may hit an internal error. A program that runs
# out of fuel (exit 3) is skipped.
#   usage: scripts/fuzz-model-mv.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
modes=("" bif mv rec)
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; ref=0; fuel=0; skip=0; long=0; slow=0; bad=0
for ((s=first; s<first+n; s++)); do
  m="${modes[$((s % ${#modes[@]}))]}"
  save() { cp "$tmp/p.verse" "$root/fuzz-model-mv-$s.verse"; cp "$tmp/p.expected" "$root/fuzz-model-mv-$s.expected"; }
  # (the mode is a flag of its own, or none)
  python3 -I "$root/scripts/models/mv.py" "$s" "$tmp" $m 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED ${m:-plain} seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  # (SKIP long: the model gave up on a program that prints more than 12000 lines)
  if grep -q '^SKIP long' "$tmp/p.expected"; then long=$((long+1)); continue; fi
  # (a program whose ints overflow, which the model does not follow: skipped)
  if grep -q '^SKIP' "$tmp/p.expected"; then skip=$((skip+1)); continue; fi
  # (a program the model predicts to print more than 12000 lines may not finish within the
  # timeout below, rec mode's enumerations at times: skipped, not counted as bad)
  if [[ $(wc -l < "$tmp/p.expected") -gt 12000 ]]; then long=$((long+1)); continue; fi
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
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
    bad=$((bad+1)); save; echo "LEAN TIMEOUT ${m:-plain} seed $s, and C (exit $ce) differs from the model (saved fuzz-model-mv-$s.verse)"; continue
  fi
  { cat "$tmp/l.out"; echo "exit=$le"; } > "$tmp/l.full"
  if grep -qi "internal" "$tmp/l.err" || ! cmp -s "$tmp/l.full" "$tmp/p.expected"; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH ${m:-plain} seed $s (Lean exit $le, saved fuzz-model-mv-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  [[ $le -eq 4 ]] && { ref=$((ref+1)); continue; }
  [[ -s "$tmp/p.vbc" ]] || { bad=$((bad+1)); save; echo "NO BYTECODE ${m:-plain} seed $s"; continue; }
  (ulimit -v 4000000; timeout 60 "$cv" "$tmp/p.vbc") > "$tmp/c.out" 2> /dev/null; ce=$?
  ran=$((ran+1))
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); save; echo "C MISMATCH ${m:-plain} seed $s (C exit $ce, saved fuzz-model-mv-$s.verse)"
  fi
done
echo "fuzz-model-mv: $n programs from seed $first, $ran ran in both, $ref refused as the model says, $fuel out of fuel, $skip skipped (an overflow), $long skipped (over 12000 lines), $slow slow in Lean (C matches the model), $bad bad"
[[ $bad -eq 0 ]]
