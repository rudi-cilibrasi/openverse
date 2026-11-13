#!/usr/bin/env bash
# Differential fuzzing of the bitwise functions: random Verse programs of
# BitAnd, BitOr, BitXor, BitNot, BitShiftLeft and BitShiftRight
# (scripts/gen-bitwise.py), run by the Lean reference interpreter and by
# cverse; both must print exactly what Python's unbounded ints give under the
# Book's rules and openverse's 64-bit ints (the generator's expected output,
# exit code and error: some programs end with the overflow error).
#   usage: scripts/fuzz-bitwise.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-200}"; first="${2:-1}"; cv="${3:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0
for ((s=first; s<first+n; s++)); do
  rm -f "$tmp/p.verse" "$tmp/want" "$tmp/p.vbc"
  if ! python3 -I "$root/scripts/gen-bitwise.py" "$s" "$tmp/p.verse" "$tmp/want" ||
      [[ ! -f "$tmp/p.verse" || ! -f "$tmp/want" ]]; then
    bad=$((bad+1)); echo "GENERATOR FAILED seed $s"; continue
  fi
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  { cat "$tmp/l.out"; echo "exit=$le"; cat "$tmp/l.err"; } > "$tmp/l.full"
  ok=1
  if ! cmp -s "$tmp/l.full" "$tmp/want" || [[ ! -s "$tmp/p.vbc" ]]; then ok=0
  else
    timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
    { cat "$tmp/c.out"; echo "exit=$ce"; cat "$tmp/c.err"; } > "$tmp/c.full"
    cmp -s "$tmp/c.full" "$tmp/want" || ok=0
  fi
  if [[ $ok -eq 0 ]]; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-bitwise-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-bitwise-$s.verse)"
  fi
done
echo "fuzz-bitwise: $n programs from seed $first, $bad bad"
[[ $bad -eq 0 ]]
