#!/usr/bin/env bash
# Differential fuzzing of generic task roots (#244): random programs whose
# generic <suspends> functions call each other at ever bigger types
# (scripts/gen-conc-poly.py), each run by the Lean reference interpreter and
# by cverse. Lean and C must agree, and no program may be refused (the
# generator writes valid programs) or hit an internal error.
#   usage: scripts/fuzz-conc-poly.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0
for ((s=first; s<first+n; s++)); do
  python3 -I "$root/scripts/gen-conc-poly.py" "$s" > "$tmp/p.verse"
  rm -f "$tmp/p.vbc"
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  if [[ ! -s "$tmp/p.vbc" ]]; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-poly-$s.verse"
    echo "REFUSED or INTERNAL seed $s (exit $le, saved fuzz-conc-poly-$s.verse): $(head -c 200 "$tmp/l.err")"
    continue
  fi
  ran=$((ran+1))
  timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>/dev/null; ce=$?
  if [[ $ce -ne $le ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out"; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-poly-$s.verse"
    echo "MISMATCH seed $s (Lean exit $le, C exit $ce; saved fuzz-conc-poly-$s.verse)"
  fi
done
echo "fuzz-conc-poly: $n programs from seed $first, $ran run in both, $bad bad"
[[ $bad -eq 0 ]]
