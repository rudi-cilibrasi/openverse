#!/usr/bin/env bash
# Differential fuzzing of generic task roots (#244): random programs whose
# generic <suspends> functions call each other at ever bigger types
# (scripts/gen-conc-poly.py), each run with copies at small closed types
# (the default) and with generic roots only (OPENVERSE_GENERIC_ROOTS=1), by
# the Lean reference interpreter and by cverse. Lean and C must agree in
# each mode, both modes must print the same, and no program may be refused
# (the generator writes valid programs) or hit an internal error.
#   usage: scripts/fuzz-conc-poly.sh [COUNT [FIRST_SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-100}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ran=0; bad=0
for ((s=first; s<first+n; s++)); do
  python3 -I "$root/scripts/gen-conc-poly.py" "$s" > "$tmp/p.verse"
  for mode in plain gr; do
    if [[ $mode == gr ]]; then export OPENVERSE_GENERIC_ROOTS=1; else unset OPENVERSE_GENERIC_ROOTS; fi
    rm -f "$tmp/$mode.vbc"
    timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/$mode.vbc" > "$tmp/$mode.l.out" 2> "$tmp/$mode.l.err"; le=$?
    if [[ ! -s "$tmp/$mode.vbc" ]]; then
      bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-poly-$s.verse"
      echo "REFUSED or INTERNAL ($mode) seed $s (exit $le, saved fuzz-conc-poly-$s.verse): $(head -c 200 "$tmp/$mode.l.err")"
      continue
    fi
    ran=$((ran+1))
    timeout 60 "$cv" "$tmp/$mode.vbc" > "$tmp/$mode.c.out" 2>/dev/null; ce=$?
    if [[ $ce -ne $le ]] || ! cmp -s "$tmp/$mode.l.out" "$tmp/$mode.c.out"; then
      bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-poly-$s.verse"
      echo "MISMATCH ($mode) seed $s (Lean exit $le, C exit $ce; saved fuzz-conc-poly-$s.verse)"
    fi
  done
  unset OPENVERSE_GENERIC_ROOTS
  if [[ -s "$tmp/plain.l.out" && -s "$tmp/gr.l.out" ]] && ! cmp -s "$tmp/plain.l.out" "$tmp/gr.l.out"; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-conc-poly-$s.verse"
    echo "MODES DIFFER seed $s (saved fuzz-conc-poly-$s.verse)"
  fi
done
echo "fuzz-conc-poly: $n programs from seed $first, $ran runs, $bad bad"
[[ $bad -eq 0 ]]
