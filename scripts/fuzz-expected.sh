#!/usr/bin/env bash
# Shared runner for generators whose valid programs must succeed and print
# the complete expected output. Called by fuzz-choice.sh and fuzz-floats.sh.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
kind="${1:?fuzzer name required}"; gen="${2:?generator required}"
n="${3:-200}"; first="${4:-1}"; cv="${5:-$root/runtime/build/cverse}"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0
for ((s=first; s<first+n; s++)); do
  # A failed generator must never leave the previous seed's input in use.
  rm -f "$tmp/p.verse" "$tmp/want.out" "$tmp/p.vbc"
  if ! python3 -I "$gen" "$s" "$tmp/p.verse" "$tmp/want.out" ||
      [[ ! -f "$tmp/p.verse" || ! -f "$tmp/want.out" ]]; then
    bad=$((bad+1)); echo "GENERATOR FAILED seed $s"; continue
  fi
  timeout 60 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2>&1; le=$?; sed -i -E '/^[^ ]*:[0-9]+:[0-9]+: warning: /d' "$tmp/l.out"
  ok=1
  if [[ $le -ne 0 ]] || ! cmp -s "$tmp/l.out" "$tmp/want.out"; then ok=0
  elif [[ ! -s "$tmp/p.vbc" ]]; then ok=0
  else
    timeout 60 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2>&1; ce=$?
    if [[ $ce -ne 0 ]] || ! cmp -s "$tmp/c.out" "$tmp/want.out"; then ok=0; fi
  fi
  if [[ $ok -eq 0 ]]; then
    bad=$((bad+1)); cp "$tmp/p.verse" "$root/fuzz-$kind-$s.verse"
    echo "MISMATCH seed $s (saved fuzz-$kind-$s.verse)"
  fi
done
echo "fuzz-$kind: $n programs from seed $first, $bad bad"
[[ $bad -eq 0 ]]
