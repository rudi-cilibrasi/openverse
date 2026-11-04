#!/usr/bin/env bash
# Run every tests/verse/*.verse with the Lean reference interpreter and compare
# stdout plus the exit code with NAME.expected. With --c, also compile each to
# OVBC and run it with the C runtime (runtime/build/cverse), which must agree
# byte for byte with the Lean result.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
withc=0; [[ "${1:-}" == "--c" ]] && withc=1
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0
for f in "$root"/tests/verse/*.verse; do
  n="$(basename "$f" .verse)"
  { "$ov" run "$f" 2>"$tmp/$n.lean.err"; echo "exit=$?"; } >"$tmp/$n.lean.out"
  if ! cmp -s "$tmp/$n.lean.out" "$root/tests/verse/$n.expected"; then
    echo "FAIL $n (lean):"; diff "$root/tests/verse/$n.expected" "$tmp/$n.lean.out" | head -20
    cat "$tmp/$n.lean.err" | head -5
    fail=$((fail+1)); continue
  fi
  if [[ $withc -eq 1 ]]; then
    "$ov" emit "$f" -o "$tmp/$n.vbc" || { echo "FAIL $n (emit)"; fail=$((fail+1)); continue; }
    { "$cv" "$tmp/$n.vbc" 2>"$tmp/$n.c.err"; echo "exit=$?"; } >"$tmp/$n.c.out"
    if ! cmp -s "$tmp/$n.lean.out" "$tmp/$n.c.out" || ! cmp -s "$tmp/$n.lean.err" "$tmp/$n.c.err"; then
      echo "FAIL $n (C differs from Lean):"; diff "$tmp/$n.lean.out" "$tmp/$n.c.out" | head -20
      diff "$tmp/$n.lean.err" "$tmp/$n.c.err" | head -5
      fail=$((fail+1)); continue
    fi
  fi
  pass=$((pass+1))
done
for f in "$root"/tests/errors/*.verse; do
  n="$(basename "$f" .verse)"
  want="$(sed -n 's/^# expect: //p' "$f" | head -1)"
  "$ov" check "$f" >/dev/null 2>"$tmp/$n.err"; code=$?
  if [[ $code -ne 4 ]] || ! grep -qF "$want" "$tmp/$n.err"; then
    echo "FAIL errors/$n: exit $code, wanted 4 and '$want', got: $(cat "$tmp/$n.err")"
    fail=$((fail+1)); continue
  fi
  pass=$((pass+1))
done
echo "tests: $pass passed, $fail failed"
[[ $fail -eq 0 ]]
