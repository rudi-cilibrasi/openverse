#!/usr/bin/env bash
# The reference interpreter's output costs its own length (#782): `openverse run` of a loop of
# N Prints finishes within LIMIT seconds, with the exact output. Before the fix a Print copied
# everything printed so far (2,000 Prints 0.2 s, 32,000 two minutes), so 200,000 could not finish
# in an hour; now they take under a second, which leaves a wide margin on a loaded machine.
# Two programs: every Print kept, and Prints of a failed <decides> call discarded among kept ones
# (a failure context rolls its output back). With cverse built, its output must be the same bytes.
#   usage: tests/scripts/test-print-linear.sh [N [LIMIT]]      (default 200000 60)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
n="${1:-200000}"; limit="${2:-60}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/kept.verse" <<EOF
Main():void =
    for (I := 1..$n):
        Print("line {I}")
EOF
awk -v n="$n" 'BEGIN { for (i = 1; i <= n; i++) print "line " i }' >"$tmp/kept.want"

# (`Try` prints, then fails unless I is a multiple of 3: two calls in three are rolled back)
cat >"$tmp/rollback.verse" <<EOF
Try(I:int)<transacts><decides>:void =
    Print("tried {I}")
    Mod[I, 3] = 0
Main()<transacts>:void =
    for (I := 1..$n):
        if (Try[I]) then Print("kept {I}") else Print("undone {I}")
EOF
awk -v n="$n" 'BEGIN { for (i = 1; i <= n; i++)
  if (i % 3 == 0) { print "tried " i; print "kept " i } else print "undone " i }' >"$tmp/rollback.want"

describe() { echo "    $(wc -l <"$1") lines, sha256 $(sha256sum <"$1" | cut -c1-16), first '$(head -n 1 "$1")', last '$(tail -n 1 "$1")'"; }
for p in kept rollback; do
  start=$SECONDS; code=0
  timeout "$limit" "$ov" run "$tmp/$p.verse" --emit "$tmp/$p.vbc" >"$tmp/$p.out" 2>"$tmp/$p.err" || code=$?
  if [[ $code -eq 124 ]]; then
    echo "print-linear: FAIL $p: $n iterations did not finish in $limit s (the output is not linear, #782)" >&2; exit 1
  fi
  if [[ $code -ne 0 || -s "$tmp/$p.err" ]]; then
    echo "print-linear: FAIL $p: exit $code: $(head -n 3 "$tmp/$p.err")" >&2; exit 1
  fi
  if ! cmp -s "$tmp/$p.out" "$tmp/$p.want"; then
    echo "print-linear: FAIL $p: wrong output" >&2
    { echo "  wanted:"; describe "$tmp/$p.want"; echo "  got:"; describe "$tmp/$p.out"; } >&2
    exit 1
  fi
  took=$((SECONDS - start)); withc=""
  if [[ -x "$cv" ]]; then
    "$cv" "$tmp/$p.vbc" >"$tmp/$p.c.out" 2>"$tmp/$p.c.err" || { echo "print-linear: FAIL $p: cverse: $(head -n 3 "$tmp/$p.c.err")" >&2; exit 1; }
    cmp -s "$tmp/$p.out" "$tmp/$p.c.out" || { echo "print-linear: FAIL $p: cverse's output differs" >&2; exit 1; }
    withc=", cverse agrees"
  fi
  echo "print-linear: $p: $n iterations, $(wc -l <"$tmp/$p.out") lines in $took s (limit $limit)$withc"
done
