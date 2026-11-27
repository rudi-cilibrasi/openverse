#!/usr/bin/env bash
# A failure context that writes costs the reference interpreter what it writes, not the size of
# the heap (#780): with H objects on the heap, N conditions that each set a field and then fail
# finish within LIMIT seconds. On an array heap each of them copied the whole heap (the state the
# context rolls back to still holds it), so the run cost N·H: 30,000 of each took 2 s, and the
# default 400,000 of each would take about six minutes; on the persistent heap of
# Core/PersistentHeap.lean it takes a few seconds, which leaves a wide margin on a loaded machine.
# The second program allocates in each failing condition instead. With cverse built, its output
# must be the same bytes.
#   usage: tests/scripts/test-heap-linear.sh [H [N [LIMIT]]]      (default 400000 400000 120)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
h="${1:-400000}"; n="${2:-400000}"; limit="${3:-120}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

# (every write is rolled back, so the field ends as it began)
cat >"$tmp/write.verse" <<EOF
cell := class{var X:int = 0}
Main():void =
    Cs := for (I := 1..$h) { cell{} }
    C := cell{}
    var Count:int = 0
    for (I := 1..$n):
        if (set C.X = I, I < 0) then Print("never")
        set Count += 1
    Print("{Count} {C.X} {Cs.Length}")
EOF
echo "$n 0 $h" >"$tmp/write.want"

cat >"$tmp/alloc.verse" <<EOF
cell := class{var X:int = 0}
Main():void =
    Cs := for (I := 1..$h) { cell{} }
    var Count:int = 0
    for (I := 1..$n):
        if (D := cell{X := I}, D.X < 0) then Print("never")
        set Count += 1
    Print("{Count} {Cs.Length}")
EOF
echo "$n $h" >"$tmp/alloc.want"

for p in write alloc; do
  start=$SECONDS; code=0
  timeout "$limit" "$ov" run "$tmp/$p.verse" --emit "$tmp/$p.vbc" >"$tmp/$p.out" 2>"$tmp/$p.err" || code=$?
  if [[ $code -eq 124 ]]; then
    echo "heap-linear: FAIL $p: $n failing conditions over $h objects did not finish in $limit s (a failure context copies the heap, #780)" >&2; exit 1
  fi
  if [[ $code -ne 0 || -s "$tmp/$p.err" ]]; then
    echo "heap-linear: FAIL $p: exit $code: $(head -n 3 "$tmp/$p.err")" >&2; exit 1
  fi
  if ! cmp -s "$tmp/$p.out" "$tmp/$p.want"; then
    echo "heap-linear: FAIL $p: wanted '$(cat "$tmp/$p.want")', got '$(head -n 1 "$tmp/$p.out")'" >&2; exit 1
  fi
  took=$((SECONDS - start)); withc=""
  if [[ -x "$cv" ]]; then
    "$cv" "$tmp/$p.vbc" >"$tmp/$p.c.out" 2>"$tmp/$p.c.err" || { echo "heap-linear: FAIL $p: cverse: $(head -n 3 "$tmp/$p.c.err")" >&2; exit 1; }
    cmp -s "$tmp/$p.out" "$tmp/$p.c.out" || { echo "heap-linear: FAIL $p: cverse's output differs" >&2; exit 1; }
    withc=", cverse agrees"
  fi
  echo "heap-linear: $p: $n failing conditions over $h objects in $took s (limit $limit)$withc"
done
