#!/usr/bin/env bash
# A map's lookup is one native scan (#795): building a map of N entries and looking every key up
# four times finishes within LIMIT seconds on the reference interpreter, with the right sum. As
# interpreted loops over the pairs, 8,000 entries took 73 s (10 s to build, 63 s for the lookups);
# as the primitives mapGet and mapFind they take about 4 s. The cost is still quadratic in N: a
# lookup is linear, and this only bounds its constant. With cverse built, its output must be the
# same bytes.
#   usage: tests/scripts/test-map-scan.sh [N [LIMIT]]      (default 8000 45)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
n="${1:-8000}"; limit="${2:-45}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/map.verse" <<EOF
Main():void =
    var M:[int]int = map{}
    for (I := 1..$n):
        if (set M[I] = I * 2) {}
    var S:int = 0
    for (R := 1..4, I := 1..$n):
        if (V := M[I]) then set S += V
    Print("{S} {M.Length}")
EOF
echo "$((4 * n * (n + 1))) $n" >"$tmp/map.want"

start=$SECONDS; code=0
timeout "$limit" "$ov" run "$tmp/map.verse" --emit "$tmp/map.vbc" >"$tmp/map.out" 2>"$tmp/map.err" || code=$?
if [[ $code -eq 124 ]]; then
  echo "map-scan: FAIL: $n entries and $((4 * n)) lookups did not finish in $limit s (a lookup interprets a loop over the pairs, #795)" >&2; exit 1
fi
if [[ $code -ne 0 || -s "$tmp/map.err" ]]; then
  echo "map-scan: FAIL: exit $code: $(head -n 3 "$tmp/map.err")" >&2; exit 1
fi
if ! cmp -s "$tmp/map.out" "$tmp/map.want"; then
  echo "map-scan: FAIL: wanted '$(cat "$tmp/map.want")', got '$(head -n 1 "$tmp/map.out")'" >&2; exit 1
fi
took=$((SECONDS - start)); withc=""
if [[ -x "$cv" ]]; then
  "$cv" "$tmp/map.vbc" >"$tmp/map.c.out" 2>"$tmp/map.c.err" || { echo "map-scan: FAIL: cverse: $(head -n 3 "$tmp/map.c.err")" >&2; exit 1; }
  cmp -s "$tmp/map.out" "$tmp/map.c.out" || { echo "map-scan: FAIL: cverse's output differs" >&2; exit 1; }
  withc=", cverse agrees"
fi
echo "map-scan: $n entries, $((4 * n)) lookups in $took s (limit $limit)$withc"
