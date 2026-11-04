#!/bin/sh
# run_core.sh CVERSE LEAN COREDIR WORKDIR
#
# For every COREDIR/NAME.vbc: check that the file is what the Lean binary
# emits for its example NAME, then run it with CVERSE and require stdout,
# stderr and the exit code to be identical to `LEAN example NAME`.
cv="$1"; lean="$2"; dir="$3"; work="$4"
if [ ! -x "$lean" ]; then
    echo "run_core: the Lean binary $lean is missing (build it with lake build)" >&2
    exit 1
fi
mkdir -p "$work"
pass=0; fail=0
for f in "$dir"/*.vbc; do
    n=$(basename "$f" .vbc)
    if ! "$lean" example "$n" --emit "$work/$n.lean.vbc" 2>"$work/$n.emit.err" ||
       ! cmp -s "$f" "$work/$n.lean.vbc"; then
        echo "FAIL $n: $f differs from 'openverse example $n --emit' (stale test input?)"
        fail=$((fail + 1)); continue
    fi
    "$lean" example "$n" >"$work/$n.lean.out" 2>"$work/$n.lean.err"; le=$?
    "$cv" "$f" >"$work/$n.c.out" 2>"$work/$n.c.err"; ce=$?
    if [ "$le" -ne "$ce" ] || ! cmp -s "$work/$n.lean.out" "$work/$n.c.out" ||
       ! cmp -s "$work/$n.lean.err" "$work/$n.c.err"; then
        echo "FAIL $n: lean exit $le, $(basename "$cv") exit $ce"
        diff "$work/$n.lean.out" "$work/$n.c.out" | head -10
        diff "$work/$n.lean.err" "$work/$n.c.err" | head -5
        fail=$((fail + 1)); continue
    fi
    echo "ok   $n ($(basename "$cv"): exit $ce, $(wc -c <"$work/$n.c.out") bytes, same as Lean)"
    pass=$((pass + 1))
done
echo "core: $pass passed, $fail failed"
[ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]
