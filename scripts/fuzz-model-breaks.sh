#!/usr/bin/env bash
# Compare source-loop break/rollback predictions with Lean and C: for each seed, a break in a
# for's filters, and one in the clauses of an if condition, first{} or option{} with choices,
# among them blocks with a defer: (and at times a choice of their own) left by a break or return.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0
for ((s=first; s<first+n; s++)); do
  for form in for first-success; do
    flag=(); name="$s"
    if [[ $form == first-success ]]; then flag=(--first-success); name="$s-first-success"; fi
    python3 -I "$root/scripts/models/choice_break.py" "$s" "$tmp/p.expected" "${flag[@]}" >"$tmp/p.verse" || exit 1
    rm -f "$tmp/p.vbc"
    timeout 120 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" >"$tmp/lean.out" 2>"$tmp/lean.err"; le=$?
    timeout 120 "$cv" "$tmp/p.vbc" >"$tmp/c.out" 2>"$tmp/c.err"; ce=$?
    if [[ $le != 0 || $ce != 0 ]] || ! cmp -s "$tmp/lean.out" <(tail -n +2 "$tmp/p.expected") ||
        ! cmp -s "$tmp/lean.out" "$tmp/c.out" || ! cmp -s "$tmp/lean.err" "$tmp/c.err"; then
      cp "$tmp/p.verse" "$root/fuzz-model-breaks-$name.verse"
      cp "$tmp/p.expected" "$root/fuzz-model-breaks-$name.expected"
      echo "BAD source-break model seed $s ($form): Lean exit $le, C exit $ce (saved fuzz-model-breaks-$name.verse)"
      head -c 300 "$tmp/lean.err"
      bad=$((bad+1))
    fi
  done
done
echo "fuzz-model-breaks: $((2*n)) programs from seed $first, $((2*n-bad)) matched both runtimes, $bad bad"
[[ $bad -eq 0 ]]
