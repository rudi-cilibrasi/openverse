#!/usr/bin/env bash
# Heterogeneous composed choices: independent prefix/filter rollback, result
# packets, mutable copy-outs, waiting state and cancellation oracle. Each
# 120-seed cycle covers five input shapes in first-success, for and waiting
# contexts, with empty/nonempty trailing generators and cancellation.
#   usage: scripts/fuzz-model-heterogeneous.sh [COUNT [FIRST_SEED [--methods|--generic-methods|--members|--callable-fields|--aliases|--writes|--nested-writes|--result-aliases|--numeric-writes|--named-methods]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-120}"; first="${2:-1}"
mode_args=(); tag=heterogeneous
case ${3:-} in
  --methods) mode_args+=(--methods); tag=dictionary ;;
  --generic-methods) mode_args+=(--generic-methods); tag=polymorphic-dictionary ;;
  --named-methods) mode_args+=(--named-methods); tag=named-method-dictionary ;;
  --nested-writes) mode_args+=(--nested-writes); tag=nested-write-dictionary ;;
  --numeric-writes) mode_args+=(--numeric-writes); tag=numeric-write-dictionary ;;
  --indexed-writes) mode_args+=(--indexed-writes); tag=indexed-write-dictionary ;;
  --writes) mode_args+=(--writes); tag=write-dictionary ;;
  --result-aliases) mode_args+=(--result-aliases); tag=result-alias-dictionary ;;
  --aliases) mode_args+=(--aliases); tag=alias-dictionary ;;
  --members) mode_args+=(--members); tag=member-dictionary ;;
  --callable-fields) mode_args+=(--callable-fields); tag=callable-field-dictionary ;;
esac
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; bad=0
for ((s=first; s<first+n; s++)); do
  g="choice_heterogeneous"
  save() { cp "$tmp/p.verse" "$root/fuzz-model-$tag-$s.verse"; cp "$tmp/p.exp" "$root/fuzz-model-$tag-$s.expected"; }
  python3 -I "$root/scripts/models/$g.py" "$s" "$tmp/p.exp" "${mode_args[@]}" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED $g seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  rm -f "$tmp/p.vbc"
  timeout 120 "$ov" run "$tmp/p.verse" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?
  want=$(head -1 "$tmp/p.exp" | sed 's/exit=//')
  if [[ $le != "$want" ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le $g seed $s (saved fuzz-model-$tag-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH $g seed $s (saved fuzz-model-$tag-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
  if [[ $ce != "$want" ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    bad=$((bad+1)); save; echo "C MISMATCH $g seed $s (C exit $ce, saved fuzz-model-$tag-$s.verse)"; continue
  fi
  ok=$((ok+1))
done
echo "fuzz-model-$tag: $n programs from seed $first, $ok ran as the model says, $bad bad"
[[ $bad -eq 0 ]]
