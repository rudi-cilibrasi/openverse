#!/usr/bin/env bash
# Model-based fuzzing of classes that fix, repeat, relate or hide type
# arguments (GADTs, #209): random programs from twenty-nine independent models
# (scripts/models/gadt_*.py, from the reviews of #236, #242, #243 and #250,
# with the clauses after a cast from #277 and named arguments with defaults of no
# type of their own through opening dispatches from #317, and covariant <suspends>
# overrides through them from #324, also spawned on a value of the class itself from
# #321, and through a class between that redeclares it narrower from #337; interfaces that
# give a parent interface other type arguments from #344, their defaults from #347, also in
# classes giving composite arguments from #355; interfaces referred to through views, with
# fields and defaults, from the reviews of #390, #399, #405 and #523, gadt_views, with casts
# beside the object's type and to interfaces that open type arguments, #351 and #53; refining
# casts as clauses of any failure context, after clauses with effects, gadt_cast_contexts,
# with later casts of an opening cast's fields from #250's follow-up),
# each predicting the program's output, or the message of the refusal it
# expects. Each seed uses one model in turn. Lean must match the model, and C
# must match Lean; no program may hit an internal error. With --aliases, each
# program's types are written through type aliases first
# (scripts/models/aliases.py, a random stream of its own): an alias is the type
# it names, so the model's expectation holds as it is. A seed in three also
# runs scripts/models/gadt_upper.py, upper bounds on a GADT's type parameter
# (#502), on a random stream of its own, so the other models keep their seeds.
#   usage: scripts/fuzz-model-gadt.sh [COUNT [FIRST_SEED [--aliases]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-60}"; first="${2:-1}"; aliases="${3:-}"
tag=gadt; [[ $aliases == --aliases ]] && tag=gadt-aliases
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
gens=(gadt_rel gadt_rel2 gadt_exist gadt_refine gadt_open gadt_bounds gadt_covariant gadt_immediate gadt_super gadt_defaults gadt_spawn_defaults gadt_method_values gadt_function_values gadt_function_tuples gadt_method_instances gadt_method_tuples gadt_spawn_callers gadt_spawn_body gadt_event_body gadt_first_returns gadt_choice_values gadt_waiting_effects gadt_context_methods gadt_method_variance gadt_contexts gadt_task_order gadt_waiting_contexts gadt_views gadt_cast_contexts)
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok=0; ref=0; bad=0
upper=0
for ((s=first; s<first+n; s++)); do
 models=("${gens[$((s % ${#gens[@]}))]}")
 # (#502: the stream of its own)
 (( (s * 2654435761 + 502) % 3 == 0 )) && models+=(gadt_upper)
 for g in "${models[@]}"; do
  [[ $g == gadt_upper ]] && upper=$((upper+1))
  save() { cp "$tmp/p.verse" "$root/fuzz-model-$tag-$g-$s.verse"; cp "$tmp/p.exp" "$root/fuzz-model-$tag-$g-$s.expected"; }
  python3 -I "$root/scripts/models/$g.py" "$s" "$tmp/p.exp" > "$tmp/p.verse" 2> "$tmp/gen.err" ||
    { bad=$((bad+1)); echo "GENERATOR FAILED $g seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
  if [[ $aliases == --aliases ]]; then
    python3 -I "$root/scripts/models/aliases.py" "$s" < "$tmp/p.verse" > "$tmp/a.verse" 2> "$tmp/gen.err" ||
      { bad=$((bad+1)); echo "ALIASES FAILED $g seed $s: $(tail -1 "$tmp/gen.err")"; continue; }
    mv "$tmp/a.verse" "$tmp/p.verse"
  fi
  rm -f "$tmp/p.vbc"
  # The lexical-field variants call Concatenate and Id, and their for/lazy
  # ones the ordinary Sum/Lazy helpers, in a field's default, which a data
  # member may not (#511; UEFN 43.12 error 3582, #724).
  # (#724: the models write parametric interfaces with var fields and generic
  # functions over parametric classes whose var fields hold their parameters,
  # openverse's extension, which Epic's compiler refuses, 3552 and 3502)
  compat=(--parametric-var-fields)
  if [[ $g == gadt_contexts ]] && (( s % 9 == 1 )); then
    compat+=(--extended-defaults)
  fi
  # These two models are of openverse's own reading of a named parameter's
  # default, which the Book refuses (DefaultNamed.versetest 805-878): a
  # <computes> method's default that writes, its effects the caller's
  # (gadt_spawn_defaults, #468), and a default that waits (gadt_waiting_contexts,
  # #283).
  case $g in gadt_spawn_defaults|gadt_waiting_contexts) compat+=(--extended-defaults) ;; esac
  # This model signals in a <decides> function's for body and checks that a
  # failure rolls the signal back: the legacy transactional mode (#515; Epic's
  # compiler, and openverse's default, refuse such a Signal).
  # (its <decides> function signals, so it keeps Epic's default effect,
  # no_rollback, which its call in a condition cannot have: the old rule
  # too, --default-rollback)
  case $g in gadt_event_body) compat+=(--signal-rollback --default-rollback) ;; esac
  # These models bind functions and methods of generic receivers through
  # generic functions (`Bind(…):type{_()<computes>:t}`), a conversion of
  # function values whose calls Epic's compiler refuses (UEFN 43.12, error
  # 3502, #724): openverse's conversions, --function-coercions.
  case $g in gadt_function_*|gadt_method_*|gadt_context_methods|gadt_choice_values) compat+=(--function-coercions) ;; esac
  # (#515: Epic's default effect, written out: <transacts> where a function without one is called from a failure context or <transacts> code;
  # not for the models whose functions spawn, written for the default effect already: a spawn has no_rollback,
  # which no <transacts> function may have, #724)
  case $g in
    gadt_spawn_callers|gadt_spawn_body|gadt_spawn_defaults) ;;
    *) python3 -I "$root/scripts/models/default_effect.py" "$tmp/p.verse" ;;
  esac
  timeout 120 "$ov" run "$tmp/p.verse" "${compat[@]}" --emit "$tmp/p.vbc" > "$tmp/l.out" 2> "$tmp/l.err"; le=$?; sed -i -E '/^[^ ]*:[0-9]+:[0-9]+: warning: /d' "$tmp/l.err"
  want=$(head -1 "$tmp/p.exp" | sed 's/exit=//')
  if [[ $want == 4 ]]; then
    msg=$(sed -n 2p "$tmp/p.exp")
    # (the model's message has the types it wrote; the program has them with
    # <transacts> written out, #515)
    if [[ $le == 4 ]] && sed 's/<transacts>//g' "$tmp/l.err" | grep -qF "$msg" && ! grep -q "internal" "$tmp/l.err"; then ref=$((ref+1)); continue; fi
    bad=$((bad+1)); save; echo "EXPECTED REFUSAL $g seed $s (exit $le, saved fuzz-model-$tag-$g-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if [[ $le != "$want" ]]; then
    bad=$((bad+1)); save; echo "LEAN EXIT $le $g seed $s (saved fuzz-model-$tag-$g-$s.verse): $(head -c 200 "$tmp/l.err")"; continue
  fi
  if ! diff -q <(tail -n +2 "$tmp/p.exp") "$tmp/l.out" > /dev/null; then
    bad=$((bad+1)); save; echo "MODEL MISMATCH $g seed $s (saved fuzz-model-$tag-$g-$s.verse)"; continue
  fi
  timeout 120 "$cv" "$tmp/p.vbc" > "$tmp/c.out" 2> "$tmp/c.err"; ce=$?
  if [[ $ce != "$want" ]] || ! cmp -s "$tmp/l.out" "$tmp/c.out" || ! cmp -s "$tmp/l.err" "$tmp/c.err"; then
    bad=$((bad+1)); save; echo "C MISMATCH $g seed $s (C exit $ce, saved fuzz-model-$tag-$g-$s.verse)"; continue
  fi
  ok=$((ok+1))
 done
done
echo "fuzz-model-$tag: $n seeds from seed $first, $upper of them also with upper bounds; $ok ran as the model says, $ref refused as it says, $bad bad"
[[ $bad -eq 0 ]]
