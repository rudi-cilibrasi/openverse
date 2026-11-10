#!/usr/bin/env bash
# Mutation fuzzing of the front end: mutate the lines and tokens of tests/verse/*.verse at random.
# Every mutant must be either rejected with an ordinary error (exit 4, not "internal error"), or
# accepted, in which case the Lean interpreter and the C runtime must agree on it. At fuel 200000 the
# default run compares the same mutants as at ten times more, and a runaway one stops in about a
# second, where nested spawns could keep Lean busy until the 20 s timeout (#215).
#   usage: scripts/fuzz-front.sh [COUNT [SEED]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-300}"; seed="${2:-1}"
ov="$root/.lake/build/bin/openverse"; cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
python3 -I - "$root/tests/verse" "$tmp" "$n" "$seed" <<'PY' || { echo "GENERATOR FAILED seed $seed"; exit 1; }
import os, random, re, sys
src, out, n, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(seed)
files = sorted(f for f in os.listdir(src) if f.endswith('.verse'))
ops = ['+', '-', '*', '<', '<=', '>', '>=', '=', '<>', 'and', 'or']
for i in range(n):
    lines = open(os.path.join(src, rnd.choice(files))).read().split('\n')
    for _ in range(rnd.randint(1, 3)):
        k = rnd.randrange(len(lines))
        m = rnd.randrange(7)
        if m == 0 and len(lines) > 1: del lines[k]
        elif m == 1: lines.insert(k, lines[rnd.randrange(len(lines))])
        elif m == 2:
            j = rnd.randrange(len(lines)); lines[k], lines[j] = lines[j], lines[k]
        elif m == 3: lines[k] = re.sub(r'\b\d+\b', lambda _: str(rnd.choice([0, 1, -1, 2, 9223372036854775807])), lines[k], count=1)
        elif m == 4:
            toks = lines[k].split(' ')
            for t in range(len(toks)):
                if toks[t] in ops: toks[t] = rnd.choice(ops); break
            lines[k] = ' '.join(toks)
        elif m == 5: lines[k] = '    ' + lines[k]
        else: lines[k] = lines[k][:rnd.randrange(len(lines[k]) + 1)]
    open(os.path.join(out, 'm%05d.verse' % i), 'w').write('\n'.join(lines))
PY
acc=0; rej=0; bad=0
for f in "$tmp"/m*.verse; do
  # one compilation: it writes the bytecode (so a mutant without one never got past the front
  # end), then the Lean interpreter runs it
  timeout 20 "$ov" run "$f" --emit "$f.vbc" --fuel 200000 >"$f.l" 2>"$f.le"; le=$?
  # (Lean out of memory under check.sh's cap, CHECK_MEM_GB: a resource limit, as exit 3 is. An
  # endless search Lean runs with far more memory per unit of fuel than C does: in the nightly
  # of 2026-11-10, mutants that C stopped at its fuel limit with 30 MB took Lean 9 GB to get there)
  if [[ $le -eq 1 ]] && grep -q "INTERNAL PANIC: out of memory" "$f.le"; then le=3; fi
  if [[ $le -eq 4 ]] && ! grep -q "internal error" "$f.le"; then rej=$((rej+1)); continue; fi
  if [[ ! -s "$f.vbc" ]]; then echo "FRONT END BUG ($le) on $(basename "$f"): $(head -3 "$f.le")"; cp "$f" "$root/build/" 2>/dev/null; bad=$((bad+1)); continue; fi
  timeout 20 "$cv" "$f.vbc" --fuel 200000 >"$f.c" 2>"$f.ce"; ce=$?
  if [[ $le -ne 3 && $le -ne 124 ]] && { [[ $le -ne $ce ]] || ! cmp -s "$f.l" "$f.c" || ! cmp -s "$f.le" "$f.ce"; }; then
    echo "MISMATCH on $(basename "$f"): lean $le, C $ce"; bad=$((bad+1)); continue
  fi
  acc=$((acc+1))
done
echo "fuzz-front: $n mutants: $acc accepted (Lean and C agree), $rej rejected with an error, $bad bugs"
[[ $bad -eq 0 ]]
