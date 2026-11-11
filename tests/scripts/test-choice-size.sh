#!/usr/bin/env bash
# Doubling a sequence of generic choices must not multiply its bytecode by 16.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
for kind in composed exclusive binding typed-first typed-for typed-exclusive refined-for refined-state; do
  sizes=()
  for count in 4 8; do
    python3 - "$kind" "$count" >"$tmp/p.verse" <<'PY'
import sys
kind, count = sys.argv[1], int(sys.argv[2])
print('Two(N:int):int = N | N + 1')
print('Pick(X:t where t:type):t = X | X')
print('Early(N:int):int =\n    if (N < 0):\n        return 0\n    N | N + 1')
if kind.startswith('refined-'):
    print('pair(a:type, b:type) := class:\n    A:a\n    B:b')
    print('dup(t:type) := class(pair(t, t)):\n    C:int = 4')
value = {'composed': '(Two(0) | Two(2))', 'exclusive': 'Early(0)',
         'binding': '(Pick(I) | Pick(I))', 'typed-first': '(Two(0) | Two(2))',
         'typed-for': '(Two(0) | Two(2))', 'typed-exclusive': 'Early(0)',
         'refined-for': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-state': 'if (D := dup[P]) then (D.C | D.C + 1) else 0'}[kind]
clauses = ', '.join(f'A{i} := {value}' for i in range(count))
if kind == 'refined-state':
    params = ', '.join(f'P{i}:pair(a{i}, b{i})' for i in range(count))
    tparams = ', '.join(f'a{i}:type, b{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i} := if (D := dup[P{i}]) then (D.C | D.C + 1) else 0, A{i} = 4, set Total += A{i}' for i in range(count))
    print(f'Run({params} where {tparams}):int =\n    var Total:int = 0\n    R := for ({clauses}):\n        set Total += 1\n        Total\n    Total + R.Length')
elif kind == 'refined-for':
    print(f'Run(I:t, P:pair(a, b) where t:type, a:type, b:type):[]t = for ({clauses}) {{ I }}')
elif kind == 'typed-first':
    print(f'Run(Unused:t where t:type):int = if ({clauses}, E:[]t = array{{}}) then E.Length else -1')
elif kind.startswith('typed-'):
    print(f'Run(Unused:t where t:type):int =\n    R := for ({clauses}):\n        E:[]t = array{{}}\n        E.Length\n    R.Length')
else:
    print(f'Run(I:t where t:type):[]t = for ({clauses}) {{ I }}')
if kind == 'refined-state':
    args = ', '.join('dup(int){A := 1, B := 2}' if i % 2 == 0 else 'dup(string){A := "s", B := "t"}' for i in range(count))
    print(f'Main():void = Print("{{Run({args})}}")')
elif kind == 'refined-for':
    print('Main():void = Print("{Run(7, dup(int){A := 1, B := 2}).Length}")')
else:
    print('Main():void = Print("{Run(7)}")' if kind.startswith('typed-') else 'Main():void = Print("{Run(7).Length}")')
PY
    timeout 30 "$root/.lake/build/bin/openverse" emit "$tmp/p.verse" -o "$tmp/p.vbc"
    sizes+=("$(wc -c <"$tmp/p.vbc")")
  done
  if (( sizes[1] > 3 * sizes[0] )); then
    echo "test-choice-size: $kind grew from ${sizes[0]} to ${sizes[1]} bytes" >&2
    exit 1
  fi
  echo "test-choice-size: $kind, 4 choices=${sizes[0]} bytes, 8 choices=${sizes[1]} bytes"
done
