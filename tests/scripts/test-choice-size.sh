#!/usr/bin/env bash
# Doubling a sequence of generic choices must not multiply its bytecode by 16.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
for kind in composed exclusive binding typed-first typed-for typed-exclusive refined-for refined-state refined-failure lazy-first lazy-for lazy-effect-first lazy-effect-for lazy-alt-first lazy-alt-for lazy-failure-for lazy-alt-failure-for lazy-exclusive-failure-for refined-lazy-failure refined-return refined-lazy-return refined-nested-body refined-nested-failure lazy-generic-first construct-first construct-for construct-failure method-first method-for method-failure; do
  sizes=()
  for count in 4 8; do
    python3 - "$kind" "$count" >"$tmp/p.verse" <<'PY'
import sys
kind, count = sys.argv[1], int(sys.argv[2])
print('Two(N:int):int = N | N + 1')
if kind.startswith('method-'):
    print('box(t:type) := class:\n    A:t\n    Both()<transacts>:t = A | A')
    print('fixed := class(box(int)):\n    Both<override>()<transacts>:int = A + 1 | A + 2')
    print('extra(t:type,u:type) := class(box(t)):\n    E:u\n    Both<override>()<transacts>:t = A | A')
    clauses = ', '.join(f'A{i} := P.Both()' for i in range(count))
    if kind == 'method-first':
        print(f'Run(P:box(t) where t:type):int = if ({clauses}, E:[]t = array{{}}) then E.Length else -1')
    else:
        specs = '<decides>' if kind == 'method-failure' else ''
        test = '\n        1 = 1' if specs else ''
        print(f'Run(P:box(t) where t:type){specs}:int =\n    R := for ({clauses}):{test}\n        A0\n    R.Length')
    specs = '<decides>' if kind == 'method-failure' else ''
    brackets = ('[', ']') if specs else ('(', ')')
    print(f'Main(){specs}:void = Print("{{Run{brackets[0]}fixed{{A:=1}}{brackets[1]}}}")')
    sys.exit(0)
if kind.startswith('construct-'):
    print('Note(N:int)<transacts>:int =\n    Print("default {N}")\n    N')
    fields = '; '.join(f'D{i}:int = Note({i}); Y{i}:int' for i in range(count))
    print(f'pack(t:type) := struct {{ E:[]t = Concatenate(); {fields} }}')
    values = ', '.join(f'Y{i} := (Two(0) | Two(2))' for i in range(count))
    binding = f'P:pack(t) = pack{{{values}}}'
    if kind == 'construct-first':
        print(f'Run(Unused:t where t:type):int = if ({binding}) then P.E.Length + P.Y0 else -1')
    else:
        specs = '<decides>' if kind == 'construct-failure' else ''
        test = '\n        P.Y0 >= 0' if specs else ''
        print(f'Run(Unused:t where t:type){specs}:int =\n    R := for ({binding}):{test}\n        P.E.Length + P.Y0\n    R.Length')
    specs = '<decides>' if kind == 'construct-failure' else ''
    call = 'Run[7]' if specs else 'Run(7)'
    print(f'Main(){specs}:void = Print("{{{call}}}")')
    sys.exit(0)
if kind.startswith('lazy-'):
    effectful = 'effect' in kind or 'alt' in kind or 'failure' in kind or 'generic' in kind
    failable = 'failure' in kind
    print('counter := class:\n    var N:int = 0')
    params = 'C:counter, N:int' if effectful else 'N:int'
    args = 'C, N - 1' if effectful else 'N - 1'
    effects = 'transacts' if effectful else 'computes'
    print(f'Lazy({params})<{effects}><decides>:int =\n    N >= 0')
    if effectful:
        print('    set C.N += 1')
    print(f'    N | Lazy[{args}]')
    call = 'Lazy[C, 2]' if effectful else 'Lazy[2]'
    value = f'({call} | Two(0))' if 'alt' in kind else '(Two(0) | Two(2))'
    if 'exclusive' in kind:
        print('Early(N:int):int =\n    if (N < 0):\n        return 0\n    N | N + 1')
        value = 'Early(0)'
    clauses = ', '.join(f'A{i} := {value}' for i in range(count))
    if 'alt' not in kind:
        clauses += f', L := {call}'
    specs = '<decides>' if failable else ''
    if kind == 'lazy-generic-first':
        print(f'Run(Unused:t where t:type):int =\n    C := counter{{}}\n    if ({clauses}, E:[]t = array{{}}, A{count-1} = 1) then E.Length else -1')
        print('Main():void = Print("{Run(7)} {Run(\"s\")}")')
        sys.exit(0)
    print(f'Main(){specs}:void =\n    C := counter{{}}')
    if kind.endswith('first'):
        print(f'    if ({clauses}, A{count-1} = 1) then Print("{{A0}} {{C.N}}")')
    elif failable:
        print(f'    R := for ({clauses}):\n        A0 >= 0\n        A0\n    Print("{{R.Length}} {{C.N}}")')
    else:
        print(f'    R := for ({clauses}) {{ A0 }}\n    Print("{{R.Length}} {{C.N}}")')
    sys.exit(0)
print('Pick(X:t where t:type):t = X | X')
print('Early(N:int):int =\n    if (N < 0):\n        return 0\n    N | N + 1')
if kind in ('refined-lazy-failure', 'refined-lazy-return', 'refined-nested-body', 'refined-nested-failure'):
    print('counter := class:\n    var N:int = 0')
    print('Lazy(C:counter, N:int)<transacts><decides>:int =\n    N >= 0\n    set C.N += 1\n    N | Lazy[C, N - 1]')
if kind.startswith('refined-'):
    print('pair(a:type, b:type) := class:\n    A:a\n    B:b')
    print('dup(t:type) := class(pair(t, t)):\n    C:int = 4')
value = {'composed': '(Two(0) | Two(2))', 'exclusive': 'Early(0)',
         'binding': '(Pick(I) | Pick(I))', 'typed-first': '(Two(0) | Two(2))',
         'typed-for': '(Two(0) | Two(2))', 'typed-exclusive': 'Early(0)',
         'refined-nested-body': '', 'refined-nested-failure': '',
         'refined-for': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-state': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-failure': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-return': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-lazy-return': 'if (D := dup[P]) then (D.C | D.C + 1) else 0',
         'refined-lazy-failure': 'if (D := dup[P]) then (D.C | D.C + 1) else 0'}[kind]
clauses = ', '.join(f'A{i} := {value}' for i in range(count))
if kind in ('refined-nested-body', 'refined-nested-failure'):
    params = ', '.join(f'P{i}:pair(a{i}, b{i})' for i in range(count))
    tparams = ', '.join(f'a{i}:type, b{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i} := if (D := dup[P{i}]) then (D.C | D.C + 1) else 0, A{i} = 4' for i in range(count))
    effects = '<decides>' if kind.endswith('failure') else ''
    test = '\n            L > 0' if effects else ''
    print(f'''Run({params} where {tparams})<transacts>{effects}:int =
    C := counter{{}}
    var Total:int = 0
    R := for ({clauses}):
        defer: set Total += 1
        for (L := Lazy[C, 2]):
            set Total += L{test}
            Total
    Total + R.Length''')
elif kind in ('refined-state', 'refined-failure', 'refined-lazy-failure', 'refined-return', 'refined-lazy-return'):
    params = ', '.join(f'P{i}:pair(a{i}, b{i})' for i in range(count))
    tparams = ', '.join(f'a{i}:type, b{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i} := if (D := dup[P{i}]) then (D.C | D.C + 1) else 0, A{i} = 4, set Total += A{i}' for i in range(count))
    effects = '<decides>' if kind in ('refined-failure', 'refined-lazy-failure') else ''
    test = ('\n        if (Total > 0):\n            return Total' if kind in ('refined-return', 'refined-lazy-return') else '\n        Total > 0' if effects else '')
    init = '\n    C := counter{}' if kind in ('refined-lazy-failure', 'refined-lazy-return') else ''
    if init:
        clauses += ', L := Lazy[C, 2]'
    print(f'Run({params} where {tparams}){effects}:int ={init}\n    var Total:int = 0\n    R := for ({clauses}):\n        set Total += 1{test}\n        Total\n    Total + R.Length')
elif kind == 'refined-for':
    print(f'Run(I:t, P:pair(a, b) where t:type, a:type, b:type):[]t = for ({clauses}) {{ I }}')
elif kind == 'typed-first':
    print(f'Run(Unused:t where t:type):int = if ({clauses}, E:[]t = array{{}}) then E.Length else -1')
elif kind.startswith('typed-'):
    print(f'Run(Unused:t where t:type):int =\n    R := for ({clauses}):\n        E:[]t = array{{}}\n        E.Length\n    R.Length')
else:
    print(f'Run(I:t where t:type):[]t = for ({clauses}) {{ I }}')
if kind in ('refined-state', 'refined-failure', 'refined-lazy-failure', 'refined-return', 'refined-lazy-return', 'refined-nested-body', 'refined-nested-failure'):
    args = ', '.join('dup(int){A := 1, B := 2}' if i % 2 == 0 else 'dup(string){A := "s", B := "t"}' for i in range(count))
    effects = '<decides>' if kind in ('refined-failure', 'refined-lazy-failure', 'refined-nested-failure') else ''
    brackets = ('[', ']') if effects else ('(', ')')
    print(f'Main(){effects}:void = Print("{{Run{brackets[0]}{args}{brackets[1]}}}")')
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
