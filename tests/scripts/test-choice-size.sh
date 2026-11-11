#!/usr/bin/env bash
# Doubling a sequence of generic choices must not multiply its bytecode by 16.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
for kind in composed exclusive binding typed-first typed-for typed-exclusive refined-for refined-state refined-failure lazy-first lazy-for lazy-effect-first lazy-effect-for lazy-alt-first lazy-alt-for lazy-failure-for lazy-alt-failure-for lazy-exclusive-failure-for refined-lazy-failure refined-return refined-lazy-return refined-nested-body refined-nested-failure lazy-generic-first construct-first construct-for construct-failure method-first method-for method-failure lazy-named-first lazy-named-for lazy-named-generic-first bound-first bound-for bound-failure covariant-first covariant-for covariant-failure tuple-super-first tuple-super-for tuple-super-failure lazy-tuple-first lazy-tuple-for lazy-tuple-generic-first immediate-suspends-refined immediate-suspends-composed immediate-suspends-exclusive immediate-suspends-nested refined-retry-first super-first super-for super-failure super-body mutual-generic-first mutual-generic-for mutual-generic-alt-first; do
  sizes=()
  for count in 4 8; do
    python3 - "$kind" "$count" >"$tmp/p.verse" <<'PY'
import sys
kind, count = sys.argv[1], int(sys.argv[2])
print('Two(N:int):int = N | N + 1')
if kind == 'refined-retry-first':
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count))
    checks = ','.join(f'A{i}=5' for i in range(count))
    print(f'Run({params} where {tparams}):int = if({clauses},{checks})then A0 else -1')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main():void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('immediate-suspends-'):
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('Early(N:int):int =\n    if(N<0):return 0\n    N|N+1')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    values = [f'if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)]
    if kind.endswith('composed'): values = ['(Two(0)|Two(2))'] * count
    if kind.endswith('exclusive'): values = ['Early(0)'] * count
    clauses = ','.join(f'A{i}:={v}' for i,v in enumerate(values))
    nested = '\n        var Local:int=A0\n        if(F:=dup[P0]):set Local+=F.C\n        set Total+=Local' if kind.endswith('nested') else '\n        set Total+=A0'
    print(f'Run({params} where {tparams})<suspends>:int =\n    var Total:int=0\n    branch:\n        Sleep(0.1)\n        Print("observe {{Total}}")\n    Sleep(0.0)\n    R:=for({clauses}):\n        Empty:[]a0=Concatenate(){nested}\n        Empty.Length\n    Sleep(0.2)\n    R.Length')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('super-'):
    print('base := class:\n    Limit()<computes>:int = 1')
    print('child := class(base):\n    Limit<override>()<computes>:int = 100')
    clauses = ', '.join(f'A{i}:=(Two(0)|Two(2))' for i in range(count))
    if kind == 'super-first':
        print(f'    Run()<transacts>:int = if({clauses}, (super:)Limit()=1) then A0 else -1')
    else:
        specs = '<decides>' if kind == 'super-failure' else ''
        suffix = '' if kind == 'super-body' else ', (super:)Limit()=1'
        check = '\n            1=1' if specs else ''
        body = 'A0+(super:)Limit()' if kind == 'super-body' else 'A0'
        print(f'    Run()<transacts>{specs}:int =\n        R:=for({clauses}{suffix}):{check}\n            {body}\n        R.Length')
    specs = '<decides>' if kind == 'super-failure' else ''
    call = 'child{}.Run[]' if specs else 'child{}.Run()'
    print(f'Main()<transacts>{specs}:void = Print("{{{call}}}")')
    sys.exit(0)
if kind.startswith('mutual-generic-'):
    print('''Left(X:t,N:int where t:type)<transacts>:t =
    Print("left {N}")
    if(N>0)then(X|Right((X,N-1)))else X
Right(X:u,N:int,?E:[]u=Concatenate() where u:type)<transacts>:u =
    Print("right {N}")
    if(N>0)then(X|Left((X,N-1)))else X''')
    clauses = ', '.join(f'A{i}:=' +
        ('(Left((I,1))|Right((I,1)))' if kind == 'mutual-generic-alt-first' else 'Left((I,1))')
        for i in range(count))
    if kind == 'mutual-generic-for':
        print(f'Run(I:t where t:type)<transacts>:int =\n    R:=for({clauses}): I\n    R.Length')
    else:
        print(f'Run(I:t where t:type)<transacts>:int = if({clauses},E:[]t=Concatenate())then E.Length else -1')
    print('Main():void = Print("{Run(7)}")')
    raise SystemExit
if kind.startswith('tuple-super-'):
    print('box(t:type) := class:\n    Both(X:t,Y:[]t)<transacts>:t = if(Y.Length=0) then (X|X) else X')
    print('child(u:type) := class(box(u)):\n    Both<override>(X:u,Y:[]u)<transacts>:u = (super:)Both((X,Y))')
    params = ', '.join(f'P{i}:child(t{i}),I{i}:t{i}' for i in range(count))
    tparams = ', '.join(f't{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i}:=P{i}.Both((I{i},array{{}}))' for i in range(count))
    if kind == 'tuple-super-first':
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses}, E:[]t0=array{{A0}}) then E.Length else -1')
    else:
        specs = '<decides>' if kind == 'tuple-super-failure' else ''
        test = '\n        1=1' if specs else ''
        print(f'Run({params} where {tparams})<transacts>{specs}:int =\n    R:=for({clauses}):{test}\n        A0\n    R.Length')
    args = ', '.join('child(int){},1' if i%2==0 else 'child(string){},"s"' for i in range(count))
    specs = '<decides>' if kind == 'tuple-super-failure' else ''
    call = f'Run[{args}]' if specs else f'Run({args})'
    print(f'Main()<transacts>{specs}:void = Print("{{{call}}}")')
    sys.exit(0)
if kind.startswith('covariant-'):
    print('value(t:type) := class { V:t }')
    print('narrow(t:type) := class(value(t)) { Code:int=1 }')
    print('box(t:type) := class:\n    A:narrow(t)\n    B:narrow(t)\n    Both()<transacts>:value(t) = A | B')
    print('child(t:type) := class(box(t)):\n    Both<override>()<transacts>:narrow(t) = B | A')
    params = ', '.join(f'P{i}:child(t{i})' for i in range(count))
    tparams = ', '.join(f't{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i}:=P{i}.Both()' for i in range(count))
    if kind == 'covariant-first':
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses}, E:[]t0=array{{A0.V}}, A0.Code=1) then E.Length else -1')
    else:
        specs = '<decides>' if kind == 'covariant-failure' else ''
        test = '\n        A0.Code=1' if specs else ''
        print(f'Run({params} where {tparams})<transacts>{specs}:int =\n    R:=for({clauses}):{test}\n        A0.V\n    R.Length')
    args = ', '.join('child(int){A:=narrow(int){V:=1},B:=narrow(int){V:=2}}' if i%2==0 else 'child(string){A:=narrow(string){V:="s"},B:=narrow(string){V:="t"}}' for i in range(count))
    specs = '<decides>' if kind == 'covariant-failure' else ''
    call = f'Run[{args}]' if specs else f'Run({args})'
    print(f'Main()<transacts>{specs}:void = Print("{{{call}}}")')
    sys.exit(0)
if kind.startswith('bound-'):
    print('box(t:type) := class { A:t }')
    print('tight(t:subtype(comparable),u:subtype(comparable)) := class(box(t)) { E:u }')
    params = ', '.join(f'P{i}:box(t{i})' for i in range(count))
    tparams = ', '.join(f't{i}:type' for i in range(count))
    clauses = ', '.join(f'A{i}:=if(D:=tight[P{i}]) then (if(D.A=D.A,D.E=D.E) then(D.A|D.A) else D.A) else P{i}.A' for i in range(count))
    if kind == 'bound-first':
        print(f'Run({params} where {tparams}):int = if({clauses}, E:[]t0=array{{}}) then E.Length else -1')
    else:
        specs = '<decides>' if kind == 'bound-failure' else ''
        test = '\n        1=1' if specs else ''
        print(f'Run({params} where {tparams}){specs}:int =\n    R:=for({clauses}):{test}\n        A0\n    R.Length')
    args = ', '.join('tight(int,string){A:=1,E:="s"}' if i%2==0 else 'tight(string,int){A:="s",E:=1}' for i in range(count))
    specs = '<decides>' if kind == 'bound-failure' else ''
    call = f'Run[{args}]' if specs else f'Run({args})'
    print(f'Main(){specs}:void = Print("{{{call}}}")')
    sys.exit(0)
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
    effectful = any(tag in kind for tag in ('effect', 'alt', 'failure', 'generic', 'named', 'tuple'))
    failable = 'failure' in kind
    print('counter := class:\n    var N:int = 0')
    params = 'C:counter, N:int' if effectful else 'N:int'
    args = 'C, N - 1' if effectful else 'N - 1'
    if 'named' in kind:
        params += ', ?Step:int = 1'
        args += ', ?Step := Step'
    if 'tuple' in kind:
        args = f'({args})'
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
    if 'generic' in kind:
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
