#!/usr/bin/env bash
# Doubling a sequence of generic choices must not multiply its bytecode by 16.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# Keep modes sorted on separate lines so independent additions merge cleanly.
kinds=(
  binding
  bound-failure
  bound-first
  bound-for
  bound-method-first
  bound-method-for
  bound-method-nested-first
  bound-method-phantom-first
  clause-break-composed
  clause-break-exclusive
  clause-break-refined
  clause-return-composed
  clause-return-exclusive
  clause-return-refined
  composed
  construct-failure
  construct-first
  construct-for
  covariant-failure
  covariant-first
  covariant-for
  cross-super-failure
  cross-super-first
  cross-super-for
  cross-super-lazy-first
  dispatch-default-failure
  dispatch-default-first
  dispatch-default-for
  exclusive
  immediate-suspends-composed
  immediate-suspends-exclusive
  immediate-suspends-nested
  immediate-suspends-refined
  lazy-alt-failure-for
  lazy-alt-first
  lazy-alt-for
  lazy-effect-first
  lazy-effect-for
  lazy-exclusive-failure-for
  lazy-failure-for
  lazy-first
  lazy-for
  lazy-generic-first
  lazy-named-first
  lazy-named-for
  lazy-named-generic-first
  lazy-tuple-first
  lazy-tuple-for
  lazy-tuple-generic-first
  method-failure
  method-first
  method-for
  method-instance-first
  method-instance-for
  mutual-generic-alt-first
  mutual-generic-first
  mutual-generic-for
  open-function-first
  open-function-for
  open-tuple-first
  open-tuple-for
  outer-effect-composed
  outer-effect-exclusive
  outer-effect-refined
  own-method-covariant-first
  own-method-failure
  own-method-first
  own-method-for
  recursive-return-eager
  recursive-return-first
  recursive-return-for
  recursive-return-mutual-first
  refined-failure
  refined-for
  refined-lazy-failure
  refined-lazy-return
  refined-nested-body
  refined-nested-failure
  refined-retry-first
  refined-return
  refined-state
  return-defer-failure
  return-defer-first
  return-defer-for
  return-defer-method-first
  spawn-default-composed
  spawn-default-refined
  spawn-default-view
  super-body
  super-failure
  super-first
  super-for
  suspends-return
  suspends-return-generic
  suspends-return-lazy
  tuple-super-failure
  tuple-super-first
  tuple-super-for
  typed-exclusive
  typed-first
  typed-for
  waiting-refined
  waiting-refined-lazy
  waiting-refined-opened
  waiting-refined-return
  waiting-refined-state
)
for kind in "${kinds[@]}"; do
  sizes=()
  for count in 4 8; do
    python3 - "$kind" "$count" >"$tmp/p.verse" <<'PY'
import sys
kind, count = sys.argv[1], int(sys.argv[2])
print('Two(N:int):int = N | N + 1')
if kind.startswith('method-instance-'):
    print('''box(t:type):=class:
    V:t
    Same(X:u where u:type)<computes>:u=X''')
    params = ','.join(f'B{i}:box(a{i}),X{i}:b{i}' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    binds = '\n'.join(f'    F{i}:type{{_(:b{i})<computes>:b{i}}}=B{i}.Same' for i in range(count))
    clauses = ','.join(f'A{i}:=F{i}(X{i})|F{i}(X{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]a0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]a0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{binds}\n{body}')
    args = []
    for i in range(count):
        ty, value, x = ('int','7','"s"') if i%2==0 else ('string','"v"','9')
        args.extend([f'box({ty}){{V:={value}}}',x])
    print(f'Main():void=Print("{{Run({",".join(args)})}}")')
    sys.exit(0)
if kind.startswith('open-tuple-'):
    print('Id(X:t where t:type)<computes>:t=X')
    params = ','.join(f'X{i}:a{i},Y{i}:b{i}' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    binds = '\n'.join(f'    F{i}:type{{_(:a{i},:b{i})<computes>:tuple(a{i},b{i})}}=Id' for i in range(count))
    clauses = ','.join(f'A{i}:=F{i}(X{i},Y{i})|F{i}(X{i},Y{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]a0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]a0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{binds}\n{body}')
    args = ','.join('7,"s"' if i%2==0 else '"v",9' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('open-function-'):
    print('Id(X:t where t:type)<computes>:t=X')
    params = ','.join(f'X{i}:t{i}' for i in range(count))
    tparams = ','.join(f't{i}:type' for i in range(count))
    binds = '\n'.join(f'    F{i}:type{{_(:t{i})<computes>:t{i}}}=Id' for i in range(count))
    clauses = ','.join(f'A{i}:=F{i}(X{i})|F{i}(X{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]t0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]t0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{binds}\n{body}')
    args = ','.join('7' if i%2==0 else '"s"' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('bound-method-'):
    print('''cell:=class{var N:int=0}
box(t:type,u:type):=class:
    V:t
    Extra:u
    C:cell
    Same(X:t)<transacts>:t=block{set C.N+=1;X}
    Array(X:[]t)<transacts>:[]t=block{set C.N+=1;X}
    Size()<transacts>:int=block{set C.N+=1;3}''')
    nested, phantom = 'nested' in kind, 'phantom' in kind
    params = ','.join(f'B{i}:box(a{i},b{i}),X{i}:' + (f'[]a{i}' if nested else f'a{i}') for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    method = 'Size' if phantom else 'Array' if nested else 'Same'
    binds = '\n'.join(f'    F{i}:=B{i}.{method}' for i in range(count))
    calls = [f'F{i}()' if phantom else f'F{i}(X{i})' for i in range(count)]
    clauses = ','.join(f'A{i}:={call}|{call}' for i,call in enumerate(calls))
    result = 'A0.Length' if nested else 'A0' if phantom else 'E.Length'
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]b0=Concatenate())then {result} else -1'
    else:
        body = f'    R:=for({clauses},E:[]b0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<transacts>:int=\n{binds}\n{body}')
    args = []
    for i in range(count):
        ty, value, extra_ty, extra = ('int','7','string','"s"') if i%2==0 else ('string','"x"','int','9')
        args.extend([f'box({ty},{extra_ty}){{V:={value},Extra:={extra},C:=cell{{}}}}', f'array{{{value}}}' if nested else value])
    print(f'Main():void=Print("{{Run({",".join(args)})}}")')
    sys.exit(0)
if kind.startswith('recursive-return-'):
    eager = kind.endswith('eager')
    mutual = 'mutual' in kind
    if eager:
        print('Id(X:t where t:type)<computes>:t = X\nProduce(X:t,Y:t,N:int where t:type)<computes>:t =\n    if(N<=0):return X|Y\n    NextN:=N-1\n    return Id(Produce(X,Y,NextN))')
    else:
        target = 'Other' if mutual else 'Produce'
        print(f'''Produce(X:t,Y:t,N:int where t:type)<transacts>:t =
    if(N<=0):
        Print("base")
        V:=X
        return V|Y
    Print("visit")
    NextN:=N-1
    return X|{target}(Y,X,NextN)''')
        if mutual:
            print('''Other(Y:u,X:u,N:int where u:type)<transacts>:u =
    if(N<=0):return Y|X
    NextN:=N-1
    Print("other")
    return Y|Produce(X,Y,NextN)''')
    params = ','.join(f'X{i}:t{i},Y{i}:t{i}' for i in range(count))
    tparams = ','.join(f't{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=Produce(X{i},Y{i},2)' for i in range(count))
    if kind.endswith('first'):
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses},E:[]t0=array{{A0}})then E.Length else -1')
    else:
        print(f'Run({params} where {tparams})<transacts>:int = (for({clauses}):A0).Length')
    args = ','.join('1,2' if i%2==0 else '"x","y"' for i in range(count))
    print(f'Main():void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('waiting-refined'):
    opened = kind.endswith('opened')
    lazy = kind.endswith('lazy')
    returning = kind.endswith('return')
    state = kind.endswith('state')
    if opened:
        print('expr(t:type):=class{}')
        print('pairE(a:type,b:type):=class(expr(tuple(a,b))){L:a;R:b;C:int=4}')
        params = ','.join(f'P{i}:expr(t{i})' for i in range(count))
        tparams = ','.join(f't{i}:type' for i in range(count))
        values = [f'if(D{i}:=pairE[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)]
        args = ','.join('pairE(int,string){L:=1,R:="s"}' for _ in range(count))
    else:
        print('pair(a:type,b:type):=class{A:a;B:b}')
        print('dup(t:type):=class(pair(t,t)){C:int=4}')
        print('Lazy(N:int)<computes><decides>:int=\n    N>=0\n    N|Lazy[N-1]')
        params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
        tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
        values = [f'if(D{i}:=dup[P{i}])then ' +
                  (f'Lazy[D{i}.C-3]' if lazy else f'(D{i}.C|D{i}.C+1)') + 'else 0'
                  for i in range(count)]
        args = ','.join('dup(int){A:=1,B:=2}' for _ in range(count))
    clauses = []
    for i, value in enumerate(values):
        clauses.append(f'A{i}:={value}')
        if state: clauses.append(f'set Total+=A{i}')
    total = '+'.join(f'A{i}' for i in range(count))
    print(f'Run({params} where {tparams})<suspends>:{"int" if returning else "void"} =')
    if state: print('    var Total:int=0')
    if returning: print('    defer:Print("source")')
    print(f'    {"" if returning else "R:="}for({",".join(clauses)}):')
    print('        Sleep(0.0)')
    if opened: print('        Empty:[]t0=array{}')
    if state: print('        set Total+=1')
    print(f'        {"return " if returning else ""}{total}')
    print('    -1' if returning else '    Print("rows {R.Length}' + (' {Total}' if state else '') + '")')
    print(f'Main()<suspends>:void = ' + (f'Print("{{Run({args})}}")' if returning else f'Run({args})'))
    raise SystemExit
if kind.startswith('clause-break-'):
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('Early(N:int):int =\n    if(N<0):return 0\n    N|N+1')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    values = [f'if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)]
    generic = kind.endswith('refined')
    if kind.endswith('composed'): values = ['(Two(0)|Two(2))'] * count
    if kind.endswith('exclusive'): values = ['Early(0)'] * count
    clauses = [f'A{i}:={v}' for i,v in enumerate(values)]
    ret_ty, result, selected = ('a0', 'P0.A', 5) if generic else ('int', 'Total', 1)
    clauses[1:1] = ['set Total+=A0', f'if(A0={selected})then break else 0']
    print(f'Run({params} where {tparams})<suspends>:{ret_ty} =\n    var Total:int=0\n    defer:Print("source {{Total}}")\n    Sleep(0.0)\n    loop:\n        defer:Print("loop {{Total}}")\n        R:=for({",".join(clauses)}):\n            set Total+=1\n            A0\n        Print("rows {{R.Length}}")\n        break\n    Sleep(0.1)\n    {result}')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('return-defer-'):
    method = kind.endswith('method-first')
    if method:
        print('''base(a:type) := class:
    Anchor:a
    var Count:int=0
    Tick()<transacts>:void = set Count+=1
child(b:type) := class(base(b)):
    Pick(X:c,Y:c,Mode:int where c:type)<transacts>:tuple(b,c) =
        defer:(super:)Tick()
        if(Mode>=0):
            defer:(super:)Tick()
            if(Mode=0):return (Anchor,X)|(Anchor,Y)
        defer:(super:)Tick()
        (Anchor,X)|(Anchor,Y)''')
        params = ','.join(f'P{i}:child(a{i}),X{i}:b{i},Y{i}:b{i}' for i in range(count))
        tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
        calls = [f'P{i}.Pick(X{i},Y{i},{[0,1,-1][i%3]})' for i in range(count)]
        args = ','.join('child(int){Anchor:=7},"x","y"' if i%2==0 else 'child(string){Anchor:="s"},1,2' for i in range(count))
        value, ty = 'A0(1)', 'b0'
    else:
        print('''cell := class { var N:int=0 }
Produce(H:cell,X:t,Y:t,Mode:int where t:type)<transacts>:t =
    defer:set H.N+=1
    if(Mode>=0):
        defer:set H.N+=10
        if(Mode=0):return X|Y
    defer:set H.N+=100
    X|Y''')
        params = 'H:cell,' + ','.join(f'X{i}:t{i},Y{i}:t{i}' for i in range(count))
        tparams = ','.join(f't{i}:type' for i in range(count))
        calls = [f'Produce(H,X{i},Y{i},{[0,1,-1][i%3]})' for i in range(count)]
        args = 'cell{},' + ','.join('1,2' if i%2==0 else '"x","y"' for i in range(count))
        value, ty = 'A0', 't0'
    clauses = ','.join(f'A{i}:={call}' for i,call in enumerate(calls))
    if kind.endswith('first'):
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses},E:[]{ty}=array{{{value}}})then E.Length else -1')
    else:
        fx = '<decides>' if kind.endswith('failure') else ''
        check = '\n        1=1' if fx else ''
        print(f'Run({params} where {tparams})<transacts>{fx}:int =\n    R:=for({clauses}):{check}\n        {value}\n    R.Length')
    fx = '<decides>' if kind.endswith('failure') else ''
    br = ('[',']') if fx else ('(',')')
    print(f'Main(){fx}:void = Print("{{Run{br[0]}{args}{br[1]}}}")')
    sys.exit(0)
if kind.startswith('cross-super-'):
    print('''base(t:type) := class:
    Data:t
    Scalar(X:u,?E:[]t=Concatenate() where u:type)<transacts>:tuple(t,u,int) =
        Print("scalar")
        (Data,X,E.Length)
child(v:type) := class(base(v)):
    Values(X:w where w:type)<transacts>:tuple(v,w,int) =
        (super:)Scalar(X)|(super:)Scalar(X,?E:=array{Data})
    Walk(X:w,N:int where w:type)<transacts><decides>:tuple(v,w,int) =
        N>=0
        (super:)Scalar(X)|Self.Walk[X,N-1]''')
    params = ','.join(f'P{i}:child(a{i}),X{i}:b{i}' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    lazy = kind.endswith('lazy-first')
    clauses = ','.join(f'A{i}:=P{i}.Walk[X{i},1]' if lazy else f'A{i}:=P{i}.Values(X{i})' for i in range(count))
    if kind.endswith('first'):
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses},E:[]b0=array{{A0(1)}})then E.Length else -1')
    else:
        fx = '<decides>' if kind.endswith('failure') else ''
        check = '\n        1=1' if fx else ''
        print(f'Run({params} where {tparams})<transacts>{fx}:int =\n    R:=for({clauses}):{check}\n        A0(1)\n    R.Length')
    args = ','.join('child(int){Data:=7},"s"' if i%2==0 else 'child(string){Data:="a"},9' for i in range(count))
    fx = '<decides>' if kind.endswith('failure') else ''
    br = ('[',']') if fx else ('(',')')
    print(f'Main(){fx}:void = Print("{{Run{br[0]}{args}{br[1]}}}")')
    sys.exit(0)
if kind.startswith('spawn-default-'):
    viewed = kind.endswith('view')
    refined = not kind.endswith('composed')
    print('pair(a:type,b:type) := class { A:a;B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    root = 'sink' if viewed else 'base'
    if viewed:
        print('first(z:type) := interface { Tag():z }')
        print('sink(t:type) := interface { Run(P:pair(a,b),?N:int=0 where a:type,b:type)<suspends>:int }')
        print('impl(z:type,y:type) := class(first(z),sink(y)):\n    Marker:z\n    Seed:int=4\n    Tag<override>():z=Marker')
        instance = 'impl(string,int){Marker:="x"}'
    else:
        print('base(t:type) := class { Run(P:pair(a,b),?N:int=0 where a:type,b:type)<suspends>:int=0 }')
        print('impl(z:type) := class(base(int)):\n    Marker:z\n    Seed:int=4')
        instance = 'impl(string){Marker:="x"}'
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P])then(D{i}.C|D{i}.C+1)else 0' if refined else f'A{i}:=(Two(0)|Two(2))' for i in range(count))
    print(f'    Run<override>(P:pair(c,d),?N:int=Seed where c:type,d:type)<suspends>:int=\n        var Total:int=0\n        for({clauses}):set Total+=1\n        Sleep(0.0)\n        N+Total')
    print(f'Start(P:{root}(t),X:pair(a,b) where t:type,a:type,b:type):task(int)=spawn{{P.Run(X)}}')
    print(f'Main()<suspends>:void=\n    T:=Start({instance},dup(int){{A:=1,B:=2}})\n    Print("{{T.Await()}}")')
    sys.exit(0)
if kind.startswith('clause-return-'):
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('Early(N:int):int =\n    if(N<0):return 0\n    N|N+1')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    values = [f'if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)]
    generic = kind.endswith('refined')
    if kind.endswith('composed'): values = ['(Two(0)|Two(2))'] * count
    if kind.endswith('exclusive'): values = ['Early(0)'] * count
    clauses = [f'A{i}:={v}' for i,v in enumerate(values)]
    ret_ty, result, selected = ('a0', 'P0.A', 5) if generic else ('int', 'Total', 1)
    clauses[1:1] = ['set Total+=A0', f'if(A0={selected})then return {result} else 0']
    print(f'Run({params} where {tparams})<suspends>:{ret_ty} =\n    var Total:int=0\n    defer:Print("source {{Total}}")\n    Sleep(0.0)\n    R:=for({",".join(clauses)}):\n        set Total+=1\n        A0\n    Sleep(0.1)\n    {result}')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('outer-effect-'):
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('cell := class { var N:int=0 }')
    print('Early(N:int):int =\n    if(N<0):return 0\n    N|N+1')
    effect, operand = ('writes', 'set H.N=N\n    N')
    if kind.endswith('composed'): effect, operand = 'reads', 'H.N+N'
    if kind.endswith('exclusive'): effect, operand = 'allocates', 'Unused:=cell{}\n    N'
    print(f'Operand(H:cell,N:int)<{effect}>:int =\n    {operand}')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    values = [f'if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)]
    if kind.endswith('composed'): values = ['(Two(0)|Two(2))'] * count
    if kind.endswith('exclusive'): values = ['Early(0)'] * count
    clauses = ','.join(f'A{i}:={v}' for i,v in enumerate(values))
    print(f'Run(H:cell,Scope:pair(sx,sy),{params} where sx:type,sy:type,{tparams})<suspends>:int =\n    if(S:=dup[Scope]):\n        Sleep(0.0)\n        for({clauses}):return Operand(H,A0)\n    -1')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void = Print("{{Run(cell{{}},dup(int){{A:=0,B:=0}},{args})}}")')
    sys.exit(0)
if kind.startswith('suspends-return'):
    print('pair(a:type,b:type) := class { A:a; B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('counter := class { var N:int=0 }')
    print('Lazy(H:counter,N:int)<transacts><decides>:int =\n    N>=0\n    set H.N+=1\n    N|Lazy[H,N-1]')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count))
    if kind.endswith('lazy'): clauses += ',L:=Lazy[H,2]'
    generic = kind.endswith('generic')
    ret_ty, result, fallback = ('a0','P0.A','P0.A') if generic else ('int','Total','-1')
    print(f'Run({params} where {tparams})<suspends>:{ret_ty} =\n    var Total:int=0\n    H:=counter{{}}\n    defer:Print("source {{Total}}")\n    branch:\n        defer:Print("observer {{Total}}")\n        Sleep(1.0)\n    Sleep(0.0)\n    for({clauses}):\n        defer:set Total+=100\n        set Total+=A0\n        if(A0=5):return {result}\n        A0\n    Sleep(0.1)\n    {fallback}')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void = Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('own-method-'):
    covariant = kind == 'own-method-covariant-first'
    if covariant:
        print('''animal(a:type,b:type) := class { First:a; Second:b }
dog(a:type,b:type) := class(animal(a,b)) { Code:int=1 }
base(a:type) := class:
    Anchor:a
    Pick(X:b where b:type)<transacts>:animal(a,b) = animal(a,b){First:=Anchor,Second:=X}|animal(a,b){First:=Anchor,Second:=X}
child(u:type) := class(base(u)):
    Pick<override>(X:v where v:type)<transacts>:dog(u,v) = dog(u,v){First:=Anchor,Second:=X}|dog(u,v){First:=Anchor,Second:=X}''')
    else:
        print('''base(a:type) := class:
    Anchor:a
    Pick(X:b,Y:[]b,?E:?b=false where b:type)<transacts>:b = X|X
child(u:type) := class(base(u)):
    Pick<override>(X:v,Y:[]v,?E:?v=false where v:type)<transacts>:v = X|(super:)Pick((X,Y))''')
    params = ','.join(f'P{i}:child(a{i}),X{i}:b{i}' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=P{i}.Pick(X{i})' if covariant else f'A{i}:=P{i}.Pick((X{i},array{{}}))' for i in range(count))
    if kind.endswith('first'):
        value = 'A0.Second' if covariant else 'A0'
        print(f'Run({params} where {tparams})<transacts>:int = if({clauses},E:[]b0=array{{{value}}})then E.Length else -1')
    else:
        fx = '<decides>' if kind.endswith('failure') else ''
        check = '\n        1=1' if fx else ''
        print(f'Run({params} where {tparams})<transacts>{fx}:int =\n    R:=for({clauses}):{check}\n        A0\n    R.Length')
    args = ','.join('child(int){Anchor:=7},"s"' if i%2==0 else 'child(string){Anchor:="a"},9' for i in range(count))
    br = ('[',']') if kind.endswith('failure') else ('(',')')
    fx = '<decides>' if kind.endswith('failure') else ''
    print(f'Main(){fx}:void = Print("{{Run{br[0]}{args}{br[1]}}}")')
    sys.exit(0)
if kind.startswith('dispatch-default-'):
    print('box(t:type) := class:\n    Get(?X:[]t=Concatenate())<computes>:int=X.Length')
    print('fixed := class(box(int)):\n    A:int=1\n    Get<override>(?X:[]int=block{Print("default");array{A}})<computes>:int=X.Length')
    clauses = ','.join(f'A{i}:=(Two(0)|Two(2)),N{i}:=P.Get()' for i in range(count))
    if kind == 'dispatch-default-first':
        print(f'Run(P:box(t) where t:type)<transacts>:int=if({clauses})then N0 else -1')
    else:
        specs = '<decides>' if kind == 'dispatch-default-failure' else ''
        check = '\n        1=1' if specs else ''
        print(f'Run(P:box(t) where t:type)<transacts>{specs}:int=\n    R:=for({clauses}):{check}\n        N0\n    R.Length')
    specs = '<decides>' if kind == 'dispatch-default-failure' else ''
    call = 'Run[fixed{}]' if specs else 'Run(fixed{})'
    print(f'Main()<transacts>{specs}:void=Print("{{{call}}}")')
    sys.exit(0)
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
