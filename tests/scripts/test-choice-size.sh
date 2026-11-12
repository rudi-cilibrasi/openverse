#!/usr/bin/env bash
# Doubling a sequence of generic choices must not multiply its bytecode by 16.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# Each compile has a time limit only so that a hang stops the check; the bytecode size is the test.
# The slowest case takes about 7 s, but on a machine busy with other jobs local runs stopped at 30 s.
limit="${CHOICE_SIZE_TIMEOUT:-120}"
# Keep modes sorted on separate lines so independent additions merge cleanly.
kinds=(
  named-optional-first
  named-optional-for
  named-optional-waiting
  named-partial-first
  named-partial-for
  named-partial-waiting
  named-reordered-first
  named-reordered-for
  named-reordered-waiting
  named-generic-first
  named-generic-for
  named-generic-waiting
  named-inherited-first
  named-inherited-for
  named-inherited-waiting
  named-waitingdefault-first
  named-waitingdefault-for
  named-waitingdefault-waiting
  setter-nested-first
  setter-nested-for
  setter-nested-waiting
  setter-varying-first
  setter-varying-for
  setter-varying-waiting
  setter-deep-first
  setter-deep-for
  setter-deep-waiting
  setter-simple-first
  setter-simple-for
  setter-simple-waiting
  setter-compound-first
  setter-compound-for
  setter-compound-waiting
  setter-array-first
  setter-array-for
  setter-array-waiting
  setter-alias-first
  setter-alias-for
  setter-alias-waiting
  setter-choice-first
  setter-choice-for
  setter-choice-waiting
  conversion-literal-first
  conversion-literal-for
  conversion-literal-waiting
  conversion-monomorphic-first
  conversion-monomorphic-for
  conversion-monomorphic-waiting
  conversion-generic-first
  conversion-generic-for
  conversion-generic-waiting
  conversion-default-first
  conversion-default-for
  conversion-default-waiting
  conversion-refined-first
  conversion-refined-for
  conversion-refined-waiting
  conversion-refineddefault-first
  conversion-refineddefault-for
  conversion-refineddefault-waiting
  resultalias-same-first
  resultalias-same-for
  resultalias-same-waiting
  resultalias-different-first
  resultalias-different-for
  resultalias-different-waiting
  resultalias-field-first
  resultalias-field-for
  resultalias-field-waiting
  resultalias-generic-first
  resultalias-generic-for
  resultalias-generic-waiting
  alias-block-first
  alias-block-for
  alias-block-waiting
  alias-clauses-first
  alias-clauses-for
  alias-clauses-waiting
  alias-generic-first
  alias-generic-for
  alias-generic-waiting
  binding
  bound-failure
  bound-first
  bound-for
  bound-method-first
  bound-method-for
  bound-method-nested-first
  bound-method-phantom-first
  context-value-first
  context-value-for
  context-method-first
  context-method-for
  context-method-nested
  context-method-nested-dispatch
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
  context-block-composed
  context-block-exclusive
  context-block-first
  context-block-lazy-first
  context-constructor-composed
  context-constructor-exclusive
  context-constructor-first
  context-constructor-lazy-first
  context-defer-composed
  context-defer-exclusive
  context-defer-first
  context-defer-lazy-first
  context-field-default-composed
  context-field-default-exclusive
  context-field-default-first
  context-field-default-lazy-first
  context-param-default-composed
  context-param-default-exclusive
  context-param-default-first
  context-param-default-lazy-first
  context-refining-block-first
  context-refining-block-for
  context-refining-branch-first
  context-refining-branch-for
  context-refining-branch-waiting
  context-refining-constructor-first
  context-refining-constructor-for
  context-refining-defer-first
  context-refining-defer-for
  context-refining-field-first
  context-refining-field-for
  context-refining-parameter-first
  context-refining-parameter-for
  context-refining-race-first
  context-refining-race-for
  context-refining-race-waiting
  context-refining-rush-first
  context-refining-rush-for
  context-refining-rush-waiting
  context-refining-sync-first
  context-refining-sync-for
  context-refining-sync-waiting
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
  dictionary-simple-first
  dictionary-simple-for
  dictionary-simple-waiting
  dictionary-arguments-first
  dictionary-arguments-for
  dictionary-arguments-waiting
  dictionary-correlated-first
  dictionary-correlated-for
  dictionary-correlated-waiting
  dictionary-generic-first
  dictionary-generic-for
  dictionary-generic-waiting
  dictionary-generic-arguments-first
  dictionary-generic-arguments-for
  dictionary-generic-arguments-waiting
  dictionary-awaiting-waiting
  dictionary-generic-awaiting-waiting
  polymorphic-identity-first
  polymorphic-identity-for
  polymorphic-identity-waiting
  polymorphic-generic-first
  polymorphic-generic-for
  polymorphic-generic-waiting
  polymorphic-erased-first
  polymorphic-erased-for
  polymorphic-erased-waiting
  polymorphic-awaiting-waiting
  getter-simple-first
  getter-simple-for
  getter-simple-waiting
  getter-mixed-first
  getter-mixed-for
  getter-mixed-waiting
  getter-chained-first
  getter-chained-for
  getter-chained-waiting
  getter-generic-first
  getter-generic-for
  getter-generic-waiting
  getter-lengths-first
  getter-lengths-for
  getter-lengths-waiting
  getter-awaiting-waiting
  member-future-first
  member-future-for
  member-future-waiting
  member-callback-first
  member-callback-for
  member-callback-waiting
  member-callback-result-first
  member-callback-result-for
  member-callback-result-waiting
  member-awaiting-waiting
  member-mixed-first
  member-mixed-for
  member-mixed-waiting
  member-mixed-awaiting-waiting
  exclusive
  heterogeneous-nested-for
  heterogeneous-unused-first
  heterogeneous-unused-for
  heterogeneous-unused-waiting
  heterogeneous-equal-first
  heterogeneous-equal-for
  heterogeneous-equal-waiting
  heterogeneous-default-first
  heterogeneous-default-for
  heterogeneous-default-waiting
  heterogeneous-array-first
  heterogeneous-array-for
  heterogeneous-array-waiting
  heterogeneous-tuple-first
  heterogeneous-tuple-for
  heterogeneous-tuple-waiting
  heterogeneous-box-first
  heterogeneous-box-for
  heterogeneous-box-waiting
  heterogeneous-result-first
  heterogeneous-result-for
  heterogeneous-result-waiting
  heterogeneous-fields-first
  heterogeneous-fields-for
  heterogeneous-fields-waiting
  immediate-event-refined
  immediate-spawn-refined
  first-return-composed
  first-return-generic
  first-return-independent
  first-return-lazy
  first-return-mutual
  first-return-refined
  first-return-void
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
  method-tuple-first
  method-tuple-for
  method-variance-first
  method-variance-for
  method-variance-pack-first
  method-variance-pack-for
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
  waiting-default-method-composed
  waiting-default-method-lazy
  waiting-default-method-refined
  waiting-default-parameter-composed
  waiting-default-parameter-lazy
  waiting-default-parameter-refined
  waiting-composed
  waiting-composed-lazy
  waiting-exclusive
  waiting-exclusive-prefix
  waiting-generic-state
  waiting-mixed-arrays
  waiting-nested-value
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
if kind.startswith('named-'):
    _, shape, mode = kind.split('-')
    n = count
    waiting=mode=='waiting'
    print('Dup(X:t where t:type)<computes>:t=X|X')
    if shape=='waitingdefault':
     print('Next(X:int)'+('<suspends>' if waiting else '<computes>')+':int='+('block{Sleep(0.001);X}' if waiting else 'X'))
    method='M(?X:int=K)<computes>:int=X'
    args=lambda i:''
    if shape=='partial':
     method='M(?X:int=K,?Y:int=5)<computes>:int=X+Y';args=lambda i:'?Y:=3'
    elif shape=='reordered':
     method='M(?X:int=K,?Y:int=5)<computes>:int=X+Y';args=lambda i:'?Y:=3,?X:=4'
    elif shape=='generic':
     method='M(X:u,?Y:u=X where u:type)<computes>:u=Y';args=lambda i:f'A{i}.K,?Y:=A{i}.K'
    elif shape=='waitingdefault':
     method='M(?X:int=Next(K))'+('<suspends>' if waiting else '<computes>')+':int=X'
    if shape=='inherited':
     print('base:=class:\n    K:int\n    '+method+'\nca:=class(base){}\ncb:=class(base){}')
    else:
     for name in ['ca','cb']:print(name+':=class:\n    K:int\n    '+method)
    clauses=','.join(f'A{i}:=(Dup(ca{{K:=1}})|Dup(cb{{K:=2}}))' for i in range(n))
    value='+'.join(f'A{i}.M({args(i)})' for i in range(n))
    print('Main()'+('<suspends>' if waiting else '')+':void=')
    if mode=='first':print(f'    if({clauses},R:={value}):Print("ok")')
    else:
     body='block{Sleep(0.001);'+value+'}' if waiting else value
     print(f'    Rows:=for({clauses}):{body}\n    Print("{{Rows.Length}}")')
    sys.exit(0)
print('Two(N:int):int = N | N + 1')
if kind == 'heterogeneous-nested-for':
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Main():void=')
    body = '0'
    for i in range(count):
        body = f'for(A{i}:=(Dup(1)|Dup("s"))):' + body
    print('    Rows:=' + body)
    print('    Print("{Rows.Length}")')
    sys.exit(0)
if kind.startswith('conversion-'):
    _, shape, mode = kind.split('-')
    effects = '<suspends>' if mode=='waiting' else ''
    waiting = 'Sleep(0.0);' if mode=='waiting' else ''
    refined = shape in ('refined','refineddefault')
    print('ca:=class{var K:int=1}\ncb:=class{var K:rational=1}\nDup(X:t where t:type)<computes>:t=X|X')
    if refined:
        print('pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)){C:int=1}')
    if shape=='monomorphic':
        print('Value(X:int)<computes>'+effects+':int=block{'+waiting+'X}')
    elif shape=='default':
        print('Value(?X:t=1 where t:type)<computes>'+effects+':t=block{'+waiting+'X}')
    elif shape=='refineddefault':
        print('Value(P:pair(x,y),?X:t=if(D:=dup[P])then D.C else 4 where x:type,y:type,t:type)<computes>'+effects+':t=block{'+waiting+'X}')
    elif shape in ('generic','refined'):
        print('Value(X:t where t:type)<computes>'+effects+':t=block{'+waiting+'X}')
    clauses=','.join(f'A{i}:=(Dup(ca{{}})|Dup(cb{{}}))' for i in range(count))
    rhs='1' if shape=='literal' else 'Value()' if shape=='default' else 'Value(P)' if shape=='refineddefault' else 'if(D:=dup[P])then Value(D.C) else Value(4)' if shape=='refined' else 'Value(1)'
    statements=[f'set A{i}.K' + ('=' if refined else '+=') + rhs for i in range(count)]
    if mode=='waiting' and shape=='literal':
        statements.append('Sleep(0.0)')
    value='block{'+';'.join(statements+['0'])+'}'
    signature='P:pair(a,b) where a:type,b:type' if refined else ''
    print('Run('+signature+')'+effects+':int=')
    if mode=='first':
        print('    if('+clauses+',Done:='+value+',Done=0)then 1 else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    args='dup(int){A:=1,B:=2}' if refined else ''
    print('Main()'+effects+':void=Print("{Run('+args+')}" )')
    sys.exit(0)
if kind.startswith('setter-'):
    _, shape, mode = kind.split('-')
    print('Dup(X:t where t:type)<computes>:t=X|X')
    nested = shape in ('nested','varying','deep')
    alternatives=[]
    if nested:
        print('leaf:=class{var K:int=1}\nother:=class{var K:int=1}\nmid:=class{C:leaf}')
        for cls in ['ca','cb']:
            ty = 'mid' if shape=='deep' else 'other' if shape=='varying' and cls=='cb' else 'leaf'
            print(cls + ':=class{C:' + ty + '}')
            value = 'mid{C:=leaf{}}' if shape=='deep' else ty+'{}'
            alternatives.append(cls+'{C:='+value+'}')
    else:
        for cls,ty,value in [('ca','[]int','array{1}'),('cb','[]string','array{"s"}')]:
            print(cls + ':=class{var K:' + (ty if shape == 'array' else 'int') + '=' + (value if shape == 'array' else '1') + '}')
            alternatives.append(cls+'{}')
    clauses=','.join(f'A{i}:=(Dup({alternatives[0]})|Dup({alternatives[1]}))' for i in range(count))
    statements=[];terms=[]
    for i in range(count):
        name=f'A{i}'
        if shape == 'alias':
            statements.extend([f'B{i}:={name}',f'C{i}:=B{i}'])
            name=f'C{i}'
        if nested:
            name += '.C.C' if shape=='deep' else '.C'
        statements.append(f'set {name}.K' + ('=' if shape=='simple' else '+=') + ('array{}' if shape=='array' else '(1|2)' if shape=='choice' else '1'))
        terms.append(name+'.K'+('.Length' if shape=='array' else ''))
    if shape == 'choice':
        clauses += ',' + ','.join(statements)
        statements=[]
    value='block{'+';'.join(statements+['+'.join(terms)])+'}'
    effects='<suspends>' if mode=='waiting' else ''
    if mode=='waiting':
        value='block{Sleep(0.0);'+value+'}'
    print(f'Run(){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run()}}")')
    sys.exit(0)
if kind.startswith('resultalias-'):
    _, shape, mode = kind.split('-')
    generic = shape == 'generic'
    waiting = mode == 'waiting'
    effects = '<suspends>' if waiting else ''
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0')
    for root, result in [('ca','ra'),('cb','rb')]:
        print(result+('(t:subtype(comparable))' if generic else '')+':=class<computes>{K:int=1'+(';V:t' if generic else '')+'}')
        if shape == 'field':
            print(root+':=class{R:'+result+'='+result+'{}}')
        else:
            ret = root if shape=='same' else result+('(t)' if generic else '')
            body = 'Self' if shape=='same' else ret+'{'+('V:=V' if generic else '')+'}'
            params = 'Ignored:u where u:type' if generic else ''
            print(root+('(t:subtype(comparable))' if generic else '')+':=class{K:int=1'+(';V:t' if generic else '')+';Me('+params+')<computes>'+effects+':'+ret+'=block{'+('Sleep(0.0);' if waiting else '')+body+'}}')
    selected = 'Dup(P)|Dup(Q)' if generic else 'Dup(ca{})|Dup(cb{})'
    clauses=','.join(f'A{i}:=({selected})' for i in range(count))
    statements=[];terms=[]
    for i in range(count):
        value=f'A{i}.R' if shape=='field' else f'A{i}.Me('+ (f'A{(i+1)%count}' if generic else '')+')'
        statements.extend([f'B{i}:={value}',f'C{i}:=B{i}'])
        terms.append(f'C{i}.K'+(f'+Equal(C{i}.V,X)' if generic else ''))
    if waiting and shape=='field':
        statements.append('Sleep(0.0)')
    value='block{'+';'.join(statements+['+'.join(terms)])+'}'
    signature='P:ca(t),Q:cb(t),X:t where t:subtype(comparable)' if generic else ''
    print(f'Run({signature}){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    args='ca(int){V:=7},cb(int){V:=7},7' if generic else ''
    print(f'Main(){effects}:void=Print("{{Run('+args+')}")')
    sys.exit(0)
if kind.startswith('alias-'):
    _, shape, mode = kind.split('-')
    waiting = mode == 'waiting'
    effects = '<suspends>' if waiting else ''
    print('Dup(X:t where t:type)<computes>:t=X|X')
    for cls in ['ca','cb']:
        params = 'Ignored:u where u:type' if shape == 'generic' else ''
        print(cls + ':=class{K:int=1;M(' + params + ')<computes>' + effects + ':' + cls + '=block{' + ('Sleep(0.0);' if waiting else '') + 'Self}}')
    clauses=[]; aliases=[]
    for i in range(count):
        clauses.append(f'A{i}:=(Dup(ca{{}})|Dup(cb{{}}))')
        declarations=[f'B{i}:=A{i}',f'C{i}:=B{i}']
        if shape == 'clauses':
            clauses.extend(declarations)
        else:
            aliases.extend(declarations)
    terms=[f'C{i}.K+C{i}.M(' + (f'C{(i+1)%count}' if shape == 'generic' else '') + ').K' for i in range(count)]
    value='block{'+';'.join(aliases+['+'.join(terms)])+'}'
    print(f'Run(){effects}:int=')
    if mode=='first':
        print('    if('+','.join(clauses)+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+','.join(clauses)+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run()}}")')
    sys.exit(0)
if kind.startswith('member-'):
    shape, mode = '-'.join(kind.split('-')[1:-1]), kind.split('-')[-1]
    future = shape == 'future'
    result = shape == 'callback-result'
    awaiting = shape in ('awaiting','mixed-awaiting')
    mixed = shape in ('mixed','mixed-awaiting')
    print('Dup(X:t where t:type)<computes>:t=X|X')
    if future:
        for cls in ['ca','cb']:
            print(cls + ':=class{K:int=1;M(Ignored:u where u:type)<computes>:' + cls + '=Self}')
    elif result:
        print('ra:=class<computes>{K:int=1}\nrb:=class<computes>{K:int=1}')
        effects = '<computes>' + ('<suspends>' if mode == 'waiting' else '')
        wait = 'Sleep(0.0);' if mode == 'waiting' else ''
        print('MakeA(X:any)' + effects + ':ra=block{' + wait + 'ra{}}\nMakeB(X:any)' + effects + ':rb=block{' + wait + 'rb{}}')
        print('ca:=class{F:type{_(:any)' + effects + ':ra}=MakeA}\ncb:=class{F:type{_(:any)' + effects + ':rb}=MakeB}')
    else:
        for cls,ty,value,name in [('ca','int','7','Integer'),('cb','string','"s"','String')]:
            waits = awaiting and (not mixed or cls == 'cb')
            effects=('<reads><writes>' if cls=='ca' else '<transacts>') if mixed else '<computes>'
            effects += '<suspends>' if waits else ''
            print(name + '(X:' + ty + ')' + effects + ':int=block{' + ('Sleep(0.0);' if waits else '') + '1}')
            print(cls + ':=class{V:' + ty + '=' + value + ';F:type{_(:' + ty + ')' + effects + ':int}=' + name + '}')
    clauses=','.join(f'A{i}:=(Dup(ca{{}})|Dup(cb{{}}))' for i in range(count))
    terms=[]
    for i in range(count):
        later=f'A{(i+1)%count}'
        terms.append(f'A{i}.M({later}).K' if future else f'A{i}.F({later}).K' if result else f'A{i}.F(A{i}.V)')
    value='+'.join(terms)
    effects='<suspends>' if mode=='waiting' else ''
    print(f'Run(){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run()}}")')
    sys.exit(0)
if kind.startswith('getter-'):
    _, shape, mode = kind.split('-')
    generic = shape == 'generic'
    awaiting = shape == 'awaiting'
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0')
    for cls in ['ca','cb']:
        print(cls + ('(t:subtype(comparable))' if generic else '') + ':=class:')
        print('    K:int=1' + ('\n    V:t' if generic else ''))
        result = cls + ('(t)' if generic else '') if shape in ('chained','generic','awaiting') else 'int'
        value = 'Self' if shape in ('chained','generic','awaiting') else 'K'
        print('    M()<computes>' + ('<suspends>' if awaiting else '') + ':' + result + '=block{' + ('Sleep(0.0);' if awaiting else '') + value + '}')
    params=[];tparams=[];main=[]
    if generic:
        for i in range(count):
            params.extend([f'P{i}:ca(t{i})',f'Q{i}:cb(t{i})',f'V{i}:t{i}'])
            tparams.append(f't{i}:subtype(comparable)')
            typ, value = ('int','7') if i%2==0 else ('string','"s"')
            main.extend([f'ca({typ}){{V:={value}}}',f'cb({typ}){{V:={value}}}',value])
    values = 'map{1=>1})|Dup("s"))' if shape == 'lengths' else 'ca{})|Dup(cb{}))'
    clauses=','.join(f'A{i}:=(Dup(' + (f'P{i})|Dup(Q{i}))' if generic else values) for i in range(count))
    terms=[]
    for i in range(count):
        terms.append(f'Equal(A{i}.V,V{i})+Equal(A{i}.M().V,V{i})' if generic else f'A{i}.Length' if shape=='lengths' else f'A{i}.K+A{i}.M()' if shape=='mixed' else f'A{i}.M().K' if shape in ('chained','awaiting') else f'A{i}.K')
    value='+'.join(terms)
    effects='<suspends>' if mode=='waiting' else ''
    signature=','.join(params)+(' where '+','.join(tparams) if generic else '')
    print(f'Run({signature}){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run('+','.join(main)+')}")')
    sys.exit(0)
if kind.startswith('polymorphic-'):
    _, shape, mode = kind.split('-')
    generic = shape == 'generic'
    awaiting = shape == 'awaiting'
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0')
    for cls in ['ca','cb']:
        print(cls + ('(t:subtype(comparable))' if generic else '') + ':=class<unique>:')
        if generic:
            print('    V:t')
        result = 'tuple(t,u)' if generic else 'u'
        value = '(V,X)' if generic else 'X'
        print('    M(X:u where u:type)<computes>' + ('<suspends>' if awaiting else '') + ':' + result + '=block{' + ('Sleep(0.0);' if awaiting else '') + value + '}')
    params=[];tparams=[];main=[]
    if generic:
        for i in range(count):
            params.extend([f'P{i}:ca(t{i})',f'Q{i}:cb(t{i})',f'V{i}:t{i}'])
            tparams.append(f't{i}:subtype(comparable)')
            typ, value = ('int','7') if i%2==0 else ('string','"s"')
            main.extend([f'ca({typ}){{V:={value}}}',f'cb({typ}){{V:={value}}}',value])
    clauses=','.join(f'A{i}:=(Dup(' + (f'P{i})|Dup(Q{i}))' if generic else 'ca{})|Dup(cb{}))') for i in range(count))
    terms=[]
    for i in range(count):
        later=f'A{(i+1)%count}'
        call=f'A{i}.M({later})'
        if generic:
            terms.append(f'Equal({call}(0),V{i})+Equal({call}(1),{later})')
        elif shape == 'erased':
            terms.append(f'block{{Erased:any={call};Equal(A{i},A{i})}}')
        else:
            terms.append(f'Equal({call},{later})')
    value='+'.join(terms)
    effects='<suspends>' if mode=='waiting' else ''
    signature=','.join(params)+(' where '+','.join(tparams) if generic else '')
    print(f'Run({signature}){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run('+','.join(main)+')}")')
    sys.exit(0)
if kind.startswith('dictionary-'):
    _, shape, mode = kind.split('-') if kind.count('-') == 2 else ('dictionary', '-'.join(kind.split('-')[1:-1]), kind.split('-')[-1])
    generic = shape.startswith('generic')
    arguments = shape.endswith('arguments')
    awaiting = shape.endswith('awaiting')
    correlated = shape == 'correlated'
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0')
    cmp = 'subtype(comparable)' if arguments else 'type'
    if correlated:
        print('base:=class<unique>{Me()<computes>:base=Self}')
        print('ca:=class(base){Me<override>()<computes>:ca=Self}')
        print('cb:=class(base){Me<override>()<computes>:cb=Self}')
    else:
        for cls in ['ca','cb']:
            print(cls + ('(t:'+cmp+')' if generic else '') + ':=class:')
            print('    K:int=1' + ('\n    V:t' if generic else ''))
            margs = 'X:t' if arguments and generic else 'X:int' if arguments else ''
            value = 'if(X=V)then 1 else 0' if arguments and generic else 'K+X' if arguments else 'K'
            print('    M('+margs+')<computes>'+('<suspends>' if awaiting else '')+':int=block{'+('Sleep(0.0);' if awaiting else '')+value+'}')
    params=[];tparams=[];main=[]
    if generic:
        for i in range(count):
            params.extend([f'P{i}:ca(t{i})',f'Q{i}:cb(t{i})'])
            tparams.append(f't{i}:{cmp}')
            typ, value = ('int','7') if i%2==0 else ('string','"s"')
            main.extend([f'ca({typ}){{V:={value}}}',f'cb({typ}){{V:={value}}}'])
            if arguments:
                params.append(f'V{i}:t{i}');main.append(value)
    clauses=','.join(f'A{i}:=(Dup('+ (f'P{i})|Dup(Q{i}))' if generic else 'ca{})|Dup(cb{}))') for i in range(count))
    values=[]
    for i in range(count):
        value=f'Equal(A{i},A{i}.Me())' if correlated else f'A{i}.M('+ (f'V{i}' if arguments and generic else '1' if arguments else '') + ')'
        values.append(value)
    value='+'.join(values)
    effects='<suspends>' if mode=='waiting' else ''
    signature=','.join(params)+(' where '+','.join(tparams) if generic else '')
    print(f'Run({signature}){effects}:int=')
    if mode=='first':
        print('    if('+clauses+',V:='+value+',V>0)then V else -1')
    else:
        print('    Rows:=for('+clauses+'):'+value)
        print('    Rows.Length')
    print(f'Main(){effects}:void=Print("{{Run('+','.join(main)+')}")')
    sys.exit(0)
if kind.startswith('heterogeneous-'):
    _, shape, mode = kind.split('-')
    print('Dup(X:t where t:type)<computes>:t=X|X')
    print('Same(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0')
    print('Default(X:t,?Y:[]t=Concatenate() where t:type)<computes>:int=Y.Length')
    print('box(t:type):=class{V:t;K:int=1}')
    print('base:=class{K:int=1}\nca:=class(base){}\ncb:=class(base){}')
    values = {
        'unused': ('1', '"s"'), 'equal': ('1', '"s"'), 'default': ('1', '"s"'),
        'array': ('array{1}', '"s"'), 'tuple': ('(1,1)', '("s","s")'),
        'box': ('box(int){V:=1}', 'box(string){V:="s"}'),
        'result': ('1', '"s"'), 'fields': ('ca{}', 'cb{}'),
    }
    x, y = values[shape]
    clauses = []
    for i in range(count):
        clauses.append(f'A{i}:=(Dup({x})|Dup({y}))')
        score = '0' if shape in ('unused','result') else f'Same(A{i})' if shape=='equal' else f'Default(A{i})' if shape=='default' else f'A{i}.Length' if shape=='array' else f'if(A{i}(0)=A{i}(1))then 1 else 0' if shape=='tuple' else f'A{i}.K'
        clauses.append(f'S{i}:={score}')
    value = 'A0' if shape=='result' else '+'.join(f'S{i}' for i in range(count))
    effects = '<suspends>' if mode=='waiting' else ''
    print(f'Main(){effects}:void=')
    if mode=='first':
        print('    if('+','.join(clauses)+')then Print("{'+('0' if shape=='result' else value)+'}") else Print("none")')
    else:
        print('    Rows:=for('+','.join(clauses)+'):block{'+('Sleep(0.0);' if mode=='waiting' else '')+value+'}')
        print('    Print("{Rows.Length}")')
    sys.exit(0)
if kind == 'immediate-event-refined':
    print('pair(a:type,b:type) := class { A:a;B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('Log(N:int):void={}')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count))
    print(f'Run({params},E:subscribable_event(int) where {tparams}):int=\n    var Total:int=0\n    for({clauses}):\n        C:=E.Subscribe(Log)\n        E.Signal(A0)\n        set Total+=1\n    Total')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main():void=Print("{{Run({args},subscribable_event(int){{}})}}")')
    sys.exit(0)
if kind == 'immediate-spawn-refined':
    print('pair(a:type,b:type) := class { A:a;B:b }')
    print('dup(t:type) := class(pair(t,t)) { C:int=4 }')
    print('Child(N:int,X:t,?E:[]t=Concatenate() where t:type)<suspends>:void=Sleep(0.0)')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    tparams = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count))
    print(f'Run({params},X:t where {tparams},t:type):int=\n    var Total:int=0\n    for({clauses}):\n        T:=spawn{{Child(A0,X)}}\n        set Total+=1\n    Total')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count))
    print(f'Main()<suspends>:void=\n    Print("{{Run({args},array{{7}})}}")\n    Sleep(1.0)')
    sys.exit(0)
if kind.startswith(('context-block-', 'context-constructor-', 'context-defer-', 'context-field-default-', 'context-param-default-')):
    print('cell:=class{var N:int=0}')
    print('Early(N:int):int=\n    if(N<0):return 0\n    N|N+1')
    print('Lazy(N:int)<computes><decides>:int=\n    N>=0\n    N|Lazy[N-1]')
    first = kind.endswith('first')
    value = 'Lazy[3]' if kind.endswith('lazy-first') else 'Early(0)' if kind.endswith('exclusive') else '(Two(0)|Two(2))'
    clauses = ','.join(f'A{i}:={value}' for i in range(count))
    if first:
        clauses += ',' + ','.join(f'set H.N+=A{i},A{i}=0' for i in range(count))
        expr = f'block{{H:=cell{{}};if({clauses},E:[]t=Concatenate())then H.N+E.Length else -1}}'
    else:
        expr = f'block{{H:=cell{{}};R:=for({clauses}):block{{E:[]t=Concatenate();set H.N+=A0;E.Length}};R.Length+H.N}}'
    if kind.startswith('context-param-default-'):
        print(f'Run(X:t,?N:int={expr} where t:type):int=N\nMain():void=Print("{{Run(7)}}")')
    elif kind.startswith('context-field-default-'):
        print(f'box(t:type):=class{{Data:t;N:int={expr}}}\nRun(X:t where t:type):int=box(t){{Data:=X}}.N\nMain():void=Print("{{Run(7)}}")')
    elif kind.startswith('context-constructor-'):
        print(f'box(t:type):=class{{Data:t;N:int=0}}\nMake<constructor>(X:t where t:type):=box(t):\n    Data:=X\n    N:={expr}\nMain():void=Print("{{Make(7).N}}")')
    elif kind.startswith('context-block-'):
        print(f'box(t:type):=class:\n    Data:t\n    var N:int=0\n    block:set N={expr}\nRun(X:t where t:type):int=box(t){{Data:=X}}.N\nMain():void=Print("{{Run(7)}}")')
    else:
        print(f'Run(X:t where t:type):void=\n    defer:Print("{{{expr}}}")\n    Print("start")\nMain():void=Run(7)')
    sys.exit(0)
if kind.startswith('context-refining-'):
    context, mode = kind.removeprefix('context-refining-').rsplit('-', 1)
    print('pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){C:int=4}')
    print('cell:=class{var N:int=0}')
    types = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    targs = ','.join(f'a{i},b{i}' for i in range(count))
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    names = ','.join(f'P{i}' for i in range(count))
    fields = ';'.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    assignments = ','.join(f'P{i}:=P{i}' for i in range(count))
    clauses = ','.join(f'A{i}:=if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0,A{i}=4' for i in range(count))
    if mode == 'first':
        tail = f'if({clauses},set H.N+=1)then H.N else -1'
    else:
        wait = 'Sleep(0.0);' if mode == 'waiting' else ''
        tail = f'R:=for({clauses}):block{{{wait}E:[]a0=Concatenate();set H.N+=1;E.Length}};R.Length+H.N'
    expr = f'block{{H:=cell{{}};{tail}}}'
    actuals = ','.join('dup(int){}' if i%2==0 else 'dup(string){}' for i in range(count))
    if context == 'parameter':
        print(f'Run({params},?N:int={expr} where {types}):int=N')
        print(f'Use({params} where {types}):int=Run({names})')
    elif context == 'field':
        print('Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}')
        fields = ';'.join(f'Data{i}:pair(a{i},b{i})' for i in range(count))
        assignments = ','.join(f'Data{i}:=P{i}' for i in range(count))
        locals = ';'.join(f'P{i}:pair(a{i},b{i})=Pair(0)' for i in range(count))
        expr = f'block{{{locals};{expr}}}'
        print(f'box({types}):=class{{{fields};N:int={expr}}}')
        print(f'Use({params} where {types}):int=box({targs}){{{assignments}}}.N')
    elif context == 'constructor':
        print(f'box({types}):=class{{{fields};N:int=0}}')
        items = '\n'.join(f'    P{i}:=P{i}' for i in range(count))
        print(f'Make<constructor>({params} where {types}):=box({targs}):\n{items}\n    N:={expr}')
        print(f'Use({params} where {types}):int=Make({names}).N')
    elif context == 'block':
        items = '\n'.join(f'    P{i}:pair(a{i},b{i})' for i in range(count))
        print(f'box({types}):=class:\n{items}\n    var N:int=0\n    block:set N={expr}')
        print(f'Use({params} where {types}):int=box({targs}){{{assignments}}}.N')
    elif context == 'defer':
        print(f'Use({params} where {types}):void=\n    defer:Print("{{{expr}}}")\n    Print("start")')
    elif context == 'branch':
        print(f'Use({params} where {types})<suspends>:void=\n    branch:\n        Print("{{{expr}}}")\n        Sleep(0.1)\n    Sleep(0.2)')
    else:
        result = 'R(0)' if context == 'sync' else 'R'
        print(f'Use({params} where {types})<suspends>:int=\n    R:={context}:\n        block:\n            N:={expr}\n            Sleep(0.1)\n            N\n        block:\n            Sleep(0.2)\n            -1\n    {result}')
    call = f'Use({actuals})'
    body = call if context in ['defer','branch'] else f'Print("{{{call}}}")'
    suspends = '<suspends>' if context in ['sync','race','rush','branch'] else ''
    print(f'Main(){suspends}:void={body}')
    sys.exit(0)
if kind.startswith('first-return-'):
    print('pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)){C:int=4}')
    print('cell:=class{var N:int=0}')
    target = 'Other' if kind.endswith('mutual') else 'Lazy'
    print(f'Lazy(H:cell,N:int)<transacts><decides>:int=\n    N>=0\n    set H.N+=1\n    N|{target}[H,N-1]')
    if kind.endswith('mutual'):
        print('Other(H:cell,N:int)<transacts><decides>:int=\n    N>=0\n    set H.N+=1\n    N|Lazy[H,N-1]')
    independent = kind.endswith('independent')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count)) if independent else 'P:pair(a,b)'
    types = ','.join(f'a{i}:type,b{i}:type' for i in range(count)) if independent else 'a:type,b:type'
    values = [f'if(D{i}:=dup[P{i}])then(D{i}.C|D{i}.C+1)else 0' for i in range(count)] if independent else ['if(D:=dup[P])then(D.C|D.C+1)else 0']*count
    if kind.endswith(('composed','generic','void')): values = ['(Two(0)|Two(2))']*count
    if kind.endswith(('lazy','mutual')): values = ['Lazy[H,3]']*count
    clauses = ','.join(f'A{i}:={value}' for i,value in enumerate(values))
    generic, void = kind.endswith('generic'), kind.endswith('void')
    ret, result = ('[]t','array{}') if generic else ('void','') if void else ('t','X')
    clauses += ',set H.N+=1,set Total+=1,if(Total>0)then return '+result+' else 0'
    final = 'array{X}' if generic else '{}' if void else 'X'
    print(f'Run({params},X:t where {types},t:type)<transacts>:{ret}=\n    H:=cell{{}}\n    var Total:int=0\n    defer:Print("source {{Total}} {{H.N}}")\n    if({clauses}):Print("normal")\n    {final}')
    args = ','.join('dup(int){A:=1,B:=2}' if i%2==0 else 'dup(string){A:="s",B:="t"}' for i in range(count)) if independent else 'dup(int){A:=1,B:=2}'
    call = f'Run({args},7)' + ('.Length' if generic else '')
    print(f'Main():void={call}' if void else f'Main():void=Print("{{{call}}}")')
    sys.exit(0)
if kind in ('context-method-nested', 'context-method-nested-dispatch'):
    print('''box:=class:
    Same(X:t where t:type)<computes>:t=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)''')
    dispatch = kind.endswith('dispatch')
    if dispatch:
        print('''holder:=class:
    Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)''')
    receiver = 'box{}'
    for _ in range(count * 4):
        receiver = f'{"H.Apply" if dispatch else "Apply"}(({receiver}).Same,box{{}})'
    prefix = '    H:=holder{}\n' if dispatch else ''
    print(f'Main():void=\n{prefix}    F:type{{_(:int)<computes>:int}}=({receiver}).Same\n    Print("{{F(7)}}")')
    sys.exit(0)
if kind.startswith('method-variance-'):
    pack = '-pack-' in kind
    sig = 'X:rational,Y:rational' if pack else 'X:rational'
    result = 'Floor(X)+Floor(Y)' if pack else 'Floor(X)'
    print(f'''box(t:type):=class:
    V:t
    Pair({sig})<computes>:tuple(t,int)=(V,{result})''')
    params = ','.join(f'B{i}:box(t{i})' for i in range(count))
    tparams = ','.join(f't{i}:type' for i in range(count))
    fparam = ':tuple(int,int)' if pack else ':int'
    binds = '\n'.join(f'    F{i}:type{{_({fparam})<computes>:tuple(t{i},rational)}}=B{i}.Pair' for i in range(count))
    arg = '(3,4)' if pack else '7'
    clauses = ','.join(f'A{i}:=F{i}({arg})|F{i}({arg})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]t0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]t0=Concatenate()):Floor(A0(1))\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{binds}\n{body}')
    args = ','.join('box(int){V:=7}' if i%2==0 else 'box(string){V:="s"}' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('context-method-'):
    print('''box(h:type):=class:
    V:h
    Id(X:t where t:type)<computes>:t=X''')
    print('Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)')
    params = ','.join(f'B{i}:box(h{i}),X{i}:t{i}' for i in range(count))
    tparams = ','.join(f'h{i}:type,t{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=Twice(B{i}.Id,X{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]h0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]h0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{body}')
    args = ','.join('box(string){V:="tag"},7' if i%2==0 else 'box(int){V:=3},"s"' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('context-value-'):
    print('Id(X:t where t:type)<computes>:t=X')
    print('Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)')
    params = ','.join(f'X{i}:t{i}' for i in range(count))
    tparams = ','.join(f't{i}:type' for i in range(count))
    clauses = ','.join(f'A{i}:=Twice(Id,X{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]t0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]t0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{body}')
    args = ','.join('7' if i%2==0 else '"s"' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
if kind.startswith('method-tuple-'):
    print('''box(t:type):=class:
    V:t
    Id(X:u where u:type)<computes>:u=X''')
    params = ','.join(f'B{i}:box(h{i}),X{i}:a{i},Y{i}:b{i}' for i in range(count))
    tparams = ','.join(f'h{i}:type,a{i}:type,b{i}:type' for i in range(count))
    binds = '\n'.join(f'    F{i}:type{{_(:a{i},:b{i})<computes>:tuple(a{i},b{i})}}=B{i}.Id' for i in range(count))
    clauses = ','.join(f'A{i}:=F{i}(X{i},Y{i})|F{i}(X{i},Y{i})' for i in range(count))
    if kind.endswith('first'):
        body = f'    if({clauses},E:[]h0=Concatenate())then E.Length else -1'
    else:
        body = f'    R:=for({clauses},E:[]h0=Concatenate()):A0\n    R.Length'
    print(f'Run({params} where {tparams})<computes>:int=\n{binds}\n{body}')
    args = ','.join('box(string){V:="tag"},7,"s"' if i%2==0 else 'box(int){V:=3},"v",9' for i in range(count))
    print(f'Main():void=Print("{{Run({args})}}")')
    sys.exit(0)
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
if kind.startswith('waiting-default-'):
    shape, mode = kind.removeprefix('waiting-default-').rsplit('-', 1)
    print('pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){C:int=4}\ncell:=class{var N:int=0}')
    print('Lazy(N:int)<computes><decides>:int=block{N>=0;N|Lazy[N-1]}')
    params = ','.join(f'P{i}:pair(a{i},b{i})' for i in range(count))
    types = ','.join(f'a{i}:type,b{i}:type' for i in range(count))
    names = ','.join(f'P{i}' for i in range(count))
    values = [f'if(D{i}:=dup[P{i}])then ' + (f'Lazy[D{i}.C]' if mode == 'lazy' else f'(D{i}.C|D{i}.C+1)') + ' else 0' for i in range(count)]
    if mode == 'composed': values = ['(Two(0)|Two(2))']*count
    clauses = ','.join(f'A{i}:={v},A{i}=0' if mode == 'composed' else f'A{i}:={v},A{i}=4' for i,v in enumerate(values))
    expr = f'block{{H:=cell{{}};R:=for({clauses}):block{{Sleep(0.0);E:[]a0=Concatenate();set H.N+=1;E.Length}};R.Length+H.N}}'
    header = f'Run({params},?N:int={expr} where {types})<suspends>:int=N'
    if shape == 'method':
        print('box(t:type):=class:\n    X:t\n    ' + header)
        print('B:=box(string){X:="tag"}')
    else: print(header)
    call = ('B.' if shape == 'method' else '') + f'Run({names})'
    print(f'Use({params} where {types})<suspends>:int={call}')
    actual = ','.join('dup(int){}' if i%2==0 else 'dup(string){}' for i in range(count))
    print(f'Main()<suspends>:void=Print("{{Use({actual})}}")')
    sys.exit(0)
if kind.startswith('waiting-') and not kind.startswith('waiting-refined'):
    print('''Early(N:int)<computes>:int =
    if(N<0):return N
    if(N=0):return 0
    N|N+1
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Wait(N:int)<suspends>:int =
    Sleep(0.0)
    N''')
    values = ['(Two(0)|Two(2))'] * count
    if kind == 'waiting-composed-lazy': values = ['(Lazy[1]|Lazy[-1])'] * count
    if kind == 'waiting-exclusive': values = ['Early(1)'] * count
    if kind == 'waiting-exclusive-prefix': values = ['Early(-1)'] * count
    if kind in ('waiting-mixed-arrays', 'waiting-nested-value'):
        values = ['Early(1)' if i%2 else '(Two(0)|Two(2))' for i in range(count)]
    generic = kind == 'waiting-generic-state'
    clauses = []
    for i, value in enumerate(values):
        clauses.append(f'A{i}:={value}')
        if generic: clauses.append(f'set Total+=A{i}')
    print(f'Run({"Value:t where t:type" if generic else ""})<suspends>:void =')
    if generic: print('    var Total:int=0')
    if kind == 'waiting-nested-value': print('    F:type{_(:int)<suspends>:int}=Wait')
    print(f'    R:=for({",".join(clauses)}):')
    if kind == 'waiting-nested-value':
        print('        for(X:=(Two(0)|Two(2)),Y:=Early(1)):F(A0+X+Y)')
    else:
        print('        Sleep(0.0)')
        if generic: print('        set Total+=1')
        if kind == 'waiting-mixed-arrays':
            print('        Empty:[]int=array{}\n        Empty')
        else: print('        ' + ('Value' if generic else '+'.join(f'A{i}' for i in range(count))))
    print('    Print("rows {R.Length}' + (' {Total}' if generic else '') + '")')
    print('Main()<suspends>:void=Run(' + ('"x"' if generic else '') + ')')
    raise SystemExit
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
    print('cell := class<allocates> { var N:int=0 }')
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
    timeout "$limit" "$root/.lake/build/bin/openverse" emit "$tmp/p.verse" -o "$tmp/p.vbc" || {
      rc=$?
      if (( rc == 124 )); then
        echo "test-choice-size: $kind with $count choices did not compile within ${limit} s (CHOICE_SIZE_TIMEOUT)" >&2
      else
        echo "test-choice-size: $kind with $count choices: emit failed (exit $rc)" >&2
      fi
      exit 1
    }
    if [[ $kind == alias-* && $count == 4 ]]; then
      expected=256
      [[ $kind == *-first ]] && expected=8
      printf '%s\n' "$expected" >"$tmp/expected"
      timeout "$limit" "$root/.lake/build/bin/openverse" run "$tmp/p.verse" >"$tmp/lean.out"
      timeout "$limit" "$root/runtime/build/cverse" "$tmp/p.vbc" >"$tmp/c.out"
      diff -u "$tmp/expected" "$tmp/lean.out"
      diff -u "$tmp/expected" "$tmp/c.out"
    fi
    if [[ $kind == setter-* && $kind != setter-choice-* && $count == 4 ]]; then
      expected=256
      if [[ $kind == *-first ]]; then
        expected=8
        [[ $kind == setter-simple-* || $kind == setter-array-* ]] && expected=4
      fi
      printf '%s\n' "$expected" >"$tmp/expected"
      timeout "$limit" "$root/.lake/build/bin/openverse" run "$tmp/p.verse" >"$tmp/lean.out"
      timeout "$limit" "$root/runtime/build/cverse" "$tmp/p.vbc" >"$tmp/c.out"
      diff -u "$tmp/expected" "$tmp/lean.out"
      diff -u "$tmp/expected" "$tmp/c.out"
    fi
    if [[ $kind == resultalias-* && $count == 4 ]]; then
      expected=256
      if [[ $kind == *-first ]]; then
        expected=4
        [[ $kind == resultalias-generic-* ]] && expected=8
      fi
      printf '%s\n' "$expected" >"$tmp/expected"
      timeout "$limit" "$root/.lake/build/bin/openverse" run "$tmp/p.verse" >"$tmp/lean.out"
      timeout "$limit" "$root/runtime/build/cverse" "$tmp/p.vbc" >"$tmp/c.out"
      diff -u "$tmp/expected" "$tmp/lean.out"
      diff -u "$tmp/expected" "$tmp/c.out"
    fi
    if [[ ( $kind == named-* || $kind == conversion-* ) && $count == 4 ]]; then
      expected=256
      if [[ $kind == *-first ]]; then
        expected=1
        [[ $kind == named-* ]] && expected=ok
      fi
      printf '%s\n' "$expected" >"$tmp/expected"
      timeout "$limit" "$root/.lake/build/bin/openverse" run "$tmp/p.verse" >"$tmp/lean.out"
      timeout "$limit" "$root/runtime/build/cverse" "$tmp/p.vbc" >"$tmp/c.out"
      diff -u "$tmp/expected" "$tmp/lean.out"
      diff -u "$tmp/expected" "$tmp/c.out"
    fi
    sizes+=("$(wc -c <"$tmp/p.vbc")")
  done
  if (( sizes[1] > 3 * sizes[0] )); then
    echo "test-choice-size: $kind grew from ${sizes[0]} to ${sizes[1]} bytes" >&2
    exit 1
  fi
  echo "test-choice-size: $kind, 4 choices=${sizes[0]} bytes, 8 choices=${sizes[1]} bytes"
done
