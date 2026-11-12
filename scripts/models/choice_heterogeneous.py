#!/usr/bin/env python3
"""Independent choice-prefix, filter rollback, live-state and cancellation oracle."""
from pathlib import Path
import argparse, json, random
p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=Path)
p.add_argument('--control', action='store_true')
p.add_argument('--methods', action='store_true')
p.add_argument('--generic-methods', action='store_true')
p.add_argument('--members', action='store_true')
p.add_argument('--callable-fields', action='store_true')
p.add_argument('--aliases', action='store_true')
a = p.parse_args()
a.members = a.members or a.aliases
a.generic_methods = (a.generic_methods or a.members) and not a.callable_fields
a.members = a.members and not a.callable_fields
a.methods = a.methods or a.generic_methods or a.callable_fields
r = random.Random(a.seed)
method_arguments = a.methods and r.choice([False, True])
mode = ['first', 'for', 'waiting'][a.seed % 3]
shape = ['primitive', 'array', 'tuple', 'box', 'fields'][a.seed // 3 % 5]
empty = a.seed // 15 % 2 == 0
cancel = mode == 'waiting' and a.seed // 30 % 2 == 0
packed = a.seed // 60 % 2 == 0 or mode == 'first'
n = r.randint(2, 3)
boost = r.randint(1, 4)
bump = r.randint(1, 5)
levels = []
for i in range(n):
    scores = [[1, 1], [1, 1]] if shape == 'primitive' else [[r.randrange(2), r.randrange(2)], [r.randrange(2), r.randrange(2)]] if shape == 'tuple' else [[r.randrange(4), r.randrange(4)], [r.randrange(4), r.randrange(4)]]
    levels.append(dict(scores=scores, tags=[r.randint(1, 4), r.randint(1, 4)], weight=r.randint(1, 3), mod=r.randint(1, 3), want=r.randrange(3)))
for d in levels:
    d['want'] %= d['mod']
h = total = 0
lines = []
elapsed = 0.0
bumped = False

def prefix(i, j):
    global h
    tag = levels[i]['tags'][j]
    h += tag
    lines.append(f'p {tag}')

def filt(i, s, kind):
    global h, total
    d = levels[i]
    if method_arguments:
        h += i + 1
        lines.append(f'arg {i + 1}')
    if a.methods:
        h += (kind + 1) * (s + 1) + (i + 1 if method_arguments else 0)
        lines.append(f'm {chr(97 + kind)} {s}')
    lines.append(f'f {i} {s}')
    h += d['weight'] + s
    total += s + 1
    return (h + s) % d['mod'] == d['want']

def search(i, values):
    global h, total, lines
    d = levels[i]
    saved = (h, total, list(lines))
    for j in range(2):
        h, total, lines = (saved[0], saved[1], list(saved[2]))
        prefix(i, j)
        base = (h, total, list(lines))
        for s in d['scores'][j]:
            h, total, lines = (base[0], base[1], list(base[2]))
            if not filt(i, s, j):
                continue
            if i + 1 < n:
                found = search(i + 1, values + [s])
                if found is not None:
                    return found
            elif not empty:
                return sum(values) + s
    h, total, lines = saved
    return None

def walk(i, values):
    global h, total, lines
    d = levels[i]
    for j in range(2):
        prefix(i, j)
        for s in d['scores'][j]:
            saved = (h, total, len(lines))
            if not filt(i, s, j):
                h, total = saved[:2]
                del lines[saved[2]:]
                continue
            if i + 1 < n:
                yield from walk(i + 1, values + [s])
            elif not empty:
                yield (sum(values) + s)
if mode == 'first':
    found = search(0, [])
    if found is None:
        answer = -1
    else:
        h += boost + found
        total += found
        lines.append(f'body {h} {total}')
        answer = found
else:
    values = []
    interrupted = False
    for score in walk(0, []):
        if mode == 'waiting':
            finish = elapsed + 0.1
            if not bumped and finish >= 0.05:
                h += bump
                bumped = True
            if cancel and finish > 0.250001:
                lines.append(f'body {h} {total}')
                interrupted = True
                break
            elapsed = finish
        h += boost + score
        total += score
        values.append(score)
        lines.append(f'body {h} {total}')
    answer = -1 if interrupted else 10000 * len(values) + 100 * total + (sum(values) if packed else 0)
lines.append(f'source {h} {total}')
if mode == 'waiting':
    lines.append(f'background {h}')
lines.append(f'result {answer} state {h}')
a.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')
print('cell:=class{var N:int=0}\nInts(N:int)<computes>:[]int=for(I:=1..N):I\nbox(t:type):=class{V:t;K:int=0}\nbase:=class{K:int}\nca:=class(base){}\ncb:=class(base){}\nSame(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0\nPrefix(H:cell,X:t,Y:t,Tag:int where t:type)<transacts>:t=\n    Print("p {Tag}")\n    set H.N+=Tag\n    X|Y')
if a.methods:
    for name, generic, kind in [('ma', False, 'a'), ('mb', False, 'b'), ('ga', True, 'a'), ('gb', True, 'b')]:
        print(name + ('(t:type)' if generic else '') + ':=class:')
        print('    H:cell\n    ' + ('var ' if a.members or a.callable_fields else '') + 'K:int' + ('\n    V:t' if generic else ''))
        if a.callable_fields:
            callback_effects = '<reads><writes>' if kind == 'a' else '<transacts>'
            print('    F:type{_(:cell,:int' + (',:int' if method_arguments else '') + ')' + callback_effects + ':int}')
            continue
        method_params = (['Arg:int'] if method_arguments else []) + (['Ignored:u where u:type'] if a.generic_methods else [])
        method = 'Read' if a.members else 'Score'
        result = name + ('(t)' if generic else '') if a.members else 'int'
        print('    ' + method + '(' + ','.join(method_params) + ')<transacts>:' + result + '=')
        print('        Print("m ' + kind + ' {K}")')
        print('        set H.N+=' + ('1' if kind == 'a' else '2') + '*(K+1)' + ('+Arg' if method_arguments else ''))
        print('        Self' if a.members else '        K')
    if a.callable_fields:
        for kind in range(2):
            callback_effects = '<reads><writes>' if kind == 0 else '<transacts>'
            print('Callback' + str(kind) + '(H:cell,K:int' + (',Arg:int' if method_arguments else '') + ')' + callback_effects + ':int=')
            print('    Print("m ' + chr(97 + kind) + ' {K}")')
            print('    set H.N+=' + str(kind + 1) + '*(K+1)' + ('+Arg' if method_arguments else ''))
            print('    K')
    print('Score(H:cell,X:tuple(int,int)' + (',Arg:int' if method_arguments else '') + (',Ignored:u where u:type' if a.generic_methods else '') + ')<transacts>:int=')
    print('    if(X(1)=0)then Print("m a {X(0)}") else Print("m b {X(0)}")')
    print('    set H.N+=(X(1)+1)*(X(0)+1)' + ('+Arg' if method_arguments else '') + '\n    X(0)')
    print('Argument(H:cell,N:int)<transacts>:int=block{Print("arg {N}");set H.N+=N;N}')
clauses = []

def payload(s, j):
    if a.methods:
        if a.control:
            return f'({s},{j})'
        generic = shape not in ('primitive', 'fields')
        name = ('ga' if j == 0 else 'gb') if generic else ('ma' if j == 0 else 'mb')
        return name + ('(t)' if generic else '') + '{H:=H,K:=' + str(s) + (',V:=X' if generic else '') + (',F:=Callback' + str(j) if a.callable_fields else '') + '}'
    if a.control:
        return str(s)
    if shape == 'primitive':
        return str(r.randrange(7)) if j == 0 else json.dumps(r.choice(['a', 'xy', '']))
    if shape == 'array':
        return f'Ints({s})' if j == 0 else json.dumps('x' * s)
    if shape == 'fields':
        return f'{chr(99) + chr(97 + j)}{{K:={s}}}'
    if shape == 'tuple':
        return '(7,' + ('7' if s else '8') + ')' if j == 0 else '("x",' + ('"x"' if s else '"y"') + ')'
    return f"box({('int' if j == 0 else 'string')}){{V:={('7' if j == 0 else chr(34) + 'x' + chr(34))},K:={s}}}"
for i, d in enumerate(levels):
    producers = []
    for j in range(2):
        x, y = [payload(s, j) for s in d['scores'][j]]
        producers.append(f"Prefix(H,{x},{y},{d['tags'][j]})")
    score = f'A{i}' if a.control else f'Same(A{i})' if shape == 'primitive' else f'A{i}.Length' if shape == 'array' else f'if(A{i}(0)=A{i}(1))then 1 else 0' if shape == 'tuple' else f'A{i}.K'
    if a.methods:
        extra = ','.join(([f'Argument(H,{i+1})'] if method_arguments else []) + (['X'] if a.generic_methods else []))
        score = f'Score(H,A{i}' + (',' + extra if extra else '') + ')' if a.control else f'A{i}.F(A{i}.H,A{i}.K' + (',' + extra if extra else '') + ')' if a.callable_fields else f'A{i}.' + ('Read' if a.members else 'Score') + f'({extra})' + ('.K' if a.members else '')
    clauses.append(f"A{i}:=({'|'.join(producers)})")
    if a.aliases:
        clauses.extend([f'Alias{i}:=A{i}', f'B{i}:=Alias{i}'])
        score = score.replace(f'A{i}', f'B{i}')
    clauses.extend([f'S{i}:={score}', f'Print("f {i} {{S{i}}}")', f"set H.N+={d['weight']}+S{i}", f'set Total+=S{i}+1', f"Mod[H.N+S{i},{d['mod']}]={d['want']}"])
clauses.append('Z:=Items[0]' if mode == 'first' else 'Z:Items')
score = '+'.join((f'S{i}' for i in range(n)))
names = ('S0', f'S{n - 1}') if shape == 'fields' else ('A0', f'A{n - 1}')
if a.aliases:
    names = tuple(name.replace('A', 'B') for name in names)
packet = f'({names[0]},{names[1]},{score})' if packed else names[0]
body = f'set H.N+={boost}+{score};set Total+={score};Print("body {{H.N}} {{Total}}");{packet}'
effects = '<suspends><transacts>' if mode == 'waiting' else '<transacts>'
print('Use(H:cell'+(',X:t where t:type' if a.methods else '')+f'){effects}:int=\n    var Total:int=0\n    defer:Print("source {{H.N}} {{Total}}")')
if mode == 'waiting':
    print(f'    branch:\n        defer:Print("background {{H.N}}")\n        Sleep(0.05)\n        set H.N+={bump}\n        Sleep(100.0)')
print('    Items:[]int=array{' + ('' if empty else '0') + '}')
if mode == 'first':
    print('    if(' + ','.join(clauses) + ',Out:=block{' + body + '})then Out(2) else -1')
else:
    body = 'defer:Print("body {H.N} {Total}");' + ('Sleep(0.1);' if mode == 'waiting' else '') + f'set H.N+={boost}+{score};set Total+={score};{packet}'
    print('    Rows:=for(' + ','.join(clauses) + '):block{' + body + '}')
    print('    var Sum:int=0')
    if packed:
        print('    for(Row:Rows):set Sum+=Row(2)')
    print('    10000*Rows.Length+100*Total+Sum')
print('Main()' + ('<suspends>' if mode == 'waiting' else '') + ':void=\n    H:=cell{}')
if cancel:
    print('    R:=race:\n        Use(H'+(',array{7}' if a.methods else '')+')\n        block{Sleep(0.25);-1}')
else:
    print('    R:=Use(H'+(',array{7}' if a.methods else '')+')')
print('    Print("result {R} state {H.N}")')
