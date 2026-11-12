#!/usr/bin/env python3
"""Construction fields, modeled in declaration order independently of lowering.

A prefix default commits when the next field opens a generator. A scalar
selected branch shares the earlier generator's filter. Rejected filters roll
back allocations, writes and output; a failed body keeps them and stops all
remaining values. Objects saved from later values share the prefix cell.
An independent pure tree model covers eager recursive constructions too.
Direct projections exercise field types without an enclosing typed binding.
"""
from pathlib import Path
import itertools
import random
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
COUNT = int(sys.argv[1]) if len(sys.argv) > 1 else 60
FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 1


def program(seed):
    r = random.Random(seed)
    ty = r.choice(['int', 'string'])
    xs = [1, 2] if ty == 'int' else ['a', 'b']
    lit = lambda x: str(x) if ty == 'int' else '"' + x + '"'
    composed_x, trace_x = r.choice([False, True]), r.choice([False, True])
    if composed_x:
        xexpr = f'(Pick({lit(xs[0])}) | Pick({lit(xs[1])}))'
        xs = [x for x in xs for _ in (0, 1)]
    else:
        wrap = (lambda x: f'TraceX({lit(x)})') if trace_x else lit
        xexpr = ' | '.join(wrap(x) for x in xs)
    kind = r.choice(['plain', 'composed', 'branch-choice', 'branch-scalar', 'empty'])
    ys, generated = {
        'plain': ([0, 1, 2], True),
        'composed': ([0, 1, 2, 3], True),
        'branch-choice': ([0, 1], True),
        'branch-scalar': ([2], False),
        'empty': ([], True),
    }[kind]
    yexpr = {
        'plain': 'TraceY(0) | TraceY(1) | TraceY(2)',
        'composed': '(Two(0) | Two(2))',
        'branch-choice': 'if (true?) then (TraceY(0) | TraceY(1)) else TraceY(2)',
        'branch-scalar': 'if (false?) then (TraceY(0) | TraceY(1)) else TraceY(2)',
        'empty': 'None[] | None[]',
    }[kind]
    threshold, stop = r.randint(-1, 4), r.randint(0, 4)
    mode = r.choice(['for', 'first', 'fail'])
    generic, inherited = r.choice([False, True]), r.choice([False, True])
    param = 't' if generic else ty
    declaration = 'base(t:type)' if generic else 'base'
    pack = f'pack(t:type) := class(base(t)) {{}}' if generic else 'pack := class(base) {}'
    cty = f'pack({ty})' if generic else 'pack'
    context = r.choice(['explicit', 'binding', 'argument'])
    ctor = cty if context == 'explicit' else 'pack'
    value = f'{ctor}{{Y := {yexpr}, X := {xexpr}}}'
    if context == 'argument':
        value = f'Wrap({value})'
    binding = f'P:{cty} = {value}' if context == 'binding' else f'P := {value}'
    classes = f'''{declaration} := class:
    E:[]{param} = Concatenate()
    X:{param}
    D:cell = MakeCell()
    Y:int
    T:int = Tail()
    block:
        set D.N += 1
        Print("block {{Y}} cell {{D.N}}")
'''
    if inherited:
        classes += pack + '\n'
    else:
        classes = classes.replace(declaration, 'pack(t:type)' if generic else 'pack', 1)
    source = f'''# constructor/default model seed {seed}
cell := class:
    var N:int = 0
MakeCell()<transacts>:cell =
    Print("new cell")
    cell{{}}
Tail()<transacts>:int =
    Print("tail")
    9
TraceX(V:{ty})<transacts>:{ty} =
    Print("x {{V}}")
    V
TraceY(V:int)<transacts>:int =
    Print("y {{V}}")
    V
Two(V:int):int = V | V + 1
Pick(V:t where t:type):t = V | V
None()<decides>:int =
    false?
    0
Fail()<decides>:int =
    Print("fail")
    false?
    0
{classes}
Wrap(P:{cty}):{cty} = P
'''
    if mode == 'first':
        source += f'''Main():void =
    if ({binding}, P.Y >= {threshold}):
        Print("first {{P.X}} {{P.Y}} cell {{P.D.N}} empty {{P.E.Length}}")
    else:
        Print("none")
'''
    else:
        specs = '<decides>' if mode == 'fail' else ''
        failed = f'\n        if (P.Y = {stop}) then Fail[] else 0' if mode == 'fail' else ''
        source += f'''Main(){specs}:void =
    Ps := for ({binding}, P.Y >= {threshold}):
        Print("got {{P.X}} {{P.Y}} cell {{P.D.N}} empty {{P.E.Length}}"){failed}
        P
    for (P : Ps):
        Print("saved {{P.X}} {{P.Y}} cell {{P.D.N}}")
    Print("length {{Ps.Length}}")
'''

    out, saved, code = [], [], 0
    found = False
    for x in xs:
        before_x = len(out)
        if trace_x and not composed_x:
            out.append(f'x {x}')
        out.append('new cell')
        cell = {'n': 0}
        for y in ys:
            before_y, old_n = len(out), cell['n']
            if kind != 'composed':
                out.append(f'y {y}')
            out.append('tail')
            cell['n'] += 1
            out.append(f'block {y} cell {cell["n"]}')
            if y < threshold:
                cell['n'] = old_n
                del out[before_y if generated else before_x:]
                continue
            if mode == 'first':
                out.append(f'first {x} {y} cell {cell["n"]} empty 0')
                found = True
                break
            out.append(f'got {x} {y} cell {cell["n"]} empty 0')
            if mode == 'fail' and y == stop:
                out.append('fail')
                code = 1
                break
            saved.append((x, y, cell))
        if found or code:
            break
        if mode == 'first':
            del out[before_x:]
    if mode == 'first' and not found:
        out.append('none')
    elif mode != 'first' and not code:
        out.extend(f'saved {x} {y} cell {cell["n"]}' for x, y, cell in saved)
        out.append(f'length {len(saved)}')
    return source, ''.join(line + '\n' for line in out), code


def eager_program(seed):
    """Enumerate pure recursive trees and field products in declaration order.

    This models the source values directly, without an array/generator
    lowering. Eager producers cannot allocate mutable objects or print.
    Their consumers can reject filters, take one value, or fail in the body.
    """
    r = random.Random(seed * 1000003 + 28311)
    ty, value = r.choice([('int', '7'), ('string', '"s"')])
    shown = '7' if ty == 'int' else 's'
    start, step, default = r.randint(1, 3), r.randint(2, 3), r.randint(3, 9)
    order = ['V', 'K', 'J', 'D', 'E', 'T']
    r.shuffle(order)
    fields = {
        'V': 'V:t', 'K': 'K:int', 'J': 'J:int',
        'D': 'D:int = block{ N := Default(); N }',
        'E': 'E:[]t = block{ Empty:[]t=Concatenate(); Empty }',
        'T': 'T:int = Default()+1',
    }
    kind = r.choice(['plain', 'composed', 'branch', 'failure'])
    kexpr = {
        'plain': 'N*10 | N*10+1',
        'composed': 'Pick(N*10) | Pick(N*10+2)',
        'branch': 'if (Mod[N,2]=0) then (N*10 | N*10+1) else N*10+2',
        'failure': 'None[] | N*10 | None[] | N*10+1',
    }[kind]
    implicit = r.choice([True, False])
    inherited = r.choice([True, False])
    name = 'base' if inherited else 'pack'
    declaration = f'{name}(t:type) := class<computes>:\n' + ''.join('    ' + fields[f] + '\n' for f in order)
    if inherited:
        declaration += 'pack(u:type) := class<computes>(base(u)) {}\n'
    ctor = 'pack' if implicit else 'pack(t)'
    index = 'index{V:=N|N+1}'
    if r.choice([True, False]):
        index = f'outer{{Inner:={index}}}.Inner'
    edge = f'X,{index}.V-Step'
    if r.choice([True, False]):
        edge += ',?Step:=Step'
    source = f'''# eager constructor model seed {seed}
Default()<computes>:int = {default}
None()<computes><decides>:int =
    false?
    0
Pick(N:int)<computes>:int = N | N+1
index := struct<computes> {{ D:int=Default(); V:int }}
outer := struct<computes> {{ D:int=Default(); Inner:index }}
{declaration}
R(X:t,N:int,?Step:int={step} where t:type)<computes><decides>:pack(t) =
    if (N>0) then ({ctor}{{J:=0|1,K:={kexpr},V:=X|X}} | R[{edge}]) else {ctor}{{J:=0,K:=0,V:=X}}
Fail()<decides>:int =
    Print("fail")
    false?
    0
'''
    threshold, stop = r.randint(0, 3), r.randint(0, 2)
    mode = r.choice(['for', 'first', 'fail'])
    binding = f'P:=R[{value},{start}]'
    predicate = f'Mod[P.K+P.J,3]>={threshold}'
    line = '"value {P.V} {P.K} {P.J} {P.D} {P.E.Length} {P.T}"'
    if mode == 'first':
        source += f'''Main():void =
    if ({binding},{predicate}) then Print({line}) else Print("none")
'''
    else:
        specs = '<decides>' if mode == 'fail' else ''
        failure = f'\n        if (Mod[P.K,3]={stop}) then Fail[] else 0' if mode == 'fail' else ''
        source += f'''Main(){specs}:void =
    Ps := for ({binding},{predicate}):
        Print({line}){failure}
        P
    Print("length {{Ps.Length}}")
'''

    def values(n):
        if n <= 0:
            return [(0, 0)]
        ks = {
            'plain': [n*10, n*10+1],
            'composed': list(range(n*10, n*10+4)),
            'branch': [n*10, n*10+1] if n % 2 == 0 else [n*10+2],
            'failure': [n*10, n*10+1],
        }[kind]
        choices = {'V': [shown, shown], 'K': ks, 'J': [0, 1]}
        # Non-choice defaults have one value at their declaration position.
        products = itertools.product(*(choices.get(f, [None]) for f in order))
        result = []
        for product in products:
            record = dict(zip(order, product))
            result.append((record['K'], record['J']))
        for argument in [n, n+1]:
            result.extend(values(argument-step))
        return result

    out, count, status = [], 0, 0
    for k, j in values(start):
        if (k+j) % 3 < threshold:
            continue
        out.append(f'value {shown} {k} {j} {default} 0 {default+1}')
        count += 1
        if mode == 'first':
            break
        if mode == 'fail' and k % 3 == stop:
            out.append('fail')
            status = 1
            break
    if mode == 'first' and count == 0:
        out.append('none')
    elif mode != 'first' and status == 0:
        out.append(f'length {count}')
    return source, ''.join(line + '\n' for line in out), status


def projection_program(seed):
    """Model struct values and producer results without Core type inference."""
    r = random.Random(seed * 1000033 + 445)
    x = r.choice(['7', '"s"', 'array{1,2}', 'option{7}', '(7,"s")'])
    y = r.choice(['2', '"key"', "(2,'k')"])
    n, depth, default = r.randint(2, 6), r.randint(1, 4), r.randint(10, 20)
    fields = ['E:[]a=Concatenate()', 'O:?a=false', 'M:[b]a=map{}',
              'T:tuple(?a,[]b)=(false,Concatenate())', 'W:leaf(a)=leaf{}',
              'V:a', 'K:b', f'N:int={default}+0']
    r.shuffle(fields)
    suffix = r.choice(['N', 'E.Length', 'M.Length', 'T(1).Length', 'W.E.Length'])
    omitted = r.choice([True, False])
    scalar_fields = 'V:=X,K:=Y' + ('' if omitted else ',N:=N')
    scalar = (default if omitted else n) if suffix == 'N' else 0
    lower, cut = r.randint(n, n+2), r.randint(0, depth+1)
    fail = r.choice([True, False])
    stop = r.randint(0, depth+2)
    failure = f'\n        if(V={stop})then Fail[] else 0' if fail else ''
    specs = '<decides>' if fail else ''
    source = f'''# struct projection model seed {seed}
leaf(t:type) := struct<computes> {{ E:[]t=Concatenate() }}
pack(a:type,b:subtype(comparable)) := struct<computes>:
''' + ''.join('    ' + field + '\n' for field in fields) + f'''
One(X:a,Y:b,N:int where a:type,b:subtype(comparable))<computes>:int = pack(a,b){{{scalar_fields}}}.{suffix}
Swap(X:b,Y:a,N:int where a:subtype(comparable),b:type)<computes>:int = One(X,Y,N)
Many(X:a,Y:b,N:int where a:type,b:subtype(comparable))<computes>:int = pack(a,b){{V:=X,N:=N|N+1,K:=Y}}.N
Tree(X:a,Y:b,N:int where a:type,b:subtype(comparable))<computes>:int =
    if(N>0)then (pack(a,b){{K:=Y,N:=N|N+1,V:=X}}.N | Tree(X,Y,N-1)) else pack(a,b){{K:=Y,N:=0,V:=X}}.N
Lazy(X:a,Y:b,N:int where a:type,b:subtype(comparable))<transacts><decides>:int =
    N>0
    Print("visit {{N}}")
    pack(a,b){{N:=N,V:=X,K:=Y}}.N | Lazy[X,Y,N-1]
Fail()<decides>:int =
    Print("fail")
    false?
    0
Main(){specs}:void =
    Print("one {{Swap({x},{y},{n})}}")
    for(V:=Many({x},{y},{n}), V>={lower}): Print("many {{V}}")
    for(V:=Tree({x},{y},{depth})):
        Print("tree {{V}}"){failure}
    if(V:=Lazy[{x},{y},{depth}], V<{cut})then Print("first {{V}}")else Print("none")
'''
    out = [f'one {scalar}']
    out.extend(f'many {v}' for v in [n, n+1] if v >= lower)
    tree = [v for level in range(depth, 0, -1) for v in [level, level+1]] + [0]
    for v in tree:
        out.append(f'tree {v}')
        if fail and v == stop:
            out.append('fail')
            return source, ''.join(line + '\n' for line in out), 1
    chosen = next((v for v in range(depth, 0, -1) if v < cut), None)
    if chosen is None:
        out.append('none')
    else:
        out.extend(f'visit {v}' for v in range(depth, chosen-1, -1))
        out.append(f'first {chosen}')
    return source, ''.join(line + '\n' for line in out), 0


def main():
    bad = 0
    with tempfile.TemporaryDirectory(prefix='choice-defaults-') as directory:
        tmp = Path(directory)
        cases = ((seed, variant, model) for seed in range(FIRST, FIRST + COUNT)
                 for variant, model in [('defaults', program), ('eager', eager_program),
                                        ('projection', projection_program)])
        for seed, variant, model in cases:
            source, want, status = model(seed)
            artifact = ROOT / f'fuzz-choice-{variant}-{seed}'
            path, vbc = tmp / 'p.verse', tmp / 'p.vbc'
            path.write_text(source)
            vbc.unlink(missing_ok=True)
            lean = subprocess.run([str(ROOT / '.lake/build/bin/openverse'), 'run', str(path), '--emit', str(vbc)],
                                  capture_output=True, text=True, timeout=30)
            if (lean.stdout, lean.returncode) != (want, status):
                bad += 1
                artifact.with_suffix('.verse').write_text(source)
                artifact.with_suffix('.expected').write_text(want + f'exit={status}\n')
                artifact.with_suffix('.actual').write_text(lean.stdout + f'exit={lean.returncode}\n' + lean.stderr)
                print(f'MODEL MISMATCH {variant} seed {seed}: exit {lean.returncode}; {lean.stderr[:200]}', flush=True)
                continue
            c = subprocess.run([str(ROOT / 'runtime/build/cverse'), str(vbc)],
                               capture_output=True, text=True, timeout=30)
            if (c.stdout, c.stderr, c.returncode) != (lean.stdout, lean.stderr, lean.returncode):
                bad += 1
                artifact.with_suffix('.verse').write_text(source)
                print(f'C MISMATCH {variant} seed {seed}', flush=True)
    print(f'choice-defaults: {COUNT} default, {COUNT} eager and {COUNT} projection model programs from seed {FIRST}, {bad} bad')
    return bool(bad)


if __name__ == '__main__':
    raise SystemExit(main())
