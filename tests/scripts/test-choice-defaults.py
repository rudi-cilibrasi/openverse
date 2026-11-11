#!/usr/bin/env python3
"""Construction fields, modeled in declaration order independently of lowering.

A prefix default commits when the next field opens a generator. A scalar
selected branch shares the earlier generator's filter. Rejected filters roll
back allocations, writes and output; a failed body keeps them and stops all
remaining values. Objects saved from later values share the prefix cell.
"""
from pathlib import Path
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


def main():
    bad = 0
    with tempfile.TemporaryDirectory(prefix='choice-defaults-') as directory:
        tmp = Path(directory)
        for seed in range(FIRST, FIRST + COUNT):
            source, want, status = program(seed)
            path, vbc = tmp / 'p.verse', tmp / 'p.vbc'
            path.write_text(source)
            vbc.unlink(missing_ok=True)
            lean = subprocess.run([str(ROOT / '.lake/build/bin/openverse'), 'run', str(path), '--emit', str(vbc)],
                                  capture_output=True, text=True, timeout=30)
            if (lean.stdout, lean.returncode) != (want, status):
                bad += 1
                (ROOT / f'fuzz-choice-defaults-{seed}.verse').write_text(source)
                (ROOT / f'fuzz-choice-defaults-{seed}.expected').write_text(want + f'exit={status}\n')
                (ROOT / f'fuzz-choice-defaults-{seed}.actual').write_text(lean.stdout + f'exit={lean.returncode}\n' + lean.stderr)
                print(f'MODEL MISMATCH seed {seed}: exit {lean.returncode}; {lean.stderr[:200]}', flush=True)
                continue
            c = subprocess.run([str(ROOT / 'runtime/build/cverse'), str(vbc)],
                               capture_output=True, text=True, timeout=30)
            if (c.stdout, c.stderr, c.returncode) != (lean.stdout, lean.stderr, lean.returncode):
                bad += 1
                (ROOT / f'fuzz-choice-defaults-{seed}.verse').write_text(source)
                print(f'C MISMATCH seed {seed}', flush=True)
    print(f'choice-defaults: {COUNT} model programs from seed {FIRST}, {bad} bad')
    return bool(bad)


if __name__ == '__main__':
    raise SystemExit(main())
