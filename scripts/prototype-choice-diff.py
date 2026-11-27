#!/usr/bin/env python3
"""Differential test of choice: openverse against the Verse team's prototype (augustss/verse-semantics).
Random programs in the fragment both accept; openverse's result becomes the expected value of a
`testeq` case that the prototype's tester checks (it compares the `all` of both sides, so order and
repetition count).
See docs/research/prototype-choice-conformance.md.
usage: prototype-choice-diff.py OPENVERSE TESTER SEED COUNT [DEPTH]
  OPENVERSE  the openverse binary (.lake/build/bin/openverse)
  TESTER     the prototype's tester (cabal list-bin exe:tester in a verse-semantics checkout)"""
import random, subprocess, sys, os, re, tempfile, concurrent.futures as cf
CMP = ['<', '<=', '>', '>=', '<>', '=']

class G:
    def __init__(s, rnd, depth): s.r, s.depth, s.fns, s.arrs = rnd, depth, [], []
    def leaf(s, vars):
        if vars and s.r.random() < 0.5:
            v = s.r.choice(vars); return (v, v.upper())
        n = s.r.randint(0, 9); return (str(n), str(n))
    def expr(s, d, vars):
        r = s.r
        if d <= 0 or r.random() < 0.2: return s.leaf(vars)
        kinds = ['add', 'add', 'mul', 'sub', 'choice', 'choice', 'choice', 'cmp', 'if', 'if2', 'one', 'tup']
        if s.fns: kinds += ['call', 'call', 'call']
        if s.arrs: kinds += ['idx', 'len']
        k = r.choice(kinds)
        a = s.expr(d - 1, vars); b = s.expr(d - 1, vars)
        if k in ('add', 'mul', 'sub'):
            op = {'add': '+', 'mul': '*', 'sub': '-'}[k]
            return (f'({a[0]}{op}{b[0]})', f'({a[1]} {op} {b[1]})')
        if k == 'choice': return (f'({a[0]}|{b[0]})', f'({a[1]} | {b[1]})')
        if k == 'cmp':
            op = r.choice(CMP); return (f'({a[0]}{op}{b[0]})', f'({a[1]} {op} {b[1]})')
        if k == 'one': return (f'one{{{a[0]}}}', f'first{{{a[1]}}}')
        if k == 'call':
            f, n = r.choice(s.fns)
            if n == 1: return (f'{f}[{a[0]}]', f'{f.upper()}[{a[1]}]')
            return (f'{f}[{a[0]},{b[0]}]', f'{f.upper()}[{a[1]}, {b[1]}]')
        if k == 'idx':
            x = r.choice(s.arrs); return (f'{x}[{a[0]}]', f'{x.upper()}[{a[1]}]')
        if k == 'len':
            x = r.choice(s.arrs); return (f'Length[{x}]', f'{x.upper()}.Length')
        if k == 'tup':
            i = r.randint(0, 1); return (f'({a[0]},{b[0]})[{i}]', f'({a[1]}, {b[1]})({i})')
        op = r.choice(['<', '>', '=', '<>'])
        if k == 'if':
            c = s.expr(d - 1, vars); e = s.expr(d - 1, vars)
            return (f'if({a[0]}{op}{b[0]}){{{c[0]}}}else{{{e[0]}}}',
                    f'(if ({a[1]} {op} {b[1]}) then {c[1]} else {e[1]})')
        # if2: a condition that binds a name from a choice, then tests it
        nm = 'q' + str(len(vars)); k2 = s.leaf(vars)
        c = s.expr(d - 1, vars + [nm]); e = s.expr(d - 1, vars)
        return (f'if({nm}:={a[0]}; {nm}{op}{k2[0]}){{{c[0]}}}else{{{e[0]}}}',
                f'(if ({nm.upper()} := {a[1]}, {nm.upper()} {op} {k2[1]}) then {c[1]} else {e[1]})')
    def case(s):
        r = s.r; s.fns, s.arrs = [], []; odefs = []; vdefs = []
        for name in ['f', 'g'][:r.choice([0, 0, 1, 1, 2])]:
            t = r.random()
            if t < 0.25:        # two parameters
                b = s.expr(s.depth - 1, ['a', 'b'])     # may call the functions defined before it
                odefs.append(f'{name}(a:int,b:int)<closed>:int := {b[0]}')
                vdefs.append(f'{name.upper()}(A:int, B:int)<computes><decides>:int = {b[1]}')
                s.fns.append((name, 2))
            elif t < 0.5:       # recursive: counts up to a bound, a choice at every level
                k = r.randint(0, 3); base = s.expr(s.depth - 2, ['a']); step = s.expr(s.depth - 2, ['a'])
                rec = (f'{name}[a+1]', f'{name.upper()}[A + 1]')
                x, y = (rec, step) if r.random() < 0.5 else (step, rec)
                odefs.append(f'{name}(a:int)<closed>:int := if(a>{k}){{{base[0]}}}else{{({x[0]}|{y[0]})}}')
                vdefs.append(f'{name.upper()}(A:int)<computes><decides>:int = '
                             f'(if (A > {k}) then {base[1]} else ({x[1]} | {y[1]}))')
                s.fns.append((name, 1))
            else:
                b = s.expr(s.depth - 1, ['a'])
                odefs.append(f'{name}(a:int)<closed>:int := {b[0]}')
                vdefs.append(f'{name.upper()}(A:int)<computes><decides>:int = {b[1]}')
                s.fns.append((name, 1))
        n = r.randint(0, 3); vars = []; o = []; v = []
        for i in range(n):
            name = 'xyzw'[i]; t = r.random()
            if t < 0.2:      # a filter: a comparison, or its negation, so that it can fail
                a = s.expr(s.depth - 2, vars); b = s.expr(s.depth - 2, vars); op = r.choice(CMP)
                if r.random() < 0.3: o.append(f'not({a[0]}{op}{b[0]})'); v.append(f'not ({a[1]} {op} {b[1]})')
                else: o.append(f'({a[0]}{op}{b[0]})'); v.append(f'({a[1]} {op} {b[1]})')
            elif t < 0.3:    # an array built by an inner for, with one clause or two and a filter
                a = s.expr(s.depth - 1, vars); nm = 'i' + name
                if r.random() < 0.4:
                    n2 = 'j' + name; a2 = s.expr(s.depth - 2, vars + [nm]); op = r.choice(CMP)
                    k2 = s.leaf(vars + [nm]); b = s.expr(s.depth - 2, vars + [nm, n2])
                    o.append(f'{name}:=for({nm}:={a[0]}; {n2}:={a2[0]}; {n2}{op}{k2[0]}){{{b[0]}}}')
                    v.append(f'{name.upper()} := for (E{name.upper()} : array{{0}}, {nm.upper()} := {a[1]}, '
                             f'{n2.upper()} := {a2[1]}, {n2.upper()} {op} {k2[1]}) {{ {b[1]} }}')
                else:
                    b = s.expr(s.depth - 2, vars + [nm])
                    o.append(f'{name}:=for({nm}:={a[0]}){{{b[0]}}}')
                    v.append(f'{name.upper()} := for (E{name.upper()} : array{{0}}, {nm.upper()} := {a[1]}) {{ {b[1]} }}')
                s.arrs.append(name)
            elif t < 0.4:    # an array literal, its elements' choices the array's
                es = [s.expr(s.depth - 2, vars) for _ in range(r.randint(1, 3))]
                o.append(f'{name}:=array{{{",".join(e[0] for e in es)}}}')
                v.append(f'{name.upper()} := array{{{", ".join(e[1] for e in es)}}}')
                s.arrs.append(name)
            elif t < 0.45 and s.arrs:   # two arrays joined
                x, y = r.choice(s.arrs), r.choice(s.arrs)
                o.append(f'{name}:=({x}+{y})'); v.append(f'{name.upper()} := ({x.upper()} + {y.upper()})')
                s.arrs.append(name)
            elif t < 0.55 and s.arrs:   # a generator over an array's elements
                x = r.choice(s.arrs)
                o.append(f'{name}:{x}'); v.append(f'{name.upper()} : {x.upper()}'); vars.append(name)
            else:
                e = s.expr(s.depth - 1, vars)
                o.append(f'{name}:={e[0]}'); v.append(f'{name.upper()} := {e[1]}'); vars.append(name)
        if r.random() < 0.25:   # the values are arrays: a for, whose body may have several values
            a = s.expr(s.depth - 1, vars); b = s.expr(s.depth - 1, vars + ['k'])
            o.append(f'for(k:={a[0]}){{{b[0]}}}')
            v.append(f'R := for (EK : array{{0}}, K := {a[1]}) {{ {b[1]} }}')
            return ('; '.join(odefs + ['all{' + '; '.join(o) + '}']),
                    '\n'.join(vdefs), 'for (D : array{0}, ' + ', '.join(v) + ') { "<{Show(R)}>" }', True)
        e = s.expr(s.depth, vars)
        o.append(e[0]); v.append(f'R := {e[1]}')
        return ('; '.join(odefs + ['all{' + '; '.join(o) + '}']),
                '\n'.join(vdefs), 'for (D : array{0}, ' + ', '.join(v) + ') { R }', False)

def run_ov(binp, defs, body, arrays, d, n):
    shown = 'Join(' + body + ', "")' if arrays else 'Show(' + body + ')'
    src = ('Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")\n' + defs +
           '\nMain():void =\n    Print("[{' + shown + '}]")\n')
    f = os.path.join(d, f'p{n}.verse'); open(f, 'w').write(src)
    try: p = subprocess.run([binp, 'run', f], capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired: return 'TIMEOUT'
    out = (p.stdout + p.stderr).strip()
    if re.fullmatch(r'\[[-\d,<>]*\]', out): return out
    return 'REFUSED: ' + re.sub(r'^\S+\.verse:\d+:\d+: ', '', out.split('\n')[0])[:150]

def main():
    if len(sys.argv) < 5: sys.exit(__doc__)
    binp, tester, seed, count = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    depth = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    g = G(random.Random(seed), depth)
    cases = [g.case() for _ in range(count)]
    with tempfile.TemporaryDirectory() as d:
        with cf.ThreadPoolExecutor(12) as ex:
            ovs = list(ex.map(lambda ic: run_ov(binp, ic[1][1], ic[1][2], ic[1][3], d, ic[0]), enumerate(cases)))
        lines = []
        for i, (c, rv) in enumerate(zip(cases, ovs)):
            if rv.startswith('['):
                neg = lambda x: f'(0-{x[1:]})' if x.startswith('-') else x
                arr = lambda t: 'array{' + ','.join(neg(x) for x in t.split(',') if x) + '}'
                exp = ('array{' + ','.join(arr(t) for t in re.findall(r'<([-\d,]*)>', rv)) + '}'
                       if c[3] else arr(rv[1:-1]))
                lines.append(f'testeq("c{i}",pass){{ {c[0]} }} {{ {exp} }}')
        # the prototype in small batches side by side: one large case then costs its batch's time only
        def run(name, batch, limit):
            tf = os.path.join(d, f't{name}.versetest')
            open(tf, 'w').write('\n'.join(batch) + '\n')
            try:
                return subprocess.run([tester, tf, '--assume-verified', '-m', '100000'],
                                      capture_output=True, text=True, timeout=limit).stdout
            except subprocess.TimeoutExpired:
                return None
        def oracle(k):
            batch = lines[k:k + 10]
            out = run(k, batch, 240)
            if out is not None: return out
            # (a batch out of time: each of its cases alone, so that one large case costs only itself)
            return '\n'.join(run(f'{k}x{j}', [c], 60) or '' for j, c in enumerate(batch))
        with cf.ThreadPoolExecutor(10) as ex:
            out = '\n'.join(ex.map(oracle, range(0, len(lines), 10)))
    verdict = {}
    for m in re.finditer(r'^c(\d+)\s+t\w+\.versetest:\d+\s+(.*)$', out, re.M):
        verdict[int(m.group(1))] = m.group(2)
    tally = {}
    for i, (c, rv) in enumerate(zip(cases, ovs)):
        vd = verdict.get(i, '')
        kind = ('ov-refused' if not rv.startswith('[') else 'agree' if vd.startswith('Expected success')
                else 'prototype-limit' if 'timeout' in vd or 'loop' in vd or not vd else 'DIFFER')
        tally[kind] = tally.get(kind, 0) + 1
        if kind != 'agree':
            print(f'{kind} {vd}\n  oracle    {c[0]}\n  openverse {c[1]!r} {c[2]}\n            {rv}')
    print('TALLY', seed, depth, tally)
main()
