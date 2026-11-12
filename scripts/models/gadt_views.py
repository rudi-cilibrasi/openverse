#!/usr/bin/env python3
"""Interfaces that classes give arbitrary type arguments, referred to
through views (#351, #405, #523, #526, #529, #530): random hierarchies of
interfaces with fields and default methods and classes below them (with
class parents, compound and closed arguments), whose values are read,
set, dispatched on and cast back, directly and from generic code, also
through <suspends> methods. Each program's output is predicted.

usage: gadt_views.py SEED OUT.exp > PROGRAM.verse
(from the reviews' view generators, vgen/vgen399/vgen405)"""
import random, sys
seed = int(sys.argv[1]); R = random.Random(seed)
# (the reviews' environment switches, chosen from the seed)
_F = random.Random(seed * 7919 + 1)
FORCE_OV = _F.random() < 0.25
NOABS = _F.random() < 0.25
SUSP = _F.random() < 0.3
NODEF = _F.random() < 0.15
ADD = _F.choice([0.7, 0.7, 1.0])
BASE = [('int',), ('string',), ('char',)]
def rtype(depth, vars_):
    opts = []
    if vars_: opts += [('var', v) for v in vars_] * 3
    opts += BASE
    if depth > 0: opts += ['arr', 'opt', 'tup']
    c = R.choice(opts)
    if c == 'arr': return ('arr', rtype(depth - 1, vars_))
    if c == 'opt': return ('opt', rtype(depth - 1, vars_))
    if c == 'tup': return ('tup', rtype(depth - 1, vars_), rtype(depth - 1, vars_))
    return c
def closed(depth): return rtype(depth, [])
def sub(t, s):
    if t[0] == 'var': return s.get(t[1], t)
    if t[0] in ('arr', 'opt'): return (t[0], sub(t[1], s))
    if t[0] == 'tup': return ('tup', sub(t[1], s), sub(t[2], s))
    return t
def ty(t):
    k = t[0]
    if k == 'var': return t[1]
    if k in ('int', 'string', 'char'): return k
    if k == 'arr': return '[]' + ty(t[1])
    if k == 'opt': return '?' + ty(t[1])
    return f"tuple({ty(t[1])}, {ty(t[2])})"
def lit(t):
    k = t[0]
    if k == 'int': return str(R.randint(0, 9))
    if k == 'string': return '"' + R.choice('abc') + '"'
    if k == 'char': return "'" + R.choice('xyz') + "'"
    if k == 'arr': return 'array{' + lit(t[1]) + '}'
    if k == 'opt': return 'option{' + lit(t[1]) + '}'
    if k == 'tup': return '(' + lit(t[1]) + ', ' + lit(t[2]) + ')'
    raise Exception(t)
SHOWN = {}
def shname(t):
    nm = 'Sh_' + ty(t).replace('?', 'o_').replace('[]', 'a_').replace('tuple(', 'T_').replace(', ', '_').replace(')', '_')
    if t not in SHOWN:
        k = t[0]
        if k == 'int': b = f'{nm}(X:int):string = "{{X}}"'
        elif k == 'string': b = f'{nm}(X:string):string = X'
        elif k == 'char': b = f'{nm}(X:char):string = "{{X}}"'
        elif k == 'tup':
            a1, a2 = shname(t[1]), shname(t[2])
            b = f'{nm}(X:{ty(t)}):string = "({{{a1}(X(0))}},{{{a2}(X(1))}})"'
        elif k == 'opt':
            a1 = shname(t[1]); b = f'{nm}(X:{ty(t)}):string = if (Y := X?) then "s{{{a1}(Y)}}" else "n"'
        else:
            a1 = shname(t[1]); b = f'{nm}(X:{ty(t)}):string = if (Y := X[0]) then "a{{{a1}(Y)}}" else "e"'
        SHOWN[t] = b
    return nm
def shval(L):
    # the shown form of a literal as lit writes it
    L = L.strip()
    if L == 'array{}': return 'e'
    if L == 'false': return 'n'
    if L.startswith('array{'): return 'a' + shval(L[6:-1])
    if L.startswith('option{'): return 's' + shval(L[7:-1])
    if L.startswith('('):
        inner = L[1:-1]; d = 0
        for i, ch in enumerate(inner):
            if ch in '({': d += 1
            elif ch in ')}': d -= 1
            elif ch == ',' and d == 0: return '(' + shval(inner[:i]) + ',' + shval(inner[i+1:]) + ')'
    if L.startswith('"') or L.startswith("'"): return L[1:-1]
    return L
# interfaces
NI = R.randint(3, 5)
ifs = []   # name, params, parent (name, args) or None, method arg type, has default
for i in range(NI):
    np_ = R.choice([0, 1, 1, 2, 2])
    ps = [f"p{j}" for j in range(np_)]
    parent = None
    if i > 0 and R.random() < 0.5:
        q = R.randrange(i)
        qn, qps = ifs[q][0], ifs[q][1]
        parent = (qn, [rtype(1, ps) for _ in qps])
    mt = ('var', R.choice(ps)) if ps else ('int',)
    ifs.append((f"i{i}", ps, parent, mt, (R.random() < 0.3) and not NODEF))
IF = {x[0]: x for x in ifs}
DIRECT = _F.random() < 0.6
NFLD = _F.choice([1, 2, 2, 3])
IFLD = {}
def dlit(t):
    if not any(True for _ in tvars(t)): return lit(t)
    if t[0] == 'arr': return 'array{}'
    if t[0] == 'opt': return 'false'
    return None
def tvars(t):
    if t[0] == 'var': yield t[1]
    elif t[0] in ('arr', 'opt'): yield from tvars(t[1])
    elif t[0] == 'tup': yield from tvars(t[1]); yield from tvars(t[2])
for (n, ps, parent, mt, dflt) in ifs:
    fl = []
    for k in range(R.randint(0, NFLD)):
        T = rtype(1, ps)
        isvar = R.random() < 0.8
        d = dlit(T) if R.random() < 0.6 else None
        fl.append((f"Q{n}_{k}", T, isvar, d))
    IFLD[n] = fl
COV = {}
def root(n):
    while IF[n][2]: n = IF[n][2][0]
    return n
def reach(n, args):
    # (interface, args) pairs reached from n(args), n included
    out = [(n, args)]
    p = IF[n][2]
    if p:
        s = dict(zip(IF[n][1], args))
        out += reach(p[0], [sub(a, s) for a in p[1]])
    return out
# classes
CL = {}
def ifaces_of(c, args):
    # (iface, args) reached by an object of class c at args
    cc = CL[c]
    s = dict(zip(cc[1], args))
    out = []
    if cc[2]:
        out += ifaces_of(cc[2][0], [sub(a, s) for a in cc[2][1]])
    for (n, a) in cc[3]:
        out += reach(n, [sub(x, s) for x in a])
    return out
classes = []   # name, params, parent class (name,args) or None, listed ifaces [(name,args)], overrides set, abstract
NC = R.randint(2, 5)
for c in range(NC):
    name = f"c{c}"
    if c > 0 and R.random() < 0.4:
        pc = R.choice(classes)
        np_ = R.choice([0, 1, 1, 2])
        ps = [f"t{j}" for j in range(np_)]
        pargs = [rtype(1, ps) for _ in pc[1]]
        # (#399) at times also list interfaces whose families the parent does not reach
        proots = set(root(n) for (n, a) in ifaces_of(pc[0], [('var', v) for v in pc[1]]))
        listed = []
        if R.random() < ADD:
            k = R.choice([1, 1, 2])
            for n in R.sample([x[0] for x in ifs], len(ifs)):
                if len(listed) >= k: break
                if root(n) in proots: continue
                proots.add(root(n))
                listed.append((n, [rtype(1, ps) for _ in IF[n][1]]))
        classes.append([name, ps, (pc[0], pargs), listed, set(), False]); CL[name] = classes[-1]
    else:
        np_ = R.choice([1, 2, 2, 3])
        ps = [f"t{j}" for j in range(np_)]
        k = R.choice([1, 2, 2, 3])
        roots, listed = set(), []
        for n in R.sample([x[0] for x in ifs], len(ifs)):
            if len(listed) >= k: break
            if root(n) in roots: continue
            # ancestors' roots too: n's family
            roots.add(root(n))
            listed.append((n, [rtype(1, ps) for _ in IF[n][1]]))
        classes.append([name, ps, None, listed, set(), (R.random() < 0.3) and not NOABS]); CL[name] = classes[-1]
def chain(c):
    out = [c]
    while CL[c][2]: c = CL[c][2][0]; out.append(c)
    return out
def fields_of(c, args):
    cc = CL[c]; s = dict(zip(cc[1], args)); out = []
    if cc[2]: out += fields_of(cc[2][0], [sub(a, s) for a in cc[2][1]])
    out += [(f"F{c}_{v}", sub(('var', v), s)) for v in cc[1] if f"F{c}_{v}" in FIELDS]
    return out
FIELDS = set()
for cc in classes:
    for v in cc[1]:
        if R.random() < 0.5: FIELDS.add(f"F{cc[0]}_{v}")
# overrides: root class must implement every non-default method it reaches
for cc in classes:
    own = [('var', v) for v in cc[1]]
    ifl = ifaces_of(cc[0], own)
    for (n, a) in ifl:
        must = cc[2] is None and not IF[n][4] and not cc[5]
        if must or R.random() < 0.4: cc[4].add(n)
    if FORCE_OV and cc[2] is not None and not cc[4] and ifl: cc[4].add(R.choice(ifl)[0])
# concrete classes implement what is still abstract
for cc in classes:
    if cc[5]: continue
    own = [('var', v) for v in cc[1]]
    for (n, a) in ifaces_of(cc[0], own):
        if IF[n][4]: continue
        if not any(n in CL[d][4] for d in chain(cc[0])): cc[4].add(n)
DEFK = {x[0]: R.randint(10, 49) for x in ifs}
DEFC = {x[0]: R.randint(50, 99) for x in classes}
def nimpl(c, n, K, O):
    for d in chain(c):
        if n in CL[d][4]: return f"{d}.N{DEFC[d] if K is None else K}{'s' if O else 'n'}"
    return f"{n}.N{DEFK[n] if K is None else K}{'s' if O else 'n'}"
lines = []
for (n, ps, parent, mt, dflt) in ifs:
    head = f"{n}({', '.join(p + ':type' for p in ps)})" if ps else n
    par = f"({parent[0]}({', '.join(ty(a) for a in parent[1])}))" if parent and parent[1] else (f"({parent[0]})" if parent else '')
    lines.append(f"{head} := interface{par}:")
    for (f, T, isvar, d) in IFLD[n]:
        lines.append(f"    {'var ' if isvar else ''}{f}:{ty(T)}" + (f" = {d}" if d is not None else ''))
        lines.append(f"    D_{f}():{ty(T)} = {f}")
        if isvar:
            lines.append(f"    U_{f}(V:{ty(T)}):void = set {f} = V")
        if SUSP:
            lines.append(f"    SD_{f}()<suspends>:{ty(T)} =")
            lines.append(f"        Sleep(0.0)")
            lines.append(f"        {f}")
    m = f"    M{n}(X:{ty(mt)}):string"
    lines.append(m + (f' = "{n}.def"' if dflt else ''))
    lines.append(f"    E{n}(X:{ty(mt)}):{ty(mt)} = X")
    lines.append(f"    P{n}(X:{ty(mt)}, Y:w where w:type):tuple({ty(mt)}, w) = (X, Y)")
    lines.append(f'    N{n}(X:{ty(mt)}, ?K:int = {DEFK[n]}, ?O:?{ty(mt)} = false):string = "{n}.N" + "{{K}}" + (if (O?) then "s" else "n")')
    if SUSP: lines.append(f'    S{n}(X:{ty(mt)})<suspends>:string = "{n}.def"')
for cc in classes:
    name, ps, parent, listed, ovs, _ = cc
    head = f"{name}({', '.join(p + ':type' for p in ps)})" if ps else name
    if parent:
        pa = f"{parent[0]}({', '.join(ty(a) for a in parent[1])})" if parent[1] else parent[0]
        extra = ''.join(', ' + ((n + '(' + ', '.join(ty(x) for x in a) + ')') if a else n) for (n, a) in listed)
        lines.append(f"{head} := class({pa}{extra}):")
    else:
        lines.append(f"{head} := class{'<abstract>' if cc[5] else ''}({', '.join((n + '(' + ', '.join(ty(x) for x in a) + ')') if a else n for (n, a) in listed)}):")
    body = []
    for v in ps:
        if f"F{name}_{v}" in FIELDS: body.append(f"    F{name}_{v}:{v}")
    own = [('var', v) for v in ps]
    for (n, a) in ifaces_of(name, own):
        if n in ovs:
            mt = sub(IF[n][3], dict(zip(IF[n][1], a)))
            body.append(f'    M{n}<override>(X:{ty(mt)}):string = "{name}.M{n}"')
            body.append(f'    N{n}<override>(X:{ty(mt)}, ?K:int = {DEFC[name]}, ?O:?{ty(mt)} = false):string = "{name}.N" + "{{K}}" + (if (O?) then "s" else "n")')
            body.append(f'    P{n}<override>(X:{ty(mt)}, Y:w where w:type):tuple({ty(mt)}, w) = (X, Y)')
            if SUSP:
                body.append(f'    S{n}<override>(X:{ty(mt)})<suspends>:string =')
                body.append(f'        Sleep(0.0)')
                body.append(f'        "{name}.S{n}"')
    COV[name] = {}
    for (n, a) in ifaces_of(name, own):
        sa = dict(zip(IF[n][1], a))
        for (f, T, isvar, d) in IFLD[n]:
            if R.random() < 0.35:
                Tc = sub(T, sa)
                dl = dlit(Tc)
                if dl is None: continue
                COV[name][f] = dl
                body.append(f"    {'var ' if isvar else ''}{f}<override>:{ty(Tc)} = {dl}")
    if not body: body.append(f'    Dummy{name}():int = 0')
    lines += body
# generic callers
for (n, ps, parent, mt, dflt) in ifs:
    for (f, T, isvar, d) in IFLD[n]:
        if ps:
            w = ' where ' + ', '.join(p + ':type' for p in ps)
            X = f"X:{n}({', '.join(ps)})"
        else:
            w = ''; X = f"X:{n}"
        lines.append(f"GF_{f}({X}{w}):{ty(T)} = X.{f}")
        if isvar:
            lines.append(f"SF_{f}({X}, V:{ty(T)}{w}):void = set X.{f} = V")
        if SUSP:
            lines.append(f"GSF_{f}({X}{w})<suspends>:{ty(T)} =")
            lines.append(f"        Sleep(0.0)")
            lines.append(f"        X.{f}")
for (n, ps, parent, mt, dflt) in ifs:
    if ps:
        lines.append(f"G{n}(X:{n}({', '.join(ps)}), V:{ty(mt)} where {', '.join(p + ':type' for p in ps)}):string = X.M{n}(V)")
    else:
        lines.append(f"G{n}(X:{n}, V:int):string = X.M{n}(V)")
mainAt = len(lines)
if SUSP:
    for (n, ps, parent, mt, dflt) in ifs:
        if ps: lines.append(f"GS{n}(X:{n}({', '.join(ps)}), V:{ty(mt)} where {', '.join(p + ':type' for p in ps)})<suspends>:string = X.S{n}(V)")
        else: lines.append(f"GS{n}(X:{n}, V:int)<suspends>:string = X.S{n}(V)")
def ps_of(n): return IF[n][1]
for (n, ps, parent, mt, dflt) in ifs:
    if ps: lines.append(f"GN{n}(X:{n}({', '.join(ps)}), V:{ty(mt)} where {', '.join(p + ':type' for p in ps)}):string = X.N{n}(V)")
GDEF = _F.random() < 0.4
if GDEF:
    # #526: each field default D_f that a generic interface reaches, called through a generic
    # receiver of that interface (inherited defaults included).
    for (n, ps, parent, mt, dflt) in ifs:
        if not ps: continue
        for (m, b) in reach(n, [('var', p) for p in ps]):
            sb = dict(zip(IF[m][1], b))
            for (f, T, isvar, d) in IFLD[m]:
                lines.append(f"GD_{n}_{f}(X:{n}({', '.join(ps)}) where {', '.join(p + ':type' for p in ps)}):{ty(sub(T, sb))} = X.D_{f}()")
mainAt = len(lines)
lines.append("Main()<suspends>:void =" if SUSP else "Main():void =")
exp = []
objs = []
k = 0
for cc in classes:
    if cc[5]: continue
    for rep in range(R.choice([1, 2])):
        args = [closed(1 if R.random() < 0.3 else 0) for _ in cc[1]]
        fs = fields_of(cc[0], args)
        init = {}
        sets = [(f, lit(t)) for f, t in fs]
        for (n, a) in ifaces_of(cc[0], args):
            sa = dict(zip(IF[n][1], a))
            for (f, T, isvar, d) in IFLD[n]:
                ov = next((COV[x][f] for x in chain(cc[0]) if f in COV.get(x, {})), None)
                dv = ov if ov is not None else d
                if dv is None or R.random() < 0.3:
                    L = lit(sub(T, sa)); sets.append((f, L)); init[f] = L
                else: init[f] = dv
        e = (f"{cc[0]}({', '.join(ty(a) for a in args)})" if args else cc[0]) + '{' + ', '.join(f"{f} := {L}" for f, L in sets) + '}'
        objs.append((cc[0], args, e, init))
def impl(c, n):
    for d in chain(c):
        if n in CL[d][4]: return f"{d}.M{n}"
    return f"{n}.def"
groups = {}
for (c, args, e, init) in objs:
    for (n, a) in ifaces_of(c, args):
        key = (n, tuple(a))
        groups.setdefault(key, []).append((c, args, e, init))
gi = 0
for (n, a), members in groups.items():
    tyI = f"{n}({', '.join(ty(x) for x in a)})" if a else n
    mt = sub(IF[n][3], dict(zip(IF[n][1], a)))
    lines.append(f"    A{gi}:[]{tyI} = array{{{', '.join(m[2] for m in members)}}}")
    lines.append(f'    for (X : A{gi}) {{ Print("{{X.M{n}({lit(mt)})}} {{G{n}(X, {lit(mt)})}}") }}')
    for (c, args, e, init) in members:
        exp.append(f"{impl(c, n)} {impl(c, n)}")
    L = lit(mt)
    lines.append(f'    for (X : A{gi}) {{ Print({shname(mt)}(X.E{n}({L}))) }}')
    for (c, args, e, init) in members:
        exp.append(shval(L))
    lines.append(f'    for (X : A{gi}) {{ Print("{{X.N{n}({lit(mt)})}} {{X.N{n}({lit(mt)}, ?K := 7)}} {{X.N{n}({lit(mt)}, ?O := option{{{lit(mt)}}})}}") }}')
    for (c, args, e, init) in members:
        exp.append(f"{nimpl(c, n, None, False)} {nimpl(c, n, 7, False)} {nimpl(c, n, None, True)}")
    if ps_of(n):
        lines.append(f'    for (X : A{gi}) {{ Print(GN{n}(X, {lit(mt)})) }}')
        for (c, args, e, init) in members:
            exp.append(nimpl(c, n, None, False))
    L2 = lit(mt); wt = closed(1); L3 = lit(wt)
    shp = shname(('tup', mt, wt))
    lines.append(f'    for (X : A{gi}) {{ Print({shp}(X.P{n}({L2}, {L3}))) }}')
    for (c, args, e, init) in members:
        exp.append('(' + shval(L2) + ',' + shval(L3) + ')')
    if SUSP:
        lines.append(f'    for (X : A{gi}):')
        lines.append(f'        T := spawn{{X.S{n}({lit(mt)})}}')
        lines.append(f'        Print("{{X.S{n}({lit(mt)})}} {{T.Await()}} {{GS{n}(X, {lit(mt)})}}")')
        for (c, args, e, init) in members:
            t = impl(c, n).replace('.M', '.S'); exp.append(f"{t} {t} {t}")
    # casts back to each class
    for cc in classes:
        if not any(cc[0] in chain(m[0]) for m in members): continue
        if not any(x == n for (x, _) in ifaces_of(cc[0], [('var', v) for v in cc[1]])): continue
        if R.random() < 0.3: continue
        lines.append(f"    for (X : A{gi}):")
        lines.append(f'        if (C := {cc[0]}[X]) then Print("y") else Print("n")')
        for (c, args, e, init) in members:
            exp.append("y" if cc[0] in chain(c) else "n")
    vis = []
    for (m, b) in reach(n, a):
        sb = dict(zip(IF[m][1], b))
        for (f, T, isvar, d) in IFLD[m]:
            vis.append((m, f, sub(T, sb), isvar))
    if vis:
        body = []
        exps = [[] for _ in members]
        for (m, f, Tt, isvar) in vis:
            sh = shname(Tt)
            cur = [mm[3][f] for mm in members]
            def P(expr):
                body.append(f"        Print({sh}({expr}))")
                for i in range(len(members)): exps[i].append(shval(cur[i]))
            if DIRECT: P(f"X.{f}")
            else: P(f"GF_{f}(X)")
            if isvar:
                L2 = lit(Tt)
                body.append(f"        set X.{f} = {L2}" if DIRECT else f"        SF_{f}(X, {L2})")
                cur = [L2] * len(members)
            P(f"GF_{f}(X)")
            if isvar:
                L3 = lit(Tt); body.append(f"        SF_{f}(X, {L3})"); cur = [L3] * len(members)
            P(f"X.D_{f}()")
            if GDEF and IF[n][1]: P(f"GD_{n}_{f}(X)")
            if isvar:
                L4 = lit(Tt); body.append(f"        X.U_{f}({L4})"); cur = [L4] * len(members)
                P(f"GF_{f}(X)" if not DIRECT else f"X.{f}")
            if SUSP:
                P(f"X.SD_{f}()")
                P(f"GSF_{f}(X)")
        lines.append(f"    for (X : A{gi}):")
        lines += body
        for e_ in exps: exp.extend(e_)
    gi += 1
# (Main is never empty)
lines.append('    Print("end")')
exp.append("end")
lines[mainAt:mainAt] = list(SHOWN.values())
sys.stdout.write('\n'.join(lines) + '\n')
open(sys.argv[2], 'w').write('exit=0\n' + '\n'.join(exp) + '\n')
