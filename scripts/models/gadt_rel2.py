#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the review of #236 (classes that repeat or relate type arguments), updated for #242.
"""Generator + model for openverse PR #236 (classes that repeat or relate
type arguments override).  Writes a Verse program to stdout and the model's
expected result to the file given as argv[2]: first line 'exit=N', then the
expected stdout (for exit 0) or a substring of the expected error (exit 4).

Model: every object knows its class and closed type arguments; a call runs the
implementation nearest the object's class (Verse dynamic dispatch), and its
body is evaluated here.  Refusals (the documented ones) are predicted from the
pins rules of docs/DESIGN.md so that accepted programs must run.
"""
import random, sys

seed = int(sys.argv[1]); out_exp = sys.argv[2]
R = random.Random(seed)
def ch(p): return R.random() < p

# ---------------------------------------------------------------- types
INT, STR = ('int',), ('string',)
def Opt(t): return ('opt', t)
def Arr(t): return ('arr', t)
def V(n): return ('var', n)

def tyt(t):
    k = t[0]
    if k == 'int': return 'int'
    if k == 'string': return 'string'
    if k == 'opt': return '?' + tyt(t[1])
    if k == 'arr': return '[]' + tyt(t[1])
    if k == 'var': return t[1]
    if k == 'cls': return f"{t[1]}({', '.join(tyt(a) for a in t[2])})" if t[2] else t[1]
    raise ValueError(t)

def subst(t, s):
    k = t[0]
    if k == 'var': return s.get(t[1], t)
    if k == 'pos': return s.get(('pos', t[1]), t)
    if k in ('opt', 'arr'): return (k, subst(t[1], s))
    if k == 'cls': return ('cls', t[1], tuple(subst(a, s) for a in t[2]))
    return t

def tvars(t):
    k = t[0]
    if k == 'var': return [t[1]]
    if k in ('opt', 'arr'): return tvars(t[1])
    if k == 'cls': return [v for a in t[2] for v in tvars(a)]
    return []

def poss(t):
    k = t[0]
    if k == 'pos': return [t[1]]
    if k in ('opt', 'arr'): return poss(t[1])
    return []

def match(p, a, s):
    """first-order matching of pattern p (vars) against closed a."""
    if s is None: return None
    if p[0] == 'var':
        if p[1] in s: return s if s[p[1]] == a else None
        s = dict(s); s[p[1]] = a; return s
    if p[0] != a[0]: return None
    if p[0] in ('opt', 'arr'): return match(p[1], a[1], s)
    if p[0] == 'cls':
        if p[1] != a[1] or len(p[2]) != len(a[2]): return None
        for x, y in zip(p[2], a[2]): s = match(x, y, s)
        return s
    return s

# ---------------------------------------------------------------- values
def show(v, t):
    k = t[0]
    if k == 'int': return str(v)
    if k == 'string': return v
    if k == 'opt': return 'n' if v is None else f"s({show(v[1], t[1])})"
    if k == 'arr': return '[' + ''.join(show(x, t[1]) + ',' for x in v) + ']'
    raise ValueError(t)

def lit(t, depth=0):
    """(verse text, value) of a literal of closed type t"""
    k = t[0]
    if k == 'int':
        n = R.randint(-3, 30); return (str(n) if n >= 0 else f"({n})", n)
    if k == 'string':
        w = R.choice(['ka', 'lo', 'mi', 'zu', 'ber', 'q']); return f'"{w}"', w
    if k == 'opt':
        if ch(0.3): return 'false', None
        x, v = lit(t[1], depth + 1); return f"option{{{x}}}", ('some', v)
    if k == 'arr':
        n = R.randint(0, 2); xs = [lit(t[1], depth + 1) for _ in range(n)]
        return f"array{{{', '.join(x for x, _ in xs)}}}", [v for _, v in xs]
    raise ValueError(t)

SHOWN = {}
def shname(t):
    nm = 'Sh_' + tyt(t).replace('?', 'o_').replace('[]', 'a_')
    if t not in SHOWN:
        k = t[0]
        if k == 'int': body = f'{nm}(X:int):string = "{{X}}"'
        elif k == 'string': body = f'{nm}(X:string):string = X'
        elif k == 'opt':
            inner = shname(t[1])
            body = f'{nm}(X:{tyt(t)}):string = if (Y := X?) then "s({{{inner}(Y)}})" else "n"'
        else:
            inner = shname(t[1])
            body = (f'{nm}(X:{tyt(t)}):string =\n    var Acc:string = "["\n'
                    f'    for (E : X):\n        set Acc = "{{Acc}}{{{inner}(E)}},"\n    "{{Acc}}]"')
        SHOWN[t] = body
    return nm

# ---------------------------------------------------------------- classes
class Cls:
    def __init__(s, name, params, parent, pargs, iface=False):
        s.name, s.params, s.parent, s.pargs, s.iface = name, params, parent, pargs, iface
        s.meths = {}        # method -> (verse body text, python fn(env)->value)
        s.extra = []        # (field, type over own params, default text or None, default value)
        s.children = []

ROOT_P = ['t', 'u']
METHODS = ['Get', 'Snd', 'Name', 'Put', 'Peek', 'Tag']
IFACE_M = ['Peek', 'Tag']
classes = {}
order = []

def add(c):
    classes[c.name] = c; order.append(c)
    if c.parent: classes[c.parent].children.append(c)

def chain(c):
    out = []
    while c is not None:
        out.append(c); c = classes[c.parent] if c.parent else None
    return out

def args_at(c, args, target):
    while c is not target:
        s = dict(zip(c.params, args))
        args = [subst(a, s) for a in c.pargs]
        c = classes[c.parent]
    return args

def pair_args(c, args):
    """the type arguments (at ip, the top) of c at its own args: pair gives ip
    exactly its own, so these are also pair's for pair's classes."""
    return args_at(c, args, IP if IFACE else root)

def core_args(c):
    if c.parent is None: return [V(p) for p in c.params]
    if IFACE and c.parent == 'pair' and False: pass
    q = classes[c.parent]
    s = dict(zip(q.params, c.pargs))
    cs = [subst(a, s) for a in core_args(q)]
    for p in c.params:
        if V(p) not in cs: cs.append(V(p))
    return cs

def pins_of(c):
    cs = core_args(c)
    first = {}
    for i, a in enumerate(cs):
        if a[0] == 'var' and a[1] not in first: first[a[1]] = i
    s = {v: ('pos', j) for v, j in first.items()}
    own = []
    for i, a in enumerate(cs):
        if a[0] == 'var' and first[a[1]] == i: own.append(None)
        else: own.append(subst(a, s))
    if c.parent is None: return own
    pq = pins_of(classes[c.parent])
    return [o if o is None or all(j < len(pq) for j in poss(o)) else (pq[i] if i < len(pq) else None)
            for i, o in enumerate(own)]

def is_sub(c, e):
    return any(x.name == e.name for x in chain(c))

def impl_of(c, m):
    for x in chain(c):
        if m in x.meths: return x
    raise ValueError((c.name, m))

def concrete_below(c):
    out = [] if c.iface else [c]
    for k in c.children: out += concrete_below(k)
    return out

# ---------------------------------------------------------------- build hierarchy
IFACE = ch(0.5)
IP = Cls('ip', ['p', 'q'], None, None, iface=True)
if IFACE: add(IP)
root = Cls('pair', ROOT_P, 'ip' if IFACE else None, [V('t'), V('u')] if IFACE else None)
root.meths = {'Get': ('A', lambda o, x: o['A']), 'Snd': ('B', lambda o, x: o['B']),
              'Name': ('"pair"', lambda o, x: 'pair'), 'Put': ('set A = X', None),
              'Peek': ('B', lambda o, x: o['B']), 'Tag': ('"pair"', lambda o, x: 'pair')}
add(root)
VIA = ch(0.5)
if VIA: root.meths['Via'] = ('Get()', None)
# classes implementing ip directly, repeating or relating its arguments
IR = []
for nm, ps, pa in [] if not IFACE else [('ir', ['x'], [V('x'), V('x')]), ('iro', ['x'], [Opt(V('x')), V('x')]),
                   ('iri', [], [INT, INT]), ('irs', ['x'], [V('x'), STR])]:
    if ch(0.45):
        c = Cls(nm, ps, 'ip', pa); add(c); IR.append(c)
        c.meths['Peek'] = R.choice([('B', lambda o, x: o['B'])] +
            ([('A', lambda o, x: o['A'])] if pa[0] == pa[1] else []))
        c.meths['Tag'] = (f'"{nm}"', (lambda nm: lambda o, x: nm)(nm))
        if ch(0.5):
            k = Cls(nm + 'k', [], nm, [INT] if ps else [])
            if ps and pa[0] == pa[1] or nm == 'iri':
                k.meths['Peek'] = ('A + 100', lambda o, x: o['A'] + 100)
            k.meths['Tag'] = (f'"{nm}k"', (lambda nm: lambda o, x: nm)(nm + 'k'))
            add(k); IR.append(k)
def in_pair(c): return is_sub(c, root)

PATS = []   # parent-arg templates as functions of own params
def rand_pargs(q, nparams):
    """parent type arguments for a new subclass of q with params x[, y]."""
    ps = ['x', 'y'][:nparams]
    def leaf():
        r = R.random()
        if ps and r < 0.55: return V(R.choice(ps))
        return R.choice([INT, STR])
    def te(d=0):
        r = R.random()
        if d < 1 and r < 0.18: return Opt(te(d + 1))
        if d < 1 and r < 0.3: return Arr(te(d + 1))
        return leaf()
    return ps, [te() for _ in q.params]

ncls = R.randint(3, 8)
counter = 0
for _ in range(ncls * 3):
    if len(order) > ncls + 2 + len(IR): break
    q = R.choice([c for c in order if not c.iface and in_pair(c)])
    if len(chain(q)) > 4: continue
    nparams = R.choice([0, 1, 1, 1, 2])
    ps, pa = rand_pargs(q, nparams)
    # every own param must appear somewhere (or we add a field of its type)
    counter += 1
    c = Cls(f"c{counter}", ps, q.name, pa)
    add(c)

# a "repeating" shape is likely: force a few classic ones
def force(name, ps, parent, pa):
    c = Cls(name, ps, parent, pa); add(c); return c
if ch(0.7): force('dup', ['x'], 'pair', [V('x'), V('x')])
if ch(0.5): force('opp', ['x'], 'pair', [Opt(V('x')), V('x')])
if ch(0.4): force('arp', ['x'], 'pair', [V('x'), Arr(V('x'))])
if ch(0.4): force('ipp', ['x'], 'pair', [INT, V('x')])
if 'dup' in classes and ch(0.6): force('dupi', [], 'dup', [INT])
if 'dup' in classes and ch(0.5): force('dupo', ['y'], 'dup', [Opt(V('y'))])
if 'dup' in classes and ch(0.3): force('dupx', ['x', 'w'], 'dup', [V('x')])
if 'dupx' in classes and ch(0.6): force('dupxr', ['w'], 'dupx', [Opt(V('w')), V('w')])
if 'dupx' in classes and ch(0.5): force('dupxc', [], 'dupx', [INT, STR])

if IFACE:
    for c in list(order):
        if c.name in classes and not c.iface and len(core_args(c)) > 2:
            for d in concrete_below(c):
                if d.name in classes:
                    del classes[d.name]; order.remove(d)
                    classes[d.parent].children.remove(d) if d.parent in classes and d in classes[d.parent].children else None
for c in order:
    if c.iface or c is root or c in IR: continue
    q = classes[c.parent]
    # field of each own param that does not occur bare in its core args (so its value exists)
    for p in c.params:
        if not any(a == V(p) for a in c.pargs) or len(core_args(c)) > 2:
            if not any(f == f"W{p}{c.name}" for f, *_ in c.extra):
                c.extra.append((f"W{p}{c.name}", V(p), None, None))
    if ch(0.4):
        n = R.randint(0, 9); c.extra.append((f"K{c.name}", INT, str(n), n))

def field_tys(c):
    """field -> type over c's own params"""
    pa = pair_args(c, [V(p) for p in c.params])
    d = {'A': pa[0], 'B': pa[1]}
    for x in reversed(chain(c)):
        if x.iface: continue
        if x is c:
            for f, t, _, _ in x.extra: d[f] = t
        else:
            # translate x's extra field types to c's params
            # (map through the chain from c up to x)
            s = {}
            args = [V(p) for p in c.params]; y = c
            while y is not x:
                s2 = dict(zip(y.params, args))
                args = [subst(a, s2) for a in y.pargs]; y = classes[y.parent]
            s = dict(zip(x.params, args))
            for f, t, _, _ in x.extra: d[f] = subst(t, s)
    return d

def can_override(c):
    return len(core_args(c)) == 2

# ---------------------------------------------------------------- override bodies
def expr_of(t, env, depth=0):
    """(text, fn(o,x)) of an expression of type t (over c's params) from fields env"""
    cands = []
    for f, ft in env.items():
        if ft == t: cands.append((f, (lambda f: lambda o, x: o[f])(f)))
    if t == INT:
        for f, ft in env.items():
            if ft == INT:
                k = R.randint(1, 9)
                cands.append((f"{f} + {k}", (lambda f, k: lambda o, x: o[f] + k)(f, k)))
                for g, gt in env.items():
                    if gt == INT and g != f:
                        cands.append((f"{f} * 2 + {g}", (lambda f, g: lambda o, x: o[f] * 2 + o[g])(f, g)))
        k = R.randint(40, 99); cands.append((str(k), (lambda k: lambda o, x: k)(k)))
    if t == STR:
        w = R.choice(['aa', 'bb', 'cc']); cands.append((f'"{w}"', (lambda w: lambda o, x: w)(w)))
    if t[0] == 'opt' and depth < 2:
        sub = expr_of(t[1], env, depth + 1)
        if sub: cands.append((f"option{{{sub[0]}}}", (lambda g: lambda o, x: ('some', g(o, x)))(sub[1])))
        cands.append(('false', lambda o, x: None))
    if t[0] == 'arr' and depth < 2:
        sub = expr_of(t[1], env, depth + 1)
        if sub:
            cands.append((f"array{{{sub[0]}, {sub[0]}}}", (lambda g: lambda o, x: [g(o, x), g(o, x)])(sub[1])))
        cands.append(('array{}', lambda o, x: []))
    if not cands: return None
    # prefer non-trivial field use
    return R.choice(cands)

def super_val(c, m):
    q = classes[c.parent]
    return lambda o, x: run_impl(impl_of(q, m), m, o, x)

def run_impl(e, m, o, x):
    return e.meths[m][1](o, x)

for c in order:
    if c.iface or c is root or c in IR or not in_pair(c): continue
    if not can_override(c): continue
    env = field_tys(c)
    pa = pair_args(c, [V(p) for p in c.params])
    for m in METHODS:
        if not ch(0.5): continue
        if m in ('Get', 'Snd', 'Peek'):
            if ch(0.2):
                c.meths[m] = (f'(super:){m}()', super_val(c, m)); continue
            e = expr_of(pa[0] if m == 'Get' else pa[1], env)
            if e: c.meths[m] = e
        elif m == 'Tag':
            if ch(0.3):
                sv = super_val(c, m)
                c.meths[m] = (f'"{c.name}/{{(super:)Tag()}}"', (lambda nm, sv: lambda o, x: f"{nm}/{sv(o, x)}")(c.name, sv))
            else:
                c.meths[m] = (f'"t{c.name}"', (lambda nm: lambda o, x: nm)('t' + c.name))
        elif m == 'Name':
            ints = [f for f, t in env.items() if t == INT]
            if ints and ch(0.6):
                f = R.choice(ints)
                c.meths[m] = (f'"{c.name} {{{f}}}"', (lambda nm, f: lambda o, x: f"{nm} {o[f]}")(c.name, f))
            else:
                c.meths[m] = (f'"{c.name}"', (lambda nm: lambda o, x: nm)(c.name))
        elif m == 'Put':
            opts = [f for f, t in env.items() if t == pa[0] and f in ('A', 'B')]
            if pa[0] == INT and ch(0.4):
                k = R.randint(1, 5); f = R.choice(opts)
                c.meths[m] = (f'set {f} = X + {k}', ('set', f, k))
            else:
                f = R.choice(opts); c.meths[m] = (f'set {f} = X', ('set', f, 0))

root.meths['Put'] = ('set A = X', ('set', 'A', 0))

# ---------------------------------------------------------------- pins / dispatch prediction
# ---------------------------------------------------------------- callers
var_pool = ['a', 'b']
def rand_pattern():
    def leaf():
        return V(R.choice(var_pool)) if ch(0.7) else R.choice([INT, STR])
    def te(d=0):
        r = R.random()
        if d == 0 and r < 0.15: return Opt(te(1))
        if d == 0 and r < 0.25: return Arr(te(1))
        return leaf()
    base = [[V('a'), V('b')], [V('a'), V('a')], [INT, V('b')], [Opt(V('a')), V('a')],
            [V('a'), Arr(V('a'))], [V('a'), INT], [Opt(V('a')), Opt(V('a'))]]
    if ch(0.6): return R.choice(base)
    return [te(), te()]

callers = []   # (name, recv class, pattern args (over vars), method, text)
lines_fn = []
def mk_caller(rc, pat, m, via=None):
    vs = []
    for t in pat:
        for v in tvars(t):
            if v not in vs: vs.append(v)
    where = (' where ' + ', '.join(f"{v}:type" for v in vs)) if vs else ''
    rty = ('cls', rc.name, tuple(pat))
    pa = pair_args(rc, list(pat))
    nm = f"{m}_{len(callers)}"
    if m in ('Get', 'Via'): ret = pa[0]
    elif m in ('Snd', 'Peek'): ret = pa[1]
    elif m in ('Name', 'Tag'): ret = STR
    else: ret = None
    if via is None:
        if m == 'Put':
            txt = f"{nm}(P:{tyt(rty)}, X:{tyt(pa[0])}{where}):void = P.Put(X)"
        else:
            txt = f"{nm}(P:{tyt(rty)}{where}):{tyt(ret)} = P.{m}()"
    else:
        # nested generic: call an existing, more general caller
        inner = via
        if m == 'Put':
            txt = f"{nm}(P:{tyt(rty)}, X:{tyt(pa[0])}{where}):void = {inner[0]}(P, X)"
        else:
            txt = f"{nm}(P:{tyt(rty)}{where}):{tyt(ret)} = {inner[0]}(P)"
    callers.append((nm, rc, pat, m, txt, via))
    return callers[-1]

def meths_for(c):
    if c.iface or not in_pair(c): return IFACE_M
    if not IFACE: return [m for m in METHODS if m not in IFACE_M] + (['Via'] if VIA else []) + IFACE_M
    return METHODS + (['Via'] if VIA else [])
ncallers = R.randint(6, 14)
for _ in range(ncallers):
    r = R.random()
    rc = root if r < 0.55 else (IP if IFACE else root) if r < 0.8 else R.choice(order)
    m = R.choice(meths_for(rc))
    if rc is root or rc is IP:
        pat = rand_pattern()
    else:
        pat = [V('a') if ch(0.6) else R.choice([INT, STR]) for _ in rc.params]
        if not rc.params: pat = []
    mk_caller(rc, pat, m)
# nested generic callers
for _ in range(R.randint(0, 3)):
    base = [c for c in callers if c[1] in (root, IP) and c[5] is None]
    if not base: break
    inner = R.choice(base)
    # a pattern that is an instance of inner's pattern
    s = {v: R.choice([V('a'), INT, Opt(V('a')), STR]) for v in var_pool}
    pat = [subst(t, s) for t in inner[2]]
    mk_caller(inner[1], pat, inner[3], via=inner)

# ---------------------------------------------------------------- objects and main
CLOSED = [INT, STR, Opt(INT), Arr(INT), Arr(STR)]
objs = []   # (name, class, args, fields dict, static type args at class)
main = []
expect = []

def make_obj(c):
    args = [R.choice(CLOSED) for _ in c.params]
    ft = field_tys(c)
    s = dict(zip(c.params, args))
    vals = {}; parts = []
    defaults = {}
    for x in chain(c):
        for f, t, dtxt, dval in x.extra:
            if dtxt is not None: defaults[f] = dval
    for f, t in ft.items():
        ct = subst(t, s)
        if f in defaults and ch(0.5):
            vals[f] = defaults[f]; continue
        txt, v = lit(ct); vals[f] = v; parts.append(f"{f} := {txt}")
    nm = f"O{len(objs)}"
    targs = f"({', '.join(tyt(a) for a in args)})" if c.params else ''
    # static type: the class itself, or the root at its pair args
    pa = pair_args(c, args)
    r = R.random()
    if r < 0.25 and in_pair(c):
        main.append(f"    {nm}:pair({tyt(pa[0])}, {tyt(pa[1])}) = {c.name}{targs}{{{', '.join(parts)}}}")
        st = (root, pa)
    elif r < 0.45 and IFACE:
        main.append(f"    {nm}:ip({tyt(pa[0])}, {tyt(pa[1])}) = {c.name}{targs}{{{', '.join(parts)}}}")
        st = (IP, pa)
    else:
        main.append(f"    {nm} := {c.name}{targs}{{{', '.join(parts)}}}")
        st = (c, args)
    o = {'name': nm, 'cls': c, 'args': args, 'vals': vals, 'static': st, 'ft': {f: subst(t, s) for f, t in ft.items()}}
    objs.append(o)
    return o

def run_method(o, m, x=None):
    if m == 'Via': m = 'Get'
    e = impl_of(o['cls'], m)
    body = e.meths[m]
    if m == 'Put':
        _, f, k = body[1] if isinstance(body[1], tuple) else ('set', 'A', 0)
        o['vals'][f] = x + k if k else x
        return None
    return body[1](o['vals'], x)

def static_up(o, rc):
    """o's static type viewed at receiver class rc: its args there, or None"""
    sc, sargs = o['static']
    if not is_sub(sc, rc): return None
    # walk from sc up to rc
    args = list(sargs); y = sc
    while y is not rc:
        s = dict(zip(y.params, args)); args = [subst(a, s) for a in y.pargs]; y = classes[y.parent]
    return args

used_callers = set()
def do_call(o, cl):
    nm, rc, pat, m, txt, via = cl
    up = static_up(o, rc)
    if up is None: return False
    s = {}
    for p, a in zip(pat, up): s = match(p, a, s)
    if s is None: return False
    used_callers.add(nm)
    if via: used_callers.add(via[0])
    pa = pair_args(rc, [subst(t, s) for t in pat])
    if m == 'Put':
        txt_, xv = lit(pa[0])
        main.append(f"    {nm}({o['name']}, {txt_})")
        run_method(o, 'Put', xv)
        # observe through Get_any-ish: direct field reads at the static type
        sc, sargs = o['static']
        spa = pair_args(sc, list(sargs))
        main.append(f"    Print(\"{o['name']}.A={{{shname(spa[0])}({o['name']}.A)}} B={{{shname(spa[1])}({o['name']}.B)}}\")")
        expect.append(f"{o['name']}.A={show(o['vals']['A'], o['ft']['A'])} B={show(o['vals']['B'], o['ft']['B'])}")
        return True
    rt = pa[0] if m in ('Get', 'Via') else pa[1] if m in ('Snd', 'Peek') else STR
    v = run_method(o, m)
    main.append(f"    Print(\"{nm} {o['name']}: {{{shname(rt)}({nm}({o['name']}))}}\")")
    expect.append(f"{nm} {o['name']}: {show(v, rt)}")
    return True

nobj = R.randint(4, 10)
for _ in range(nobj):
    c = R.choice([c for c in order if not c.iface])
    o = make_obj(c)
    tries = 0; done = 0
    while tries < 12 and done < 4:
        tries += 1
        if do_call(o, R.choice(callers)): done += 1
    # direct method call at the static type
    if ch(0.5):
        sc, sargs = o['static']
        m = R.choice([m for m in meths_for(sc) if m != 'Put'])
        spa = pair_args(sc, list(sargs))
        rt = spa[0] if m in ('Get', 'Via') else spa[1] if m in ('Snd', 'Peek') else STR
        v = run_method(o, m)
        main.append(f"    Print(\"direct {o['name']}: {{{shname(rt)}({o['name']}.{m}())}}\")")
        expect.append(f"direct {o['name']}: {show(v, rt)}")

# arrays of objects with the same pair-level static type
groups = {}
for o in objs:
    sc, sargs = o['static']
    k = tuple(pair_args(sc, list(sargs)))
    groups.setdefault(k, []).append(o)
for k, os_ in groups.items():
    if len(os_) < 2 or not ch(0.8): continue
    allpair = all(o['static'][0] is not IP and in_pair(o['static'][0]) for o in os_)
    at = root if allpair and (ch(0.6) or not IFACE) else IP
    cands = []
    for cl in callers:
        if cl[1] is not at or cl[3] == 'Put': continue
        s = {}
        for p, a in zip(cl[2], k): s = match(p, a, s)
        if s is None: continue
        cands.append((cl, s))
    if not cands: continue
    cl, s = R.choice(cands)
    an = f"Arr{len(main)}"
    main.append(f"    {an}:[]{at.name}({tyt(k[0])}, {tyt(k[1])}) = array{{{', '.join(o['name'] for o in os_)}}}")
    rt = k[0] if cl[3] in ('Get', 'Via') else k[1] if cl[3] in ('Snd', 'Peek') else STR
    main.append(f"    for (P : {an}):\n        Print(\"arr {cl[0]}: {{{shname(rt)}({cl[0]}(P))}}\")")
    used_callers.add(cl[0])
    if cl[5]: used_callers.add(cl[5][0])
    for o in os_:
        expect.append(f"arr {cl[0]}: {show(run_method(o, cl[3]), rt)}")

# ---------------------------------------------------------------- emit
def cls_text(c):
    out = []
    tp = f"({', '.join(p + ':type' for p in c.params)})" if c.params else ''
    if c.iface:
        return "ip(p:type, q:type) := interface:\n    Peek():q\n    Tag():string"
    if c is root:
        out.append("pair(t:type, u:type) := class(ip(t, u)):" if IFACE else "pair(t:type, u:type) := class:")
        out.append("    var A:t\n    var B:u")
        out.append("    Get():t = A\n    Snd():u = B\n    Name():string = \"pair\"\n    Put(X:t):void = set A = X")
        ov = '<override>' if IFACE else ''
        out.append(f"    Peek{ov}():u = B\n    Tag{ov}():string = \"pair\"")
        if VIA: out.append("    Via():t = Get()")
        return '\n'.join(out)
    q = classes[c.parent]
    qa = f"({', '.join(tyt(a) for a in c.pargs)})" if q.params else ''
    out.append(f"{c.name}{tp} := class({q.name}{qa}):")
    if q.iface:
        pa0 = pair_args(c, [V(p) for p in c.params])
        out.append(f"    var A:{tyt(pa0[0])}\n    var B:{tyt(pa0[1])}")
    for f, t, d, _ in c.extra:
        out.append(f"    {'var ' if False else ''}{f}:{tyt(t)}" + (f" = {d}" if d is not None else ''))
    pa = pair_args(c, [V(p) for p in c.params])
    for m, (txt, _) in c.meths.items():
        if m == 'Get': out.append(f"    Get<override>():{tyt(pa[0])} = {txt}")
        elif m == 'Snd': out.append(f"    Snd<override>():{tyt(pa[1])} = {txt}")
        elif m == 'Name': out.append(f"    Name<override>():string = {txt}")
        elif m == 'Put': out.append(f"    Put<override>(X:{tyt(pa[0])}):void = {txt}")
        elif m == 'Peek': out.append(f"    Peek<override>():{tyt(pa[1])} = {txt}")
        elif m == 'Tag': out.append(f"    Tag<override>():string = {txt}")
    if len(out) == 1: out.append(f"    Z{c.name}:int = 0")
    return '\n'.join(l for l in out if l != '')

prog = [f"# genrel seed {seed}"]
for c in order: prog.append(cls_text(c))
for cl in callers:
    if cl[0] in used_callers: prog.append(cl[4])
for t, body in SHOWN.items(): prog.append(body)
prog.append("Main():void =")
prog += main if main else ["    Print(\"none\")"]
print('\n'.join(prog))
with open(out_exp, 'w') as fh:
    fh.write("exit=0\n" + ''.join(l + '\n' for l in expect))
