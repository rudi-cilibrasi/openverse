#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the reviews of #234, #239 and #245 (choice and functions with several values, #208, #235).
"""Random programs with choices INSIDE expressions (PR #234, phase 2), and an
independent model written from docs/LANGUAGE.md's "Choice" section (not from
scripts/gen-choice.py, and not from the lifting code).

The model is a continuation-passing evaluator: operands are evaluated left to
right, as ordinary expressions are, and a choice is a choice point where it
is written. That is what "the code before a choice runs once; each
alternative then runs the rest", "spatial order" and "lifting ... in the order
they are evaluated" say, without reference to how lifting is done.

- first-success contexts (if condition, first{}, if{}, option{}, logic{},
  not, left of or): depth-first; an alternative leading to no success is
  rolled back to the state the choice was reached in; no success at all:
  everything since the context began is rolled back;
- a for / for{}: a choice is a generator; a failure rolls back to the most
  recent generator (its alternative's own clauses failed); effects of
  segments that succeeded are kept, even if later generators give nothing;
- set L op= e: L's indices, then (op=) L's old value, then e;
- comparison chains: each pair is checked as soon as both operands are
  evaluated (the choice-free order: `0 > 1 < X` never evaluates X).

PR #237 (phase 3a) adds, under the flag `bif`, an `if ... else if ... else`
whose branches are choices or plain values, anywhere a choice may be. The
model, from LANGUAGE.md and the PR text only: its conditions run where the if
is written, once, each a first-success context of its own (kept if it
succeeds, rolled back if it fails), in order; the first that succeeds picks
its branch (else the last); the if is then a choice over the picked branch's
alternatives (a choice point even when it has one, as "is itself a choice"
says), each evaluated in the state the condition left, seeing its names.

usage: gen-ex.py SEED OUTDIR [flags...]   -> OUTDIR/p.verse, OUTDIR/p.expected
flags: heavy     (with bif: more of them, longer chains, longer conditions)
       bif       (branchy ifs; without it the programs are #234's, seed for seed)
       cf        (the choice-free twin: each choice is its first alternative)
       nochain   (no choice in operand >= 2 of a comparison chain: known bug)
       noforset  (no op= / indexed set in a for)
"""
import copy
import random
import sys

seed = int(sys.argv[1])
outdir = sys.argv[2]
flags = set(sys.argv[3:])


def _skip_eager_overflow(exc_type, exc, tb):
    # (a program whose recursive values would overflow when all computed at
    # the call, #246: marked SKIP for the driver, not modelled)
    if exc_type.__name__ == 'EagerOverflow':
        open(f"{outdir}/p.verse", "w").write("Main():void = {}\n")
        open(f"{outdir}/p.expected", "w").write("SKIP overflow (not modelled; #246 for one in a value never taken)\n")
        sys.exit(0)
    sys.__excepthook__(exc_type, exc, tb)


sys.excepthook = _skip_eager_overflow
R = random.Random(seed)

PRE = '''Pos(X:int)<decides>:int =
    X > 0
    X
Even(X:int)<decides>:int =
    Mod[X, 2] = 0
    X
Tw(A:int, B:int):int = A * 10 + B
Tell(S:string, X:int):int =
    Print(S)
    X
ctr := class:
    var C:int = 0
    Next()<transacts>:int =
        set C += 1
        C - 1
    Add(X:int)<transacts>:int =
        set C += X
        C
'''


class EagerOverflow(Exception):
    """An int leaves 64-bit range: the program stops with an overflow, which
    is not modelled (where it stops, which prints a failure context keeps).
    A recursive function's values are all computed at the call (#245), so
    this also covers one in a value a first success would not reach (#246)."""


def chk(v):
    if not (-(1 << 63) <= v < (1 << 63)):
        raise EagerOverflow()
    return v


class Fail(Exception):
    pass


class St:
    def __init__(self):
        self.vars = {}
        self.binds = {}
        self.A = [0, 0, 0, 0]
        self.F = 1.0
        self.out = []

    def copy(self):
        return copy.deepcopy(self)


uid = [0]


def fresh(p):
    uid[0] += 1
    return f"{p}{uid[0]}"


def lookup(st, n):
    return st.binds[n] if n in st.binds else st.vars[n]


# ----------------------------------------------------------------- generation
# expression nodes:
#  ('lit',k) ('ref',n) ('tell',s,e) ('bprint',s,e) ('bset',v,op,k,e)
#  ('bin',op,a,b) ('tw',a,b) ('twt',a,b) ('pos',e) ('even',e) ('next',) ('add',e)
#  ('idx',[e1,e2,e3],i) ('cmp',e0,[(op,e)...]) ('choice',[alts])
#  ('optor', clauses, default) ('orx', e1, e2) ('ifx', clauses, then, else)
OPS = ['>', '<', '<>', '=', '>=', '<=']
CHAIN = [False]
NCH = [0]   # choices generated in the current test (bounded)

# ---- PR #239 (phase 3b), flag `mv`: functions with several values, inlined
# at their calls. LANGUAGE.md: "a call of it is a choice: it goes where a
# choice can go, and its values come in the callee's spatial order, at the
# call's place. Such a call is inlined: its arguments are evaluated first, in
# order, then its body runs in the caller's clauses, so the body's effects are
# rolled back or kept as the caller's are." The model inlines: a call
# evaluates its arguments left to right (CPS), binds them to the parameters,
# then runs the body's statements and value as the caller's own code, with
# every name the body binds renamed for that (dynamic) call site.
MV = 'mv' in flags
# ---- PR #245 (phase 3c), flag `rec`: effect-free recursive functions with
# several values. LANGUAGE.md: their values are computed at the call, all of
# them, in order; for finite ones that is the same as taking them one by
# one. The model is a separate list-monad evaluator (values in spatial
# order: a choice concatenates, operands combine left to right with the
# leftmost varying slowest, failure gives none), written from that text; a
# call is then a choice point over the list, in the caller's context.
REC = 'rec' in flags
RFUNCS = []
RX = {'fi': None}
FUNCS = []
CTX = {'ctrs': None, 'nofail': False, 'fmax': None, 'plim': 64}
PROD = [1]          # upper bound of the number of values (bounded)
SITE = [0]


def leaf(scope, vars_):
    k = R.random()
    if scope and k < 0.4:
        return ('ref', R.choice(scope))
    if vars_ and k < 0.55:
        return ('ref', R.choice(vars_))
    return ('lit', R.randint(-1, 5))


def gen_e(scope, vars_, d, ch):
    """an int expression; ch: whether a choice may be inside (liftably)."""
    if 'bif' in flags and ch and NCH[0] < 4 and d < 3 and R.random() < (0.4 if 'heavy' in flags else 0.14) \
            and (not MV or PROD[0] * 3 <= CTX['plim']):
        NCH[0] += 1
        if MV:
            PROD[0] *= 3
        return gen_bif(scope, vars_, d)
    if REC and ch and NCH[0] < 4 and RFUNCS and R.random() < 0.2:
        m = gen_rcall(scope, vars_, d)
        if m is not None:
            return m
    if MV and ch and NCH[0] < 4 and not CTX.get('nomcall') and FUNCS[:CTX['fmax'] if CTX['fmax'] is not None else len(FUNCS)] and R.random() < 0.25:
        m = gen_mcall(scope, vars_, d)
        if m is not None:
            return m
    k = R.random()
    if ch and NCH[0] < 4 and k < 0.22 and (not MV or PROD[0] * 3 <= CTX['plim']):
        NCH[0] += 1
        n = R.randint(2, 3)
        if MV:
            PROD[0] *= n
        alts = []
        for _ in range(n):
            if R.random() < 0.08 and d < 3:
                # a directly nested choice is spliced
                alts.append(('choice', [gen_e(scope, vars_, d + 2, False) for _ in range(2)]))
            else:
                alts.append(gen_e(scope, vars_, d + 1, False))
        return ('choice', alts)
    if d >= 3 or k < 0.32:
        return leaf(scope, vars_)
    k = R.random()
    if k < 0.10:
        return ('tell', fresh("t"), gen_e(scope, vars_, d + 1, ch))
    if k < 0.16:
        return ('bprint', fresh("p"), gen_e(scope, vars_, d + 1, False))
    if k < 0.22 and vars_:
        return ('bset', R.choice(vars_), R.choice(['=', '+=']), R.randint(-1, 7), gen_e(scope, vars_, d + 1, False))
    if k < 0.40:
        op = R.choice(['+', '-', '+', '*'])
        a = gen_e(scope, vars_, d + 1, ch)
        b = gen_e(scope, vars_, d + 1, ch) if op != '*' else ('lit', R.randint(-1, 3))
        if op == '*' and R.random() < 0.5:
            a, b = b, a
        return ('bin', op, a, b)
    if k < 0.48:
        return ('tw', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch))
    if k < 0.51:
        return ('twt', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch))
    if CTX['nofail'] and (0.51 <= k < 0.59 or 0.69 <= k < 0.83):
        return leaf(scope, vars_)     # (a body without <decides> cannot fail)
    if k < 0.59:
        return (R.choice(['pos', 'even']), gen_e(scope, vars_, d + 1, ch))
    if k < 0.64:
        if CTX['ctrs'] is not None:
            return ('cnext', R.choice(CTX['ctrs'])) if CTX['ctrs'] else leaf(scope, vars_)
        return ('next',)
    if k < 0.69:
        if CTX['ctrs'] is not None:
            return ('cadd', R.choice(CTX['ctrs']), gen_e(scope, vars_, d + 1, ch)) if CTX['ctrs'] else leaf(scope, vars_)
        return ('add', gen_e(scope, vars_, d + 1, ch))
    if k < 0.75:
        return ('idx', [gen_e(scope, vars_, d + 2, ch) for _ in range(3)], gen_e(scope, vars_, d + 2, ch))
    if k < 0.83:
        return gen_cmp(scope, vars_, d + 1, ch)
    saved = CTX['nofail']
    CTX['nofail'] = False      # (a nested failure context may fail inside)
    try:
        if k < 0.89:
            cl, _ = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True, lastval=True)
            return ('optor', cl, leaf(scope, vars_))
        if k < 0.94:
            return ('orx', gen_e(scope, vars_, d + 1, True), leaf(scope, vars_))
        cl, sc2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
        cl.append(failable(sc2, vars_))
        return ('ifx', cl, leaf(sc2, vars_), leaf(scope, vars_))
    finally:
        CTX['nofail'] = saved


def gen_rcall(scope, vars_, d):
    cands = [(i, n) for i in range(len(RFUNCS)) for n in range(0, 4)
             if rub(i, n) * PROD[0] <= CTX['plim'] and rub(i, n) >= 1
             and not (CTX['nofail'] and RFUNCS[i]['decides'])]
    if not cands:
        return None
    i, n = R.choice(cands)
    NCH[0] += 1
    PROD[0] *= rub(i, n)
    # (known bug: a choice or a call with several values in the argument of a
    # recursive one is refused or miscompiled; flag argbug keeps them)
    if True:
        return ('rcall', i, n, gen_e(scope, vars_, d + 1, True))
    # (known bugs: a failing argument of a recursive call loses the other
    # alternatives in a body, and keeps the effects before it in a for)
    saved = CTX['nofail']
    CTX['nofail'] = True
    try:
        return ('rcall', i, n, gen_e(scope, vars_, d + 1, False))
    finally:
        CTX['nofail'] = saved


# the bodies of recursive functions: effect-free expressions over N, A, Y
def rleaf(sc):
    return ('ref', R.choice(sc)) if R.random() < 0.6 else ('lit', R.randint(-1, 4))


def gen_rx(sc, d, fi, dec):
    k = R.random()
    if d >= 2 or k < 0.35:
        return rleaf(sc)
    if k < 0.6:
        return ('bin', R.choice(['+', '-', '*']), gen_rx(sc, d + 1, fi, dec), gen_rx(sc, d + 1, fi, dec))
    if k < 0.72:
        return ('ctw', gen_rx(sc, d + 1, fi, dec), gen_rx(sc, d + 1, fi, dec))
    if k < 0.82 and dec and not RX.get('inarg'):
        return ('cpos', gen_rx(sc, d + 1, fi, dec))
    if k < 0.9 and dec and not RX.get('inarg'):
        return ('cmpf', gen_rx(sc, d + 1, fi, dec), R.choice(OPS), gen_rx(sc, d + 1, fi, dec))
    js = [j for j in range(fi) if dec or not RFUNCS[j]['decides']]
    if js and R.random() < 0.5 and not RX.get('inarg'):
        j = R.choice(js)
        return ('rrec', j, gen_rarg(sc, d + 1, fi, dec))
    return rleaf(sc)


def gen_rarg(sc, d, fi, dec):
    if True:
        return gen_rx(sc, d, fi, dec)
    RX['inarg'] = True
    try:
        return gen_rx(sc, d, fi, dec)
    finally:
        RX['inarg'] = False


def gen_ralts(sc, fi, dec):
    alts = [gen_rx(sc, 1, fi, dec) for _ in range(R.randint(1, 2))]
    for _ in range(R.choice([1, 1, 2])):
        alts.insert(R.randint(0, len(alts)), ('rrec', fi, gen_rarg(sc, 1, fi, dec)))
    return alts


def gen_rfunc(fi):
    dec = R.random() < 0.7
    f = {'name': f"Rq{fi}", 'decides': dec, 'lo': R.choice([0, 1]), 'locals': [], 'shape': None}
    sc = ['N', 'A']
    if dec:
        if R.random() < 0.4:
            f['locals'].append(('Y', gen_rx(sc, 1, fi, dec)))
            sc = sc + ['Y']
        alts = gen_ralts(sc, fi, dec)
        if R.random() < 0.6:
            f['shape'] = ('plain', alts)
        else:
            f['shape'] = ('operand', R.choice(['+', '*', '-']), gen_rx(sc, 1, fi, dec), alts, R.random() < 0.5)
    else:
        f['shape'] = ('branchy', gen_rx(sc, 1, fi, dec), gen_ralts(sc, fi, dec))
    return f


def show_rx(e, f):
    t = e[0]
    if t == 'lit':
        return str(e[1])
    if t == 'ref':
        return e[1]
    if t == 'bin':
        return f"({show_rx(e[2], f)} {e[1]} {show_rx(e[3], f)})"
    if t == 'ctw':
        return f"CTw({show_rx(e[1], f)}, {show_rx(e[2], f)})"
    if t == 'cpos':
        return f"CPos[{show_rx(e[1], f)}]"
    if t == 'cmpf':
        return f"({show_rx(e[1], f)} {e[2]} {show_rx(e[3], f)})"
    if t == 'rrec':
        g = RFUNCS[e[1]] if e[1] < len(RFUNCS) else f
        a = show_rx(e[2], f)
        return f"{g['name']}[N - 1, {a}]" if g['decides'] else f"{g['name']}(N - 1, {a})"
    raise AssertionError(e)


def show_ralts(alts, f):
    if 'cf' in flags:
        return "(" + show_rx(alts[0], f) + ")"
    return "(" + " | ".join(show_rx(a, f) for a in alts) + ")"


def show_rfunc(f):
    if f['decides']:
        L = [f"{f['name']}(N:int, A:int)<computes><decides>:int =", f"    N >= {f['lo']}"]
        L += [f"    {x} := {show_rx(e, f)}" for x, e in f['locals']]
        sh = f['shape']
        if sh[0] == 'plain':
            L.append("    " + show_ralts(sh[1], f))
        else:
            o, x, alts, left = sh[1], show_rx(sh[2], f), show_ralts(sh[3], f), sh[4]
            L.append(f"    {alts} {o} {x}" if left else f"    {x} {o} {alts}")
        return L
    base, alts = f['shape'][1], f['shape'][2]
    return [f"{f['name']}(N:int, A:int)<computes>:int = if (N <= {f['lo']}) then {show_rx(base, f)} else {show_ralts(alts, f)}"]


def rvals(e, env, f):
    """the values of e, in order (list monad)."""
    t = e[0]
    if t == 'lit':
        return [e[1]]
    if t == 'ref':
        return [env[e[1]]]
    if t in ('bin', 'ctw'):
        a, b = (e[2], e[3]) if t == 'bin' else (e[1], e[2])
        out = []
        for x in rvals(a, env, f):
            for y in rvals(b, env, f):
                out.append(chk(x * 10 + y if t == 'ctw' else {'+': x + y, '-': x - y, '*': x * y}[e[1]]))
        return out
    if t == 'cpos':
        return [x for x in rvals(e[1], env, f) if x > 0]
    if t == 'cmpf':
        return [x for x in rvals(e[1], env, f) for y in rvals(e[3], env, f) if cmpf(x, e[2], y)]
    if t == 'rrec':
        return [v for av in rvals(e[2], env, f) for v in rcall_vals(e[1] if e[1] < len(RFUNCS) else f['idx'], env['N'] - 1, av)]
    raise AssertionError(e)


def ralts_vals(alts, env, f):
    if 'cf' in flags:
        alts = alts[:1]
    return [v for a in alts for v in rvals(a, env, f)]


RMEMO = {}


def rcall_vals(fi, n, a):
    key = (fi, n, a)
    if key in RMEMO:
        return RMEMO[key]
    f = RFUNCS[fi]
    env = {'N': n, 'A': a}
    out = []
    if f['decides']:
        if n >= f['lo']:
            envs = [env]
            for x, e in f['locals']:
                envs = [dict(en, **{x: v}) for en in envs for v in rvals(e, en, f)]
            sh = f['shape']
            for en in envs:
                if sh[0] == 'plain':
                    out += ralts_vals(sh[1], en, f)
                else:
                    o, xe, alts, left = sh[1], sh[2], sh[3], sh[4]
                    ops = {'+': lambda p, q: p + q, '*': lambda p, q: p * q, '-': lambda p, q: p - q}[o]
                    if left:
                        out += [chk(ops(p, q)) for p in ralts_vals(alts, en, f) for q in rvals(xe, en, f)]
                    else:
                        out += [chk(ops(p, q)) for p in rvals(xe, en, f) for q in ralts_vals(alts, en, f)]
    else:
        out = rvals(f['shape'][1], env, f) if n <= f['lo'] else ralts_vals(f['shape'][2], env, f)
    RMEMO[key] = out
    return out


def rub_e(e, n, f):
    t = e[0]
    if t in ('lit', 'ref'):
        return 1
    if t in ('bin', 'ctw', 'cmpf'):
        return rub_e(e[2] if t == 'bin' else e[1], n, f) * rub_e(e[3] if t in ('bin', 'cmpf') else e[2], n, f)
    if t == 'cpos':
        return rub_e(e[1], n, f)
    if t == 'rrec':
        return rub_e(e[2], n, f) * rub(e[1] if e[1] < len(RFUNCS) else f['idx'], n - 1)
    raise AssertionError(e)


RUB = {}


def rub(fi, n):
    """an upper bound of the number of values of R_fi with N = n."""
    if (fi, n) in RUB:
        return RUB[(fi, n)]
    f = RFUNCS[fi]
    if n < -1:
        return 0
    if f['decides']:
        if n < f['lo']:
            u = 0
        else:
            u = 1
            for _, e in f['locals']:
                u *= rub_e(e, n, f)
            sh = f['shape']
            alts = sh[1] if sh[0] == 'plain' else sh[3]
            a = sum(rub_e(x, n, f) for x in (alts[:1] if 'cf' in flags else alts))
            u *= a * (1 if sh[0] == 'plain' else rub_e(sh[2], n, f))
    else:
        if n <= f['lo']:
            u = rub_e(f['shape'][1], n, f)
        else:
            alts = f['shape'][2]
            u = sum(rub_e(x, n, f) for x in (alts[:1] if 'cf' in flags else alts))
    RUB[(fi, n)] = u
    return u


def gen_mcall(scope, vars_, d):
    lim = CTX['fmax'] if CTX['fmax'] is not None else len(FUNCS)
    cands = [i for i in range(lim)
             if FUNCS[i]['count'] * PROD[0] <= CTX['plim']
             and not (CTX['nofail'] and FUNCS[i]['decides'])
             and not (CTX['ctrs'] is not None and not CTX['ctrs'] and FUNCS[i]['nctr'])]
    if not cands:
        return None
    fi = R.choice(cands)
    f = FUNCS[fi]
    NCH[0] += 1
    PROD[0] *= f['count']
    args = []
    for _, t in f['params']:
        if t == 'ctr':
            args.append(('obj', R.choice(['K', 'J'])) if CTX['ctrs'] is None else ('ref', R.choice(CTX['ctrs'])))
        else:
            args.append(gen_e(scope, vars_, d + 1, True))
    SITE[0] += 1
    return ('mcall', fi, args, f"s{SITE[0]}")


def gen_alts(scope, vars_, d):
    return [gen_e(scope, vars_, d + 1, False) for _ in range(R.choice([1, 2, 2, 3]))]


def gen_bif(scope, vars_, d):
    arms = []
    for _ in range(R.choice([1, 1, 2, 3, 4] if 'heavy' in flags else [1, 1, 2, 3])):
        saved = CTX['nofail']
        CTX['nofail'] = False
        cl, sc2 = gen_clauses(list(scope), vars_, d + 1, R.randint(0, 3 if 'heavy' in flags else 2), allow_gen=False, inner=True)
        CTX['nofail'] = saved
        cl.append(failable(sc2, vars_))
        arms.append((cl, gen_alts(sc2, vars_, d)))
    els = gen_alts(scope, vars_, d)
    if all(len(a) == 1 for _, a in arms) and len(els) == 1:
        els.append(gen_e(scope, vars_, d + 1, False))
    return ('bif', arms, els, R.random() < 0.5)


def gen_cmp(scope, vars_, d, ch):
    if CTX['fmax'] is not None and 'cmpbug' not in flags:
        # (known bug: a call of a function with several values in a comparison
        # in a function's statement hangs the compiler; flag cmpbug keeps it)
        saved = CTX.get('nomcall', False)
        CTX['nomcall'] = True
        try:
            return gen_cmp0(scope, vars_, d, ch)
        finally:
            CTX['nomcall'] = saved
    return gen_cmp0(scope, vars_, d, ch)


def gen_cmp0(scope, vars_, d, ch):
    n = R.choice([1, 1, 1, 2])
    e0 = gen_e(scope, vars_, d + 1, ch)
    rest = []
    for i in range(n):
        c2 = ch and not ('nochain' in flags and i >= 1)
        x = gen_e(scope, vars_, d + 1, c2)
        if i >= 1 and top_choice_e(x):
            CHAIN[0] = True
        rest.append((R.choice(OPS), x))
    return ('cmp', e0, rest)


def show(e):
    t = e[0]
    if t == 'lit':
        return str(e[1])
    if t == 'ref':
        return e[1]
    if t == 'tell':
        return f'Tell("{e[1]}", {show(e[2])})'
    if t == 'bprint':
        return f'(Print("{e[1]}"); {show(e[2])})'
    if t == 'bset':
        return f'(set {e[1]} {e[2]} {e[3]}; {show(e[4])})'
    if t == 'bin':
        return f'({show(e[2])} {e[1]} {show(e[3])})'
    if t == 'tw':
        return f'Tw({show(e[1])}, {show(e[2])})'
    if t == 'twt':
        return f'Tw(({show(e[1])}, {show(e[2])}))'
    if t == 'pos':
        return f'Pos[{show(e[1])}]'
    if t == 'even':
        return f'Even[{show(e[1])}]'
    if t == 'next':
        return 'K.Next()'
    if t == 'add':
        return f'K.Add({show(e[1])})'
    if t == 'idx':
        return 'array{' + ", ".join(show(x) for x in e[1]) + '}[' + show(e[2]) + ']'
    if t == 'cmp':
        return '(' + show(e[1]) + "".join(f' {op} {show(x)}' for op, x in e[2]) + ')'
    if t == 'choice':
        if 'cf' in flags:
            return '(' + show(alts_of(e)[0]) + ')'
        return '(' + " | ".join(show(a) for a in e[1]) + ')'
    if t == 'optor':
        return f'(option{{{show_cl(e[1], "; ")}}}? or {show(e[2])})'
    if t == 'orx':
        return f'({show(e[1])} or {show(e[2])})'
    if t == 'ifx':
        return f'(if ({show_cl(e[1], ", ")}) then {show(e[2])} else {show(e[3])})'
    if t == 'rcall':
        f = RFUNCS[e[1]]
        return f"{f['name']}[{e[2]}, {show(e[3])}]" if f['decides'] else f"{f['name']}({e[2]}, {show(e[3])})"
    if t == 'mcall':
        f = FUNCS[e[1]]
        a = ", ".join(show(x) for x in e[2])
        return f"{f['name']}[{a}]" if f['decides'] else f"{f['name']}({a})"
    if t == 'obj':
        return e[1]
    if t == 'cnext':
        return f"{e[1]}.Next()"
    if t == 'cadd':
        return f"{e[1]}.Add({show(e[2])})"
    if t == 'bif':
        out = ''
        for i, (cl, alts) in enumerate(e[1]):
            out += ('if' if i == 0 else ' else if') + f' ({show_cl(cl, ", ")}) then {show_alts(alts)}'
        return '(' + out + f' else {show_alts(e[2])})'
    raise AssertionError(e)


def show_alts(alts):
    if 'cf' in flags or len(alts) == 1:
        return '(' + show(alts[0]) + ')'
    return '(' + " | ".join(show(a) for a in alts) + ')'


def alts_of(e):
    if 'cf' in flags:   # the choice-free twin: each choice is its first alternative
        a = e[1][0]
        return alts_of(a) if a[0] == 'choice' else [a]
    out = []
    for a in e[1]:
        out += alts_of(a) if a[0] == 'choice' else [a]
    return out


# clause nodes:
#  ('bind',x,e) ('sbind',x,[e1,e2]) ('filter',cmp) ('setv',v,op,e) ('seti',op,e)
#  ('setf',e) ('print',s) ('range',x,lo,hi) ('not',clauses) ('logic',clauses)
def gen_clauses(scope, vars_, d, n, allow_gen, inner=False, lastval=False, isfor=False):
    cl = []
    for i in range(n):
        k = R.random()
        last = lastval and i == n - 1
        if k < 0.33 or last:
            if last and R.random() < 0.4 and scope:
                cl.append(('filter', gen_cmp(scope, vars_, d, True)))
            else:
                x = fresh("X")
                cl.append(('bind', x, gen_e(scope, vars_, d, True)))
                scope = scope + [x]
        elif k < 0.38 and not inner:
            x = fresh("S")
            cl.append(('sbind', x, [gen_e(scope, vars_, d + 1, True) for _ in range(2)]))
        elif k < 0.55:
            cl.append(('filter', gen_cmp(scope, vars_, d, True)))
        elif k < 0.64 and vars_:
            op = '=' if (isfor and 'noforset' in flags) else R.choice(['=', '+=', '*='])
            cl.append(('setv', R.choice(vars_), op, gen_e(scope, vars_, d, True)))
        elif k < 0.69 and not inner:
            op = '=' if (isfor and 'noforset' in flags) else R.choice(['=', '+='])
            if not (isfor and 'noforset' in flags):
                cl.append(('seti', op, gen_e(scope, vars_, d, True)))
        elif k < 0.73 and not inner and not (isfor and 'noforset' in flags):
            cl.append(('setf', gen_e(scope, vars_, d + 1, True)))
        elif k < 0.79:
            cl.append(('print', fresh("c")))
        elif k < 0.85 and not inner:
            c2, s2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
            cl.append(('not', c2 + [failable(s2, vars_)]))
        elif k < 0.90 and not inner:
            c2, s2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
            cl.append(('logic', c2 + [failable(s2, vars_)]))
        elif allow_gen:
            x = fresh("R")
            lo = R.randint(0, 2)
            cl.append(('range', x, lo, lo + R.randint(0, 2)))
            scope = scope + [x]
        else:
            cl.append(('print', fresh("c")))
    return cl, scope


def failable(scope, vars_):
    return ('filter', ('cmp', leaf(scope, vars_), [(R.choice(OPS), leaf(scope, vars_))]))


def top_choice_e(e):
    t = e[0]
    if t in ('choice', 'bif', 'mcall', 'rcall'):
        return True
    if t in ('lit', 'ref', 'next', 'bprint', 'bset', 'optor', 'orx', 'ifx', 'obj', 'cnext'):
        return False
    if t == 'cadd':
        return top_choice_e(e[2])
    if t in ('tell', 'pos', 'even', 'add'):
        return top_choice_e(e[-1])
    if t == 'bin':
        return top_choice_e(e[2]) or top_choice_e(e[3])
    if t in ('tw', 'twt'):
        return top_choice_e(e[1]) or top_choice_e(e[2])
    if t == 'idx':
        return any(top_choice_e(x) for x in e[1]) or top_choice_e(e[2])
    if t == 'cmp':
        return top_choice_e(e[1]) or any(top_choice_e(x) for _, x in e[2])
    raise AssertionError(e)


def top_choice_c(c):
    t = c[0]
    if t == 'bind':
        return top_choice_e(c[2])
    if t == 'sbind':
        return any(top_choice_e(x) for x in c[2])
    if t == 'filter':
        return top_choice_e(c[1])
    if t == 'setv':
        return top_choice_e(c[3])
    if t in ('seti', 'setf'):
        return top_choice_e(c[-1])
    return False


def show_c(c):
    t = c[0]
    if t == 'bind':
        e = c[2]
        if e[0] == 'bif' and e[3]:
            return f"{c[1]} := " + show(e)[1:-1]
        return f"{c[1]} := " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'sbind':
        return f'{c[1]} := "<{{{show(c[2][0])}}}-{{{show(c[2][1])}}}>"'
    if t == 'filter':
        s = show(c[1])
        return s[1:-1]
    if t == 'setv':
        e = c[3]
        return f"set {c[1]} {c[2]} " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'seti':
        e = c[2]
        return f"set A[Mod[J.Next(), 4]] {c[1]} " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'setf':
        e = c[1]
        return "set F *= " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'print':
        return f'Print("{c[1]}")'
    if t == 'range':
        return f"{c[1]} := {c[2]}..{c[3]}"
    if t == 'not':
        return f"not ({show_cl(c[1], '; ')})"
    if t == 'logic':
        return f"logic{{{show_cl(c[1], '; ')}}}?"
    raise AssertionError(c)


def show_cl(cl, sep):
    return sep.join(show_c(c) for c in cl)


# ---------------------------------------------------------------- the model
def choice_point(thunks, st, k, mode):
    """thunks: f(s, k) for each alternative, in spatial order."""
    if mode == 'first':
        for th in thunks:
            s1 = st.copy()
            try:
                return th(s1, k)
            except Fail:
                continue
        raise Fail()
    cur = st
    for th in thunks:
        s1 = cur.copy()
        try:
            cur = th(s1, k)
        except Fail:
            pass
    return cur


def first_inner(run, st):
    """a nested first-success context: (value, state) or None; st untouched."""
    s0 = st.copy()
    try:
        return run(s0, lambda v, s: (v, s))
    except Fail:
        return None


def cmpf(a, op, b):
    return {'>': a > b, '<': a < b, '<>': a != b, '=': a == b, '>=': a >= b, '<=': a <= b}[op]


def ev(e, st, k, mode):
    t = e[0]
    if t == 'lit':
        return k(e[1], st)
    if t == 'ref':
        return k(lookup(st, e[1]), st)
    if t == 'tell':
        def k2(v, s):
            s.out.append(e[1])
            return k(v, s)
        return ev(e[2], st, k2, mode)
    if t == 'bprint':
        st.out.append(e[1])
        return ev(e[2], st, k, mode)
    if t == 'bset':
        st.vars[e[1]] = e[3] if e[2] == '=' else chk(st.vars[e[1]] + e[3])
        return ev(e[4], st, k, mode)
    if t in ('bin', 'tw', 'twt'):
        a, b = (e[2], e[3]) if t == 'bin' else (e[1], e[2])

        def ka(va, s1):
            def kb(vb, s2):
                if t != 'bin':
                    return k(chk(va * 10 + vb), s2)
                return k(chk({'+': va + vb, '-': va - vb, '*': va * vb}[e[1]]), s2)
            return ev(b, s1, kb, mode)
        return ev(a, st, ka, mode)
    if t in ('pos', 'even'):
        def kp(v, s):
            if (v > 0) if t == 'pos' else (v % 2 == 0):
                return k(v, s)
            raise Fail()
        return ev(e[1], st, kp, mode)
    if t == 'next':
        v = st.vars['K.C']
        st.vars['K.C'] += 1
        return k(v, st)
    if t == 'add':
        def kadd(v, s):
            s.vars['K.C'] = chk(s.vars['K.C'] + v)
            return k(s.vars['K.C'], s)
        return ev(e[1], st, kadd, mode)
    if t == 'idx':
        elems = e[1] + [e[2]]

        def go(i, acc, s):
            if i == len(elems):
                j = acc[-1]
                if 0 <= j < 3:
                    return k(acc[j], s)
                raise Fail()
            return ev(elems[i], s, lambda v, s2: go(i + 1, acc + [v], s2), mode)
        return go(0, [], st)
    if t == 'cmp':
        def go(i, prev, first, s):
            if i == len(e[2]):
                return k(first, s)
            op, x = e[2][i]

            def kc(v, s2):
                if not cmpf(prev, op, v):
                    raise Fail()
                return go(i + 1, v, first, s2)
            return ev(x, s, kc, mode)
        return ev(e[1], st, lambda v0, s: go(0, v0, v0, s), mode)
    if t == 'obj':
        return k(e[1], st)
    if t == 'cnext':
        o = lookup(st, e[1]) + '.C'
        v = st.vars[o]
        st.vars[o] += 1
        return k(v, st)
    if t == 'cadd':
        o = lookup(st, e[1]) + '.C'

        def kca(v, s):
            s.vars[o] = chk(s.vars[o] + v)
            return k(s.vars[o], s)
        return ev(e[2], st, kca, mode)
    if t == 'rcall':
        def krc(av, s):
            vs = rcall_vals(e[1], e[2], av)
            if 'cf' in flags:
                if not vs:
                    raise Fail()
                return k(vs[0], s)
            return choice_point([(lambda s2, k2, v=v: k2(v, s2)) for v in vs], s, k, mode)
        return ev(e[3], st, krc, mode)
    if t == 'mcall':
        body = inst(e[1], e[3])
        args = e[2]

        def go(i, vals, s):
            if i == len(args):
                for p, v in zip(body['params'], vals):
                    s.binds[p] = v
                return run_body(body['stmts'], body['val'], s, k, mode)
            return ev(args[i], s, lambda v, s2: go(i + 1, vals + [v], s2), mode)
        return go(0, [], st)
    if t == 'choice' and 'cf' in flags:
        return ev(alts_of(e)[0], st, k, mode)
    if t == 'choice':
        return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in alts_of(e)], st, k, mode)
    if t == 'optor':
        res = first_inner(lambda s, kk: run_clauses(e[1], s, lambda s2: kk(clause_value(e[1], s2), s2), 'first'), st)
        if res is not None:
            return k(res[0], res[1])
        return ev(e[2], st, k, mode)
    if t == 'orx':
        res = first_inner(lambda s, kk: ev(e[1], s, kk, 'first'), st)
        if res is not None:
            return k(res[0], res[1])
        return ev(e[2], st, k, mode)
    if t == 'bif':
        for cl, alts in e[1]:
            res = first_inner(lambda s, kk, cl=cl: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
            if res is not None:
                return bif_alts(alts, res[1], k, mode)
        return bif_alts(e[2], st, k, mode)
    if t == 'ifx':
        res = first_inner(lambda s, kk: run_clauses(e[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            return ev(e[2], res[1], k, mode)
        return ev(e[3], st, k, mode)
    raise AssertionError(e)


def binders_of(x, acc):
    """every name a callee's body binds (parameters aside)."""
    if isinstance(x, tuple):
        if x and x[0] in ('bind', 'sbind', 'range', 'slet', 'svar') and isinstance(x[1], str):
            acc.add(x[1])
        for y in x:
            binders_of(y, acc)
    elif isinstance(x, list):
        for y in x:
            binders_of(y, acc)
    return acc


def rename(x, own, site):
    if isinstance(x, list):
        return [rename(y, own, site) for y in x]
    if not isinstance(x, tuple) or not x:
        return x
    if not isinstance(x[0], str):
        return tuple(rename(y, own, site) for y in x)
    t = x[0]
    if t == 'mcall':
        return ('mcall', x[1], rename(x[2], own, site), f"{site}/{x[3]}")
    if t in ('ref', 'cnext', 'snext', 'bind', 'sbind', 'range', 'slet', 'svar', 'sset', 'bset', 'cadd', 'setv') and isinstance(x[1], str) and x[1] in own:
        return (t, f"{site}.{x[1]}") + tuple(rename(y, own, site) for y in x[2:])
    return (t,) + tuple(rename(y, own, site) for y in x[1:])


INST = {}


def inst(fi, site):
    """the body of FUNCS[fi] for the call site `site`: its names renamed."""
    key = (fi, site)
    if key not in INST:
        f = FUNCS[fi]
        own = set(p for p, _ in f['params']) | binders_of(f['stmts'], set()) | binders_of(f['val'], set())
        INST[key] = {'params': [f"{site}.{p}" for p, _ in f['params']],
                     'stmts': rename(f['stmts'], own, site), 'val': rename(f['val'], own, site)}
    return INST[key]


def run_body(stmts, val, st, k, mode):
    if not stmts:
        return ev(val, st, k, mode)
    c = stmts[0]

    def nxt(s):
        return run_body(stmts[1:], val, s, k, mode)
    t = c[0]
    if t == 'sprint':
        st.out.append(c[1])
        return nxt(st)
    if t == 'slet':
        def kl(v, s):
            s.binds[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kl, mode)
    if t == 'svar':
        def kv(v, s):
            s.vars[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kv, mode)
    if t == 'sset':
        old = st.vars[c[1]]

        def kss(x, s):
            s.vars[c[1]] = x if c[2] == '=' else chk(old + x)
            return nxt(s)
        return ev(c[3], st, kss, mode)
    if t == 'sfilt':
        return ev(c[1], st, lambda _, s: nxt(s), mode)
    if t == 'snext':
        o = lookup(st, c[1]) + '.C'
        st.vars[o] += 1
        return nxt(st)
    raise AssertionError(c)


def bif_alts(alts, st, k, mode):
    if 'cf' in flags:
        return ev(alts[0], st, k, mode)
    return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in alts], st, k, mode)


def clause_value(cl, s):
    c = cl[-1]
    if c[0] == 'bind':
        return s.binds[c[1]]
    if c[0] == 'filter':
        return s.binds['$last']
    raise AssertionError(c)


def run_clauses(cl, st, k, mode):
    """k(state) after the last clause; returns what k returns."""
    if not cl:
        return k(st)
    c = cl[0]

    def nxt(s):
        return run_clauses(cl[1:], s, k, mode)
    t = c[0]
    if t == 'bind':
        def kb(v, s):
            s.binds[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kb, mode)
    if t == 'sbind':
        def ka(va, s1):
            def kb2(vb, s2):
                s2.binds[c[1]] = f"<{va}-{vb}>"
                return nxt(s2)
            return ev(c[2][1], s1, kb2, mode)
        return ev(c[2][0], st, ka, mode)
    if t == 'filter':
        def kf(v, s):
            s.binds['$last'] = v
            return nxt(s)
        return ev(c[1], st, kf, mode)
    if t == 'setv':
        v, op = c[1], c[2]
        old = st.vars[v]

        def ks(x, s):
            s.vars[v] = x if op == '=' else chk(old + x if op == '+=' else old * x)
            return nxt(s)
        return ev(c[3], st, ks, mode)
    if t == 'seti':
        op = c[1]
        i = st.vars['J.C'] % 4
        st.vars['J.C'] += 1
        old = st.A[i]

        def ksi(x, s):
            s.A[i] = x if op == '=' else chk(old + x)
            return nxt(s)
        return ev(c[2], st, ksi, mode)
    if t == 'setf':
        old = st.F

        def ksf(x, s):
            s.F = old * x
            return nxt(s)
        return ev(c[1], st, ksf, mode)
    if t == 'print':
        st.out.append(c[1])
        return nxt(st)
    if t == 'range':
        def mk(v):
            def th(s, k2):
                s.binds[c[1]] = v
                return k2(None, s)
            return th
        return choice_point([mk(v) for v in range(c[2], c[3] + 1)], st, lambda _, s: nxt(s), mode)
    if t == 'not':
        res = first_inner(lambda s, kk: run_clauses(c[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            raise Fail()
        return nxt(st)
    if t == 'logic':
        res = first_inner(lambda s, kk: run_clauses(c[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is None:
            raise Fail()
        return nxt(res[1])
    raise AssertionError(c)


def fmt_float(f):
    # (openverse floats have no negative zero: LANGUAGE.md, float)
    r = repr(float(f) + 0.0)
    return r


# ---------------------------------------------------------------- programs
POOL = ['Y', 'Q', 'K', 'J', 'A', 'F', 'N0a', 'N1b', 'V', 'W', 'Z', 'X', 'B', 'S', 'O', 'Lg']


def top_choice_s(c):
    t = c[0]
    if t in ('slet', 'svar'):
        return top_choice_e(c[2])
    if t == 'sset':
        return top_choice_e(c[3])
    if t == 'sfilt':
        return top_choice_e(c[1])
    return False


def show_s(c):
    t = c[0]
    if t == 'sprint':
        return f'Print("{c[1]}")'
    if t == 'slet':
        return f"{c[1]} := {show(c[2])}"
    if t == 'svar':
        return f"var {c[1]}:int = {show(c[2])}"
    if t == 'sset':
        return f"set {c[1]} {c[2]} {show(c[3])}"
    if t == 'sfilt':
        return show(c[1])[1:-1]
    if t == 'snext':
        return f"{c[1]}.Next()"
    raise AssertionError(c)


def gen_func(i):
    decides = R.random() < 0.3
    names = R.sample(POOL, len(POOL))
    params = [(names.pop(), 'int') for _ in range(R.randint(0, 2))]
    if R.random() < 0.3:
        params.insert(R.randint(0, len(params)), (names.pop(), 'ctr'))
    ctrs = [p for p, t in params if t == 'ctr']
    CTX.update(ctrs=ctrs, nofail=not decides, fmax=i, plim=12)
    NCH[0] = 0
    PROD[0] = 1
    scope = [p for p, t in params if t == 'int']
    vars_ = []
    stmts = []
    for _ in range(R.randint(0, 3)):
        k = R.random()
        if k < 0.2:
            stmts.append(('sprint', fresh("m")))
        elif k < 0.5:
            x = names.pop()
            stmts.append(('slet', x, gen_e(scope, vars_, 1, True)))
            scope = scope + [x]
        elif k < 0.65:
            v = names.pop()
            stmts.append(('svar', v, gen_e(scope, vars_, 1, True)))
            vars_ = vars_ + [v]
        elif k < 0.8 and vars_:
            stmts.append(('sset', R.choice(vars_), R.choice(['=', '+=']), gen_e(scope, vars_, 1, True)))
        elif k < 0.9 and decides and scope:
            stmts.append(('sfilt', gen_cmp(scope, vars_, 1, True)))
        elif ctrs:
            stmts.append(('snext', R.choice(ctrs)))
        else:
            stmts.append(('sprint', fresh("m")))
    val = gen_e(scope, vars_, 1, True)
    if not (any(top_choice_s(c) for c in stmts) or top_choice_e(val)):
        val = ('bin', '+', val, ('choice', [('lit', R.randint(0, 3)), leaf(scope, vars_)]))
        PROD[0] *= 2
    f = {'name': f"M{i}", 'params': params, 'decides': decides, 'stmts': stmts, 'val': val,
         'count': PROD[0], 'nctr': len(ctrs)}
    CTX.update(ctrs=None, nofail=False, fmax=None, plim=64)
    return f


def show_func(f):
    ps = ", ".join(f"{p}:{t}" for p, t in f['params'])
    L = [f"{f['name']}({ps}){'<decides>' if f['decides'] else ''}:int ="]
    L += ["    " + show_s(c) for c in f['stmts']]
    L.append("    " + show(f['val']))
    return L


lines = []
out = []
tests = []
if REC:
    lines += ["CTw(A:int, B:int)<computes>:int = A * 10 + B",
              "CPos(X:int)<computes><decides>:int =", "    X > 0", "    X"]
    for i in range(R.randint(1, 3)):
        f = gen_rfunc(i)
        f['idx'] = i
        RFUNCS.append(f)
        RUB.clear()
        if rub(i, 3) > 200:   # (keep the arrays small)
            pass
    for f in RFUNCS:
        lines += show_rfunc(f)
if MV:
    for i in range(R.randint(1, 4)):
        FUNCS.append(gen_func(i))
    for f in FUNCS:
        lines += show_func(f)
NT = R.randint(2, 5)
for ti in range(NT):
    name = f"T{ti}"
    NCH[0] = 0
    PROD[0] = 1
    vars_ = [f"N{ti}a", f"N{ti}b"]
    st = St()
    st.vars = {v: 0 for v in vars_}
    st.vars['K.C'] = 0
    st.vars['J.C'] = 0
    L = [f"{name}():void ="]
    for v in vars_:
        L.append(f"    var {v}:int = 0")
    L.append("    K := ctr{}")
    L.append("    J := ctr{}")
    L.append("    var A:[]int = array{0, 0, 0, 0}")
    L.append("    var F:float = 1.0")
    kind = R.choice(['if', 'if', 'for', 'for', 'first', 'formacro', 'ifmacro', 'option', 'logic', 'not', 'or'])
    isfor = kind in ('for', 'formacro')
    n = R.randint(1, 4)
    lastval = kind in ('first', 'formacro', 'ifmacro', 'option', 'or')
    cl, scope = gen_clauses([], vars_, 0, n, allow_gen=isfor, lastval=lastval, isfor=isfor)
    if kind not in ('for', 'formacro', 'option'):
        cl.append(('filter', ('cmp', leaf(scope, vars_), [(R.choice(OPS), leaf(scope, vars_))])))
    if not any(top_choice_c(c) for c in cl):
        # make sure there is a choice inside an expression, lifted at the top
        x = fresh("X")
        e = ('bin', '+', ('tell', fresh("t"), leaf([], vars_)), ('choice', [('lit', 1), ('lit', 2)]))
        cl.insert(0, ('bind', x, e))
        scope = [x] + scope
    show_state = ('Print("st {' + vars_[0] + '} {' + vars_[1] + '} {K.C} {J.C} '
                  '{A[0] or 9}{A[1] or 9}{A[2] or 9}{A[3] or 9} {F}")')

    def state_line(s):
        return (f"st {s.vars[vars_[0]]} {s.vars[vars_[1]]} {s.vars['K.C']} {s.vars['J.C']} "
                + "".join(str(x) for x in s.A) + " " + fmt_float(s.F))
    binds = [c[1] for c in cl if c[0] in ('bind', 'range', 'sbind')]
    vals_str = " ".join("{" + b + "}" for b in binds)

    def vals(s):
        return " ".join(str(s.binds[b]) for b in binds)
    tout = []
    body_first = lambda s2: s2
    if kind == 'if':
        L.append(f"    if ({show_cl(cl, ', ')}):")
        L.append(f'        Print("then {vals_str}")')
        L.append("    else:")
        L.append('        Print("else")')
        res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            st = res[1]
            st.out.append(f"then {vals(st)}")
        else:
            st.out.append("else")
    elif kind in ('first', 'ifmacro', 'option', 'or'):
        body = show_cl(cl, '; ')
        if kind == 'first':
            L.append(f'    if (V := first{{{body}}}) then Print("first {{V}}") else Print("none")')
        elif kind == 'ifmacro':
            L.append(f'    V := if{{{body}}} else -7')
            L.append('    Print("v {V}")')
        elif kind == 'option':
            L.append(f'    O := option{{{body}}}')
            L.append('    if (V := O?) then Print("o {V}") else Print("o none")')
        else:
            L.append(f'    W := ({body}) or -7')
            L.append('    Print("w {W}")')
        res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(clause_value(cl, s2), s2), 'first'), st)
        if res is not None:
            v, st = res
            st.out.append({'first': f"first {v}", 'ifmacro': f"v {v}", 'option': f"o {v}", 'or': f"w {v}"}[kind])
        else:
            st.out.append({'first': "none", 'ifmacro': "v -7", 'option': "o none", 'or': "w -7"}[kind])
    elif kind == 'logic':
        L.append(f"    Lg := logic{{{show_cl(cl, '; ')}}}")
        L.append('    if (Lg?) then Print("l true") else Print("l false")')
        res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            st = res[1]
            st.out.append("l true")
        else:
            st.out.append("l false")
    elif kind == 'not':
        L.append(f"    if (not ({show_cl(cl, '; ')})) then Print(\"not ok\") else Print(\"not fail\")")
        res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
        st.out.append("not fail" if res is not None else "not ok")
    elif kind == 'for':
        L.append(f"    for ({show_cl(cl, ', ')}):")
        L.append(f'        Print("body {vals_str}")')

        def fbody(s):
            s.out.append(f"body {vals(s)}")
            return s
        s0 = st.copy()
        try:
            st = run_clauses(cl, s0, fbody, 'all')
        except Fail:
            pass
    else:  # formacro
        last = cl[-1]
        L.append(f"    Vs := for{{{show_cl(cl, '; ')}}}")
        L.append('    for (V : Vs) { Print("e {V}") }')
        vs = []

        def fbody2(s):
            vs.append(clause_value(cl, s))
            return s
        s0 = st.copy()
        try:
            st = run_clauses(cl, s0, fbody2, 'all')
        except Fail:
            pass
        st.out += [f"e {v}" for v in vs]
    L.append("    " + show_state)
    tout = st.out + [state_line(st)]
    lines += L
    tests.append(name)
    out += [f"== {name}"] + tout

src_main = ["Main():void ="] + [f'    Print("== {n}")\n    {n}()' for n in tests]
open(f"{outdir}/p.verse", "w").write(PRE + "\n".join(lines) + "\n" + "\n".join(src_main) + "\n")
open(f"{outdir}/p.chain", "w").write("1" if CHAIN[0] else "0")
open(f"{outdir}/p.expected", "w").write("".join(l + "\n" for l in out) + "exit=0\n")
