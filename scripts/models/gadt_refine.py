#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the review of #247 (casts that refine type arguments, #243).
"""Generator + model for openverse PR #247 (#243): refining casts in generic code.

Generic functions over pair(a, b) (or an interface ip(a, b) above pair) contain
`if (D := T[P]) ... else ...` where T's pins hold only under a refinement:
dup (b = a), dupi (a = b = int), opp (a = ?b), ipp (a = int), dupx (b = a, adds
a parameter), dmid (b = a, below a pin-free class).  Branches print, write a
var field, fail (in <decides> functions), read captured params and a var
changed before the cast, use written types under the refinement, and nest a
second refining cast.  The cast is often followed by more clauses (#277):
comparisons, a choice, a Print and a set of the object's field, so that
`if (D := T[P], rest) then B else E` is `if (D := T[P]) then (if (rest) then B
else E) else E`.  The model: the cast succeeds iff the object's class is at or
below T; Print is transactional (rolled back with a failed condition), and so is
the field set.
argv: seed expfile
"""
import random, sys
seed = int(sys.argv[1]); out_exp = sys.argv[2]
R = random.Random(seed)
def ch(p): return R.random() < p
# (#395: at times the refined branch sets Acc, a var from outside it, read after the if; a
# generator of its own decides, so seeds keep their other programs)
R395 = random.Random(seed * 1000003 + 395)

INT, STR = ('int',), ('string',)
def Opt(t): return ('opt', t)
def Arr(t): return ('arr', t)
def tyt(t):
    if t[0] in ('int', 'string'): return t[0]
    if t[0] == 'opt': return '?' + tyt(t[1])
    if t[0] == 'arr': return '[]' + tyt(t[1])
def show(v, t):
    if t == INT: return str(v)
    if t == STR: return v
    if t[0] == 'opt': return 'n' if v is None else f"s({show(v[1], t[1])})"
    if t[0] == 'arr': return '[' + ''.join(show(x, t[1]) + ',' for x in v) + ']'
SHOWN = {}
def shname(t):
    nm = 'Sh_' + tyt(t).replace('?', 'o_').replace('[]', 'a_')
    if t not in SHOWN:
        if t == INT: b = f'{nm}(X:int):string = "{{X}}"'
        elif t == STR: b = f'{nm}(X:string):string = X'
        elif t[0] == 'opt':
            i = shname(t[1]); b = f'{nm}(X:{tyt(t)}):string = if (Y := X?) then "s({{{i}(Y)}})" else "n"'
        else:
            i = shname(t[1])
            b = f'{nm}(X:{tyt(t)}):string =\n    var Acc:string = "["\n    for (E : X):\n        set Acc = "{{Acc}}{{{i}(E)}},"\n    "{{Acc}}]"'
        SHOWN[t] = b
    return nm
def lit(t):
    if t == INT:
        n = R.randint(0, 30); return str(n), n
    if t == STR:
        w = R.choice(['ka', 'lo', 'mi']); return f'"{w}"', w
    if t[0] == 'opt':
        if ch(0.3): return 'false', None
        x, v = lit(t[1]); return f"option{{{x}}}", ('some', v)
    if t[0] == 'arr':
        xs = [lit(t[1]) for _ in range(R.randint(0, 2))]
        return f"array{{{', '.join(x for x, _ in xs)}}}", [v for _, v in xs]

IFACE = ch(0.3)
# classes: name -> (params, parent, parent args as fn of params, has own C)
CL = {
    'pair': (['t', 'u'], None),
    'dup': (['x'], 'pair'), 'dupi': ([], 'dup'), 'dupx': (['x', 'w'], 'dup'),
    'opp': (['x'], 'pair'), 'ipp': (['x'], 'pair'), 'mid': (['t', 'u'], 'pair'), 'dmid': (['x'], 'mid'),
}
def pair_args(c, args):
    """the pair-level type arguments of class c at its own closed args"""
    if c == 'pair' or c == 'mid': return list(args)
    if c == 'dup': return [args[0], args[0]]
    if c == 'dupi': return [INT, INT]
    if c == 'dupx': return [args[0], args[0]]
    if c == 'opp': return [Opt(args[0]), args[0]]
    if c == 'ipp': return [INT, args[0]]
    if c == 'dmid': return [args[0], args[0]]
def below(c, t):
    while c is not None:
        if c == t: return True
        c = CL[c][1]
    return False
CDEF = {'dup': R.randint(0, 5), 'opp': R.randint(0, 5), 'ipp': R.randint(0, 5), 'dmid': R.randint(0, 5)}
def cfield_owner(c):
    while c is not None:
        if c in CDEF: return c
        c = CL[c][1]
    return None

prog_cls = []
if IFACE:
    prog_cls.append("ip(t:type, u:type) := interface:\n    Tag():string")
prog_cls.append(f'''pair(t:type, u:type) := class{"(ip(t, u))" if IFACE else ""}:
    A:t
    B:u
    var N:int = 0''' + ('\n    Tag<override>():string = "pair"' if IFACE else ''))
prog_cls.append(f'''dup(x:type) := class(pair(x, x)):
    C:int = {CDEF['dup']}
dupi := class(dup(int)):
    E:int = 0
''' + ('' if IFACE else '''dupx(x:type, w:type) := class(dup(x)):
    W:w
''') + f'''opp(x:type) := class(pair(?x, x)):
    C:int = {CDEF['opp']}
ipp(x:type) := class(pair(int, x)):
    C:int = {CDEF['ipp']}
mid(t:type, u:type) := class(pair(t, u)):
    M:int = 0
dmid(x:type) := class(mid(x, x)):
    C:int = {CDEF['dmid']}''')

# cast menu: target -> list of (ret var 'a'|'b', branch text, branch value fn(o, env), else text, else fn)
# inside the branch D is the object at T; env has K, X (a value), Acc
def vA(o, e): return o['A']
def vB(o, e): return o['B']
MENU = {
    'dup':  [('a', 'D.B', vB, 'P.A', vA), ('b', 'D.A', vA, 'P.B', vB), ('a', 'X', lambda o, e: e['X'], 'P.A', vA),
             ('b', 'WT:b = D.A', vA, 'P.B', vB)],
    'dmid': [('b', 'D.A', vA, 'P.B', vB), ('a', 'WT:b = D.A', vA, 'P.A', vA)],
    'dupi': [('a', 'D.A + D.B + K', lambda o, e: o['A'] + o['B'] + e['K'], 'P.A', vA),
             ('b', 'D.B * 2 + Acc', lambda o, e: o['B'] * 2 + e['Acc'], 'P.B', vB),
             ('a', 'WT:a = D.C + 1', lambda o, e: o['C'] + 1, 'P.A', vA)],
    'opp':  [('b', 'if (V := D.A?) then V else D.B', lambda o, e: o['A'][1] if o['A'] is not None else o['B'], 'P.B', vB),
             ('a', 'option{D.B}', lambda o, e: ('some', o['B']), 'P.A', vA),
             ('a', 'WT:?b = option{X}', lambda o, e: None, 'P.A', vA)],   # X : a = ?b there
    'ipp':  [('a', 'D.A + Acc', lambda o, e: o['A'] + e['Acc'], 'P.A', vA), ('a', 'WT:a = D.C', lambda o, e: o['C'], 'P.A', vA)],
}
# fix the opp 'X' entry: X : a = ?b, option{X} would be ??b; use X directly
MENU['opp'][2] = ('a', 'WT:?b = X', lambda o, e: e['X'], 'P.A', vA)

funcs = []    # dicts
# clauses after the cast (#277): ('cmpC', n) D.C > n; ('cmpK', n) K > n;
# ('choice', i, n) Yi := (1 | 2), Yi > n; ('print', i or None) Print("c F" or "c F {Yi}");
# ('bump', n) set D.N += n
def mk_rest(name):
    rest = []; ys = []
    for _ in range(R.randint(1, 3)):
        k = R.choice(['cmpC', 'cmpK', 'choice', 'print', 'print', 'bump'])
        if k == 'cmpC': rest.append(('cmpC', R.randint(0, 5)))
        elif k == 'cmpK': rest.append(('cmpK', R.randint(0, 8)))
        elif k == 'choice':
            i = len(ys); ys.append(i); rest.append(('choice', i, R.randint(0, 2)))
        elif k == 'print': rest.append(('print', ys[-1] if ys and ch(0.6) else None))
        else: rest.append(('bump', R.randint(1, 5)))
    return rest
def rest_text(f):
    out = []
    for c in f['rest']:
        if c[0] == 'cmpC': out.append(f"D.C > {c[1]}")
        elif c[0] == 'cmpK': out.append(f"K > {c[1]}")
        elif c[0] == 'choice': out.append(f"Y{c[1]} := (1 | 2), Y{c[1]} > {c[2]}")
        elif c[0] == 'print':
            out.append(f'Print("c {f["name"]}")' if c[1] is None else f'Print("c {f["name"]} {{Y{c[1]}}}")')
        else: out.append(f"set D.N += {c[1]}")
    return ''.join(', ' + x for x in out)
# the clauses after the cast, for an object below T: (ok, printed lines, N delta).
# Each choice keeps the first alternative its comparison accepts (no clause after it
# depends on its value other than a Print), so the condition succeeds iff every
# comparison can, and then its effects are the clauses' own, in order.
def run_rest(f, o, K):
    out = []; dN = 0; ys = {}
    for c in f['rest']:
        if c[0] == 'cmpC':
            if not o['C'] > c[1]: return False, [], 0
        elif c[0] == 'cmpK':
            if not K > c[1]: return False, [], 0
        elif c[0] == 'choice':
            ok = [y for y in (1, 2) if y > c[2]]
            if not ok: return False, [], 0
            ys[c[1]] = ok[0]
        elif c[0] == 'print':
            out.append(f"c {f['name']}" if c[1] is None else f"c {f['name']} {ys[c[1]]}")
        else: dN += c[1]
    return True, out, dN
def mk_func(k):
    T = R.choice(list(MENU))
    ret, btxt, bfn, etxt, efn = R.choice(MENU[T])
    f = {'name': f"G{k}", 'T': T, 'ret': ret, 'btxt': btxt, 'bfn': bfn, 'etxt': etxt, 'efn': efn}
    f['decides'] = ch(0.3)
    f['acc'] = R.randint(0, 9) if ch(0.6) else None
    f['pre'] = ch(0.4); f['inp'] = ch(0.5); f['outp'] = ch(0.4); f['post'] = ch(0.3)
    f['bump'] = ch(0.4)                       # set D.N += 1 in the branch
    f['aset'] = R395.random() < 0.4           # set Acc += 7 in the branch, Acc printed after (#395)
    f['ebump'] = ch(0.2)                      # set P.N += 10 in the else
    f['fail'] = f['decides'] and ch(0.8) and T != 'mid'
    f['thr'] = R.randint(0, 5)
    f['nest'] = T == 'dup' and ret == 'a' and ch(0.35)
    f['iface'] = IFACE and ch(0.5)
    alts = [(t2, e) for t2 in MENU if t2 != T for e in MENU[t2] if e[0] == ret]
    f['rest'] = mk_rest(f['name']) if ch(0.5) else []
    f['second'] = None
    if alts and ch(0.4):
        t2, (r2, b2, bf2, _, _) = R.choice(alts)
        f['second'] = (t2, b2, bf2, ch(0.5))
    return f
for k in range(R.randint(3, 7)): funcs.append(mk_func(k))

def ftext(f):
    rt = f['ret']
    eff = '<decides>' if f['decides'] else ''
    recv = 'ip(a, b)' if f['iface'] else 'pair(a, b)'
    L = [f"{f['name']}(P:{recv}, K:int, X:a where a:type, b:type){eff}:{rt} ="]
    L.append(f"    var Acc:int = K")
    if f['acc'] is not None: L.append(f"    set Acc += {f['acc']}")
    if f['pre']: L.append(f'    Print("pre {f["name"]} {{Acc}}")')
    L.append(f"    R := if (D := {f['T']}[P]{rest_text(f)}):")
    if f['inp']: L.append(f'        Print("in {f["name"]} {{Acc}} {{K}}")')
    if f['bump']: L.append("        set D.N += 1")
    if f['aset']: L.append("        set Acc += 7")
    if f['fail']: L.append(f"        D.C > {f['thr']}")
    if f['nest']:
        L.append("        if (E := dupi[D]) then E.A + E.B + K else D.B")
    elif f['btxt'].startswith('WT:'):
        decl, ex = f['btxt'][3:].split(' = ', 1)
        L.append(f"        Z:{decl} = {ex}")
        L.append("        Z")
    else:
        L.append(f"        {f['btxt']}")
    L.append("    else:")
    ind = "        "
    if f['second']:
        t2, b2, _, p2 = f['second']
        L.append(f"        if (D2 := {t2}[P]):")
        if p2: L.append(f'            Print("in2 {f["name"]}")')
        if b2.startswith('WT:'):
            decl, ex = b2[3:].split(' = ', 1)
            L.append(f"            Z2:{decl} = {ex.replace('D.', 'D2.')}")
            L.append("            Z2")
        else:
            L.append(f"            {b2.replace('D.', 'D2.')}")
        L.append("        else:")
        ind = "            "
    if f['outp']: L.append(f'{ind}Print("out {f["name"]}")')
    if f['ebump']: L.append(f"{ind}set P.N += 10" if not f['iface'] else f"{ind}Print(\"e\")")
    L.append(f"{ind}{f['etxt'] if not f['iface'] else f['etxt'].replace('P.', 'PP.')}")
    if f['aset']: L.append(f'    Print("acc {f["name"]} {{Acc}}")')
    if f['post']: L.append(f'    Print("post {f["name"]}")')
    L.append("    R")
    txt = '\n'.join(L)
    if f['iface']:
        # through an interface, P has no fields: read them in the else via a pair cast that does not refine
        txt = txt.replace("    R := if (D :=", "    R := if (D :=")
    return txt

# the interface variant needs the else value from P's fields: give the else a plain cast to pair
def fix_iface(f, txt):
    if not f['iface']: return txt
    # else branch: PP := pair[P] cannot fail for our objects (all are pairs); use a nested if
    lines = txt.split('\n')
    out = []
    for l in lines:
        if 'PP.' in l:
            ind = l[:len(l) - len(l.lstrip())]
            expr = l.strip()
            out.append(f"{ind}if (PP := pair[P]) then {expr} else Err()")
        else:
            out.append(l)
    return '\n'.join(out)

# model of one call; returns (ok, value, effects(list of printed lines), obj N delta)
def run_call(f, o, K, Xv):
    out = []; env = {'K': K, 'X': Xv}
    acc = K + (f['acc'] or 0); env['Acc'] = acc
    N0 = o['N']
    if f['pre']: out.append(f"pre {f['name']} {acc}")
    rok = False
    if below(o['cls'], f['T']):
        rok, rout, rdN = run_rest(f, o, K)
    if rok:
        out.extend(rout); o['N'] += rdN
        if f['inp']: out.append(f"in {f['name']} {acc} {K}")
        if f['bump']: o['N'] += 1
        if f['aset']:                         # (#395: the refined branch's set of Acc, which
            acc += 7; env['Acc'] = acc        # the branch's value reads after it)
        if f['fail'] and not (o['C'] > f['thr']):
            o['N'] = N0
            return False, None, [], 0
        if f['nest']:
            v = (o['A'] + o['B'] + K) if below(o['cls'], 'dupi') else o['B']
        else:
            v = f['bfn'](o, env)
    elif f['second'] and below(o['cls'], f['second'][0]):
        if f['second'][3]: out.append(f"in2 {f['name']}")
        v = f['second'][2](o, env)
    else:
        if f['outp']: out.append(f"out {f['name']}")
        if f['ebump']:
            if f['iface']: out.append("e")
            else: o['N'] += 10
        v = f['efn'](o, env)
    if f['aset']: out.append(f"acc {f['name']} {acc}")
    if f['post']: out.append(f"post {f['name']}")
    return True, v, out, o['N'] - N0

# objects
CLS = ['pair', 'dup', 'dupi', 'opp', 'ipp', 'mid', 'dmid'] + ([] if IFACE else ['dupx'])
TYS = [INT, STR, Opt(INT), Arr(INT)]
main, expect = [], []
objs = []
for i in range(R.randint(4, 9)):
    c = R.choice(CLS)
    np = len(CL[c][0])
    args = [R.choice(TYS) for _ in range(np)]
    if c in ('pair', 'mid') and ch(0.4): args = [args[0], args[0]]     # pair(t, t) objects that are not dups
    pa = pair_args(c, args)
    o = {'name': f"O{i}", 'cls': c, 'args': args, 'pa': pa, 'N': 0}
    fl = []
    x, v = lit(pa[0]); o['A'] = v; fl.append(f"A := {x}")
    x, v = lit(pa[1]); o['B'] = v; fl.append(f"B := {x}")
    own = cfield_owner(c)
    o['C'] = CDEF[own] if own else 0
    if own and ch(0.6):
        n = R.randint(0, 6); o['C'] = n; fl.append(f"C := {n}")
    if c == 'dupx':
        x, _ = lit(args[1]); fl.append(f"W := {x}")
    targs = f"({', '.join(tyt(t) for t in args)})" if args else ''
    st = R.random()
    if st < 0.4:
        main.append(f"    {o['name']}:pair({tyt(pa[0])}, {tyt(pa[1])}) = {c}{targs}{{{', '.join(fl)}}}")
    else:
        main.append(f"    {o['name']} := {c}{targs}{{{', '.join(fl)}}}")
    objs.append(o)
    for _ in range(R.randint(1, 3)):
        f = R.choice(funcs)
        K = R.randint(0, 9); xs, xv = lit(pa[0])
        rt = pa[0] if f['ret'] == 'a' else pa[1]
        ok, v, outl, dN = run_call(f, o, K, xv)
        call = f"{f['name']}({o['name']}, {K}, {xs})" if not f['decides'] else f"{f['name']}[{o['name']}, {K}, {xs}]"
        if f['decides']:
            main.append(f'    if (V := {call}) then Print("{f["name"]} {o["name"]}: {{{shname(rt)}(V)}}") else Print("{f["name"]} {o["name"]}: failed")')
            expect.extend(outl)
            expect.append(f"{f['name']} {o['name']}: {show(v, rt) if ok else 'failed'}")
        else:
            main.append(f'    Print("{f["name"]} {o["name"]}: {{{shname(rt)}({call})}}")')
            expect.extend(outl)
            expect.append(f"{f['name']} {o['name']}: {show(v, rt)}")
        main.append(f'    Print("N {{{o["name"]}.N}}")')
        expect.append(f"N {o['N']}")
# a generic loop over same-typed objects
groups = {}
for o in objs: groups.setdefault(tuple(o['pa']), []).append(o)
for k, os_ in groups.items():
    if len(os_) < 2 or not ch(0.7): continue
    fs = [f for f in funcs if not f['decides']]
    if not fs: break
    f = R.choice(fs); K = R.randint(0, 9); xs, xv = lit(k[0])
    rt = k[0] if f['ret'] == 'a' else k[1]
    an = f"Ps{len(main)}"
    main.append(f"    {an}:[]pair({tyt(k[0])}, {tyt(k[1])}) = array{{{', '.join(o['name'] for o in os_)}}}")
    main.append(f'    for (Q : {an}):\n        Print("loop {f["name"]}: {{{shname(rt)}({f["name"]}(Q, {K}, {xs}))}} {{Q.N}}")')
    for o in os_:
        ok, v, outl, dN = run_call(f, o, K, xv)
        expect.extend(outl); expect.append(f"loop {f['name']}: {show(v, rt)} {o['N']}")

loops = []
for k in range(R.randint(0, 2)):
    T = R.choice(list(MENU)); start = R.randint(0, 5)
    nm = f"L{k}"
    loops.append(f'''{nm}(Ps:[]pair(a, b), K:int where a:type, b:type):int =
    var S:int = K
    var Hits:int = 0
    for (P : Ps):
        set S += 1
        H := if (D := {T}[P]):
            Print("{nm} {{S}}")
            1
        else:
            0
        set Hits += H
    Hits''')
    for kk, os_ in groups.items():
        if not ch(0.6): continue
        an = f"Qs{len(main)}"
        main.append(f"    {an}:[]pair({tyt(kk[0])}, {tyt(kk[1])}) = array{{{', '.join(o['name'] for o in os_)}}}")
        main.append(f'    Print("{nm} hits {{{nm}({an}, {start})}}")')
        Sv = start; hits = 0
        for o in os_:
            Sv += 1
            if below(o['cls'], T): expect.append(f"{nm} {Sv}"); hits += 1
        expect.append(f"{nm} hits {hits}")
prog = [f"# genrefine seed {seed}"] + prog_cls + loops
for f in funcs: prog.append(fix_iface(f, ftext(f)))
prog += list(SHOWN.values())
prog.append("Main():void =")
prog += main
print('\n'.join(prog))
open(out_exp, 'w').write("exit=0\n" + ''.join(l + '\n' for l in expect))
