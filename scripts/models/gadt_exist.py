#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the review of #242 (existentials, #209).
"""Generator + model for openverse PR #242 (existentials, #209 step 2).

A GADT-style hierarchy under ex(t) with classes whose own type parameters
occur only inside the argument they give ex (pairE, optE, arrE, mkE, flipE,
swapE), or nowhere (fstE, sndE, eqE, cntE), subclasses that repeat or fix
them (dupP, leafP, fstI), add more (tagged), and non-overriding methods that
take hidden type parameters (mkE.Swap/Both, pairE.Helper).  Objects are
random expression trees of closed types; the model evaluates each call by
dynamic dispatch (the object's class) and prints at the closed static type.
argv: seed expfile.  expfile: 'exit=0' then the expected stdout.
Also a placeholder section: a non-parametric class above generic ones.
"""
import random, sys
seed = int(sys.argv[1]); out_exp = sys.argv[2]
R = random.Random(seed)
def ch(p): return R.random() < p

INT, STR, LOG = ('int',), ('string',), ('logic',)
def Tup(a, b): return ('tup', a, b)
def Opt(a): return ('opt', a)
def Arr(a): return ('arr', a)

def tyt(t):
    k = t[0]
    if k in ('int', 'string', 'logic'): return k
    if k == 'tup': return f"tuple({tyt(t[1])}, {tyt(t[2])})"
    if k == 'opt': return '?' + tyt(t[1])
    if k == 'arr': return '[]' + tyt(t[1])
    if k == 'var': return t[1]
    raise ValueError(t)

def comparable(t):
    return t[0] in ('int', 'string', 'logic') or (t[0] in ('opt', 'arr') and comparable(t[1])) or \
        (t[0] == 'tup' and comparable(t[1]) and comparable(t[2]))

def show(v, t):
    k = t[0]
    if k == 'int': return str(v)
    if k == 'string': return v
    if k == 'logic': return 'T' if v else 'F'
    if k == 'tup': return f"({show(v[0], t[1])},{show(v[1], t[2])})"
    if k == 'opt': return 'n' if v is None else f"s({show(v[1], t[1])})"
    if k == 'arr': return '[' + ''.join(show(x, t[1]) + ',' for x in v) + ']'

SHOWN = {}
def shname(t):
    nm = 'Sh_' + tyt(t).replace('?', 'o_').replace('[]', 'a_').replace('tuple(', 'T_').replace(', ', '_').replace(')', '_')
    if t not in SHOWN:
        k = t[0]
        if k == 'int': b = f'{nm}(X:int):string = "{{X}}"'
        elif k == 'string': b = f'{nm}(X:string):string = X'
        elif k == 'logic': b = f'{nm}(X:logic):string = if (X?) then "T" else "F"'
        elif k == 'tup':
            a1, a2 = shname(t[1]), shname(t[2])
            b = f'{nm}(X:{tyt(t)}):string = "({{{a1}(X(0))}},{{{a2}(X(1))}})"'
        elif k == 'opt':
            a1 = shname(t[1])
            b = f'{nm}(X:{tyt(t)}):string = if (Y := X?) then "s({{{a1}(Y)}})" else "n"'
        else:
            a1 = shname(t[1])
            b = (f'{nm}(X:{tyt(t)}):string =\n    var Acc:string = "["\n    for (E : X):\n'
                 f'        set Acc = "{{Acc}}{{{a1}(E)}},"\n    "{{Acc}}]"')
        SHOWN[t] = b
    return nm

def lit(t):
    k = t[0]
    if k == 'int':
        n = R.randint(0, 20); return str(n), n
    if k == 'string':
        w = R.choice(['ka', 'lo', 'mi', 'zu']); return f'"{w}"', w
    if k == 'logic':
        b = ch(0.5); return ('true' if b else 'false'), b
    if k == 'tup':
        x, v = lit(t[1]); y, w = lit(t[2]); return f"({x}, {y})", (v, w)
    if k == 'opt':
        if ch(0.3): return 'false', None
        x, v = lit(t[1]); return f"option{{{x}}}", ('some', v)
    if k == 'arr':
        xs = [lit(t[1]) for _ in range(R.randint(0, 3))]
        return f"array{{{', '.join(x for x, _ in xs)}}}", [v for _, v in xs]

# ---------------------------------------------------------------- class menu
# each optional class: include flag, and a variant of its Eval
INC = {n: ch(p) for n, p in [('cst', .6), ('pairE', .9), ('fstE', .7), ('sndE', .5), ('optE', .5),
                              ('arrE', .4), ('eqE', .6), ('cntE', .5), ('mkE', .7), ('flipE', .5),
                              ('swapE', .5), ('dupP', .5), ('leafP', .4), ('fstI', .4), ('tagged', .5),
                              ('mid', .4), ('wchain', .5)]}
if not (INC['cst'] or INC['optE']): INC['wchain'] = False
WOV = {}
for w in ['w2', 'w3', 'w4']:
    # all or none: a class with an override that inherits another method from a
    # class with fewer type arguments is refused (documented relate-beyond)
    WOV[w + 'e'] = WOV[w + 'n'] = ch(0.5)
DIRECT = True   # construct leaf-like classes in place (fixed in #242)
CMP = True     # comparable existentials (fixed in #242)
if not CMP: INC['eqE'] = INC['cntE'] = False
if not INC['pairE']: INC['dupP'] = INC['leafP'] = INC['tagged'] = False
if not INC['fstE']: INC['fstI'] = False
if not INC['mkE']: INC['flipE'] = False
V = {}   # variants
V['pairE'] = R.choice(['plain', 'local', 'helper'])
V['dupP'] = R.choice(['swap', 'name'])
V['root_pick'] = ch(0.5)
V['fstE_pick'] = ch(0.5)
V['pairE_pick'] = ch(0.5)
V['tagged_eval'] = ch(0.4)
V['mkE_eval'] = R.choice(['plain', 'swapcall'])
V['cntE_local'] = ch(0.5)

classes = []   # (verse text)
def C(txt): classes.append(txt)

C('''ex(t:type) := class<abstract>:
    Eval():t
    Name():string = "ex"''' + ('''
    Pick(X:t):t = X''' if V['root_pick'] else ''))
C('''lit := class(ex(int)):
    V:int
    Eval<override>():int = V
    Name<override>():string = "lit"''')
C('''slit := class(ex(string)):
    V:string
    Eval<override>():string = V''')
C('''iszero := class(ex(logic)):
    E:ex(int)
    Eval<override>():logic = logic{E.Eval() = 0}''')
if INC['cst']:
    C('''cst(t:type) := class(ex(t)):
    V:t
    Eval<override>():t = V
    Name<override>():string = "cst"''')
if INC['pairE']:
    body = {'plain': "(L.Eval(), R.Eval())",
            'local': "\n        var X:a = L.Eval()\n        Y:b = R.Eval()\n        set X = L.Eval()\n        (X, Y)",
            'helper': "(Helper()(1), Helper()(0))"}[V['pairE']]
    C(f'''pairE(a:type, b:type) := class(ex(tuple(a, b))):
    L:ex(a)
    R:ex(b)
    Eval<override>():tuple(a, b) = {body}
    Name<override>():string = "pairE"
    Helper():tuple(b, a) = (R.Eval(), L.Eval())''' + ('''
    Pick<override>(X:tuple(a, b)):tuple(a, b) = (X(0), R.Eval())''' if V['root_pick'] and V['pairE_pick'] else ''))
if INC['fstE']:
    C('''fstE(a:type, b:type) := class(ex(a)):
    P:ex(tuple(a, b))
    Eval<override>():a = P.Eval()(0)''' + ('''
    Pick<override>(X:a):a =
        var Z:b = P.Eval()(1)
        set Z = P.Eval()(1)
        X''' if V['root_pick'] and V['fstE_pick'] else ''))
if INC['sndE']:
    C('''sndE(a:type, b:type) := class(ex(b)):
    P:ex(tuple(a, b))
    Eval<override>():b = P.Eval()(1)
    Name<override>():string = "sndE"''')
if INC['optE']:
    C('''optE(a:type) := class(ex(?a)):
    E:ex(a)
    Eval<override>():?a = option{E.Eval()}''')
if INC['arrE']:
    C('''arrE(a:type) := class(ex([]a)):
    E:ex(a)
    N:int
    Eval<override>():[]a =
        X := E.Eval()
        for (I := 0..N - 1) { X }''')
if INC['eqE']:
    C('''eqE(a:subtype(comparable)) := class(ex(logic)):
    L:ex(a)
    R:ex(a)
    Eval<override>():logic = logic{L.Eval() = R.Eval()}
    Name<override>():string = if (L.Eval() = R.Eval()) then "eqE=" else "eqE/"''')
if INC['cntE']:
    loc = "\n        var Last:a = K\n        set Last = K" if V['cntE_local'] else ""
    C(f'''cntE(a:subtype(comparable)) := class(ex(int)):
    Xs:[]a
    K:a
    Eval<override>():int ={loc}
        var N:int = 0
        for (X : Xs, X = K) {{ set N += 1 }}
        N + cst(a){{V := K}}.Eval2()''' if INC['cst'] else f'''cntE(a:subtype(comparable)) := class(ex(int)):
    Xs:[]a
    K:a
    Eval<override>():int ={loc}
        var N:int = 0
        for (X : Xs, X = K) {{ set N += 1 }}
        N''')
if INC['mkE']:
    ev = "(X, Y)" if V['mkE_eval'] == 'plain' else "(Swap().Both()(1), Swap().Both()(0))"
    C(f'''mkE(a:type, b:type) := class(ex(tuple(a, b))):
    X:a
    Y:b
    Eval<override>():tuple(a, b) = {ev}
    Both():tuple(a, b) = (X, Y)
    Swap():mkE(b, a) = mkE(b, a){{X := Y, Y := X}}''')
if INC['flipE']:
    C('''flipE(a:type, b:type) := class(ex(tuple(b, a))):
    X:a
    Y:b
    Eval<override>():tuple(b, a) = mkE(b, a){X := Y, Y := X}.Eval()''')
if INC['swapE']:
    C('''swapE(a:type, b:type) := class(ex(tuple(b, a))):
    P:ex(tuple(a, b))
    Eval<override>():tuple(b, a) =
        Q := P.Eval()
        (Q(1), Q(0))''')
if INC['dupP']:
    if V['dupP'] == 'swap':
        C('''dupP(a:type) := class(pairE(a, a)):
    Eval<override>():tuple(a, a) = (R.Eval(), L.Eval())''')
    else:
        C('''dupP(a:type) := class(pairE(a, a)):
    Name<override>():string = "dupP/{(super:)Name()}"''')
if INC['leafP']:
    C('''leafP := class(pairE(int, string)):
    Eval<override>():tuple(int, string) = (L.Eval() + 100, R.Eval())''')
if INC['fstI']:
    C('''fstI(b:type) := class(fstE(int, b)):
    Eval<override>():int = P.Eval()(0) + 1000''')
if INC['tagged']:
    C('''tagged(a:type, b:type, n:type) := class(pairE(a, b)):
    Tag:n
    Name<override>():string = "tagged/{(super:)Name()}"''' + ('''
    Eval<override>():tuple(a, b) =
        var T:n = Tag
        set T = Tag
        (super:)Eval()''' if V['tagged_eval'] else ''))
if INC['mid']:
    C('''mid(a:type, b:type) := class<abstract>(ex(tuple(a, b))):
    Z:int = 0
leaf2(x:type) := class(mid(x, string)):
    V:x
    Eval<override>():tuple(x, string) = (V, "m")
leaf3 := class(mid(int, int)):
    Eval<override>():tuple(int, int) = (Z, Z + 1)''')
if INC['wchain']:
    C('''w1(a:type) := class(ex([]a)):
    E:ex(a)
    Eval<override>():[]a = array{E.Eval()}
    Name<override>():string = "w1"''')
    C('''w2(b:type) := class(w1(?b)):
    G:ex(b)''' + ('''
    Eval<override>():[]?b = array{option{G.Eval()}, E.Eval()}''' if WOV['w2e'] else '') + ('''
    Name<override>():string = "w2"''' if WOV['w2n'] else ''))
    C('''w3(c:type) := class(w2(tuple(c, int))):
    K:c''' + ('''
    Eval<override>():[]?tuple(c, int) =
        var Z:c = K
        array{option{(Z, 7)}}''' if WOV['w3e'] else '') + ('''
    Name<override>():string = "w3/{(super:)Name()}"''' if WOV['w3n'] else ''))
    C('''w4 := class(w3(string)):
    Q:int = 0''' + ('''
    Eval<override>():[]?tuple(string, int) = (super:)Eval()''' if WOV['w4e'] else '') + ('''
    Name<override>():string = "w4"''' if WOV['w4n'] else ''))
if INC['cst'] and INC['cntE']:
    # cst's extra method used by cntE: a non-override called on an object made in an override
    classes[[i for i, c in enumerate(classes) if c.startswith('cst(')][0]] += '\n    Eval2():int = 0'

# ---------------------------------------------------------------- expression trees
# node: (text, value, type, kind, extra) ; evaluate via model functions
CLOSED_BASE = [INT, STR, LOG]
def rtype(d=0):
    r = R.random()
    if d < 2 and r < 0.3: return Tup(rtype(d + 1), rtype(d + 1))
    if d < 2 and r < 0.38 and INC['optE']: return Opt(rtype(d + 1))
    if d < 2 and r < 0.45 and INC['arrE']: return Arr(rtype(d + 1))
    if d < 1 and r < 0.6 and INC['wchain']:
        return Arr(Opt(Tup(R.choice([STR, INT]), INT))) if ch(0.6) else Arr(Opt(rtype(2)))
    return R.choice(CLOSED_BASE)

class Node:
    def __init__(s, txt, ty, ev, name, pick=None, cls=''):
        s.txt, s.ty, s.ev, s.name, s.pick, s.cls = txt, ty, ev, name, pick, cls

def gen(t, d=0):
    """random ex(t) object of closed type t"""
    opts = []
    if d > 3:
        opts = []
    k = t[0]
    def base():
        if t == INT:
            x, v = lit(INT); return Node(f"lit{{V := {x}}}", t, lambda: v, 'lit', cls='lit')
        if t == STR:
            x, v = lit(STR); return Node(f"slit{{V := {x}}}", t, lambda: v, 'ex', cls='slit')
        if t == LOG:
            e = gen(INT, d + 1)
            return Node(f"iszero{{E := {e.txt}}}", t, lambda: e.ev() == 0, 'ex', cls='iszero')
        if INC['cst']:
            x, v = lit(t); return Node(f"cst({tyt(t)}){{V := {x}}}", t, lambda: v, 'cst', cls='cst')
        return None
    cands = []
    if d < 4:
        if INC['fstE'] and can_make(Tup(t, INT)):
            def f():
                u = rtype(2); p = gen(Tup(t, u), d + 1)
                if INC['fstI'] and t == INT and ch(0.4):
                    return Node(f"fstI({tyt(u)}){{P := {p.txt}}}", t, lambda: p.ev()[0] + 1000, 'ex', cls='fstI')
                return Node(f"fstE({tyt(t)}, {tyt(u)}){{P := {p.txt}}}", t, lambda: p.ev()[0], 'ex',
                            pick=(lambda x: (p.ev(), x)[1]) if V['root_pick'] and V['fstE_pick'] else None, cls='fstE')
            cands.append(f)
        if INC['sndE'] and can_make(Tup(INT, t)):
            def f():
                u = rtype(2); p = gen(Tup(u, t), d + 1)
                return Node(f"sndE({tyt(u)}, {tyt(t)}){{P := {p.txt}}}", t, lambda: p.ev()[1], 'sndE', cls='sndE')
            cands.append(f)
        if t == LOG and INC['eqE']:
            def f():
                u = R.choice([INT, STR, Tup(INT, STR), Opt(INT)])
                if not can_make(u): u = INT
                l, r = gen(u, d + 1), gen(u, d + 1)
                if ch(0.4): r = l   # same subtree text: equal values
                return Node(f"eqE({tyt(u)}){{L := {l.txt}, R := {r.txt}}}", t, lambda: l.ev() == r.ev(),
                            ('eqE', l, r), cls='eqE')
            cands.append(f)
        if t == INT and INC['cntE']:
            def f():
                u = R.choice([INT, STR, Tup(INT, LOG)])
                xs = [lit(u) for _ in range(R.randint(0, 4))]
                kk = R.choice(xs) if xs and ch(0.6) else lit(u)
                cnt = sum(1 for _, v in xs if v == kk[1])
                return Node(f"cntE({tyt(u)}){{Xs := array{{{', '.join(x for x, _ in xs)}}}, K := {kk[0]}}}", t,
                            lambda: cnt, 'ex', cls='cntE')
            cands.append(f)
    if k == 'tup':
        a, b = t[1], t[2]
        if INC['pairE']:
            def f():
                l, r = gen(a, d + 1), gen(b, d + 1)
                pick = (lambda x: (x[0], r.ev())) if V['root_pick'] and V['pairE_pick'] else None
                if INC['dupP'] and a == b and ch(0.4):
                    if V['dupP'] == 'swap':
                        return Node(f"dupP({tyt(a)}){{L := {l.txt}, R := {r.txt}}}", t, lambda: (r.ev(), l.ev()),
                                    'dupPs', pick=pick, cls='dupP')
                    return Node(f"dupP({tyt(a)}){{L := {l.txt}, R := {r.txt}}}", t, lambda: (l.ev(), r.ev()),
                                'dupPn', pick=pick, cls='dupP')
                if INC['leafP'] and t == Tup(INT, STR) and ch(0.4):
                    return Node((f"leafP{{L := {l.txt}, R := {r.txt}}}" if DIRECT else f"NewLeafP({l.txt}, {r.txt})"), t, lambda: (l.ev() + 100, r.ev()),
                                'pairE', pick=pick, cls='leafP')
                if INC['tagged'] and ch(0.3):
                    n = rtype(2); x, _ = lit(n)
                    return Node(f"tagged({tyt(a)}, {tyt(b)}, {tyt(n)}){{L := {l.txt}, R := {r.txt}, Tag := {x}}}", t,
                                lambda: (l.ev(), r.ev()), 'tagged', pick=pick, cls='tagged')
                return Node(f"pairE({tyt(a)}, {tyt(b)}){{L := {l.txt}, R := {r.txt}}}", t,
                            lambda: (l.ev(), r.ev()), 'pairE', pick=pick, cls='pairE')
            cands += [f, f]
        if INC['mkE']:
            def f():
                (x, v), (y, w) = lit(a), lit(b)
                return Node(f"mkE({tyt(a)}, {tyt(b)}){{X := {x}, Y := {y}}}", t, lambda: (v, w), 'ex', cls='mkE')
            cands.append(f)
        if INC['flipE']:
            def f():
                (x, v), (y, w) = lit(b), lit(a)   # flipE(b', a') : ex(tuple(a', b')) with X:b', Y:a'... see below
                # flipE(p, q) := ex(tuple(q, p)), X:p, Y:q  -> Eval = (Y, X)
                return Node(f"flipE({tyt(b)}, {tyt(a)}){{X := {x}, Y := {y}}}", t, lambda: (w, v), 'ex', cls='flipE')
            cands.append(f)
        if INC['swapE'] and d < 4:
            def f():
                p = gen(Tup(b, a), d + 1)
                return Node(f"swapE({tyt(b)}, {tyt(a)}){{P := {p.txt}}}", t, lambda: (p.ev()[1], p.ev()[0]), 'ex', cls='swapE')
            cands.append(f)
        if INC['mid'] and b == STR:
            def f():
                x, v = lit(a)
                return Node(f"leaf2({tyt(a)}){{V := {x}}}", t, lambda: (v, "m"), 'ex', cls='leaf2')
            cands.append(f)
        if INC['mid'] and t == Tup(INT, INT):
            def f():
                z = R.randint(0, 9)
                return Node((f"leaf3{{Z := {z}}}" if DIRECT else f"NewLeaf3({z})"), t, lambda: (z, z + 1), 'ex', cls='leaf3')
            cands.append(f)
    if k == 'opt' and INC['optE']:
        def f():
            e = gen(t[1], d + 1)
            return Node(f"optE({tyt(t[1])}){{E := {e.txt}}}", t, lambda: ('some', e.ev()), 'ex', cls='optE')
        cands.append(f)
    if k == 'arr' and INC['wchain'] and d < 4:
        el = t[1]
        def f():
            e = gen(el, d + 1)
            return Node(f"w1({tyt(el)}){{E := {e.txt}}}", t, lambda: [e.ev()], 'w1', cls='w1')
        cands.append(f)
        if el[0] == 'opt' and can_make(el):
            def f2():
                b = el[1]; e = gen(el, d + 1); g = gen(b, d + 1)
                w2ev = lambda: ([('some', g.ev()), e.ev()] if WOV['w2e'] else [e.ev()])
                w2nm = "w2" if WOV['w2n'] else "w1"
                if b[0] == 'tup' and b[2] == INT and ch(0.6):
                    c = b[1]; x, v = lit(c)
                    w3ev = (lambda: [('some', (v, 7))]) if WOV['w3e'] else w2ev
                    w3nm = ("w3/" + w2nm) if WOV['w3n'] else w2nm
                    if c == STR and ch(0.5):
                        w4ev = w3ev
                        w4nm = "w4" if WOV['w4n'] else w3nm
                        return Node((f"w4{{E := {e.txt}, G := {g.txt}, K := {x}}}" if DIRECT else f"NewW4({e.txt}, {g.txt}, {x})"), t, w4ev, ('nm', w4nm), cls='w4')
                    return Node(f"w3({tyt(c)}){{E := {e.txt}, G := {g.txt}, K := {x}}}", t, w3ev, ('nm', w3nm), cls='w3')
                return Node(f"w2({tyt(b)}){{E := {e.txt}, G := {g.txt}}}", t, w2ev, ('nm', w2nm), cls='w2')
            cands += [f2, f2]
    if k == 'arr' and INC['arrE']:
        def f():
            e = gen(t[1], d + 1); n = R.randint(0, 3)
            return Node(f"arrE({tyt(t[1])}){{E := {e.txt}, N := {n}}}", t, lambda: [e.ev()] * n, 'ex', cls='arrE')
        cands.append(f)
    if d >= 4: cands = [c for c in cands if getattr(c, 'structural', False)] or cands
    if cands and (ch(0.75) or base() is None):
        return R.choice(cands)()
    b = base()
    if b is None:
        # a type with no constructor here: fall back to cst if present else a pairE etc.
        if cands: return R.choice(cands)()
        raise KeyError(t)
    return b

def can_make(t, d=0):
    k = t[0]
    if t in (INT, STR, LOG): return True
    if INC['cst']: return True
    if k == 'tup': return (INC['pairE'] and can_make(t[1]) and can_make(t[2])) or INC['mkE'] or INC['flipE']
    if k == 'opt': return INC['optE'] and can_make(t[1])
    if k == 'arr': return (INC['arrE'] or INC['wchain']) and can_make(t[1])
    return False

def name_of(n):
    """model of Name() on node n"""
    kd = n.name
    if kd == 'w1': return "w1"
    if isinstance(kd, tuple) and kd[0] == 'nm': return kd[1]
    if isinstance(kd, tuple) and kd[0] == 'eqE':
        return "eqE=" if kd[1].ev() == kd[2].ev() else "eqE/"
    if kd == 'lit': return "lit"
    if kd == 'cst': return "cst"
    if kd == 'sndE': return "sndE"
    if kd in ('pairE',): return "pairE"
    if kd == 'dupPs': return "pairE"
    if kd == 'dupPn': return "dupP/pairE"
    if kd == 'tagged': return "tagged/pairE"
    return "ex"

# ---------------------------------------------------------------- callers over ex(pattern)
def pvars(p):
    if p[0] == 'var': return [p[1]]
    if p[0] == 'tup': return pvars(p[1]) + [v for v in pvars(p[2]) if v not in pvars(p[1])]
    if p[0] in ('opt', 'arr'): return pvars(p[1])
    return []
def match(p, a, s):
    if s is None: return None
    if p[0] == 'var':
        if p[1] in s: return s if s[p[1]] == a else None
        s = dict(s); s[p[1]] = a; return s
    if p[0] != a[0]: return None
    if p[0] == 'tup': return match(p[2], a[2], match(p[1], a[1], s))
    if p[0] in ('opt', 'arr'): return match(p[1], a[1], s)
    return s
def subst(p, s):
    if p[0] == 'var': return s[p[1]]
    if p[0] == 'tup': return Tup(subst(p[1], s), subst(p[2], s))
    if p[0] in ('opt', 'arr'): return (p[0], subst(p[1], s))
    return p
A_, B_ = ('var', 'a'), ('var', 'b')
PATS = [Arr(Opt(A_)), Arr(Opt(Tup(A_, INT))), Arr(Opt(Tup(STR, INT))), A_, A_, INT, STR, LOG, Tup(A_, B_), Tup(A_, A_), Tup(INT, B_), Tup(A_, STR), Opt(A_), Arr(A_), Tup(Tup(A_, B_), A_)]
callers = []
used = set()
def mk_caller(pat, m):
    vs = pvars(pat)
    where = f" where {', '.join(v + ':type' for v in vs)}" if vs else ''
    nm = f"{m}{len(callers)}"
    pt = tyt(pat)
    if m == 'Run': txt = f"{nm}(E:ex({pt}){where}):{pt} = E.Eval()"
    elif m == 'Nm': txt = f"{nm}(E:ex({pt}){where}):string = E.Name()"
    elif m == 'Pk': txt = f"{nm}(E:ex({pt}), X:{pt}{where}):{pt} = E.Pick(X)"
    elif m == 'Arr':
        txt = f"{nm}(Es:[]ex({pt}){where}):[]{pt} = for (E : Es) {{ E.Eval() }}"
    elif m == 'Via':   # generic over ex(t) calling another generic caller
        inner = R.choice([c for c in callers if c[2] == 'Run' and c[1] == A_] or [None])
        if inner is None: return None
        txt = f"{nm}(E:ex({pt}){where}):{pt} = {inner[0]}(E)"
        used.add(inner[0])
    callers.append((nm, pat, m, txt))
    return callers[-1]
mk_caller(A_, 'Run')
for _ in range(R.randint(4, 10)):
    m = R.choice(['Run', 'Run', 'Nm', 'Arr', 'Via'] + (['Pk'] if V['root_pick'] else []))
    mk_caller(R.choice(PATS), m)

# ---------------------------------------------------------------- main
main, expect = [], []
def emit_call(obj_txt, node, static_t):
    cs = [c for c in callers if match(c[1], static_t, {}) is not None]
    if not cs: return
    c = R.choice(cs); nm, pat, m, _ = c; used.add(nm)
    if m in ('Run', 'Via'):
        main.append(f'    Print("{nm}: {{{shname(static_t)}({nm}({obj_txt}))}}")')
        expect.append(f"{nm}: {show(node.ev(), static_t)}")
    elif m == 'Nm':
        main.append(f'    Print("{nm}: {{{nm}({obj_txt})}}")')
        expect.append(f"{nm}: {name_of(node)}")
    elif m == 'Pk':
        x, v = lit(static_t)
        main.append(f'    Print("{nm}: {{{shname(static_t)}({nm}({obj_txt}, {x}))}}")')
        expect.append(f"{nm}: {show(node.pick(v) if node.pick else v, static_t)}")
    elif m == 'Arr':
        main.append(f'    Print("{nm}: {{{shname(Arr(static_t))}({nm}(array{{{obj_txt}, {obj_txt}}}))}}")')
        expect.append(f"{nm}: {show([node.ev(), node.ev()], Arr(static_t))}")

objs = []
for i in range(R.randint(4, 9)):
    for _ in range(20):
        t = rtype()
        if can_make(t): break
    try:
        n = gen(t)
    except KeyError:
        continue
    nm = f"O{i}"
    if ch(0.5):
        main.append(f"    {nm}:ex({tyt(t)}) = {n.txt}")
    else:
        main.append(f"    {nm} := {n.txt}")
    objs.append((nm, n, t))
    for _ in range(R.randint(1, 4)): emit_call(nm, n, t)
    if ch(0.4):
        main.append(f'    Print("direct {nm}: {{{shname(t)}({nm}.Eval())}} {{{nm}.Name()}}")')
        expect.append(f"direct {nm}: {show(n.ev(), t)} {name_of(n)}")
# arrays of same-typed objects through a generic loop
bytype = {}
for nm, n, t in objs: bytype.setdefault(t, []).append((nm, n))
for t, l in bytype.items():
    if len(l) >= 2:
        an = f"Es{len(main)}"
        main.append(f"    {an}:[]ex({tyt(t)}) = array{{{', '.join(nm for nm, _ in l)}}}")
        main.append(f"    for (E : {an}):\n        Print(\"loop: {{{shname(t)}(Run0(E))}}\")")
        used.add('Run0')
        for nm, n in l: expect.append(f"loop: {show(n.ev(), t)}")
# hidden parameters: non-overriding methods of mkE / pairE, directly and through generic code
if INC['mkE']:
    a, b = rtype(2), rtype(2)
    (x, v), (y, w) = lit(a), lit(b)
    main.append(f"    M := mkE({tyt(a)}, {tyt(b)}){{X := {x}, Y := {y}}}")
    main.append(f'    Print("swap: {{{shname(Tup(b, a))}(M.Swap().Both())}} {{{shname(Tup(b, a))}(SwapAny(M))}} {{{shname(Tup(b, a))}(M.Swap().Eval())}}")')
    expect.append(f"swap: {show((w, v), Tup(b, a))} {show((w, v), Tup(b, a))} {show((w, v), Tup(b, a))}")
    callers.append(('SwapAny', None, 'x', "SwapAny(M:mkE(a, b) where a:type, b:type):tuple(b, a) = M.Swap().Both()"))
    used.add('SwapAny')
if INC['pairE']:
    a, b = rtype(2), rtype(2)
    l, r = gen(a, 2), gen(b, 2)
    main.append(f"    PH := pairE({tyt(a)}, {tyt(b)}){{L := {l.txt}, R := {r.txt}}}")
    main.append(f'    Print("helper: {{{shname(Tup(b, a))}(PH.Helper())}} {{{shname(Tup(b, a))}(HelperAny(PH))}}")')
    expect.append(f"helper: {show((r.ev(), l.ev()), Tup(b, a))} {show((r.ev(), l.ev()), Tup(b, a))}")
    callers.append(('HelperAny', None, 'x', "HelperAny(P:pairE(a, b) where a:type, b:type):tuple(b, a) = P.Helper()"))
    used.add('HelperAny')

# ---------------------------------------------------------------- placeholder section
PH = ch(0.6)
if PH:
    C('''shape := class<abstract>:
    Area():int
    Kind():string = "shape"
sq := class(shape):
    S:int
    Area<override>():int = S * S
gbox(t:type) := class(shape):
    N:int
    V:t
    Area<override>():int = N
    Kind<override>():string = "gbox"
gbox2(t:type, u:type) := class(gbox(t)):
    W:u
    Area<override>():int = N + 1000
holder := class:
    Sh:shape''')
    shapes = []
    for i in range(R.randint(2, 5)):
        r = R.random()
        if r < 0.3:
            s = R.randint(1, 9); shapes.append((f"sq{{S := {s}}}", s * s, "shape"))
        elif r < 0.65:
            n = R.randint(0, 50); t = rtype(2); x, _ = lit(t)
            shapes.append((f"gbox({tyt(t)}){{N := {n}, V := {x}}}", n, "gbox"))
        else:
            n = R.randint(0, 50); t = rtype(2); u = rtype(2); x, _ = lit(t); y, _ = lit(u)
            shapes.append((f"gbox2({tyt(t)}, {tyt(u)}){{N := {n}, V := {x}, W := {y}}}", n + 1000, "gbox"))
    main.append(f"    Ss:[]shape = array{{{', '.join(s for s, _, _ in shapes)}}}")
    main.append("    var Cur:?shape = false\n    for (S : Ss):\n        set Cur = option{S}\n        Print(\"area {S.Area()} {S.Kind()}\")")
    for _, a, k in shapes: expect.append(f"area {a} {k}")
    main.append("    if (C := Cur?) then Print(\"last {C.Area()}\")")
    expect.append(f"last {shapes[-1][1]}")
    s, a, k = R.choice(shapes)
    main.append(f"    H := holder{{Sh := {s}}}\n    Print(\"held {{H.Sh.Area()}}\")")
    expect.append(f"held {a}")
    if ch(0.5):
        main.append("    var One:shape = Ss[0] or sq{S := 1}\n    Print(\"one {One.Area()}\")")
        expect.append(f"one {shapes[0][1]}")

if not DIRECT:
    if INC['leafP']: classes.append("NewLeafP(L:ex(int), R:ex(string)):leafP = leafP{L := L, R := R}")
    if INC['mid']: classes.append("NewLeaf3(Z:int):leaf3 = leaf3{Z := Z}")
    if INC['wchain']: classes.append("NewW4(E:ex(?tuple(string, int)), G:ex(tuple(string, int)), K:string):w4 = w4{E := E, G := G, K := K}")
prog = [f"# genexist seed {seed}"] + classes
for c in callers:
    if c[0] in used: prog.append(c[3])
prog += list(SHOWN.values())
prog.append("Main():void =")
prog += main or ['    Print("none")']
print('\n'.join(prog))
open(out_exp, 'w').write("exit=0\n" + ''.join(l + '\n' for l in expect))
