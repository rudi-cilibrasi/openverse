#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the review of #252 (casts that open existential type arguments, #250).
"""Generator + model for openverse PR #252 (#250): refining casts that open
existential type arguments, matching on pairE/fstE/... in generic code.

Objects are expression trees over ex(t); generated matchers (Ev: values, Ds:
strings, Sz: <decides> sizes with a var-field write) test the classes in a
random order with opening casts (pairE[E], fstE[E], dupP[E], tagged[E], ...),
recurse on the opened parts, pass opened values through generic functions
(Id, Flip, First, MkCst, which need the opened witnesses), nest a refining
cast (lit[P.L]) or another opening cast (pairE[P.L]) in a branch, and read a
var changed before the cast.  Some casts are followed by more clauses (#277)
where the else has no other cast (#286): Ds's last rule reads a var, ClosedSum
binds and compares an opened value, and Sz's fstE rule calls Sz in the
condition, so the call's failure is the else and its field writes are rolled
back.  The model evaluates each matcher by the first rule whose class is at or
above the object's class (and whose clauses hold).
argv: seed expfile [--cmp]
"""
import random, sys
seed = int(sys.argv[1]); out_exp = sys.argv[2]
R = random.Random(seed)
def ch(p): return R.random() < p
CMP = True   # comparable opened parameters (fixed in #252)

INT, STR, LOG = ('int',), ('string',), ('logic',)
def Tup(a, b): return ('tup', a, b)
def Opt(a): return ('opt', a)
def tyt(t):
    if t[0] in ('int', 'string', 'logic'): return t[0]
    if t[0] == 'tup': return f"tuple({tyt(t[1])}, {tyt(t[2])})"
    if t[0] == 'opt': return '?' + tyt(t[1])
def show(v, t):
    if t == INT: return str(v)
    if t == STR: return v
    if t == LOG: return 'T' if v else 'F'
    if t[0] == 'tup': return f"({show(v[0], t[1])},{show(v[1], t[2])})"
    if t[0] == 'opt': return 'n' if v is None else f"s({show(v[1], t[1])})"
SHOWN = {}
def shname(t):
    nm = 'Sh_' + tyt(t).replace('?', 'o_').replace('tuple(', 'T_').replace(', ', '_').replace(')', '_')
    if t not in SHOWN:
        if t == INT: b = f'{nm}(X:int):string = "{{X}}"'
        elif t == STR: b = f'{nm}(X:string):string = X'
        elif t == LOG: b = f'{nm}(X:logic):string = if (X?) then "T" else "F"'
        elif t[0] == 'tup':
            a1, a2 = shname(t[1]), shname(t[2])
            b = f'{nm}(X:{tyt(t)}):string = "({{{a1}(X(0))}},{{{a2}(X(1))}})"'
        else:
            a1 = shname(t[1]); b = f'{nm}(X:{tyt(t)}):string = if (Y := X?) then "s({{{a1}(Y)}})" else "n"'
        SHOWN[t] = b
    return nm
def lit(t):
    if t == INT:
        n = 13 if ch(0.12) else R.randint(0, 20); return str(n), n
    if t == STR:
        w = R.choice(['ka', 'lo', 'mi']); return f'"{w}"', w
    if t == LOG:
        b = ch(0.5); return ('true' if b else 'false'), b
    if t[0] == 'tup':
        x, v = lit(t[1]); y, w = lit(t[2]); return f"({x}, {y})", (v, w)
    if t[0] == 'opt':
        if ch(0.3): return 'false', None
        x, v = lit(t[1]); return f"option{{{x}}}", ('some', v)

V = {'dupP': R.choice(['swap', 'none']), 'cmp': CMP and ch(0.7)}
CLASSES = f'''ex(t:type) := class<abstract>:
    Eval():t
    Name():string = "ex"
    var Hits:int = 0
lit := class(ex(int)):
    V:int
    Eval<override>():int = V
    Name<override>():string = "lit"
slit := class(ex(string)):
    V:string
    Eval<override>():string = V
cst(t:type) := class(ex(t)):
    V:t
    Eval<override>():t = V
    Name<override>():string = "cst"
pairE(a:type, b:type) := class(ex(tuple(a, b))):
    L:ex(a)
    R:ex(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
fstE(a:type, b:type) := class(ex(a)):
    P:ex(tuple(a, b))
    Eval<override>():a = P.Eval()(0)
sndE(a:type, b:type) := class(ex(b)):
    P:ex(tuple(a, b))
    Eval<override>():b = P.Eval()(1)
mkE(a:type, b:type) := class(ex(tuple(a, b))):
    X:a
    Y:b
    Eval<override>():tuple(a, b) = (X, Y)
optE(a:type) := class(ex(?a)):
    E:ex(a)
    Eval<override>():?a = option{{E.Eval()}}
dupP(a:type) := class(pairE(a, a)):''' + ('''
    Eval<override>():tuple(a, a) = (R.Eval(), L.Eval())''' if V['dupP'] == 'swap' else '''
    Z:int = 0''') + '''
tagged(a:type, b:type, n:type) := class(pairE(a, b)):
    Tag:n
leafP := class(pairE(int, string)):
    Eval<override>():tuple(int, string) = (L.Eval() + 100, R.Eval())''' + ('''
eqE(a:subtype(comparable)) := class(ex(logic)):
    L:ex(a)
    R:ex(a)
    Eval<override>():logic = logic{L.Eval() = R.Eval()}''' if V['cmp'] else '') + '''
Id(X:x where x:type):x = X
Flip(T:tuple(x, y) where x:type, y:type):tuple(y, x) = (T(1), T(0))
First(T:tuple(x, y) where x:type, y:type):x = T(0)
MkCst(X:x where x:type):ex(x) = cst(x){V := X}'''

PARENT = {'lit': None, 'slit': None, 'cst': None, 'pairE': None, 'fstE': None, 'sndE': None, 'mkE': None,
          'optE': None, 'dupP': 'pairE', 'tagged': 'pairE', 'leafP': 'pairE', 'eqE': None}
def below(c, t):
    while c is not None:
        if c == t: return True
        c = PARENT[c]
    return False

# ---------------------------------------------------------------- trees
class N:
    def __init__(s, cls, ty, txt, **kw):
        s.cls, s.ty, s.txt = cls, ty, txt
        s.__dict__.update(kw)
def native(n):
    c = n.cls
    if c in ('lit', 'slit', 'cst'): return n.v
    if c == 'pairE' or c == 'tagged': return (native(n.L), native(n.R))
    if c == 'dupP': return (native(n.R), native(n.L)) if V['dupP'] == 'swap' else (native(n.L), native(n.R))
    if c == 'leafP': return (native(n.L) + 100, native(n.R))
    if c == 'fstE': return native(n.P)[0]
    if c == 'sndE': return native(n.P)[1]
    if c == 'mkE': return (n.x, n.y)
    if c == 'optE': return ('some', native(n.E))
    if c == 'eqE': return native(n.L) == native(n.R)

def rtype(d=0):
    r = R.random()
    if d < 2 and r < 0.35: return Tup(rtype(d + 1), rtype(d + 1))
    if d < 2 and r < 0.42: return Opt(rtype(d + 1))
    return R.choice([INT, STR, LOG])

def gen(t, d=0):
    cands = []
    if t == INT: cands += ['lit'] * 3
    if t == STR: cands += ['slit'] * 2
    if t == LOG and V['cmp'] and d < 4: cands += ['eqE'] * 2
    cands += ['cst']
    if d < 4: cands += ['fstE', 'sndE']
    if t[0] == 'tup':
        cands += ['pairE'] * 4 + ['mkE']
        if t[1] == t[2]: cands += ['dupP'] * 2
        if t == Tup(INT, STR): cands += ['leafP'] * 2
        cands += ['tagged']
    if t[0] == 'opt': cands += ['optE'] * 2
    c = R.choice(cands)
    if c in ('lit', 'slit', 'cst'):
        x, v = lit(t)
        txt = {'lit': f"lit{{V := {x}}}", 'slit': f"slit{{V := {x}}}", 'cst': f"cst({tyt(t)}){{V := {x}}}"}[c]
        return N(c, t, txt, v=v)
    if c == 'fstE':
        u = rtype(2); p = gen(Tup(t, u), d + 1)
        return N(c, t, f"fstE({tyt(t)}, {tyt(u)}){{P := {p.txt}}}", P=p)
    if c == 'sndE':
        u = rtype(2); p = gen(Tup(u, t), d + 1)
        return N(c, t, f"sndE({tyt(u)}, {tyt(t)}){{P := {p.txt}}}", P=p)
    if c == 'eqE':
        u = R.choice([INT, STR, Tup(INT, STR)])
        l = gen(u, d + 1); r = l if ch(0.4) else gen(u, d + 1)
        return N(c, t, f"eqE({tyt(u)}){{L := {l.txt}, R := {r.txt}}}", L=l, R=r)
    if c in ('pairE', 'dupP', 'tagged', 'leafP'):
        l, r = gen(t[1], d + 1), gen(t[2], d + 1)
        if c == 'pairE': txt = f"pairE({tyt(t[1])}, {tyt(t[2])}){{L := {l.txt}, R := {r.txt}}}"
        elif c == 'dupP': txt = f"dupP({tyt(t[1])}){{L := {l.txt}, R := {r.txt}}}"
        elif c == 'leafP': txt = f"NewLeafP({l.txt}, {r.txt})"
        else:
            nt = rtype(2); x, _ = lit(nt)
            txt = f"tagged({tyt(t[1])}, {tyt(t[2])}, {tyt(nt)}){{L := {l.txt}, R := {r.txt}, Tag := {x}}}"
        return N(c, t, txt, L=l, R=r)
    if c == 'mkE':
        (x, v), (y, w) = lit(t[1]), lit(t[2])
        return N(c, t, f"mkE({tyt(t[1])}, {tyt(t[2])}){{X := {x}, Y := {y}}}", x=v, y=w)
    if c == 'optE':
        e = gen(t[1], d + 1)
        return N(c, t, f"optE({tyt(t[1])}){{E := {e.txt}}}", E=e)

# ---------------------------------------------------------------- matchers
# Ev rules: (class, branch text, model fn(n, log) -> value)
LOG_ = []
def ev(n):
    for cls, _, fn in EV_RULES:
        if below(n.cls, cls): return fn(n)
    return native(n)
PV = R.choice(['plain', 'generic', 'reflit', 'nestopen'])
def pair_rule(n):
    if PV == 'reflit':
        if n.L.cls == 'lit': return (n.L.v + 1000, ev(n.R))
        return (ev(n.L), ev(n.R))
    if PV == 'nestopen':
        if below(n.L.cls, 'pairE'): LOG_.append("nested")
        return (ev(n.L), ev(n.R))
    return (ev(n.L), ev(n.R))
PTXT = {'plain': "(Ev(P.L), Ev(P.R))",
        'generic': "Flip(Flip((Id(Ev(P.L)), Ev(MkCst(Ev(P.R))))))",
        'reflit': "if (L2 := lit[P.L]) then (L2.V + 1000, Ev(P.R)) else (Ev(P.L), Ev(P.R))",
        'nestopen': "if (Q := pairE[P.L]) then (Print(\"nested\"); (Ev(P.L), Ev(P.R))) else (Ev(P.L), Ev(P.R))"}
FV = R.choice(['plain', 'first'])
ALL_RULES = {
    'lit': ("L.V", lambda n: n.v),
    'pairE': (PTXT[PV], pair_rule),
    'dupP': ("(Ev(P.R), Ev(P.L))", lambda n: (ev(n.R), ev(n.L))),
    'leafP': ("(Ev(P.L) + 1, Ev(P.R))", lambda n: (ev(n.L) + 1, ev(n.R))),
    'tagged': ("Flip((Ev(P.R), Ev(P.L)))", lambda n: (ev(n.L), ev(n.R))),
    'fstE': ("Ev(P.P)(0)" if FV == 'plain' else "First(Id(Ev(P.P)))", lambda n: ev(n.P)[0]),
    'sndE': ("Ev(P.P)(1)", lambda n: ev(n.P)[1]),
    'mkE': ("Flip((P.Y, P.X))", lambda n: (n.x, n.y)),
    'optE': ("option{Ev(P.E)}", lambda n: ('some', ev(n.E))),
}
def eq_rule(n):
    # logic{…} is a failure context: when the comparison fails, the prints of
    # both sides' evaluation are rolled back with it
    mark = len(LOG_)
    same = ev(n.L) == ev(n.R)
    if not same: del LOG_[mark:]
    return same
if V['cmp']: ALL_RULES['eqE'] = ("logic{Ev(P.L) = Ev(P.R)}", eq_rule)
KNOWN = []   # dupP[E] and leafP[E] (fixed in #252)
order = [k for k in ALL_RULES if k != 'lit' and k not in KNOWN and ch(0.8)]
R.shuffle(order)
order = ['lit'] + order
EV_RULES = [(k, ALL_RULES[k][0], ALL_RULES[k][1]) for k in order]
def ev_text():
    L = ["Ev(E:ex(t) where t:type):t ="]
    for i, (k, txt, _) in enumerate(EV_RULES):
        kw = "if" if i == 0 else "else if"
        L.append(f"    {kw} (P := {k}[E]) then {txt}".replace("(P := lit[E]) then L.V", "(P := lit[E]) then P.V"))
    L.append("    else E.Eval()")
    return '\n'.join(L)

DS_ORDER = [k for k in ['pairE', 'dupP', 'fstE', 'sndE', 'mkE', 'optE', 'tagged'] if ch(0.75) and k not in KNOWN]
R.shuffle(DS_ORDER)
DS_THR = R.randint(0, 7) if DS_ORDER and ch(0.5) else None   # last rule: `, Acc > DS_THR`
def ds(n, K):
    acc = K + 1
    if n.cls == 'lit': return f"L{n.v}"
    for k in DS_ORDER:
        if below(n.cls, k):
            if k == DS_ORDER[-1] and DS_THR is not None and not acc > DS_THR: break
            if k in ('pairE', 'dupP', 'tagged'): return f"{k[0]}{acc}({ds(n.L, acc)},{ds(n.R, acc)})"
            if k in ('fstE', 'sndE'): return f"{k[0]}({ds(n.P, acc)})"
            if k == 'mkE': return "M"
            if k == 'optE': return f"O({ds(n.E, acc)})"
    return {'lit': 'lit', 'cst': 'cst'}.get(n.cls, 'ex')
def ds_text():
    L = ["Ds(E:ex(t), K:int where t:type):string =", "    var Acc:int = K", "    set Acc += 1",
         '    if (L := lit[E]) then "L{L.V}"']
    for k in DS_ORDER:
        if k in ('pairE', 'dupP', 'tagged'): b = f'"{k[0]}{{Acc}}({{Ds(P.L, Acc)}},{{Ds(P.R, Acc)}})"'
        elif k in ('fstE', 'sndE'): b = f'"{k[0]}({{Ds(P.P, Acc)}})"'
        elif k == 'mkE': b = '"M"'
        else: b = '"O({Ds(P.E, Acc)})"'
        cl = f", Acc > {DS_THR}" if k == DS_ORDER[-1] and DS_THR is not None else ""
        L.append(f"    else if (P := {k}[E]{cl}) then {b}")
    L.append("    else E.Name()")
    return '\n'.join(L)

# Sz: <decides>; fails on a lit 13 reached through the rules; counts pairE hits
def sz(n, hits):
    if n.cls == 'lit':
        if (n.v >= 12) if SZ_COND else (n.v == 13): raise ValueError
        return 1
    if below(n.cls, 'pairE'):
        hits[id(n)] = hits.get(id(n), 0) + 1
        return sz(n.L, hits) + sz(n.R, hits)
    if n.cls == 'fstE':
        if not SZ_COND: return sz(n.P, hits)
        h2 = dict(hits)
        try: v = sz(n.P, h2)
        except ValueError: return 1     # the else; the call's writes are rolled back
        hits.clear(); hits.update(h2); return v
    return 1
SZ_COND = ch(0.5)
SZ_TEXT = '''Sz(E:ex(t) where t:type)<decides>:int =
    if (L := lit[E]):
        L.V <> 13
        1
    else if (P := pairE[E]):
        set P.Hits += 1
        Sz[P.L] + Sz[P.R]
    else if (F := fstE[E]) then Sz[F.P]
    else 1'''
if SZ_COND:     # (and failing more often, so that the condition catches it)
    SZ_TEXT = SZ_TEXT.replace("(F := fstE[E]) then Sz[F.P]", "(F := fstE[E], S := Sz[F.P]) then S").replace("L.V <> 13", "L.V < 12")

# ---------------------------------------------------------------- main
main, expect = [], []
hits_total = {}
objs = []
for i in range(R.randint(3, 8)):
    t = rtype()
    n = gen(t)
    nm = f"O{i}"
    main.append(f"    {nm}:ex({tyt(t)}) = {n.txt}")
    objs.append((nm, n, t))
    for _ in range(R.randint(1, 3)):
        what = R.choice(['ev', 'ev', 'ds', 'sz'])
        if what == 'ev':
            LOG_.clear(); v = ev(n)
            main.append(f'    Print("ev {nm}: {{{shname(t)}(Ev({nm}))}}")')
            expect.extend(LOG_); expect.append(f"ev {nm}: {show(v, t)}")
        elif what == 'ds':
            K = R.randint(0, 5)
            main.append(f'    Print("ds {nm}: {{Ds({nm}, {K})}}")')
            expect.append(f"ds {nm}: {ds(n, K)}")
        else:
            h = {}
            try:
                s = sz(n, h); ok = True
            except ValueError:
                ok = False
            if ok:
                for k2, c2 in h.items(): hits_total[k2] = hits_total.get(k2, 0) + c2
            main.append(f'    if (S := Sz[{nm}]) then Print("sz {nm}: {{S}} {{{nm}.Hits}}") else Print("sz {nm}: fail {{{nm}.Hits}}")')
            expect.append(f"sz {nm}: {s if ok else 'fail'} {hits_total.get(id(n), 0)}")
    if ch(0.3):
        main.append(f'    Print("native {nm}: {{{shname(t)}({nm}.Eval())}}")')
        expect.append(f"native {nm}: {show(native(n), t)}")
# Sz's fstE rule with its call in the condition: a failed inner call is the
# else (1), and its write to the inner pair's Hits is rolled back
if SZ_COND:
    for i in range(R.randint(1, 2)):
        v1, v2 = R.randint(6, 16), R.randint(0, 13)
        l1, l2, l3 = (N('lit', INT, f"lit{{V := {v}}}", v=v) for v in (v1, v2, 3))
        pin = N('pairE', Tup(INT, INT), f"pairE(int, int){{L := {l1.txt}, R := {l2.txt}}}", L=l1, R=l2)
        top = N('pairE', Tup(INT, INT), '', L=N('fstE', INT, '', P=pin), R=l3)
        main.append(f"    Pin{i}:pairE(int, int) = {pin.txt}")
        main.append(f"    Top{i}:pairE(int, int) = pairE(int, int){{L := fstE(int, int){{P := Pin{i}}}, R := {l3.txt}}}")
        for _ in range(R.randint(1, 2)):
            h = {}; v = sz(top, h)          # cannot fail: the failure is caught in fstE's condition
            for k2, c2 in h.items(): hits_total[k2] = hits_total.get(k2, 0) + c2
            main.append(f'    if (S := Sz[Top{i}]) then Print("szc: {{S}} {{Top{i}.Hits}} {{Pin{i}.Hits}}") else Print("szc: fail")')
            expect.append(f"szc: {v} {hits_total.get(id(top), 0)} {hits_total.get(id(pin), 0)}")
# a closed object type: opening casts that refine to closed types
CS_THR = R.randint(0, 20) if ch(0.5) else None     # `, X := Ev(P.L), X > CS_THR`
for nm, n, t in objs:
    if t == Tup(INT, INT):
        main.append(f'    Print("closed {nm}: {{ClosedSum({nm})}}")')
        if CS_THR is None: v = ev(n.L) + ev(n.R) if below(n.cls, 'pairE') else -1
        else: v = ev(n.L) + ev(n.R) if below(n.cls, 'pairE') and ev(n.L) > CS_THR else -1
        expect.append(f"closed {nm}: {v}")
CLOSED_TXT = '''ClosedSum(E:ex(tuple(int, int))):int =
    if (P := pairE[E]) then Ev(P.L) + Ev(P.R) else -1'''
if CS_THR is not None:
    CLOSED_TXT = CLOSED_TXT.replace("(P := pairE[E]) then Ev(P.L)", f"(P := pairE[E], X := Ev(P.L), X > {CS_THR}) then X")

prog = [f"# genopen seed {seed}", CLASSES, "NewLeafP(L:ex(int), R:ex(string)):leafP = leafP{L := L, R := R}",
        ev_text(), ds_text(), SZ_TEXT, CLOSED_TXT] + list(SHOWN.values()) + ["Main():void ="] + main
print('\n'.join(prog))
open(out_exp, 'w').write("exit=0\n" + ''.join(l + '\n' for l in expect))
