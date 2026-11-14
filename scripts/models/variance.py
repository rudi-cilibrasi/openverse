#!/usr/bin/env python3
"""Variance of parametric classes (Book of Verse ch. 10, "Instantiation and
Identity"; docs/research/variance.md), modeled as the Book has it and as
openverse can take it.

A class `c(t)` has members that use `t` at random: a field (covariant), a
`var` field (invariant), a getter (covariant), a method taking a `t`
(contravariant), one taking and giving one (invariant), one taking a
callback of `t` (covariant), or none. A subclass `d(t)` may add members and
override `c`'s. The program converts an instance at one type argument to
another (`entity`, `player` below it) and uses it through the target type.

The model predicts the Book's verdict from the members' polarities (the most
permissive variance consistent with all of them), and openverse's: Verse
Core types a reference by its object's own class, so every concrete class of
the source type must allow the conversion by its *fields* alone (no field of
`t`: bivariant; fields only read: covariant; a `var` one: invariant; Core
has no contravariance). Accepted: the program's output. Refused: the
message's words.

  usage: variance.py SEED EXPECTED_FILE > program.verse
"""
import random
import sys

seed = int(sys.argv[1])
rng = random.Random(seed)

ROLES = ['co_field', 'var_field', 'int_field', 'getter', 'taker', 'ident', 'plain', 'callback']
POL = {'co_field': 'co', 'var_field': 'inv', 'int_field': 'bi', 'getter': 'co', 'taker': 'contra',
       'ident': 'inv', 'plain': 'bi', 'callback': 'co'}


def join(a, b):
    if a == 'bi':
        return b
    if b == 'bi':
        return a
    return a if a == b else 'inv'


def core_join(a, b):
    order = {'bi': 0, 'co': 1, 'inv': 2}
    return a if order[a] >= order[b] else b


counter = [0]


def fresh():
    counter[0] += 1
    return counter[0]


class Member:
    def __init__(self, role, owner):
        self.role = role
        self.owner = owner
        self.k = fresh()
        self.name = {'co_field': 'F', 'var_field': 'W', 'int_field': 'K', 'getter': 'G', 'taker': 'M',
                     'ident': 'I', 'plain': 'N', 'callback': 'E'}[role] + str(self.k)
        self.field = None  # for getters and callbacks: the field of t they read


def draw_members(owner, n, tfields):
    ms = []
    for _ in range(n):
        role = rng.choice(ROLES)
        if role in ('getter', 'callback') and not tfields:
            role = 'co_field'
        m = Member(role, owner)
        if role in ('co_field', 'var_field'):
            tfields.append(m)
        if role in ('getter', 'callback'):
            m.field = rng.choice(tfields)
        ms.append(m)
    return ms


c_members = draw_members('c', rng.randint(1, 3), [])
c_tfields = [m for m in c_members if m.role in ('co_field', 'var_field')]
has_d = rng.random() < 0.6
d_tfields = list(c_tfields)
d_members = draw_members('d', rng.randint(0, 2), d_tfields) if has_d else []
# overrides in d of c's takers and getters
overrides = []
if has_d:
    for m in c_members:
        if m.role in ('taker', 'getter', 'plain') and rng.random() < 0.5:
            overrides.append(m)


# a class that fixes c's type argument to player (#142): when it overrides a
# method of c, Verse Core records its pins, and a pinned argument is
# invariant there (docs/research/variance.md, "Pins")
has_pc = rng.random() < 0.3
pc_over = None
if has_pc:
    cands = [m for m in c_members if m.role in ('taker', 'plain')]
    if cands and rng.random() < 0.7:
        pc_over = rng.choice(cands)


def book_var(members):
    v = 'bi'
    for m in members:
        v = join(v, POL[m.role])
    return v


def core_var(fields):
    v = 'bi'
    for m in fields:
        v = core_join(v, 'inv' if m.role == 'var_field' else 'co')
    return v


var_c = book_var(c_members)
var_d = join(var_c, book_var(d_members))
core_c = core_var(c_tfields)
core_d = core_var(d_tfields)
SUB = {('player', 'entity'), ('player', 'player'), ('entity', 'entity')}


def below(x, y):
    return (x, y) in SUB


def book_ok(v, a, b):
    """The Book: a c(b) is a c(a) by variance v."""
    if a == b:
        return True
    return {'bi': True, 'co': below(b, a), 'contra': below(a, b), 'inv': False}[v]


def core_ok(v, a, b):
    if a == b:
        return True
    return {'bi': True, 'co': below(b, a), 'inv': False}[v]


# the conversion: static class, object class
cases = [('c', 'c')] + ([('c', 'd'), ('d', 'd')] if has_d else [])
static, obj = rng.choice(cases)
A = rng.choice(['entity', 'player'])
B = rng.choice(['entity', 'player'])
static_var = var_c if static == 'c' else var_d
# the source type's concrete classes: obj's static type is obj(B), whose
# classes are obj and those below it
src_classes = (['c'] + (['d'] if has_d else []) + (['pc'] if has_pc else [])) if obj == 'c' else [obj]
cores = {'c': core_c, 'd': core_d, 'pc': 'inv' if pc_over else core_c}
bok = book_ok(static_var, A, B)
cok = all(core_ok(cores[k], A, B) for k in src_classes)

ids = iter(range(10, 1000))


def value(t):
    i = next(ids)
    if t == 'entity':
        return f'entity{{ID := {i}}}', i
    return f'player{{ID := {i}, Name := "p{i}"}}', i


def decl(m, t='t'):
    r = m.role
    if r == 'co_field':
        return f'    {m.name}:{t}'
    if r == 'var_field':
        return f'    var {m.name}:{t}'
    if r == 'int_field':
        return f'    {m.name}:int'
    if r == 'getter':
        return f'    {m.name}():{t} = {m.field.name}'
    if r == 'taker':
        return f'    {m.name}(X:{t}):int = {m.k}'
    if r == 'ident':
        return f'    {m.name}(X:{t}):{t} = X'
    if r == 'plain':
        return f'    {m.name}():int = {m.k}'
    if r == 'callback':
        return f'    {m.name}(F:type{{_(:{t}):void}}):void = F({m.field.name})'


out = []
out.append('entity := class:\n    ID:int')
out.append('player := class(entity):\n    Name:string')
out.append('ShowEntity(E:entity):void = Print("cb {E.ID}")')
out.append('ShowPlayer(E:player):void = Print("cb {E.ID}")')
out.append('c(t:type) := class:\n' + '\n'.join(decl(m) for m in c_members))
if has_d:
    body = [decl(m) for m in d_members]
    for m in overrides:
        if m.role == 'taker':
            body.append(f'    {m.name}<override>(X:t):int = {m.k + 100}')
        elif m.role == 'getter':
            body.append(f'    {m.name}<override>():t = {m.field.name}')
        else:
            body.append(f'    {m.name}<override>():int = {m.k + 100}')
    out.append('d(t:type) := class(c(t)):' + ('\n' + '\n'.join(body) if body else ''))

if has_pc:
    body = []
    if pc_over is not None:
        if pc_over.role == 'taker':
            body.append(f'    {pc_over.name}<override>(X:player):int = {pc_over.k + 200}')
        else:
            body.append(f'    {pc_over.name}<override>():int = {pc_over.k + 200}')
    else:
        body.append('    PcTag:int = 0')
    out.append('pc := class(c(player)):\n' + '\n'.join(body))

# construction of obj(B): every field of obj
fields = [m for m in (c_members + (d_members if obj == 'd' else [])) if m.role in ('co_field', 'var_field', 'int_field')]
vals = {}
inits = []
for m in fields:
    if m.role == 'int_field':
        vals[m.name] = m.k
        inits.append(f'{m.name} := {m.k}')
    else:
        src, i = value(B)
        vals[m.name] = i
        inits.append(f'{m.name} := {src}')
ctor = f'{obj}({B}){{' + ', '.join(inits) + '}'

main = ['Main():void =', f'    V:{static}({A}) = {ctor}']
expect = []
visible = c_members + (d_members if static == 'd' else [])
for m in visible:
    r = m.role
    over = m in overrides and obj == 'd'
    if r in ('co_field', 'var_field'):
        main.append(f'    Print("{{V.{m.name}.ID}}")')
        expect.append(str(vals[m.name]))
    elif r == 'int_field':
        main.append(f'    Print("{{V.{m.name}}}")')
        expect.append(str(m.k))
    elif r == 'getter':
        main.append(f'    Print("{{V.{m.name}().ID}}")')
        expect.append(str(vals[m.field.name]))
    elif r == 'taker':
        src, _ = value(A)
        main.append(f'    Print("{{V.{m.name}({src})}}")')
        expect.append(str(m.k + 100 if over else m.k))
    elif r == 'ident':
        src, i = value(A)
        main.append(f'    Print("{{V.{m.name}({src}).ID}}")')
        expect.append(str(i))
    elif r == 'plain':
        main.append(f'    Print("{{V.{m.name}()}}")')
        expect.append(str(m.k + 100 if over else m.k))
    elif r == 'callback':
        fn = 'ShowEntity' if A == 'entity' else 'ShowPlayer'
        main.append(f'    V.{m.name}({fn})')
        expect.append(f'cb {vals[m.field.name]}')
# a write through the target, where it may: a var field at equal arguments
for m in visible:
    if m.role == 'var_field' and A == B:
        src, i = value(A)
        main.append(f'    set V.{m.name} = {src}')
        main.append(f'    Print("{{V.{m.name}.ID}}")')
        expect.append(str(i))
        break
main.append('    Print("done")')
expect.append('done')
out.append('\n'.join(main))
print('\n'.join(out))

with open(sys.argv[2], 'w') as f:
    if bok and cok:
        f.write('exit=0\n' + '\n'.join(expect) + '\n')
    elif not bok:
        word = 'is invariant in t' if static_var == 'inv' else ' in t'
        f.write(f'exit=4\n{word}\n')
    else:
        f.write('exit=4\nbut not in openverse yet\n')
