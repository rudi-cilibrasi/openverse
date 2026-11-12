#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-gadt.sh).
# Its model is written from docs/LANGUAGE.md (Classes, Choice), independently of
# the front end's code, for casts that refine type arguments in failure contexts
# other than an if's leading clauses (#243).
"""Refining casts as a clause anywhere in a failure context, with a state oracle.

Generic code over pair(a, b), or an interface ip(a, b) above it, casts to
dup (b = a) or fixi (a = int) in a
<decides> body, option{...}, not, the condition of an if after clauses with
effects, a for's clauses, or first{...} after or before a choice; or, after
clauses with effects in an if, a second cast, to dup, of an object a call
computes among the clauses or of a parameter, whose refinement the branch's
value needs (d = c, for an option of the second's A as a ?d). At times
the cast is inside an expression, `C0 := Peek[H, 1] + T[P].C`, after a call
with an effect that runs first; a for's clauses at times end with a
generator over values of the cast's, `Y2 : array{D.C, D.C + 1}`, and then a
filter or a binding that uses the cast; or the
cast is in a branch of an if written as an expression in a <decides> body,
evaluated only when that branch is. Clauses
before the cast print, add to a cell's var field or call a <decides> function
that does; clauses after it compare, print and add, and bind names that later
code uses. The value is the object's C, or a field whose type is the code's
type parameter only under the refinement.

The model: a cast succeeds iff the object's class is at or below the target;
a failure context that fails undoes everything it did, output included; a
first success of a choice tries its values in order; a for's clauses are a
failure context per element, its body is not. The then-branch and the body
see the cast's name and the names the clauses after it bind.
argv: seed expfile
"""
import random, sys
seed = int(sys.argv[1]); out_exp = sys.argv[2]
R = random.Random(seed)
def ch(p): return R.random() < p

CONTEXTS = ['decides', 'option', 'not', 'if', 'for', 'first', 'second', 'branch']
context = CONTEXTS[seed % len(CONTEXTS)]
target = R.choice(['dup', 'fixi'])
bare = context in ('not',) or (context in ('decides', 'option', 'if', 'second') and ch(0.15))
refined_value = (not bare) and context in ('decides', 'option') and ch(0.4)
# (the cast inside an expression: its C, after a call that adds 1 first)
inside = (not bare) and (not refined_value) and context != 'branch' and ch(0.3)
IFACE = ch(0.3)
CDEF = {'dup': R.randint(1, 6), 'fixi': R.randint(1, 6)}

# objects Main passes: (class, A, B, C)
def make_obj():
    c = target if ch(0.5) else R.choice([k for k in ('dup', 'fixi', 'pair') if k != target])
    a, b = R.randint(0, 9), R.randint(0, 9)
    if c == 'dup':
        cv = CDEF['dup'] if ch(0.5) else R.randint(0, 9)
        return (c, a, b, cv, f'dup(int){{A := {a}, B := {b}, C := {cv}}}')
    if c == 'fixi':
        cv = CDEF['fixi'] if ch(0.5) else R.randint(0, 9)
        return (c, a, b, cv, f'fixi(int){{A := {a}, B := {b}, C := {cv}}}')
    return (c, a, b, None, f'pair(int, int){{A := {a}, B := {b}}}')

class Fail(Exception): pass

# the state: the cell's N and the output so far
class St:
    def __init__(self): self.n = 0; self.out = []
    def snap(self): return (self.n, len(self.out))
    def back(self, s): self.n = s[0]; del self.out[s[1]:]

# clauses before the cast: (text, run(st)) where run may raise Fail
def pre_clause(i):
    k = R.choice(['print', 'add', 'peek'])
    if k == 'print':
        return (f'Print("p{i}")', lambda st, env: st.out.append(f'p{i}'))
    if k == 'add':
        n = R.randint(1, 5)
        def run(st, env): st.n += n
        return (f'set H.N += {n}', run)
    n = 0 if ch(0.2) else R.randint(1, 3)
    def run(st, env):
        if n <= 0: raise Fail()
        st.n += n
        env[f'M{i}'] = n
    return (f'M{i} := Peek[H, {n}]', run)

# clauses after the cast; `names` collects the names they bind
def rest_clause(i, names):
    k = R.choice(['cmp', 'print', 'add', 'bind'])
    if k == 'cmp':
        m = R.randint(0, 6)
        def run(st, env):
            if not env['D'][3] > m: raise Fail()
        return (f'D.C > {m}', run)
    if k == 'print':
        return (f'Print("r{i}")', lambda st, env: st.out.append(f'r{i}'))
    if k == 'add':
        def run(st, env): st.n += env['D'][3]
        return ('set H.N += D.C', run)
    n = R.randint(1, 5)
    names.append(f'Y{i}')
    def run(st, env): env[f'Y{i}'] = env['D'][3] + n
    return (f'Y{i} := D.C + {n}', run)

def below(c, t): return c == t

cast_name = 'D'
def cast_text(x='P'):
    return f'{target}[{x}]' if bare else f'D := {target}[{x}]'
def cast_run(st, env, obj):
    if inside: st.n += 1
    if not below(obj[0], target): raise Fail()
    env['D'] = obj

pres = [pre_clause(i) for i in range(R.randint(0, 2))]
names = []
rests = [rest_clause(i, names) for i in range(R.randint(0, 2))] if not bare else []

def value_text():
    if refined_value:
        return 'D.A' if target == 'dup' else 'D.C'
    parts = ['D.C'] + names[-1:] + ['H.N']
    return ' + '.join(parts) if not bare else 'H.N'
def value_run(st, env):
    if refined_value:
        return env['D'][1] if target == 'dup' else env['D'][3]
    v = (env['D'][3] if not bare else 0) + (env[names[-1]] if names else 0) + st.n
    return v

objs = [make_obj() for _ in range(R.randint(2, 4))]
st = St()

def run_clauses(obj, env):
    for _, r in pres: r(st, env)
    cast_run(st, env, obj)
    for _, r in rests: r(st, env)

hdr = ('''ip(a:type, b:type) := interface:
    Tag():int
''' if IFACE else '') + '''pair(a:type, b:type) := class%s:
    A:a
    B:b%s
dup(t:type) := class(pair(t, t)):
    C:int = %d
fixi(u:type) := class(pair(int, u)):
    C:int = %d
cell := class:
    var N:int = 0
Peek(H:cell, K:int)<transacts><decides>:int =
    K > 0
    set H.N += K
    K''' % ((('(ip(a, b))', '\n    Tag<override>():int = 1') if IFACE else ('', '')) + (CDEF['dup'], CDEF['fixi']))
root = 'ip' if IFACE else 'pair'
G = f'P:{root}(a, b), H:cell where a:type, b:type'
rty = ('b' if target == 'dup' else 'a') if refined_value else 'int'
body = [t for t, _ in pres] + [cast_text()] + [t for t, _ in rests]

if context == 'decides':
    fn = f'F({G})<transacts><decides>:{rty} =\n' + ''.join(f'    {t}\n' for t in body + [value_text()])
    call = lambda o: f'    if (V := F[{o[4]}, H]) then Print("F {{V}} {{H.N}}") else Print("F no {{H.N}}")'
    def model(o):
        s0 = st.snap(); env = {}
        try:
            run_clauses(o, env); v = value_run(st, env)
            st.out.append(f'F {v} {st.n}')
        except Fail:
            st.back(s0); st.out.append(f'F no {st.n}')
elif context == 'option':
    fn = f'F({G})<transacts>:?{rty} =\n    option{{' + '; '.join(body + [value_text()]) + '}\n'
    call = lambda o: f'    if (V := F({o[4]}, H)?) then Print("F {{V}} {{H.N}}") else Print("F no {{H.N}}")'
    def model(o):
        s0 = st.snap(); env = {}
        try:
            run_clauses(o, env); v = value_run(st, env)
            st.out.append(f'F {v} {st.n}')
        except Fail:
            st.back(s0); st.out.append(f'F no {st.n}')
elif context == 'not':
    fn = f'F({G})<transacts>:int =\n    if (not ({"; ".join(body)})) then 1 else 0\n'
    call = lambda o: f'    Print("F {{F({o[4]}, H)}} {{H.N}}")'
    def model(o):
        s0 = st.snap(); env = {}
        try:
            run_clauses(o, env); r = 0
        except Fail:
            r = 1
        st.back(s0)    # not undoes what its operand did
        st.out.append(f'F {r} {st.n}')
elif context == 'if':
    use = R.choice(['D', 'name', 'none']) if not bare else 'none'
    if use == 'name' and not names: use = 'D'
    if use == 'D': then_t, then_r = 'D.C * 10 + H.N', (lambda env: env['D'][3] * 10 + st.n)
    elif use == 'name': then_t, then_r = f'{names[-1]} * 100', (lambda env: env[names[-1]] * 100)
    else: then_t, then_r = 'H.N + 1000', (lambda env: st.n + 1000)
    fn = f'F({G})<transacts>:int =\n    if ({", ".join(body)}) then {then_t} else H.N - 1000\n'
    call = lambda o: f'    Print("F {{F({o[4]}, H)}} {{H.N}}")'
    def model(o):
        s0 = st.snap(); env = {}
        try:
            run_clauses(o, env); v = then_r(env)
        except Fail:
            st.back(s0); v = st.n - 1000
        st.out.append(f'F {v} {st.n}')
elif context == 'for':
    use = R.choice(['D', 'name', 'none'])
    if use == 'name' and not names: use = 'D'
    if use == 'D': body_t, body_r = 'Print("b{D.C}")', (lambda env: st.out.append(f'b{env["D"][3]}'))
    elif use == 'name': body_t, body_r = f'Print("b{{{names[-1]}}}")', (lambda env: st.out.append(f'b{env[names[-1]]}'))
    else: body_t, body_r = 'set H.N += 100', (lambda env: setattr(st, 'n', st.n + 100))
    G2 = f'Ps:[]{root}(a, b), H:cell where a:type, b:type'
    # (at times a generator after the clauses, over values of the cast's)
    gen2 = (not bare) and ch(0.4)
    # (and after it a filter of the cast's, or a binding of it the body uses)
    post = R.choice(['none', 'filter', 'bind']) if gen2 else 'none'
    clauses = ["P : Ps"] + body + (['Y2 : array{D.C, D.C + 1}'] if gen2 else []) + \
        {'none': [], 'filter': ['Y2 > D.C'], 'bind': ['W2 := Y2 + D.C']}[post]
    body2 = ('        Print("y{Y2}")\n' if gen2 else '') + ('        Print("w{W2}")\n' if post == 'bind' else '')
    fn = (f'F({G2})<transacts>:int =\n    R := for ({", ".join(clauses)}):\n'
          f'{body2}        {body_t}\n        H.N\n    R.Length\n')
    def model_all(os):
        count = 0
        for o in os:
            s0 = st.snap(); env = {}
            try:
                run_clauses(o, env)
            except Fail:
                st.back(s0); continue
            for y2 in ((o[3], o[3] + 1) if gen2 else (None,)):
                if post == 'filter' and not y2 > o[3]: continue
                if gen2: st.out.append(f'y{y2}')
                if post == 'bind': st.out.append(f'w{y2 + o[3]}')
                body_r(env); count += 1
        st.out.append(f'F {count} {st.n}')
elif context == 'branch':
    k = R.randint(0, 3)
    side = R.choice(['then', 'else'])
    castv = f'{target}[P].C + H.N'
    other = 'H.N - 100'
    tb, eb = (castv, other) if side == 'then' else (other, castv)
    G3 = 'P:pair(a, b), H:cell, N0:int where a:type, b:type'
    fn = (f'F({G3})<transacts><decides>:int =\n' + ''.join(f'    {t}\n' for t, _ in pres) +
          f'    if (N0 > {k}) then {tb} else {eb}\n')
    ns = {}
    call = lambda o: f'    if (V := F[{o[4]}, H, {ns[id(o)]}]) then Print("F {{V}} {{H.N}}") else Print("F no {{H.N}}")'
    def model(o):
        s0 = st.snap(); env = {}
        try:
            for _, r in pres: r(st, env)
            taken = 'then' if ns[id(o)] > k else 'else'
            if taken == side:
                cast_run(st, env, o); v = o[3] + st.n
            else:
                v = st.n - 100
            st.out.append(f'F {v} {st.n}')
        except Fail:
            st.back(s0); st.out.append(f'F no {st.n}')
elif context == 'second':
    computed = ch(0.6)
    k2 = R.randint(1, 3)
    second = ([f'Q2 := Take[H, Q, {k2}]', 'E := dup[Q2]'] if computed else ['E := dup[Q]'])
    G2 = 'P:pair(a, b), Q:pair(c, d), H:cell where a:type, b:type, c:type, d:type'
    fbody = [t for t, _ in pres] + [cast_text()] + second + [t for t, _ in rests]
    fn = (f'Take(H:cell, Q:pair(c, d), K:int where c:type, d:type)<transacts><decides>:pair(c, d) =\n'
          f'    K > 0\n    set H.N += K\n    Q\n'
          f'F({G2})<transacts>:?d =\n    if ({", ".join(fbody)}) then option{{E.A}} else false\n')
    def make_q():
        a = R.randint(0, 9)
        if ch(0.6): return ('dup', a, f'dup(int){{A := {a}, B := {R.randint(0, 9)}}}')
        return ('pair', a, f'pair(int, int){{A := {a}, B := {R.randint(0, 9)}}}')
    qs = {}
    call = lambda o: (lambda q: f'    if (V := F({o[4]}, {q[2]}, H)?) then Print("F {{V}} {{H.N}}") else Print("F no {{H.N}}")')(qs[id(o)])
    def model(o):
        q = qs[id(o)]
        s0 = st.snap(); env = {}
        try:
            for _, r in pres: r(st, env)
            cast_run(st, env, o)
            if computed: st.n += k2
            if q[0] != 'dup': raise Fail()
            for _, r in rests: r(st, env)
            st.out.append(f'F {q[1]} {st.n}')
        except Fail:
            st.back(s0); st.out.append(f'F no {st.n}')
else:  # first: a choice before or after the cast, its first success taken
    after_cast = not bare and ch(0.5)
    k = R.randint(0, 3)
    if after_cast:
        fbody = [t for t, _ in pres] + [cast_text(), 'X := (D.C | D.C + 1 | D.C + 2)', f'X > {k + 2}'] + [t for t, _ in rests]
    else:
        fbody = [t for t, _ in pres] + ['X := (1 | 2 | 3)', f'X > {k}', cast_text()] + [t for t, _ in rests]
    val = 'X + H.N'
    fn = f'F({G})<transacts>:int =\n    if (V := first{{{"; ".join(fbody + [val])}}}) then V else -1 - H.N\n'
    call = lambda o: f'    Print("F {{F({o[4]}, H)}} {{H.N}}")'
    def model(o):
        s0 = st.snap()
        if after_cast:
            env = {}
            try:
                for _, r in pres: r(st, env)
                cast_run(st, env, o)
            except Fail:
                st.back(s0); st.out.append(f'F {-1 - st.n} {st.n}'); return
            s1 = st.snap()
            for x in (o[3], o[3] + 1, o[3] + 2):
                e2 = dict(env); e2['X'] = x
                try:
                    if not x > k + 2: raise Fail()
                    for _, r in rests: r(st, e2)
                    v = x + st.n; st.out.append(f'F {v} {st.n}'); return
                except Fail:
                    st.back(s1)
            st.back(s0); st.out.append(f'F {-1 - st.n} {st.n}')
        else:
            env = {}
            try:
                for _, r in pres: r(st, env)
            except Fail:
                st.back(s0); st.out.append(f'F {-1 - st.n} {st.n}'); return
            s1 = st.snap()
            for x in (1, 2, 3):
                e2 = dict(env); e2['X'] = x
                try:
                    if not x > k: raise Fail()
                    cast_run(st, e2, o)
                    for _, r in rests: r(st, e2)
                    v = x + st.n; st.out.append(f'F {v} {st.n}'); return
                except Fail:
                    st.back(s1)
            st.back(s0); st.out.append(f'F {-1 - st.n} {st.n}')

main = ['Main()<transacts>:void =', '    H := cell{}']
if context == 'for':
    main.append(f'    Ps:[]{root}(int, int) = array{{{", ".join(o[4] for o in objs)}}}')
    main.append('    Print("F {F(Ps, H)} {H.N}")')
    model_all(objs)
else:
    for o in objs:
        if context == 'second': qs[id(o)] = make_q()
        if context == 'branch': ns[id(o)] = R.randint(0, 5)
        main.append(call(o))
        model(o)
if inside:
    fn = fn.replace(f'D := {target}[P]', f'C0 := Peek[H, 1] + {target}[P].C').replace('D.C', '(C0 - 1)')
print(hdr)
print(fn.rstrip('\n'))
print('\n'.join(main))
with open(out_exp, 'w') as f:
    f.write('exit=0\n' + ''.join(l + '\n' for l in st.out))
