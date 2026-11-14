#!/usr/bin/env python3
"""Random Verse programs with choices (#208), and the output they must print.

  usage: gen-choice.py SEED OUT.verse WANT.out

Each program's statements put clause lists in the three failure contexts
that take a choice's values: an `if` condition and `first{...}` (the first
success) and a `for` (all of them, by generators). The clauses mix choice
bindings, whose alternatives are literals, nested choices, or blocks that
print, change the variable `N` or fail; range generators, with choices in
their bounds too; `set N = (a | b) + k | c`; filters; and
clauses that print or change `N`; and choices inside expressions, as
`X := (a | b) + (c | d)` and `(Print(...); X) + (a | b) > c`, which the model
expands into the clauses they are lifted to (the code before a choice
first, once, then each choice in order); and choices in the operands of
`and` and on the right of `or`, also under `not` (#283). The expected output comes from the model
below, a backtracking interpreter written from the semantics in
docs/LANGUAGE.md ("Choice"), not from the compiler:

- a choice's values come in spatial order, the leftmost choice slowest;
- `if` and `first{}` take the first success: each alternative starts from
  the state at the choice point (a failed one is rolled back, its output
  too), later alternatives never run, and a failed condition leaves no trace;
- a `for` takes all of them: a choice is a generator whose alternative is
  bound in its filter, so a failing alternative is skipped and rolled back,
  while the effects of a successful filter and of the body stay;
- `A and B` is A's clauses, then B's; the left of `or` takes its own first
  success, which is then the `or`'s only value (no generator, as the `if`
  it stands for), and only when it has none are the right's values the
  `or`'s; `not` takes its first success and keeps nothing.
"""
import os
import random
import sys

# The rule a `for` follows (docs/research/readings-audit.md, "What a `for`
# undoes"): `OV_FOR_BOOK`, a comma-separated list of the kinds of choice point
# whose fors follow the Book of Verse's rule (`all`: every for), by default
# those the compiler gives that rule; a for that reaches another kind keeps
# the old one. Kinds: plain (ranges), choice (a choice whose alternatives are
# values: none has a choice of its own, a parenthesized choice spliced in),
# composed (one whose alternatives have choices of their own), exclusive (an
# `if` picking a branch with choices, an `or` with a choice on its right),
# call (a call of a function with several values anywhere in the clauses).
FOR_BOOK = set(os.environ.get('OV_FOR_BOOK', 'plain,choice').split(',')) - {''}


def has_call(x):
    """a call of a function with several values: an inlined one's alternatives
    ('pv'), or a call of one ('mcall', 'rcall')"""
    if isinstance(x, tuple) and x and x[0] in ('pv', 'mcall', 'rcall'):
        return True
    return isinstance(x, (tuple, list)) and any(has_call(y) for y in x)


def clause_kinds(c):
    k = c[0]
    kinds = {'call'} if has_call(c) else set()
    if k == 'range':
        kinds.add('plain')
    elif k in ('choice', 'setchoice'):
        alts = flat_alts(c[2]) if k == 'choice' else c[2]
        kinds.add('composed' if any(a[0] == 'plus' for a in alts) else 'choice')
    elif k in ('bchoice', 'or'):
        kinds.add('exclusive')
    return kinds


def for_rule(cls):
    kinds = set()
    for c in cls:
        kinds |= clause_kinds(c)
    return 'book' if 'all' in FOR_BOOK or kinds <= FOR_BOOK else 'old'


class St:
    def __init__(self, n=0, out=None, env=None):
        self.n = n
        self.out = out if out is not None else []
        self.env = env if env is not None else {}

    def copy(self):
        return St(self.n, list(self.out), dict(self.env))

    def assign(self, o):
        self.n, self.out, self.env = o.n, o.out, o.env


# --- alternatives -----------------------------------------------------------
# ('lit', v) | ('print', tag, v) | ('set', d, v) | ('guard', c, v): N > c, then v
# ('pv', tag|None, ref, off): an alternative of a function with several values
#   (#235), inlined: print tag if any, then the argument (a name or literal)
#   plus off
# ('plus', a, k): a's value plus k, the alternatives of `(a | …) + k` spliced
#   into the choice it is an alternative of (#283)

def alt_src(a):
    k = a[0]
    if k == 'lit':
        return str(a[1])
    if k == 'print':
        return f'(Print("{a[1]}"); {a[2]})'
    if k == 'set':
        return f'(set N += {a[1]}; {a[2]})'
    if k == 'guard':
        return f'(N > {a[1]}; {a[2]})'
    raise ValueError(a)


def alt_eval(a, st):
    """The alternative's value, or None when it fails (st is then discarded)."""
    k = a[0]
    if k == 'plus':
        v = alt_eval(a[1], st)
        return None if v is None else v + a[2]
    if k == 'pv':
        if a[1]:
            st.out.append(a[1])
        ref = a[2]
        return (st.env[ref[1]] if ref[0] == 'name' else ref[1]) + a[3]
    if k == 'lit':
        return a[1]
    if k == 'print':
        st.out.append(a[1])
        return a[2]
    if k == 'set':
        st.n += a[1]
        return a[2]
    if k == 'guard':
        return a[2] if st.n > a[1] else None
    raise ValueError(a)


# --- clauses ----------------------------------------------------------------
# ('choice', name, groups): groups is a list of alternatives or nested lists
#   (a parenthesized choice, spliced into the outer one)
# ('range', name, lo, hi)      only in a for; a bound an int or ('name', x)
# ('cmp', lhs, op, c)          lhs: ('var', x) | ('N',) | ('sum', x, y)
# ('setN', d) | ('print', tag)
# ('bindsum', x, a, b)         x := a + b of two names (always succeeds)
# ('rcall', x, f, ref, hi)     x := Rg_i[ref, hi]: a recursive function with
#                              several values (#235), the values ref..hi
# ('bchoice', x, c, alts1, alts2)  x := if (N > c) then (alts1) else (alts2): the
#                              branch picked once, then its alternatives (#235)
# ('setchoice', None, alts)   set N = a | …: a generator whose value N takes
# ('sugar', src, expansion)    a clause with choices inside its expressions:
#                              its source, and the clauses it is lifted to

def flat_alts(groups):
    out = []
    for g in groups:
        out.extend(g if isinstance(g, list) else [g])
    return out


def choice_src(groups):
    parts = []
    for g in groups:
        if isinstance(g, list):
            parts.append('(' + ' | '.join(alt_src(a) for a in g) + ')')
        else:
            parts.append(alt_src(g))
    return ' | '.join(parts)


def lhs_src(l):
    return {'var': lambda: l[1], 'N': lambda: 'N', 'sum': lambda: f'{l[1]} + {l[2]}'}[l[0]]()


def lhs_val(l, st):
    if l[0] == 'var':
        return st.env[l[1]]
    if l[0] == 'N':
        return st.n
    return st.env[l[1]] + st.env[l[2]]


OPS = {'>': lambda a, b: a > b, '<': lambda a, b: a < b, '<>': lambda a, b: a != b,
       '=': lambda a, b: a == b, '<=': lambda a, b: a <= b}


def clause_src(c):
    k = c[0]
    if k == 'rcall':
        ref = c[3]
        return f'{c[1]} := {c[2]}[{ref[1]}, {c[4]}]'
    if k == 'mcall':
        ref = c[3]
        return f'{c[1]} := {c[2]}({ref[1] if ref[0] == "name" else ref[1]})'
    if k == 'bchoice':
        return f'{c[1]} := if (N > {c[2]}) then ({choice_src(c[3])}) else ({choice_src(c[4])})'
    if k == 'sugar':
        return c[1]
    if k == 'choice':
        return f'{c[1]} := {choice_src(c[2])}'
    if k == 'range':
        return f'{c[1]} := {c[2]}..{c[3]}'
    if k == 'cmp':
        return f'{lhs_src(c[1])} {c[2]} {c[3]}'
    if k == 'setN':
        return f'set N += {c[1]}'
    if k == 'print':
        return f'Print("{c[1]}")'
    raise ValueError(c)


def for_clause_src(c):
    """A clause of a `for`: a filter that cannot fail, a print or a `set`, goes
    with one that can, `(E; true?)`, as each filter of a `for` must be able
    to fail (Book of Verse ch. 7, "Each filter must be failable", and its
    tests, for.versetest: `(set Temp = Element; true?)`); it does the same."""
    if c[0] in ('setN', 'print'):
        return f'({clause_src(c)}; true?)'
    return clause_src(c)


def apply(c, st):
    """A clause that is no generator: whether it succeeds (mutating st)."""
    k = c[0]
    if k == 'not':
        # (a failure context of its own, which takes the first success of
        # its clauses; nothing it does stays)
        return one(c[1], st.copy()) is None
    if k == 'bindsum':
        st.env[c[1]] = st.env[c[2]] + st.env[c[3]]
        return True
    if k == 'cmp':
        return OPS[c[2]](lhs_val(c[1], st), c[3])
    if k == 'setN':
        st.n += c[1]
        return True
    if k == 'print':
        st.out.append(c[1])
        return True
    raise ValueError(c)


def alts_at(c, st):
    """A generator's alternatives, from st."""
    k = c[0]
    if k == 'choice':
        return flat_alts(c[2])
    if k == 'bchoice':
        return flat_alts(c[3] if st.n > c[2] else c[4])
    if k == 'rcall':
        lo = st.env[c[3][1]] if c[3][0] == 'name' else c[3][1]
        return [('lit', v) for v in range(lo, c[4] + 1)]
    if k == 'or':
        return c[4]
    if k == 'setchoice':
        return c[2]
    def bound(b):
        return st.env[b[1]] if isinstance(b, tuple) else b
    return [('lit', v) for v in range(bound(c[2]), bound(c[3]) + 1)]


def take(c, st, v):
    """A generator's value v, bound to its name, or for `set N = …` to N."""
    if c[0] == 'setchoice':
        st.n = v
    else:
        st.env[c[1]] = v


def or_left(c, st):
    """The left of `or`, a failure context of its own that takes the first
    success of its clauses: the state after it, with the `or`'s name bound
    to its value (the names it binds are its own), or None."""
    r = one(c[2], st.copy())
    if r is None:
        return None
    v = r.env[c[3]]
    r.env = dict(st.env)
    r.env[c[1]] = v
    return r


def one(cls, st):
    """The first success of the clauses from st (a new state), or None."""
    if not cls:
        return st
    c, rest = cls[0], cls[1:]
    if c[0] == 'or':
        # (its left's value, if it has one, is its only one: its right never runs)
        r = or_left(c, st)
        if r is not None:
            return one(rest, r)
    if is_gen(c):
        for a in alts_at(c, st):
            s2 = st.copy()
            v = alt_eval(a, s2)
            if v is None:
                continue
            take(c, s2, v)
            r = one(rest, s2)
            if r is not None:
                return r
        return None
    s2 = st.copy()
    if not apply(c, s2):
        return None
    return one(rest, s2)


def expand(cls):
    """The clauses with each sugar clause replaced by those it is lifted to,
    and each call of a function with several values by the choice it is
    inlined to."""
    out = []
    for c in cls:
        if c[0] == 'sugar':
            out.extend(c[2])
        elif c[0] == 'mcall':
            out.append(('choice', c[1], c[4]))
        else:
            out.append(c)
    return out


def is_gen(c):
    return c[0] in ('choice', 'range', 'bchoice', 'rcall', 'or', 'setchoice')


def run_for(cls, body, st):
    """A for, under the rule `for_rule` gives for its clauses."""
    if for_rule(cls) == 'book':
        return run_for_book(cls, body, st)
    return run_for_old(cls, body, st)


def run_for_book(cls, body, st):
    """A for, by the Book of Verse's rule (FlowControl/for.versetest 317-392,
    Range.versetest 140, 159): its clauses are one search, depth first, as a
    first-success context's are, that goes on after each success. Reaching
    the body commits what was done since the last success; a failure undoes
    back to the most recent choice point (an alternative's own clauses, or
    an alternative whose later clauses found no success, as a whole); when
    the search ends, what it did since the last success is undone. So a
    choice point none of whose alternatives reaches the body fails."""
    def go(i, s):
        # (the state after the last body this subtree ran, or None when it
        # ran none: s is then dropped, undone)
        if i == len(cls):
            st.assign(s)
            body(st)
            return st.copy()
        c = cls[i]
        if c[0] == 'or':
            r = or_left(c, s)
            if r is not None:
                return go(i + 1, r)
        if not is_gen(c):
            return go(i + 1, s) if apply(c, s) else None
        cur, got = s, None
        for a in alts_at(c, s):
            s0 = cur.copy()
            v = alt_eval(a, s0)
            if v is None:
                continue
            take(c, s0, v)
            r = go(i + 1, s0)
            if r is not None:
                cur = got = r
        return got

    go(0, st.copy())


def run_for_old(cls, body, st):
    """A for: each success of the clauses runs body(st). A generator's
    alternative and the clauses after it, up to the next generator, are one
    unit: rolled back when one of them fails, else kept (in st) before the
    next generator runs, as the body's effects are. An `or` whose left
    succeeds has that one value, and is no generator (as the `if` it stands
    for, #331): the clauses after it are in the same unit as those before."""
    def go(i, s):
        if i == len(cls):
            st.assign(s)
            body(st)
            return
        c = cls[i]
        if c[0] == 'or':
            r = or_left(c, s)
            if r is not None:
                go(i + 1, r)
                return
        if not is_gen(c):
            if apply(c, s):
                go(i + 1, s)
            return
        st.assign(s)
        for a in alts_at(c, st):
            s0 = st.copy()
            v = alt_eval(a, s0)
            if v is None:
                continue
            take(c, s0, v)
            go(i + 1, s0)

    go(0, st.copy())


# --- generation -------------------------------------------------------------

class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.tag = 0
        # functions with several values (#235): name, offset, printing tag
        self.fns = []
        # recursive ones (#235), effect-free: names
        self.rfns = []

    def fresh_tag(self, pfx):
        self.tag += 1
        return f'{pfx}{self.tag}'

    def alt(self):
        r = self.rng.random()
        v = self.rng.randint(0, 9)
        if r < 0.45:
            return ('lit', v)
        if r < 0.65:
            return ('print', self.fresh_tag('a'), v)
        if r < 0.82:
            return ('set', self.rng.randint(1, 3), v)
        return ('guard', self.rng.randint(0, 4), v)

    def choice(self, name):
        groups = []
        for _ in range(self.rng.randint(2, 3)):
            if self.rng.random() < 0.15:
                groups.append([self.alt() for _ in range(2)])
            else:
                groups.append(self.alt())
        return ('choice', name, groups)

    def filt(self, names):
        r = self.rng.random()
        if r < 0.15:
            return ('setN', self.rng.randint(1, 2))
        if r < 0.27:
            return ('print', self.fresh_tag('c'))
        op = self.rng.choice(list(OPS))
        if names and r < 0.75:
            lhs = ('var', self.rng.choice(names))
            c = self.rng.randint(0, 9)
        elif len(names) >= 2 and r < 0.88:
            x, y = self.rng.sample(names, 2)
            lhs = ('sum', x, y)
            c = self.rng.randint(0, 18)
        else:
            lhs = ('N',)
            c = self.rng.randint(0, 6)
        return ('cmp', lhs, op, c)

    def plain_alts(self):
        return [self.alt() for _ in range(self.rng.randint(2, 3))]

    def sugar(self, name, names):
        """A clause with choices inside its expressions."""
        self.tag += 1
        t = self.tag
        a, b = f'$a{t}', f'$b{t}'
        if names and self.rng.random() < 0.5:
            # a filter: [(Print(u); ] X [)] + (alts) op c
            x = self.rng.choice(names)
            alts = self.plain_alts()
            op = self.rng.choice(list(OPS))
            c = self.rng.randint(0, 18)
            pre = []
            lhs = x
            if self.rng.random() < 0.5:
                u = self.fresh_tag('u')
                lhs = f'(Print("{u}"); {x})'
                pre = [('print', u)]
            src = f'{lhs} + ({choice_src(alts)}) {op} {c}'
            return ('sugar', src, pre + [('choice', a, alts), ('cmp', ('sum', x, a), op, c)]), None
        # a binding: name := (alts) + (alts)
        al, ar = self.plain_alts(), self.plain_alts()
        src = f'{name} := ({choice_src(al)}) + ({choice_src(ar)})'
        return ('sugar', src, [('choice', a, al), ('choice', b, ar), ('bindsum', name, a, b)]), name

    def operand(self, names):
        """An operand of `and` or `or` that may fail: its source, the clauses
        it is, and the name of its value. Its names are its own."""
        op = self.rng.choice(list(OPS))
        if names and self.rng.random() < 0.4:
            x = self.rng.choice(names)
            c = self.rng.randint(0, 9)
            return f'{x} {op} {c}', [('cmp', ('var', x), op, c)], x
        y = self.fresh_tag('L')
        alts = self.plain_alts()
        c = self.rng.randint(0, 9)
        return (f'({y} := {choice_src(alts)}; {y} {op} {c})',
                [('choice', y, alts), ('cmp', ('var', y), op, c)], y)

    def values(self, names):
        """A choice, or a call of a function with several values: its source
        and its alternatives."""
        if self.fns and self.rng.random() < 0.3:
            f, off, tag = self.rng.choice(self.fns)
            ref = ('name', self.rng.choice(names)) if names and self.rng.random() < 0.6 else ('lit', self.rng.randint(0, 9))
            return f'{f}({ref[1]})', [('pv', tag, ref, 0), ('pv', None, ref, off)]
        alts = self.plain_alts()
        return f'({choice_src(alts)})', alts

    def logic(self, name, names):
        """A clause with a choice in an operand of `and` or on the right of
        `or` (#283), and what it is: `A and B` is A's clauses, then B's; the
        left of `or` takes its first success, and only when it has none are
        the `or`'s values the right's. Each operand is a scope of its own."""
        # (a filter binds no name: only after one, as for `sugar`'s, so that
        # clauses with a choice bind a name, which `first{…}` gives)
        r = self.rng.random() * (1 if names else 0.7)
        self.tag += 1
        a = f'$a{self.tag}'
        if r < 0.35:
            # a binding: name := (A and B)
            src, cls, _ = self.operand(names)
            vsrc, alts = self.values(names)
            return ('sugar', f'{name} := ({src} and {vsrc})', cls + [('choice', name, alts)]), name
        if r < 0.7:
            # a binding: name := (A or B)
            src, cls, v = self.operand(names)
            vsrc, alts = self.values(names)
            return ('sugar', f'{name} := ({src} or {vsrc})', [('or', name, cls, v, alts)]), name
        # a filter: A and (B) op c, alone or under `not`, which takes its
        # first success and keeps nothing it does
        src, cls, _ = self.operand(names)
        vsrc, alts = self.values(names)
        op = self.rng.choice(list(OPS))
        c = self.rng.randint(0, 9)
        filt = cls + [('choice', a, alts), ('cmp', ('var', a), op, c)]
        src = f'{src} and {vsrc} {op} {c}'
        if r < 0.85:
            return ('sugar', src, filt), None
        return ('sugar', f'not ({src})', [('not', filt)]), None

    def clauses(self, prefix, in_for):
        """1-5 clauses with at least one choice."""
        cls = []
        names = []
        n = self.rng.randint(1, 5)
        has_choice = False
        for i in range(n):
            name = f'{prefix}_{i}'
            r = self.rng.random()
            if r < 0.45 or (i == n - 1 and not has_choice):
                cls.append(self.choice(name)); names.append(name); has_choice = True
            elif r < 0.52:
                cls.append(('bchoice', name, self.rng.randint(0, 4), self.plain_alts(), self.plain_alts()))
                names.append(name); has_choice = True
            elif self.rfns and r < 0.54:
                f = self.rng.choice(self.rfns)
                ref = ('name', self.rng.choice(names)) if names and self.rng.random() < 0.5 else ('lit', self.rng.randint(0, 6))
                cls.append(('rcall', name, f, ref, self.rng.randint(0, 9)))
                names.append(name); has_choice = True
            elif self.fns and r < 0.56:
                f, off, tag = self.rng.choice(self.fns)
                ref = ('name', self.rng.choice(names)) if names and self.rng.random() < 0.6 else ('lit', self.rng.randint(0, 9))
                cls.append(('mcall', name, f, ref, [('pv', tag, ref, 0), ('pv', None, ref, off)]))
                names.append(name); has_choice = True
            elif r < 0.6:
                c, bound = self.sugar(name, names)
                cls.append(c); has_choice = True
                if bound:
                    names.append(bound)
            elif r < 0.68:
                c, bound = self.logic(name, names)
                cls.append(c); has_choice = True
                if bound:
                    names.append(bound)
            elif in_for and r < 0.76:
                lo = self.rng.randint(0, 2)
                hi = lo + self.rng.randint(0, 2)
                if self.rng.random() < 0.4:
                    # (a choice in a bound, #283: lifted before the range,
                    # which is then a range for each of its values)
                    self.tag += 1
                    a = f'$a{self.tag}'
                    alts = self.plain_alts()
                    if self.rng.random() < 0.5:
                        src, rg = f'{name} := ({choice_src(alts)})..{hi + 2}', ('range', name, ('name', a), hi + 2)
                    else:
                        src, rg = f'{name} := {lo}..({choice_src(alts)})', ('range', name, lo, ('name', a))
                    cls.append(('sugar', src, [('choice', a, alts), rg])); has_choice = True
                else:
                    cls.append(('range', name, lo, hi))
                names.append(name)
            elif names and r < 0.8:
                # (#283) set N = (a | …) + k | b: a composed alternative of a
                # set's choice, its own alternatives spliced in, N taking each
                # (binding no name: only after one, as `sugar`'s filter)
                k = self.rng.randint(1, 3)
                inner, more = self.plain_alts(), self.plain_alts()
                src = f'set N = ({choice_src(inner)}) + {k} | {choice_src(more)}'
                alts = [('plus', a, k) for a in inner] + more
                cls.append(('sugar', src, [('setchoice', None, alts)])); has_choice = True
            else:
                cls.append(self.filt(names))
        return cls, names


def interp(names):
    return ' '.join('{' + x + '}' for x in names)


def program(seed):
    rng = random.Random(seed)
    g = Gen(rng)
    lines = ['# generated by scripts/gen-choice.py (#208)']
    for i in range(rng.randint(0, 3)):
        off = rng.randint(1, 5)
        tag = f'm{i}' if rng.random() < 0.5 else None
        g.fns.append((f'Mv{i}', off, tag))
        first = f'(Print("{tag}"); X)' if tag else 'X'
        lines.append(f'Mv{i}(X:int):int = {first} | X + {off}')
    for i in range(rng.randint(0, 2)):
        g.rfns.append(f'Rg{i}')
        lines += [f'Rg{i}(A:int, B:int)<computes><decides>:int =', '    A <= B', f'    A | Rg{i}[A + 1, B]']
    lines += ['Main():void =', '    var N:int = 0']
    st = St()
    for k in range(rng.randint(3, 7)):
        form = rng.choice(['if', 'if', 'for', 'for', 'first'])
        pfx = f'X{k}'
        if form == 'for':
            cls, names = g.clauses(pfx, True)
            bump = rng.randint(0, 2)
            lines.append(f'    for ({", ".join(for_clause_src(c) for c in cls)}):')
            if bump:
                lines.append(f'        set N += {bump}')
            lines.append(f'        Print("b{k} {interp(names)} {{N}}")')

            def body(s, names=names, bump=bump, k=k):
                s.n += bump
                s.out.append(f'b{k} ' + ' '.join(str(s.env[x]) for x in names) + f' {s.n}')
            run_for(expand(cls), body, st)
            # (the names of the for are not visible after it)
            st.env = {}
        elif form == 'if':
            cls, names = g.clauses(pfx, False)
            lines.append(f'    if ({", ".join(clause_src(c) for c in cls)}) then '
                         f'Print("t{k} {interp(names)} {{N}}") else Print("e{k} {{N}}")')
            r = one(expand(cls), st)
            if r is None:
                st.out.append(f'e{k} {st.n}')
            else:
                st.assign(r)
                st.out.append(f't{k} ' + ' '.join(str(st.env[x]) for x in names) + f' {st.n}')
                st.env = {}
        else:
            cls, names = g.clauses(pfx, False)
            last = names[-1]
            lines.append(f'    if (V{k} := first{{{"; ".join(clause_src(c) for c in cls)}; {last}}}) then '
                         f'Print("f{k} {{V{k}}} {{N}}") else Print("g{k} {{N}}")')
            r = one(expand(cls), st)
            if r is None:
                st.out.append(f'g{k} {st.n}')
            else:
                v = r.env[last]
                st.assign(r)
                st.env = {}
                st.out.append(f'f{k} {v} {st.n}')
    lines.append(f'    Print("end {{N}}")')
    st.out.append(f'end {st.n}')
    return '\n'.join(lines) + '\n', '\n'.join(st.out) + '\n'


def main():
    seed = int(sys.argv[1])
    src, want = program(seed)
    with open(sys.argv[2], 'w') as f:
        f.write(src)
    with open(sys.argv[3], 'w') as f:
        f.write(want)


if __name__ == '__main__':
    main()
