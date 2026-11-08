#!/usr/bin/env python3
"""Random Verse programs with choices (#208), and the output they must print.

  usage: gen-choice.py SEED OUT.verse WANT.out

Each program's statements put clause lists in the three failure contexts
that take a choice's values: an `if` condition and `first{...}` (the first
success) and a `for` (all of them, by generators). The clauses mix choice
bindings, whose alternatives are literals, nested choices, or blocks that
print, change the variable `N` or fail; range generators; filters; and
clauses that print or change `N`; and choices inside expressions, as
`X := (a | b) + (c | d)` and `(Print(...); X) + (a | b) > c`, which the model
expands into the clauses they are lifted to (the code before a choice
first, once, then each choice in order). The expected output comes from the model
below, a backtracking interpreter written from the semantics in
docs/LANGUAGE.md ("Choice"), not from the compiler:

- a choice's values come in spatial order, the leftmost choice slowest;
- `if` and `first{}` take the first success: each alternative starts from
  the state at the choice point (a failed one is rolled back, its output
  too), later alternatives never run, and a failed condition leaves no trace;
- a `for` takes all of them: a choice is a generator whose alternative is
  bound in its filter, so a failing alternative is skipped and rolled back,
  while the effects of a successful filter and of the body stay.
"""
import random
import sys


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
# ('range', name, lo, hi)      only in a for
# ('cmp', lhs, op, c)          lhs: ('var', x) | ('N',) | ('sum', x, y)
# ('setN', d) | ('print', tag)
# ('bindsum', x, a, b)         x := a + b of two names (always succeeds)
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


def apply(c, st):
    """A clause that is no generator: whether it succeeds (mutating st)."""
    k = c[0]
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


def one(cls, st):
    """The first success of the clauses from st (a new state), or None."""
    if not cls:
        return st
    c, rest = cls[0], cls[1:]
    if c[0] == 'choice':
        for a in flat_alts(c[2]):
            s2 = st.copy()
            v = alt_eval(a, s2)
            if v is None:
                continue
            s2.env[c[1]] = v
            r = one(rest, s2)
            if r is not None:
                return r
        return None
    s2 = st.copy()
    if not apply(c, s2):
        return None
    return one(rest, s2)


def expand(cls):
    """The clauses with each sugar clause replaced by those it is lifted to."""
    out = []
    for c in cls:
        out.extend(c[2] if c[0] == 'sugar' else [c])
    return out


def is_gen(c):
    return c[0] in ('choice', 'range')


def run_for(cls, body, st):
    """A for: each success of the clauses runs body(st); effects stay."""
    pre = []
    i = 0
    while i < len(cls) and not is_gen(cls[i]):
        pre.append(cls[i]); i += 1
    groups = []
    while i < len(cls):
        g = cls[i]; i += 1
        fs = []
        while i < len(cls) and not is_gen(cls[i]):
            fs.append(cls[i]); i += 1
        groups.append((g, fs))

    def filters(fs, s):
        for f in fs:
            if not apply(f, s):
                return False
        return True

    def build(gs):
        if not gs:
            body(st)
            return
        (g, fs), more = gs[0], gs[1:]
        if g[0] == 'choice':
            items = [('alt', a) for a in flat_alts(g[2])]
        else:
            items = [('val', v) for v in range(g[2], g[3] + 1)]
        for kind, x in items:
            s0 = st.copy()
            v = alt_eval(x, s0) if kind == 'alt' else x
            if v is None:
                continue
            s0.env[g[1]] = v
            if not filters(fs, s0):
                continue
            st.assign(s0)
            build(more)

    if pre:
        s0 = st.copy()
        if not filters(pre, s0):
            return
        st.assign(s0)
    build(groups)


# --- generation -------------------------------------------------------------

class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.tag = 0

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
            elif r < 0.6:
                c, bound = self.sugar(name, names)
                cls.append(c); has_choice = True
                if bound:
                    names.append(bound)
            elif in_for and r < 0.68:
                lo = self.rng.randint(0, 2)
                cls.append(('range', name, lo, lo + self.rng.randint(0, 2))); names.append(name)
            else:
                cls.append(self.filt(names))
        return cls, names


def interp(names):
    return ' '.join('{' + x + '}' for x in names)


def program(seed):
    rng = random.Random(seed)
    g = Gen(rng)
    lines = ['# generated by scripts/gen-choice.py (#208)', 'Main():void =', '    var N:int = 0']
    st = St()
    for k in range(rng.randint(3, 7)):
        form = rng.choice(['if', 'if', 'for', 'for', 'first'])
        pfx = f'X{k}'
        if form == 'for':
            cls, names = g.clauses(pfx, True)
            bump = rng.randint(0, 2)
            lines.append(f'    for ({", ".join(clause_src(c) for c in cls)}):')
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
