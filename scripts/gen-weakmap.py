#!/usr/bin/env python3
"""Random Verse programs for scripts/fuzz-weakmap.sh, with the output a model
of the Book's map semantics gives (docs/research/weak-map.md).

usage: gen-weakmap.py SEED PROGRAM.verse EXPECTED

Each program keeps three weak maps beside three ordinary maps and gives each
pair the same random stream of writes: a local `var W:weak_map(int, int)` and
`var M:[int]int`; a module-scoped `var G:weak_map(key, int)`, keyed by
objects of a class with <module_scoped_var_weak_map_key>, and `var GM:[int]int`
by their ids; a class's `var F:weak_map(int, int)` and `var HM:[int]int`. The
writes are entry sets, `+=` (which fails on a missing key), whole
replacements of the locals, and calls that write, inside failure contexts
that succeed or fail, nested, and in `for`s whose iterations fail. After each
statement the program prints every lookup of each map. A weak map must agree
with its ordinary map on every lookup, and both with the model, which keeps
the maps as dictionaries and undoes a failure context's writes.
"""
import random
import sys

KEYS = 5

HDR = '''key := class<unique><module_scoped_var_weak_map_key>:
    Id:int

holder := class:
    var F:weak_map(int, int) = map{}

var G:weak_map(key, int) = map{}

Cell(V:?int):string = if (X := V?) then "{X}" else "-"

ShowW(W:weak_map(int, int)):string =
    var S:string = ""
    for (I := 0..%(last)d):
        set S = S + " " + Cell(option{W[I]})
    S

ShowM(M:[int]int):string =
    var S:string = ""
    for (I := 0..%(last)d):
        set S = S + " " + Cell(option{M[I]})
    S

ShowG(Ks:[]key)<transacts>:string =
    var S:string = ""
    for (K : Ks):
        set S = S + " " + Cell(option{G[K]})
    S

PutG(K:key, V:int)<transacts><decides>:void =
    set G[K] = V

AddG(K:key, V:int)<transacts><decides>:void =
    set G[K] += V
''' % {'last': KEYS - 1}


class Gen:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.lines = []
        self.out = []
        # the model: the six maps
        self.m = {'W': {}, 'M': {}, 'G': {}, 'GM': {}, 'F': {}, 'HM': {}}

    # --- the model
    def snap(self):
        return {k: dict(v) for k, v in self.m.items()}

    def show(self):
        row = lambda d: ''.join(' ' + (str(d[i]) if i in d else '-') for i in range(KEYS))
        for w, o in (('W', 'M'), ('G', 'GM'), ('F', 'HM')):
            self.out.append('%s%s |%s' % (w, row(self.m[w]), row(self.m[o])))

    # --- statements: (code lines, a function of the model that applies them
    # and says whether they succeeded)
    def target(self):
        return self.r.choice(['W', 'G', 'F'])

    def write(self, t, k, v, add):
        """One write to the pair `t`, as code lines (inside a failure
        context) and its effect on the model."""
        op = '+=' if add else '='
        if t == 'W':
            code = ['set W[%d] %s %d' % (k, op, v), 'set M[%d] %s %d' % (k, op, v)]
            names = ('W', 'M')
        elif t == 'G':
            if self.r.random() < 0.5:
                code = ['set G[K%d] %s %d' % (k, op, v)]
            else:
                code = ['%s[K%d, %d]' % ('AddG' if add else 'PutG', k, v)]
            code.append('set GM[%d] %s %d' % (k, op, v))
            names = ('G', 'GM')
        else:
            code = ['set H.F[%d] %s %d' % (k, op, v), 'set HM[%d] %s %d' % (k, op, v)]
            names = ('F', 'HM')

        def apply(m):
            for n in names:
                if add:
                    if k not in m[n]:
                        return False
                    m[n][k] += v
                else:
                    m[n][k] = v
            return True
        return code, apply

    def replace(self):
        n = self.r.randrange(0, 3)
        kvs = [(self.r.randrange(KEYS), self.r.randrange(100)) for _ in range(n)]
        lit = 'map{%s}' % ', '.join('%d => %d' % kv for kv in kvs)
        code = ['set W = %s' % lit, 'set M = %s' % lit]

        def apply(m):
            d = {}
            for k, v in kvs:
                d.pop(k, None)
                d[k] = v
            m['W'] = dict(d)
            m['M'] = dict(d)
            return True
        return code, apply

    def clause(self, depth):
        """Lines of a failure context's body and their effect."""
        r = self.r.random()
        if depth < 2 and r < 0.15:
            # a nested failure context: its own success or rollback
            body, apply_in = self.block(depth + 1)
            code = ['if:'] + ['    ' + l for l in body] + ['then:', '    0']

            def apply(m):
                saved = self.copy(m)
                if not apply_in(m):
                    self.restore(m, saved)
                return True
            return code, apply
        if r < 0.25:
            return self.replace()
        k = self.r.randrange(KEYS)
        v = self.r.randrange(1, 50)
        return self.write(self.target(), k, v, self.r.random() < 0.3)

    @staticmethod
    def copy(m):
        return {k: dict(v) for k, v in m.items()}

    @staticmethod
    def restore(m, saved):
        for k in list(m):
            m[k] = saved[k]

    def block(self, depth):
        """The clauses of an `if:`, ending in a test that may fail."""
        parts = [self.clause(depth) for _ in range(self.r.randrange(1, 4))]
        ok = self.r.random() < 0.6
        code = [l for c, _ in parts for l in c] + ['0 = %d' % (0 if ok else 1)]

        def apply(m):
            for _, a in parts:
                if not a(m):
                    return False
            return ok
        return code, apply

    def statement(self):
        r = self.r.random()
        if r < 0.45:
            body, apply = self.block(0)
            code = ['if:'] + ['    ' + l for l in body] + ['then:', '    0', 'else:', '    0']
            saved = self.copy(self.m)
            if not apply(self.m):
                self.restore(self.m, saved)
            return code
        if r < 0.6:
            # a for whose iterations fail on one value
            t = self.target()
            skip = self.r.randrange(KEYS)
            add = self.r.random() < 0.3
            lines = []
            for i in range(KEYS):
                c, a = self.write(t, i, i * 10 + 1, add)
                saved = self.copy(self.m)
                if not (a(self.m) and i != skip):
                    self.restore(self.m, saved)
                lines = c
            # the code of one iteration with I for its index
            code = [l.replace('[%d]' % (KEYS - 1), '[I]').replace('K%d' % (KEYS - 1), 'Ks[I]')
                    .replace('%d' % ((KEYS - 1) * 10 + 1), 'I * 10 + 1') for l in lines]
            return (['for (I := 0..%d):' % (KEYS - 1), '    if:'] +
                    ['        ' + l for l in code] + ['        I <> %d' % skip, '    then:', '        0'])
        if r < 0.7:
            c, a = self.replace()
            a(self.m)
            return c
        k = self.r.randrange(KEYS)
        v = self.r.randrange(1, 50)
        c, a = self.write(self.target(), k, v, self.r.random() < 0.3)
        saved = self.copy(self.m)
        if not a(self.m):
            self.restore(self.m, saved)
        return ['if (%s) {}' % ', '.join(c)]

    def program(self):
        body = ['Main():void =',
                '    var W:weak_map(int, int) = map{}',
                '    var M:[int]int = map{}',
                '    var GM:[int]int = map{}',
                '    var HM:[int]int = map{}',
                '    H := holder{}']
        for i in range(KEYS):
            body.append('    K%d := key{Id := %d}' % (i, i))
        body.append('    Ks := array{%s}' % ', '.join('K%d' % i for i in range(KEYS)))
        show = ['    Print("W{ShowW(W)} |{ShowM(M)}")',
                '    Print("G{ShowG(Ks)} |{ShowM(GM)}")',
                '    Print("F{ShowW(H.F)} |{ShowM(HM)}")']
        for _ in range(self.r.randrange(6, 16)):
            body += ['    ' + l for l in self.statement()]
            body += show
            self.show()
        return HDR + '\n' + '\n'.join(body) + '\n'


def main():
    seed = int(sys.argv[1])
    g = Gen(seed)
    prog = g.program()
    with open(sys.argv[2], 'w') as f:
        f.write(prog)
    with open(sys.argv[3], 'w') as f:
        f.write('\n'.join(g.out) + '\n')


if __name__ == '__main__':
    main()
