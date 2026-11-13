#!/usr/bin/env python3
"""Random Verse programs for scripts/fuzz-equality.sh: = and <> between values
of many types, the empty value at every depth (false, (), "", array{},
map{}, an empty option), compared directly, inside arrays, options, tuples,
maps and one struct's instances, through a generic function (X = false at
t = []int), as map keys and as searched array elements. The expected output
is computed here from the Book of Verse's equality: two values are equal
when they are one value (the empty value is one value; values of different
types are different, but a struct at two instances compares field by field).

usage: gen-equality.py SEED [--expected]: the program, or its expected output
"""
import random
import sys

E = 'E'  # the one empty value


class T:
    """A type: its Verse spelling and how to make a random value of it."""


def types():
    # (Verse type, kind, element types)
    return [
        ('int', 'int'), ('logic', 'logic'), ('void', 'unit'), ('tuple()', 'unit'),
        ('?int', ('opt', 'int')), ('?logic', ('opt', 'logic')), ('?[]int', ('opt', ('arr', 'int'))),
        ('[]int', ('arr', 'int')), ('[]logic', ('arr', 'logic')), ('[]?int', ('arr', ('opt', 'int'))),
        ('[][]int', ('arr', ('arr', 'int'))), ('string', ('arr', 'char')),
        ('[int]int', ('map', 'int', 'int')), ('[logic]int', ('map', 'logic', 'int')),
        ('[[]int]logic', ('map', ('arr', 'int'), 'logic')),
        ('tuple(logic, int)', ('tup', ['logic', 'int'])), ('tuple(void, int)', ('tup', ['unit', 'int'])),
        ('tuple(?int, []int)', ('tup', [('opt', 'int'), ('arr', 'int')])),
        ('p(logic)', ('p', 'logic')), ('p(void)', ('p', 'unit')), ('p(?int)', ('p', ('opt', 'int'))),
        ('p([]int)', ('p', ('arr', 'int'))),
    ]


def spell(k):
    """The Verse spelling of a kind."""
    if k == 'int': return 'int'
    if k == 'logic': return 'logic'
    if k == 'unit': return 'void'
    if k == 'char': return 'char'
    tag = k[0]
    if tag == 'opt': return '?' + spell(k[1])
    if tag == 'arr': return 'string' if k[1] == 'char' else '[]' + spell(k[1])
    if tag == 'map': return '[' + spell(k[1]) + ']' + spell(k[2])
    if tag == 'tup': return 'tuple(' + ', '.join(spell(x) for x in k[1]) + ')'
    if tag == 'p': return 'p(' + spell(k[1]) + ')'
    raise ValueError(k)


class G:
    def __init__(self, r):
        self.r = r

    def value(self, k, d=2):
        """(Verse expression at kind k, model value)."""
        r = self.r
        if k == 'int':
            n = r.choice([0, 1, 2, 65])
            return str(n), ('i', n)
        if k == 'char':
            c = r.choice('ab')
            return "'" + c + "'", ('c', ord(c))
        if k == 'logic':
            if r.random() < 0.6: return 'false', E
            return 'true', ('t',)
        if k == 'unit':
            return r.choice(['false', '()']), E
        tag = k[0]
        if tag == 'opt':
            if d == 0 or r.random() < 0.45: return 'false', E
            e, m = self.value(k[1], d - 1)
            return 'option{' + e + '}', ('some', m)
        if tag == 'arr':
            n = 0 if d == 0 or r.random() < 0.4 else r.randint(1, 2)
            if k[1] == 'char':
                s = ''.join(r.choice('ab') for _ in range(n))
                return '"' + s + '"', E if n == 0 else ('arr', tuple(('c', ord(c)) for c in s))
            if n == 0:
                return r.choice(['array{}', 'false']), E
            es = [self.value(k[1], d - 1) for _ in range(n)]
            return 'array{' + ', '.join(e for e, _ in es) + '}', ('arr', tuple(m for _, m in es))
        if tag == 'map':
            if d == 0 or r.random() < 0.45:
                return 'map{}', E
            ps = []
            keys = []
            for _ in range(r.randint(1, 2)):
                ke, km = self.value(k[1], d - 1)
                ve, vm = self.value(k[2], d - 1)
                # (a key given twice keeps its last value, at its last position)
                idx = [i for i, (a, _) in enumerate(keys) if a == km]
                for i in reversed(idx):
                    del keys[i]
                keys.append((km, vm))
                ps.append(ke + ' => ' + ve)
            return 'map{' + ', '.join(ps) + '}', ('map', tuple(keys))
        if tag == 'tup':
            es = [self.value(x, d - 1) for x in k[1]]
            return '(' + ', '.join(e for e, _ in es) + ')', ('tup', tuple(m for _, m in es))
        if tag == 'p':
            e, m = self.value(k[1], d - 1)
            return spell(k) + '{X := ' + e + '}', ('p', m)
        raise ValueError(k)


def head(k):
    return k if isinstance(k, str) else k[0]


def comparable_pair(a, b):
    """Not a tuple against an array or a map: a tuple is the array of its
    elements, which openverse compares only where it converts."""
    return {head(a), head(b)} not in ({'tup', 'arr'}, {'tup', 'map'})


def program(seed):
    r = random.Random(seed)
    g = G(r)
    ts = types()
    lines = ['p(t:type) := struct{X:t}',
             'Show(B:logic):string = if (B?) then "y" else "n"',
             'IsFalse(X:t where t:subtype(comparable))<decides>:void = X = false',
             'IsEmptyString(X:t where t:subtype(comparable))<decides>:void = X = ""',
             'Same(X:t, Y:t where t:subtype(comparable))<decides>:void = X = Y',
             'Main():void =']
    out = []
    vars_ = []
    for i in range(r.randint(4, 8)):
        name, k = r.choice(ts)
        e, m = g.value(k)
        lines.append(f'    V{i}:{name} = {e}')
        vars_.append((f'V{i}', k, m))
    for _ in range(r.randint(6, 14)):
        what = r.random()
        if what < 0.45:
            (a, ka, ma), (b, kb, mb) = r.choice(vars_), r.choice(vars_)
            if not comparable_pair(ka, kb):
                continue
            op = r.choice(['=', '<>'])
            lines.append(f'    Print(Show(logic{{{a} {op} {b}}}))')
            eq = ma == mb
            out.append('y' if (eq if op == '=' else not eq) else 'n')
        elif what < 0.6:
            # a container of two values of one kind, against another of another
            (a, ka, ma), (b, kb, mb) = r.choice(vars_), r.choice(vars_)
            if not comparable_pair(ka, kb):
                continue
            c = r.choice(['array', 'option'])
            lines.append(f'    Print(Show(logic{{{c}{{{a}}} = {c}{{{b}}}}}))')
            out.append('y' if ma == mb else 'n')
        elif what < 0.75:
            (a, ka, ma) = r.choice(vars_)
            f, lit = r.choice([('IsFalse', None), ('IsEmptyString', None)])
            lines.append(f'    Print(Show(logic{{{f}[{a}]}}))')
            out.append('y' if ma == E else 'n')
        elif what < 0.87:
            # a map keyed by values of one kind, looked up by another value of it
            name, k = r.choice(ts)
            if k == 'int' or k == 'char':
                continue
            if isinstance(k, tuple) and k[0] in ('map',):
                continue
            entries = []
            model = []
            for j in range(r.randint(1, 3)):
                ke, km = g.value(k)
                idx = [i for i, (a, _) in enumerate(model) if a == km]
                for i in reversed(idx):
                    del model[i]
                model.append((km, j))
                entries.append(f'{ke} => {j}')
            qe, qm = g.value(k)
            lines.append(f'    M{len(out)}:[{name}]int = map{{{", ".join(entries)}}}')
            lines.append(f'    if (W := M{len(out)}[{qe}]) then Print("{{W}}") else Print("missing")')
            hit = [v for a, v in model if a == qm]
            out.append(str(hit[0]) if hit else 'missing')
        else:
            # how many elements of an array of one kind are a value of it
            name, k = r.choice(ts)
            es = [g.value(k) for _ in range(r.randint(0, 3))]
            qe, qm = g.value(k)
            arr = 'array{' + ', '.join(e for e, _ in es) + '}'
            lines.append(f'    A{len(out)}:[]{name} = {arr}')
            lines.append(f'    Print("{{for (Z : A{len(out)}, Same[Z, {qe}]) {{Z}}.Length}}")')
            out.append(str(sum(1 for _, m in es if m == qm)))
    return '\n'.join(lines) + '\n', '\n'.join(out) + '\n'


if __name__ == '__main__':
    prog, exp = program(int(sys.argv[1]))
    sys.stdout.write(exp if '--expected' in sys.argv else prog)
