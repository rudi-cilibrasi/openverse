#!/usr/bin/env python3
"""Random Verse programs for scripts/fuzz-equality.sh: = and <> between values
of many types, the empty value at every depth (false, (), "", array{},
map{}, an empty option), compared directly, inside arrays, options, tuples,
maps and one struct's instances, through a generic function (X = false at
t = []int), as map keys and as searched array elements; and values of every
comparable type boxed as `comparable` (Book of Verse ch. 11), compared boxed
and unboxed, as keys of a `[comparable]int` and as elements of a
`[]comparable` searched. The expected output is computed here from the Book
of Verse's equality: two values are equal when they are one value (the empty
value is one value; a tuple is the array of its elements; an int is the
rational it is; values of different types are different, an enum's value
never another enum's or an int, a char32 never an int, a struct never a
tuple or another struct; but a struct at two instances compares field by
field).

usage: gen-equality.py SEED [--expected]: the program, or its expected output
"""
import random
import sys
from fractions import Fraction

E = 'E'  # the one empty value


def types():
    # (Verse type, kind)
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


def boxed_types():
    # the comparable types whose values Verse Core holds like another type's
    # (`Core/Comparable.lean`), and comparable itself
    return [
        ('char32', 'c32'), ('float', 'float'), ('letters', ('enum', 'letters')),
        ('numbers', ('enum', 'numbers')), ('rational', 'rat'), ('char', 'char'),
        ('q(int)', ('q', 'int')), ('p(int)', ('p', 'int')), ('s', 's'),
        ('[]char32', ('arr', 'c32')), ('?letters', ('opt', ('enum', 'letters'))),
        ('tuple(char32, int)', ('tup', ['c32', 'int'])), ('tuple(int, int)', ('tup', ['int', 'int'])),
        ('[letters]int', ('map', ('enum', 'letters'), 'int')), ('[]tuple(int, int)', ('arr', ('tup', ['int', 'int']))),
        ('p(letters)', ('p', ('enum', 'letters'))), ('[]rational', ('arr', 'rat')),
        ('comparable', 'cmp'), ('[]comparable', ('arr', 'cmp')), ('?comparable', ('opt', 'cmp')),
    ]


ENUMS = {'letters': ['A', 'B', 'C'], 'numbers': ['One', 'Two', 'Three']}


def spell(k):
    """The Verse spelling of a kind."""
    if k == 'int': return 'int'
    if k == 'logic': return 'logic'
    if k == 'unit': return 'void'
    if k == 'char': return 'char'
    if k == 'c32': return 'char32'
    if k == 'float': return 'float'
    if k == 'rat': return 'rational'
    if k == 'cmp': return 'comparable'
    if k == 's': return 's'
    tag = k[0]
    if tag == 'enum': return k[1]
    if tag == 'opt': return '?' + spell(k[1])
    if tag == 'arr': return 'string' if k[1] == 'char' else '[]' + spell(k[1])
    if tag == 'map': return '[' + spell(k[1]) + ']' + spell(k[2])
    if tag == 'tup': return 'tuple(' + ', '.join(spell(x) for x in k[1]) + ')'
    if tag in ('p', 'q'): return tag + '(' + spell(k[1]) + ')'
    raise ValueError(k)


def norm(m):
    """The Book's identifications: a tuple is the array of its elements (the
    empty one the empty value), an int is the rational it is."""
    if not isinstance(m, tuple) or not m:
        return m
    tag = m[0]
    if tag == 'tup':
        es = tuple(norm(x) for x in m[1])
        return E if not es else ('arr', es)
    if tag == 'arr':
        return ('arr', tuple(norm(x) for x in m[1]))
    if tag == 'rat':
        return ('i', m[1]) if m[2] == 1 else m
    if tag == 'some':
        return ('some', norm(m[1]))
    if tag in ('p', 'q'):
        return (tag, norm(m[1]))
    if tag == 'map':
        return ('map', tuple((norm(a), norm(b)) for a, b in m[1]))
    return m


class G:
    def __init__(self, r):
        self.r = r
        # (values bound to typed locals first, where a comparable is expected:
        # an empty array{} or map{} there has no type of its own)
        self.pre = []
        self.n = 0

    def typed(self, k, d=2):
        """A value of kind k in a local of its type: (name, model value)."""
        e, m = self.value(k, d)
        name = f'T{self.n}'
        self.n += 1
        self.pre.append(f'    {name}:{spell(k)} = {e}')
        return name, m

    def flush(self, lines):
        lines.extend(self.pre)
        self.pre = []

    def value(self, k, d=2):
        """(Verse expression at kind k, model value)."""
        r = self.r
        if k == 'int':
            n = r.choice([0, 1, 2, 65])
            return str(n), ('i', n)
        if k == 'char':
            c = r.choice('ab')
            return "'" + c + "'", ('c', ord(c))
        if k == 'c32':
            n = r.choice([0x41, 0x61, 0x42])
            return '0u%x' % n, ('c32', n)
        if k == 'float':
            x = r.choice([0.0, 1.0, 2.0, 65.0, 0.5])
            return repr(x), ('f', x)
        if k == 'rat':
            n, dd = r.choice([(0, 1), (2, 1), (4, 2), (1, 2), (2, 4), (65, 1)])
            f = Fraction(n, dd)
            return f'Rat({n}, {dd})', ('rat', f.numerator, f.denominator)
        if k == 's':
            return 's{}', ('s',)
        if k == 'cmp':
            # a value of another comparable type, boxed
            _, k2 = r.choice(types() + boxed_types()[:-3])
            e, m = self.typed(k2, max(d - 1, 0))
            return 'comparable(' + e + ')', m
        if k == 'logic':
            if r.random() < 0.6: return 'false', E
            return 'true', ('t',)
        if k == 'unit':
            return r.choice(['false', '()']), E
        tag = k[0]
        if tag == 'enum':
            i = r.randrange(3)
            return k[1] + '.' + ENUMS[k[1]][i], ('enum', k[1], i)
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
                return r.choice(['array{}', 'false']) if k[1] != 'cmp' else 'array{}', E
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
        if tag in ('p', 'q'):
            e, m = self.value(k[1], d - 1)
            return spell(k) + '{X := ' + e + '}', (tag, m)
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
    bts = boxed_types()
    lines = ['p(t:type) := struct{X:t}',
             'q(t:type) := struct{X:t}',
             's := struct{}',
             'letters := enum{A, B, C}',
             'numbers := enum{One, Two, Three}',
             'Rat(N:int, D:int):rational = if (R := N / D) then R else 0',
             'Show(B:logic):string = if (B?) then "y" else "n"',
             'IsFalse(X:t where t:subtype(comparable))<decides>:void = X = false',
             'IsEmptyString(X:t where t:subtype(comparable))<decides>:void = X = ""',
             'Same(X:t, Y:t where t:subtype(comparable))<decides>:void = X = Y',
             'SameBoxed(X:comparable, Y:comparable)<decides>:void = X = Y',
             'SameAny(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = X = Y',
             'InArrays(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = array{X} = array{Y}',
             'Main():void =']
    out = []
    vars_ = []
    boxed = []
    for i in range(r.randint(4, 8)):
        name, k = r.choice(ts)
        e, m = g.value(k)
        g.flush(lines)
        lines.append(f'    V{i}:{name} = {e}')
        vars_.append((f'V{i}', k, m))
    for i in range(r.randint(3, 6)):
        name, k = r.choice(ts + bts)
        e, m = g.value(k)
        g.flush(lines)
        lines.append(f'    B{i}:{name} = {e}')
        boxed.append((f'B{i}', k, m))
    for _ in range(r.randint(8, 18)):
        what = r.random()
        if what < 0.3:
            (a, ka, ma), (b, kb, mb) = r.choice(vars_), r.choice(vars_)
            if not comparable_pair(ka, kb):
                continue
            op = r.choice(['=', '<>'])
            lines.append(f'    Print(Show(logic{{{a} {op} {b}}}))')
            eq = ma == mb
            out.append('y' if (eq if op == '=' else not eq) else 'n')
        elif what < 0.4:
            # a container of two values of one kind, against another of another
            (a, ka, ma), (b, kb, mb) = r.choice(vars_), r.choice(vars_)
            if not comparable_pair(ka, kb):
                continue
            c = r.choice(['array', 'option'])
            lines.append(f'    Print(Show(logic{{{c}{{{a}}} = {c}{{{b}}}}}))')
            out.append('y' if ma == mb else 'n')
        elif what < 0.5:
            # (through a generic function: at a type of any shape, an empty
            # struct is no empty value, an enum's value no int)
            (a, ka, ma) = r.choice(vars_ + boxed)
            f, lit = r.choice([('IsFalse', None), ('IsEmptyString', None)])
            lines.append(f'    Print(Show(logic{{{f}[{a}]}}))')
            out.append('y' if norm(ma) == E else 'n')
        elif what < 0.58:
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
        elif what < 0.64:
            # how many elements of an array of one kind are a value of it
            name, k = r.choice(ts)
            es = [g.value(k) for _ in range(r.randint(0, 3))]
            qe, qm = g.value(k)
            arr = 'array{' + ', '.join(e for e, _ in es) + '}'
            lines.append(f'    A{len(out)}:[]{name} = {arr}')
            lines.append(f'    Print("{{for (Z : A{len(out)}, Same[Z, {qe}]) {{Z}}.Length}}")')
            out.append(str(sum(1 for _, m in es if m == qm)))
        elif what < 0.76:
            # two values of any comparable types, boxed: equal exactly when they
            # are one value (Book of Verse ch. 11)
            (a, ka, ma), (b, kb, mb) = r.choice(boxed + vars_), r.choice(boxed + vars_)
            form = r.choice(['fn', 'both', 'left', 'right', 'generic', 'arrays'])
            if form in ('fn', 'generic', 'arrays'):
                f = {'fn': 'SameBoxed', 'generic': 'SameAny', 'arrays': 'InArrays'}[form]
                lines.append(f'    Print(Show(logic{{{f}[{a}, {b}]}}))')
                eq = norm(ma) == norm(mb)
            else:
                op = r.choice(['=', '<>'])
                x = f'comparable({a})' if form in ('both', 'left') else a
                y = f'comparable({b})' if form in ('both', 'right') else b
                lines.append(f'    Print(Show(logic{{{x} {op} {y}}}))')
                eq = norm(ma) == norm(mb)
                eq = eq if op == '=' else not eq
            out.append('y' if eq else 'n')
        elif what < 0.88:
            # a map keyed by comparable values, looked up by a value of any type
            entries = []
            model = []
            for j in range(r.randint(1, 4)):
                _, k = r.choice(ts + bts)
                ke, km = g.typed(k)
                km = norm(km)
                idx = [i for i, (a, _) in enumerate(model) if a == km]
                for i in reversed(idx):
                    del model[i]
                model.append((km, j))
                entries.append(f'{ke} => {j}')
            (q, kq, qm) = r.choice(boxed + vars_)
            g.flush(lines)
            lines.append(f'    K{len(out)}:[comparable]int = map{{{", ".join(entries)}}}')
            lines.append(f'    if (W := K{len(out)}[{q}]) then Print("{{W}}") else Print("missing")')
            hit = [v for a, v in model if a == norm(qm)]
            out.append(str(hit[0]) if hit else 'missing')
        else:
            # how many elements of a []comparable are a value of any type
            es = []
            for _ in range(r.randint(0, 4)):
                _, k = r.choice(ts + bts)
                es.append(g.typed(k))
            (q, kq, qm) = r.choice(boxed + vars_)
            g.flush(lines)
            arr = 'array{' + ', '.join(e for e, _ in es) + '}'
            lines.append(f'    C{len(out)}:[]comparable = {arr}')
            lines.append(f'    Print("{{for (Z : C{len(out)}, Z = {q}) {{Z}}.Length}}")')
            out.append(str(sum(1 for _, m in es if norm(m) == norm(qm))))
    return '\n'.join(lines) + '\n', '\n'.join(out) + '\n'


if __name__ == '__main__':
    prog, exp = program(int(sys.argv[1]))
    sys.stdout.write(exp if '--expected' in sys.argv else prog)
