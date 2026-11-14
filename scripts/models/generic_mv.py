#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by a review agent of the upkeep session,
# independently of the front end's code, for the review of #282 (generic functions with
# several values, #235).
"""Random programs with generic functions with several values (#235, PR #282),
with a model of their output, written from docs/LANGUAGE.md ("Choice",
"Functions with several values", "Parametric functions", the readings table).

    usage: generic_mv.py SEED OUTDIR [no-recursive-returns] -> OUTDIR/p.verse, OUTDIR/p.expected, OUTDIR/p.meta

The model:
  * a call of a function with several values is a choice whose values come in
    the callee's spatial order (depth first for recursive ones);
  * three paths: inlined (non-recursive), lazy (generator-shaped recursive),
    eager (other recursive <computes> ones, computed at the call as F$all);
  * where the first success is taken (if, option{}, logic{}, not, first{},
    a <decides> body), effects follow backtracking: everything an
    alternative did that leads to no success is rolled back (output included);
  * in a for, a choice is a generator: an alternative whose own clauses (up to
    the next generator, or the body) fail is rolled back; one whose clauses
    succeed keeps its effects even when later generators give no value;
  * a call on any path types as a plain generic call: its type arguments come
    from first-order matching against the arguments (no subtyping), so sibling
    classes for one t are refused (exit 4), `false`, `array{}` and a tuple for
    `[]t` convert, and `where t:subtype(comparable)` is checked at the call;
  * arguments are evaluated in order, the code before a choice once;
  * composed and conditional choices in a generic for preserve mutable
    state across generator boundaries; written-only result types retain
    their type arguments even when no captured value determines them;
  * overridden methods preserve those values through fixed/repeated/reordered
    root arguments, compound arguments, opened parameters and interface defaults;
  * effectful first-success helpers retain generic values and captures, with
    explicit witnesses for types used only by the suffix's written types;
  * generic mutual trees retain each member's type instance, item effects,
    value rollback, mutable captures and written-only witnesses;
  * a lazy one may bind its call of itself with code after it, which runs
    on each of the call's values (a return frame, #283), and what it reads
    before that call (a call of a function) is read once, before it;
  * choice points in sequence (#283): a call of itself followed by a choice,
    a choice followed by a call, two calls in sequence in an if's branch; the
    code between two points runs once for each value of the first, and a
    call of itself is a generator of its own there too;
  * a call of itself in a failure context of its own code (#283): an if's
    condition takes its first success, a for all its values, while its own
    values are taken, as anywhere; its only recursion is then through that
    context, so it is inlined, as a function recursive only through another
    that consumes it is;
  * a call of another function with several values as a choice point in a
    lazy one's code (#283): its values each go to the code after the call,
    taken with the lazy one, as a call of it is;
  * early and terminal source returns yield the same ordered values as
    explicit conditional tails, ending only their current invocation;
  * methods may infer their own type parameters independently of receiver
    arguments, including through overrides, super tuples and interface defaults;
  * methods of one name declared apart in unrelated classes and interfaces are
    each the root of a family of their own: a call through a receiver of a
    class below one of them has that family's values, and one of a class
    whose method of that name is ordinary has its one value;
  * generic overloads (#283), told apart by arity: a call takes the overload
    its arguments fit and has its values (one, or several), an overload may
    call its function's own name, and so may a generic class's method's list;
  * type parameters with upper bounds (#502; a stream of its own): a member
    read through a class bound is the instance's (its override), a result is
    at the argument's precise type, a peer u:subtype(t) gives a t, a []t
    filtered on a bound member keeps its elements' class, an int is halved
    as the rational its bound makes it, an array upper is indexed and
    measured, and a bounded class's method has several values.
"""
import random, sys, os, re

R = None
# (#387: an overridden method of a generic class; a generator of its own decides, so seeds keep
# their other programs)
R387 = None
RFrame = None
# (#283: choice points in sequence in a lazy one, LSq, LSc, LSb; a stream of its own)
RSeq = None
# (#283: a call of itself in its own if's condition or for, LNc, LNf; a stream of its own)
RNest = None
# (#283: another function with several values as a choice point in a lazy one, LOt; a stream of its own)
ROther = None
# (#283: that function called at two instances of its type parameters in one search, LOt2, int and
# the lazy one's own: a copy of it of its own takes the other; a stream of its own)
RInst = None
# (#392: a named parameter with a default; a generator of its own decides, so seeds keep their
# other programs)
R392 = None
RMethod = None
# (#283: at times every method with several values is named Vals, declared apart in the
# programs' unrelated classes and interfaces, beside an ordinary Vals of a class of its own,
# called at the end; a generator of its own decides, so seeds keep their other programs)
SHARED = False
# Source-spelling variants share the existing independent value/effect model.
RECURSIVE_RETURNS = "no-recursive-returns" not in sys.argv[3:]
# (#283) returns in a block or a case's arm too (no-return-scopes turns it off)
RETURN_SCOPES = "no-return-scopes" not in sys.argv[3:]

# ---------------------------------------------------------------- types
CLASSES = ["cat", "dog", "animal"]

class Ty:
    """A type argument kind: literals, how to show a value, a predicate."""
    def __init__(self, name):
        self.name = name

    def comparable(self):
        return self.name != "animal"

    def value(self):
        n = self.name
        if n == "int":
            v = R.randint(-2, 9); return (str(v), v)
        if n == "string":
            s = R.choice(["a", "bb", "ccc", "dd", "e"]); return ('"%s"' % s, s)
        if n == "pt":
            a, b = R.randint(0, 5), R.randint(0, 5)
            return ("pt{A := %d, B := %d}" % (a, b), ("pt", a, b))
        if n == "tup":
            i, s = R.randint(0, 5), R.choice(["a", "b", "cc"])
            return ('(%d, "%s")' % (i, s), ("tup", i, s))
        if n == "animal":
            c = R.choice(["cat", "dog"]); k = R.randint(0, 5)
            return ("%s{N := %d}" % (c, k), ("obj", c, k))
        if n == "arr":
            xs = [R.randint(0, 5) for _ in range(R.randint(1, 3))]
            return ("array{%s}" % ", ".join(map(str, xs)), ("arr", tuple(xs)))
        raise ValueError(n)

    def show(self, v):          # Verse string expression for variable v
        n = self.name
        if n == "int": return '"{%s}"' % v
        if n == "string": return v
        if n == "pt": return '"{%s.A}:{%s.B}"' % (v, v)
        if n == "tup": return '"{%s(0)}/{%s(1)}"' % (v, v)
        if n == "animal": return '"{%s.Name()} {%s.N}"' % (v, v)
        if n == "arr": return "ShowArr(%s)" % v

    def mshow(self, x):         # the model's string
        n = self.name
        if n == "int": return str(x)
        if n == "string": return x
        if n == "pt": return "%d:%d" % (x[1], x[2])
        if n == "tup": return "%d/%s" % (x[1], x[2])
        if n == "animal": return "%s %d" % (x[1], x[2])
        if n == "arr": return "[" + "".join("%d," % e for e in x[1]) + "]"

    def pred(self, v, k):       # Verse condition on variable v
        n = self.name
        if n == "int": return "%s > %d" % (v, k)
        if n in ("string", "arr"): return "%s.Length > %d" % (v, k)
        if n == "pt": return "%s.A > %d" % (v, k)
        if n == "tup": return "%s(0) > %d" % (v, k)
        if n == "animal": return "%s.N > %d" % (v, k)

    def mpred(self, x, k):
        n = self.name
        if n == "int": return x > k
        if n == "string": return len(x) > k
        if n == "arr": return len(x[1]) > k
        if n in ("pt", "tup"): return x[1] > k
        if n == "animal": return x[2] > k

    def kval(self):
        n = self.name
        if n == "int": return R.randint(-1, 8)
        if n in ("string", "arr"): return R.randint(0, 2)
        return R.randint(0, 4)

TYPES = [Ty(n) for n in ["int", "string", "pt", "tup", "animal", "arr"]]

def meq(a, b):
    return a == b   # structural (classes are not generated for comparable ones)

# ---------------------------------------------------------------- instructions
# ('print', s) ('cond', b) ('test', fn(env)) ('val', var, value)
# ('choice', [alt, ...]) where alt is a list of instructions
# ('body', fn(env))

class Refuse(Exception):
    pass

class ArgTell:
    """An int argument Tell("s", v): prints s where it is evaluated."""
    def __init__(self, s, v): self.s, self.v = s, v

class ArgChoice:
    """An int argument (v1 | v2): a choice at its place."""
    def __init__(self, vs): self.vs = vs

def plain(x):
    return x.v if isinstance(x, ArgTell) else x

# ---------------------------------------------------------------- producers
class Producer:
    """A generic function with several values. params: list of (name, kind)
    with kind 't', 'arr' ([]t) or 'int'. path: inlined/lazy/eager."""
    def __init__(self, kind, name, method_shape=None):
        self.kind, self.name = kind, name
        self.fx = False
        self.decides = False
        self.cmp = False
        self.helper = None
        k = kind
        n = name
        if k == "I2":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]
            self.src = "%s(X:t, Y:t where t:type):t = X | Y" % n
            # (#392: at times Y is a named parameter whose default is X: given as ?Y := y, or omitted)
            self.named = R392.random() < 0.3
            if self.named:
                self.src = "%s(X:t, ?Y:t = X where t:type):t = X | Y" % n
        elif k == "I3":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("Z", "t")]
            self.src = "%s(X:t, Y:t, Z:t where t:type):t = X | Y | Z" % n
        elif k == "IIf":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("C", "int")]
            self.src = "%s(X:t, Y:t, C:int where t:type):t = if (C > 0) then (X | Y) else Y" % n
        elif k == "IArr":
            self.path = "inlined"; self.params = [("A", "arr")]; self.decides = True
            self.src = "%s(A:[]t where t:type)<decides>:t = A[0] | A[2] | A[1]" % n
        elif k == "IFx":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("C", "int")]
            self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, C:int where t:type)<transacts><decides>:t =\n"
                        "    Print(\"%s {C}\")\n    C > 0\n    X | Y") % (n, n)
        elif k == "IMeth":
            # (#365: a generic class's method with several values, reached through a wrapper
            # that builds the receiver at its own type parameter)
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]; self.fx = True
            self.ovr = method_shape is not None or R387.random() < 0.5
            if self.ovr:
                # Every hierarchy has the same values Y, X, Y. Vary its
                # representation independently of the value/effect model:
                # fixed/repeated/reordered root arguments, opened extra
                # parameters, a compound root argument, and interface defaults.
                shape = method_shape or RMethod.choice(['plain', 'added', 'fixed', 'repeat', 'reorder', 'wrapped', 'interface'])
                self.method_shape = shape
                cross = shape.startswith('cross-')
                own = shape.startswith('own-') or cross
                if own:
                    shape = shape.split('-', 1)[1]
                root_tps, child_tps, parent, receiver, ctor = {
                    'plain': ('t:type', 't:type', f'c{n}(t)', f'c{n}(t)', f'd{n}(t)'),
                    'added': ('t:type', 't:type,u:type', f'c{n}(t)', f'c{n}(t)', f'd{n}(t,int)'),
                    'fixed': ('t:type,u:type', 't:type', f'c{n}(t,int)', f'c{n}(t,int)', f'd{n}(t)'),
                    'repeat': ('t:type,u:type', 't:type', f'c{n}(t,t)', f'c{n}(t,t)', f'd{n}(t)'),
                    'reorder': ('t:type,u:type', 'a:type,b:type', f'c{n}(b,a)', f'c{n}(t,int)', f'd{n}(int,t)'),
                    'wrapped': ('t:type', 'u:type', f'c{n}(tuple(char,u))', f'c{n}(tuple(char,t))', f'd{n}(t)'),
                }.get(shape, ('', '', '', f'c{n}(t)', f'e{n}(t,int)'))
                extra_field = '\n    Extra:u' if shape == 'added' else ''
                extra_value = ', Extra := 0' if shape == 'added' else ''
                child_ty = 'b' if shape == 'reorder' else 'tuple(char,u)' if shape == 'wrapped' else 't'
                x, y = ("('x',X)", "('y',Y)") if shape == 'wrapped' else ('X', 'Y')
                values = f'{ctor}{{X := {x}, Y := {y}{extra_value}}}'
                result = f'(R.M{n}())(1)' if shape == 'wrapped' else f'R.M{n}()'
                if own:
                    # The receiver's type is independent of the values' type.
                    # The ordered-value oracle remains Y, X, Y, including super.
                    receiver = re.sub(r'\bt\b', 'int', receiver)
                    ctor = re.sub(r'\bt\b', 'int', ctor)
                    anchor = "('a',0)" if shape == 'wrapped' else '0'
                    root_method = f'    M{n}(V:r,W:r,?E:[]r=Concatenate() where r:type)<transacts>:r = V|W'
                    child_method = f'    M{n}<override>(V:v,W:v,?E:[]v=Concatenate() where v:type)<transacts>:v = W|(super:)M{n}((V,W))'
                    if cross:
                        # (a super call of another method, (super:)Parent{n}
                        # in M{n}, is refused, the Book's rule: (super:)M is
                        # only in an override of M; the shape is the own one,
                        # its draw kept for the random stream)
                        self.cross_multi = RMethod.choice([False, True])
                    # (the interface shape: d{n} overrides c{n}'s default from
                    # an abstract class, as an interface overrides nothing,
                    # the Book's tests)
                    if shape == 'interface':
                        declarations = f'''c{n}(t:type) := interface:
{root_method}
d{n}(t:type,u:type) := class<abstract>(c{n}(t)):
{child_method}
e{n}(t:type,u:type) := class(d{n}(t,u)):
    Anchor:t
    Extra:u'''
                        values = f'e{n}(int,int){{Anchor:=0,Extra:=0}}'
                    else:
                        declarations = f'''c{n}({root_tps}) := class:
    Anchor:t
{root_method}
d{n}({child_tps}) := class({parent}):{extra_field}
{child_method}'''
                        values = f'{ctor}{{Anchor:={anchor}{extra_value}}}'
                    self.src = declarations + f'''
{n}(X:t,Y:t where t:type)<transacts>:t =
    R:{receiver}={values}
    R.M{n}((X,Y))'''
                elif shape == 'interface':
                    self.src = f'''c{n}(t:type) := interface:
    HX{n}()<transacts>:t
    HY{n}()<transacts>:t
    M{n}()<transacts>:t = HX{n}() | HY{n}()
d{n}(t:type,u:type) := class<abstract>(c{n}(t)):
    M{n}<override>()<transacts>:t = HY{n}() | (super:)M{n}()
e{n}(t:type,u:type) := class(d{n}(t,u)):
    X:t
    Y:t
    Extra:u
    HX{n}<override>()<transacts>:t = X
    HY{n}<override>()<transacts>:t = Y
{n}(X:t,Y:t where t:type)<transacts>:t =
    R:c{n}(t) = e{n}(t,int){{X:=X,Y:=Y,Extra:=0}}
    R.M{n}()'''
                else:
                    self.src = f'''c{n}({root_tps}) := class:
    X:t
    Y:t
    M{n}()<transacts>:t = X | Y
d{n}({child_tps}) := class({parent}):{extra_field}
    M{n}<override>()<transacts>:{child_ty} = Y | (super:)M{n}()
{n}(X:t,Y:t where t:type)<transacts>:t =
    R:{receiver} = {values}
    {result}'''
            else:
                self.src = ("c%s(t:type) := class:\n    X:t\n    Y:t\n    M%s()<transacts>:t = X | Y\n"
                            "%s(X:t, Y:t where t:type)<transacts>:t = c%s(t){X := X, Y := Y}.M%s()") % (n, n, n, n, n)
        elif k == "IFx2":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]; self.fx = True
            self.src = ("%s(X:t, Y:t where t:type)<transacts>:t =\n"
                        "    Z := X | Y\n    Print(\"%s z\")\n    Z") % (n, n)
        elif k == "INest":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("Z", "t")]
            self.helper = "I2"
        elif k == "ILz":
            self.path = "inlined"; self.params = [("A", "arr"), ("K", "int")]; self.decides = True
            self.helper = R.choice(["LElems", "LFx"])
        elif k == "ICmp":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]; self.cmp = True
            self.src = "%s(X:t, Y:t where t:subtype(comparable)):t = if (X <> Y) then (X | Y) else X" % n
        elif k == "I2i":
            self.path = "inlined"; self.params = [("X", "t"), ("C", "int"), ("D", "int")]; self.fx = True; self.decides = True
            self.src = ("%s(X:t, C:int, D:int where t:type)<transacts><decides>:t =\n"
                        "    Print(\"%s {C} {D}\")\n    C <> D\n    X | X") % (n, n)
        elif k == "IW":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]
            self.src = "%s(X:t, Y:t where t:type):t =\n    Z:t = X\n    Z | Y" % n
        elif k == "IWArr":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]; self.decides = True
            self.src = "%s(X:t, Y:t where t:type)<decides>:t =\n    Q:[]t = array{X, Y}\n    Q[1] | Q[0] | Q[2]" % n
        elif k == "IWOpt":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]; self.decides = True
            self.src = "%s(X:t, Y:t where t:type)<decides>:t =\n    O:?t = option{X}\n    E:?t = false\n    E? | Y | O?" % n
        elif k == "IWPair":
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t")]
            self.src = "%s(X:t, Y:t where t:type):t =\n    Q := pair(t, t){First := Y, Second := X}\n    Q.First | Q.Second" % n
        elif k == "LW":
            self.path = "lazy"; self.params = [("A", "arr"), ("I", "int")]; self.decides = True
            self.src = ("%s(A:[]t, I:int where t:type)<decides>:t =\n"
                        "    I < A.Length\n    Y:t = A[I]\n    Y | %s[A, I + 1]") % (n, n)
        elif k == "EW":
            self.path = "eager"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<computes><decides>:t =\n"
                        "    N > 0\n    Z:t = Y\n    X | Id(%s[Z, X, N - 1])") % (n, n)
        elif k == "LElems":
            self.path = "lazy"; self.params = [("A", "arr"), ("I", "int")]; self.decides = True
            self.src = ("%s(A:[]t, I:int where t:type)<decides>:t =\n"
                        "    I < A.Length\n    A[I] | %s[A, I + 1]") % (n, n)
        elif k == "LRep":
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<decides>:t =\n"
                        "    N > 0\n    X | %s[Y, X, N - 1]") % (n, n)
        elif k == "LTree":
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<decides>:t =\n"
                        "    N > 0\n    %s[X, Y, N - 1] | X | %s[Y, X, N - 1]") % (n, n, n)
        elif k == "LIf":
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<decides>:t =\n"
                        "    N >= 0\n    if (N > 0) then (X | %s[Y, X, N - 1]) else Y") % (n, n)
        elif k == "LFx":
            self.path = "lazy"; self.params = [("A", "arr"), ("I", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(A:[]t, I:int where t:type)<transacts><decides>:t =\n"
                        "    Print(\"%s {I}\")\n    I < A.Length\n    A[I] | %s[A, I + 1]") % (n, n, n)
        elif k == "LFx2":
            self.path = "lazy"; self.params = [("A", "arr"), ("I", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(A:[]t, I:int where t:type)<transacts><decides>:t =\n"
                        "    I < A.Length\n    Print(\"%s {I}\")\n    A[I] | %s[A, I + 1]") % (n, n, n)
        elif k == "LFxTree":
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    Print(\"%s {N}\")\n    N > 0\n    %s[X, Y, N - 1] | X | %s[Y, X, N - 1]") % (n, n, n, n)
        elif k == "LFr":
            # (#283: the call of itself bound, with code after it that runs on
            # each of its values, a return frame; taken lazily as it prints)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Z := %s[Y, X, N - 1] | X\n    Print(\"%s {N}\")\n    Z") % (n, n, n)
        elif k == "LFp":
            # (#283: a call of a function before its call of itself, bound once
            # before it, the frame using that value after each of the call's)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Z := block{ W := Id(X); V := %s[Y, X, N - 1]; Print(\"%s {N}\"); W } | Y\n    Z") % (n, n, n)
        elif k == "LSq":
            # (#283: choice points in sequence: a call of itself followed by a choice)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Z := %s[Y, X, N - 1] | X\n    Print(\"%s {N}\")\n    Z | Y") % (n, n, n)
        elif k == "LSc":
            # (#283: a choice followed by a call of itself, then by another choice;
            # N < 4, as the values multiply by four with each level)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    N < 4\n    Z := X | Y\n    Print(\"%s {N}\")\n    W := %s[Z, X, N - 1] | Y\n    W | Z") % (n, n, n)
        elif k == "LSb":
            # (#283: two calls of itself in sequence, in an if's branch; at most
            # two levels, as the second runs on each value of the first)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts>:t =\n"
                        "    if (N <= 0 or N > 2) then X else:\n        Z := %s(Y, X, N - 1)\n        Print(\"%s {N}\")\n"
                        "        W := %s(Z, Y, N - 1)\n        W | Z") % (n, n, n, n)
        elif k == "LNc":
            # (#283: a call of itself in its own if's condition, which takes its first success;
            # its only recursion, so it is inlined)
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Print(\"%s {N}\")\n    if (Z := %s[Y, X, N - 1]) then (Z | X) else Y") % (n, n, n)
        elif k == "LNf":
            # (#283: a for over a call of itself in its own code, which takes all its values)
            self.path = "inlined"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    var C:int = 0\n    for (Z := %s[Y, X, N - 1]) { set C += 1 }\n"
                        "    Print(\"%s {N} {C}\")\n    X | Y") % (n, n, n)
        elif k == "LOt":
            # (#283: a call of itself bound, then a call of another generic function with several
            # values as the value, taken with it)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%sTwo(A:t, B:t where t:type)<transacts>:t = A | B\n"
                        "%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Print(\"%s {N}\")\n    Z := %s[Y, X, N - 1] | X\n    %sTwo(Z, Y)") % (n, n, n, n, n)
        elif k == "LOt2":
            # (#283: as LOt, its Two called at int first, whatever its own type)
            self.path = "lazy"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True; self.fx = True
            self.src = ("%sTwo(A:t, B:t where t:type)<transacts>:t = A | B\n"
                        "%s(X:t, Y:t, N:int where t:type)<transacts><decides>:t =\n"
                        "    N > 0\n    Print(\"%s {N}\")\n    L := %sTwo(N, N + 10)\n    Z := %s[Y, X, N - 1] | X\n"
                        "    Print(\"%s {N} {L}\")\n    %sTwo(Z, Y)") % (n, n, n, n, n, n, n)
        elif k == "LCmp":
            self.path = "lazy"; self.params = [("A", "arr"), ("X", "t"), ("I", "int")]; self.decides = True; self.cmp = True
            self.src = ("%s(A:[]t, X:t, I:int where t:subtype(comparable))<decides>:t =\n"
                        "    I < A.Length\n    if (A[I] <> X) then (A[I] | %s[A, X, I + 1]) else %s[A, X, I + 1]") % (n, n, n)
        elif k == "ERep":
            self.path = "eager"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<computes><decides>:t =\n"
                        "    N > 0\n    X | Id(%s[Y, X, N - 1])") % (n, n)
        elif k == "ERev":
            self.path = "eager"; self.params = [("A", "arr"), ("I", "int")]; self.decides = True
            self.src = ("%s(A:[]t, I:int where t:type)<computes><decides>:t =\n"
                        "    I < A.Length\n    Id(%s[A, I + 1]) | A[I]") % (n, n)
        elif k == "ETree":
            self.path = "eager"; self.params = [("X", "t"), ("Y", "t"), ("N", "int")]; self.decides = True
            self.src = ("%s(X:t, Y:t, N:int where t:type)<computes><decides>:t =\n"
                        "    N > 0\n    Id(%s[X, Y, N - 1]) | X | Id(%s[Y, X, N - 1])") % (n, n, n)
        else:
            raise ValueError(k)
        if k == "IMeth" and SHARED:
            self.src = re.sub(rf"\bM{n}\b", "Vals", self.src)

        if RECURSIVE_RETURNS and self.path in ("lazy", "eager") and random.Random(n).random() < 0.5:
            lines = self.src.splitlines()
            if len(lines) > 1:
                # (#283: at times each return in a scope other than an if's branch, a block's or a
                # case's arm's, with the same values; a stream of its own, so seeds keep their
                # other programs)
                # (the function is <decides>, so each return is in tail position:
                # a return in a <decides> body anywhere else would leave its
                # failure context, which the Book of Verse refuses,
                # Return.versetest:157; the early return is a branch of the
                # body's last if, or an arm of its last case, the rest of the
                # body the other)
                scoped = RETURN_SCOPES and random.Random(n + "#283scope").random() < 0.5
                # (the last line's own indentation: in an else block, LSb's)
                ind = lines[-1][:len(lines[-1]) - len(lines[-1].lstrip())]
                lines[-1] = ind + "return " + lines[-1].strip()
                # (in a block of its own, when scoped)
                tail = lambda ls: ([ls[-1][:len(ls[-1]) - len(ls[-1].lstrip())] + "block:", "    " + ls[-1]]
                                   if scoped else [ls[-1]])
                if k == "LIf":
                    rest = ["NextN:=N-1", f"return X | {n}[Y,X,NextN]"]
                    if scoped:
                        lines[-1:] = (["    case(N):", "        0 => return Y", "        _ =>"] +
                                      ["            " + x for x in rest[:-1]] + tail(["            " + rest[-1]]))
                    else:
                        lines[-1:] = (["    if(N=0):", "        return Y", "    else:"] +
                                      ["        " + x for x in rest[:-1]] + tail(["        " + rest[-1]]))
                elif k in ("ERep", "ETree"):
                    first = (["    if(N<=0):", "        block:", "            false?", "            return X"] if scoped
                             else ["    if(N<=0):", "        false?", "        return X"])
                    lines[1:] = first + ["    else:"] + tail(["    " + lines[-1]])
                else:
                    lines[-1:] = tail(lines[-1:])
                self.src = "\n".join(lines)

    def bind_helper(self, h):
        """INest / ILz: an inlined generic function calling another."""
        self.helper = h
        n = self.name
        if self.kind == "INest":
            self.src = ("%s(X:t, Y:t, Z:t where t:type):t =\n"
                        "    W := %s\n    W | Z") % (n, h.call(["X", "Y"]))
        elif self.kind == "ILz":
            self.fx = h.fx
            self.src = ("%s(A:[]t, K:int where t:type)%s<decides>:t =\n"
                        "    V := %s[A, 0]\n    K > 0\n    V") % (n, "<transacts>" if h.fx else "", h.name)

    def top(self, a, var):
        """The instructions of a call as a consumer sees it. A lazily taken
        one is a generator of its own: its clauses failing gives no values,
        and rolls back only what they did (not the caller's clauses before
        it), as a recursive call computed at the call would (#246)."""
        pre, fixed, chs = [], {}, []
        for nm, kd in self.params:
            x = a[nm]
            if isinstance(x, ArgTell):
                pre.append(("print", x.s)); fixed[nm] = x.v
            elif isinstance(x, ArgChoice):
                h = "$a%s%s" % (nm, var)
                pre.append(("choice", [[("val", h, v)] for v in x.vs])); chs.append((nm, h))
            else:
                fixed[nm] = x
        def rest(env):
            b = dict(fixed)
            for nm, h in chs: b[nm] = env[h]
            ins = self.expand(b, var)
            if self.path == "lazy":
                return [("choice", [ins])]
            if self.path == "eager":
                # (computed at the call: then a generator over its values,
                # none if its clauses fail, which is no failure)
                m = Machine(); got = []
                m.forall(ins, lambda e: got.append(e[var]))
                return [("choice", [[("val", var, x)] for x in got])]
            return ins
        return pre + [("dyn", rest)]

    def call(self, args):
        if getattr(self, "named", False):
            args = [args[0]] + ([] if args[1] is None else ["?Y := " + args[1]])
        if self.decides: return "%s[%s]" % (self.name, ", ".join(args))
        return "%s(%s)" % (self.name, ", ".join(args))

    # the instructions of a call with argument values `a` (a dict), binding
    # its value to `var`
    def expand(self, a, var):
        k = self.kind
        V = lambda x: [("val", var, x)]
        if k == "I2i":
            return [("print", "%s %d %d" % (self.name, a["C"], a["D"])), ("cond", a["C"] != a["D"]),
                    ("choice", [V(a["X"]), V(a["X"])])]
        if k == "I2" or k == "IW": return [("choice", [V(a["X"]), V(a["Y"])])]
        if k == "IWArr": return [("choice", [V(a["Y"]), V(a["X"]), [("cond", False)]])]
        if k == "IWOpt": return [("choice", [[("cond", False)], V(a["Y"]), V(a["X"])])]
        if k == "IWPair": return [("choice", [V(a["Y"]), V(a["X"])])]
        if k == "LW":
            xs, i = a["A"][1], a["I"]
            if not 0 <= i < len(xs): return [("cond", False)]   # (Y:t = A[I] is a clause)
            return [("choice", [V(xs[i]) if i >= 0 else [("cond", False)], self.expand({"A": a["A"], "I": i + 1}, var)])]
        if k == "EW":
            if a["N"] <= 0: return [("cond", False)]
            return [("choice", [V(a["X"]), self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var)])]
        if k == "I3": return [("choice", [V(a["X"]), V(a["Y"]), V(a["Z"])])]
        if k == "IMeth":
            if self.ovr: return [("choice", [V(a["Y"]), V(a["X"]), V(a["Y"])])]
            return [("choice", [V(a["X"]), V(a["Y"])])]
        if k == "IIf":
            # (#331: an if adds no choice of its own; a branch without one is
            # its value, no generator, as an if with a return is not, #314)
            return [("choice", [V(a["X"]), V(a["Y"])])] if a["C"] > 0 else V(a["Y"])
        if k == "IArr":
            xs = a["A"][1]
            alts = [(V(xs[i]) if 0 <= i < len(xs) else [("cond", False)]) for i in (0, 2, 1)]
            return [("choice", alts)]
        if k == "IFx":
            return [("print", "%s %d" % (self.name, a["C"])), ("cond", a["C"] > 0),
                    ("choice", [V(a["X"]), V(a["Y"])])]
        if k == "IFx2":
            return [("choice", [V(a["X"]), V(a["Y"])]), ("print", "%s z" % self.name)]
        if k == "INest":
            inner = self.helper.top({"X": a["X"], "Y": a["Y"]}, "$w")
            # W | Z after each value of the helper
            return inner + [("choice2", var, "$w", a["Z"])]
        if k == "ILz":
            inner = self.helper.top({"A": a["A"], "I": 0}, var)
            return inner + [("cond", a["K"] > 0)]
        if k == "ICmp":
            if not meq(a["X"], a["Y"]): return [("choice", [V(a["X"]), V(a["Y"])])]
            # (#331: the else branch, without a choice of its own, is its value)
            return V(a["X"])
        if k in ("LElems", "LFx", "LFx2"):
            xs, i = a["A"][1], a["I"]
            out = []
            if k == "LFx": out.append(("print", "%s %d" % (self.name, i)))
            out.append(("cond", i < len(xs)))
            if i < len(xs):
                if k == "LFx2": out.append(("print", "%s %d" % (self.name, i)))
                out.append(("choice", [V(xs[i]) if i >= 0 else [("cond", False)], self.expand({"A": a["A"], "I": i + 1}, var)]))
            return out
        if k == "LRep" or k == "ERep":
            if a["N"] <= 0: return [("cond", False)]
            return [("choice", [V(a["X"]), self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var)])]
        if k in ("LTree", "ETree", "LFxTree"):
            out = []
            if k == "LFxTree": out.append(("print", "%s %d" % (self.name, a["N"])))
            if a["N"] <= 0: return out + [("cond", False)]
            l = self.expand({"X": a["X"], "Y": a["Y"], "N": a["N"] - 1}, var)
            r = self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var)
            return out + [("choice", [l, V(a["X"]), r])]
        if k == "LFr":
            # (the frame's print after each value of the call, and after X)
            if a["N"] <= 0: return [("cond", False)]
            back = ("print", "%s %d" % (self.name, a["N"]))
            return [("choice", [self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var) + [back],
                                V(a["X"]) + [back]])]
        if k == "LFp":
            # (each value of the call prints, then the value is X, read before it)
            if a["N"] <= 0: return [("cond", False)]
            back = ("print", "%s %d" % (self.name, a["N"]))
            return [("choice", [self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var) + [back] + V(a["X"]),
                                V(a["Y"])])]
        # (#283: a call of itself is a generator of its own, `("choice", [ins])`:
        # what the code before it did stays when its clauses fail, in a for)
        call = lambda b, v: [("choice", [self.expand(b, v)])]
        back = ("print", "%s %d" % (self.name, a.get("N", 0)))
        if k == "LSq":
            if a["N"] <= 0: return [("cond", False)]
            z = var + "z"
            after = [back, ("choice2", var, z, a["Y"])]
            return [("choice", [call({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, z) + after,
                                [("val", z, a["X"])] + after])]
        if k == "LSc":
            if a["N"] <= 0 or a["N"] >= 4: return [("cond", False)]
            z, w = var + "z", var + "w"
            return [("choice", [[("val", z, a["X"])], [("val", z, a["Y"])]]), back,
                    ("dyn", lambda env: [("choice", [call({"X": env[z], "Y": a["X"], "N": a["N"] - 1}, w),
                                                     [("val", w, a["Y"])]])]),
                    ("dyn", lambda env: [("choice", [[("val", var, env[w])], [("val", var, env[z])]])])]
        if k == "LSb":
            if a["N"] <= 0 or a["N"] > 2: return V(a["X"])
            z, w = var + "z", var + "w"
            return call({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, z) + [back,
                    ("dyn", lambda env: call({"X": env[z], "Y": a["Y"], "N": a["N"] - 1}, w)),
                    ("dyn", lambda env: [("choice", [[("val", var, env[w])], [("val", var, env[z])]])])]
        if k == "LNc":
            # (the condition a first-success context of its own: its first success kept, Z its
            # value; else the else branch, Y, what it did undone)
            if a["N"] <= 0: return [("cond", False)]
            z = var + "z"
            inner = self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, z)
            return [back, ("first", inner, z,
                           lambda zv: [("choice", [V(zv), V(a["X"])])], V(a["Y"]))]
        if k == "LNf":
            # (the for takes every value, each iteration's effects kept; then the print, X | Y)
            if a["N"] <= 0: return [("cond", False)]
            z = var + "z"
            inner = self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, z)
            return [("count", inner, var + "c"),
                    ("dyn", lambda env: [("print", "%s %d %d" % (self.name, a["N"], env[var + "c"])),
                                         ("choice", [V(a["X"]), V(a["Y"])])])]
        if k == "LOt2":
            # (the print, then each of Two's at int: N, N + 10; then each value of the call or X,
            # the print of both, then each of the other's: Z, Y)
            if a["N"] <= 0: return [("cond", False)]
            z, l, n = var + "z", var + "l", a["N"]
            return [back, ("choice", [[("val", l, n)], [("val", l, n + 10)]]),
                    ("choice", [call({"X": a["Y"], "Y": a["X"], "N": n - 1}, z), [("val", z, a["X"])]]),
                    ("dyn", lambda env: [("print", "%s %d %d" % (self.name, n, env[l])),
                                         ("choice", [V(env[z]), V(a["Y"])])])]
        if k == "LOt":
            # (the print, then each value of the call or X, then each of the other's: Z, Y)
            if a["N"] <= 0: return [("cond", False)]
            z = var + "z"
            return [back, ("choice", [call({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, z), [("val", z, a["X"])]]),
                    ("dyn", lambda env: [("choice", [V(env[z]), V(a["Y"])])])]
        if k == "LIf":
            if a["N"] < 0: return [("cond", False)]
            if a["N"] > 0:
                return [("choice", [V(a["X"]), self.expand({"X": a["Y"], "Y": a["X"], "N": a["N"] - 1}, var)])]
            return [("choice", [V(a["Y"])])]
        if k == "LCmp":
            xs, x, i = a["A"][1], a["X"], a["I"]
            if i >= len(xs): return [("cond", False)]
            rest = self.expand({"A": a["A"], "X": x, "I": i + 1}, var)
            if i < 0: return [("choice", [rest])]   # (A[I] fails in the if's condition: its else)
            if not meq(xs[i], x): return [("choice", [V(xs[i]), rest])]
            return [("choice", [rest])]
        if k == "ERev":
            xs, i = a["A"][1], a["I"]
            if i >= len(xs): return [("cond", False)]
            return [("choice", [self.expand({"A": a["A"], "I": i + 1}, var), V(xs[i]) if i >= 0 else [("cond", False)]])]
        raise ValueError(k)

# ---------------------------------------------------------------- the model's executor
# The rule a `for` follows (docs/research/readings-audit.md, "What a for
# undoes"): `OV_FOR_BOOK`, a comma-separated list of the kinds of choice point
# whose fors follow the Book of Verse's rule (`all`: every for), by default the
# kinds the compiler gives that rule; a for that reaches another kind keeps the
# old one. Every for of this model takes the values of calls of functions with
# several values (kind `call`). By that rule a
# for's clauses are one search, as a first-success context's are, that goes on
# after each success: reaching the body commits, and an alternative whose
# clauses lead to no body is undone as a whole (FlowControl/for.versetest
# 317-392, Range.versetest 140, 159). The old rule keeps what an alternative's
# own clauses did once they succeed, even when later generators give nothing.
FOR_BOOK = set(os.environ.get('OV_FOR_BOOK', 'plain,choice').split(',')) - {''}


class Machine:
    def __init__(self):
        self.out = []
        # (the bodies run so far, and the rule of the innermost for)
        self.commits = 0
        self.book = [False]

    def fail(self, mode, seg):
        del self.out[seg:]
        return False

    def run(self, seq, i, env, k, mode, seg):
        """Run seq[i:] then the continuation k(env, seg). True: stop (a first
        success was committed)."""
        while i < len(seq):
            ins = seq[i]; op = ins[0]
            if op == "print":
                self.out.append(ins[1])
            elif op == "cond":
                if not ins[1]: return self.fail(mode, seg)
            elif op == "test":
                if not ins[1](env): return self.fail(mode, seg)
            elif op == "val":
                env = dict(env); env[ins[1]] = ins[2]
            elif op == "body":
                ins[1](env)
            elif op == "dyn":
                more = ins[1](env)
                return self.run(more, 0, env, lambda e, s2, seq=seq, i=i: self.run(seq, i + 1, e, k, mode, s2), mode, seg)
            elif op == "first":
                # (#283: a first-success context of its own, as an if's condition: then's code with
                # its value, else's when it has none)
                _, inner, z, then, other = ins
                got = self.first(inner, dict(env))
                more = then(got[z]) if got is not None else other
                return self.run(more, 0, env, lambda e, s2, seq=seq, i=i: self.run(seq, i + 1, e, k, mode, s2), mode, seg)
            elif op == "count":
                # (#283: a for over every value, what each iteration does kept: their number)
                n = [0]
                self.forall(ins[1], lambda e: n.__setitem__(0, n[0] + 1), dict(env))
                env = dict(env); env[ins[2]] = n[0]
            elif op in ("choice", "choice2"):
                if op == "choice":
                    alts = ins[1]
                else:   # (W | Z: the value of W, then Z)
                    _, var, w, z = ins
                    alts = [[("val", var, env[w])], [("val", var, z)]]
                for alt in alts:
                    snap, commits = len(self.out), self.commits
                    cont = (lambda e, s, seq=seq, i=i: self.run(seq, i + 1, e, k, mode, s))
                    if self.run(alt, 0, env, cont, mode, snap): return True
                    if mode == "first" or (self.book[-1] and self.commits == commits):
                        del self.out[snap:]
                return False
            else:
                raise ValueError(op)
            i += 1
        return k(env, seg)

    def first(self, seq, env=None):
        """A context that takes the first success: the env of it, or None."""
        env = env or {}
        snap = len(self.out)
        got = []
        def k(e, s):
            got.append(e); return True
        if self.run(seq, 0, env, k, "first", snap):
            return got[0]
        del self.out[snap:]
        return None

    def forall(self, seq, body, env=None, kinds=frozenset({'call'})):
        env = env or {}
        snap, commits = len(self.out), self.commits
        def k(e, s):
            self.commits += 1
            body(e); return False
        self.book.append('all' in FOR_BOOK or kinds <= FOR_BOOK)
        try:
            self.run(seq, 0, env, k, "for", snap)
            # (the Book's rule: what the search did since the last success is undone)
            if self.book[-1] and self.commits == commits:
                del self.out[snap:]
        finally:
            self.book.pop()

# ---------------------------------------------------------------- the program
class Gen:
    def __init__(self, seed):
        global R, R387, R392, RMethod, SHARED, RFrame, RSeq, RNest, ROther, RInst
        R = random.Random(seed)
        R387 = random.Random(seed * 1000003 + 387)
        R392 = random.Random(seed * 1000003 + 392)
        RMethod = random.Random(seed * 1000003 + 283041)
        RFrame = random.Random(seed * 1000003 + 283283)
        RSeq = random.Random(seed * 1000003 + 283287)
        RNest = random.Random(seed * 1000003 + 283293)
        ROther = random.Random(seed * 1000003 + 283294)
        RInst = random.Random(seed * 1000003 + 283298)
        SHARED = random.Random(seed * 1000003 + 2834).random() < 0.4
        self.seed = seed
        self.prods = []
        self.consumers = []    # source of generic consumers
        self.main = []
        self.m = Machine()
        self.refusals = set()
        self.cnt = 0
        self.paths = set()

    def fresh(self, base):
        self.cnt += 1
        return "%s%d" % (base, self.cnt)

    def producer(self, kind):
        p = Producer(kind, self.fresh("P" + kind))
        if p.helper:
            h = self.producer(p.helper) if isinstance(p.helper, str) else p.helper
            p.bind_helper(h)
        self.prods.append(p)
        return p

    # arguments at type ty: (verse strings, model dict). mixed: the classes
    # of a t may differ (sibling classes)
    def args(self, p, ty, mode, choices=True, omit_ok=False):
        """mode (for classes): same (one class), mixed (any classes), parent
        (the first argument that gives t through a variable of the parent's
        type). Returns the arguments, their values, the lines declaring such
        variables, and the static class arguments in inference order."""
        cls = R.choice(["cat", "dog"])
        out, vals, pre = [], {}, []
        st = []     # the static class of each argument that gives t, in order
        first = True
        for (nm, kind) in p.params:
            if kind == "int":
                if nm in ("N",): v = R.randint(-1, 3)
                elif nm == "I": v = R.choice([0, 0, 0, 1, 2, 4])
                else: v = R.randint(-1, 2)
                r = R.random()
                if r < 0.2:
                    tag = self.fresh("arg"); out.append('Tell("%s", %d)' % (tag, v)); vals[nm] = ArgTell(tag, v)
                elif r < 0.4 and choices:
                    v2 = v + R.choice([-1, 1, 2])
                    out.append("(%d | %d)" % (v, v2)); vals[nm] = ArgChoice([v, v2])
                else:
                    out.append(str(v)); vals[nm] = v
            elif kind == "t":
                s, v = ty.value()
                if ty.name == "animal" and mode == "same":
                    v = ("obj", cls, v[2]); s = "%s{N := %d}" % (cls, v[2])
                if ty.name == "animal":
                    if mode == "parent" and first:
                        x = self.fresh("Pv"); pre.append("%s:animal = %s" % (x, s)); s = x
                        st.append("animal")
                    else:
                        st.append(v[1])
                first = False
                out.append(s); vals[nm] = v
            elif kind == "arr":
                xs = []
                for _ in range(R.randint(1, 3)):
                    s, v = ty.value()
                    if ty.name == "animal" and mode == "same":
                        v = ("obj", cls, v[2]); s = "%s{N := %d}" % (cls, v[2])
                    xs.append((s, v))
                lit = "array{%s}" % ", ".join(s for s, _ in xs)
                if ty.name == "animal":
                    cs = set(v[1] for _, v in xs)
                    if mode == "parent" and first:
                        x = self.fresh("Pa"); pre.append("%s:[]animal = %s" % (x, lit)); lit = x
                        st.append("animal")
                    else:
                        st.append(cs.pop() if len(cs) == 1 else "animal")
                first = False
                out.append(lit)
                vals[nm] = ("arr", tuple(v for _, v in xs))
        if getattr(p, "named", False) and omit_ok and R392.random() < 0.5:
            # (#392: Y omitted for its default X, its value drawn anyway; Producer.call names it)
            out[1] = None; vals["Y"] = vals["X"]
            if len(st) > 1: st.pop(1)
        return out, vals, pre, st

    def mixed_classes_unused(self, vals, p):
        cs = set()
        for (nm, kind) in p.params:
            if kind == "t" and isinstance(vals[nm], tuple) and vals[nm][0] == "obj":
                cs.add(vals[nm][1])
        return len(cs) > 1

    def pick_ty(self, p):
        if p.cmp: return R.choice([t for t in TYPES if t.comparable()])
        return R.choice(TYPES)

    def stmt(self):
        """One statement of Main: a consumer of a producer call."""
        p = R.choice(self.prods)
        ty = self.pick_ty(p)
        self.paths.add(p.path)
        # classes: of one class, of a parent-typed variable first, or (rarely,
        # as a plain generic call refuses most) mixed
        mode = R.choices(["same", "parent", "mixed"], [0.55, 0.35, 0.10])[0]
        form = R.choice(["for", "for", "forf", "for2", "if", "if", "ifp", "first", "option",
                         "logic", "not", "forexp", "gfor", "gif", "gopt", "gmv", "decides"])
        args, vals, pre, classes = self.args(p, ty, mode, choices=form not in ("gfor", "gif", "gopt", "decides"),
                                             omit_ok=form not in ("gfor", "gif", "gopt", "gmv"))
        st = classes[0] if classes else None
        self.main.extend(pre)
        call = p.call(args)
        if form == "not" and ty.name == "tup": form = "for"
        if st in ("cat", "dog") and form != "decides":
            # (a call types as a plain generic call: t from the first
            # argument, which a sibling class's object does not convert to)
            self.refusals.update("expected %s, found %s" % (st, actual)
                                 for actual in classes[1:] if actual != st)
        m = self.m
        V = self.fresh("V")
        k = ty.kval()
        pr = ty.pred(V, k)
        prm = (lambda e, V=V, k=k: ty.mpred(e[V], k))
        lines = []
        if form == "for":
            lines.append("for (%s := %s) { Print(%s) }" % (V, call, ty.show(V)))
            m.forall(p.top(vals, V), lambda e: m.out.append(ty.mshow(e[V])))
        elif form == "forf":
            lines.append("for (%s := %s, %s) { Print(%s) }" % (V, call, pr, ty.show(V)))
            m.forall(p.top(vals, V) + [("test", prm)], lambda e: m.out.append(ty.mshow(e[V])))
        elif form == "for2":
            q = R.choice(self.prods)
            ty2 = self.pick_ty(q)
            self.paths.add(q.path)
            args2, vals2, pre2, _ = self.args(q, ty2, "same", omit_ok=True)
            self.main.extend(pre2)
            W = self.fresh("W")
            mid = R.random() < 0.5
            if mid:
                lines.append("for (%s := %s, %s, %s := %s) { Print(%s); Print(%s) }" %
                             (V, call, pr, W, q.call(args2), ty.show(V), ty2.show(W)))
                seq = p.top(vals, V) + [("test", prm)] + q.top(vals2, W)
            else:
                lines.append("for (%s := %s, %s := %s) { Print(%s); Print(%s) }" %
                             (V, call, W, q.call(args2), ty.show(V), ty2.show(W)))
                seq = p.top(vals, V) + q.top(vals2, W)
            m.forall(seq, lambda e: (m.out.append(ty.mshow(e[V])), m.out.append(ty2.mshow(e[W]))))
        elif form in ("if", "ifp"):
            usepred = R.random() < 0.7
            extra = ""
            seq = p.top(vals, V)
            if form == "ifp":
                extra = ', Print("try %s")' % V
                seq = seq + [("print", "try %s" % V)]
            if usepred:
                lines.append("if (%s := %s%s, %s) then Print(%s) else Print(\"none\")" % (V, call, extra, pr, ty.show(V)))
                seq = seq + [("test", prm)]
            else:
                lines.append("if (%s := %s%s) then Print(%s) else Print(\"none\")" % (V, call, extra, ty.show(V)))
            e = m.first(seq)
            m.out.append(ty.mshow(e[V]) if e is not None else "none")
        elif form == "first":
            F = self.fresh("F")
            lines.append("if (%s := first{%s := %s; %s; %s}) then Print(%s) else Print(\"none\")" %
                         (F, V, call, pr, V, ty.show(F)))
            e = m.first(p.top(vals, V) + [("test", prm)])
            m.out.append(ty.mshow(e[V]) if e is not None else "none")
        elif form == "option":
            O = self.fresh("O")
            lines.append("%s := option{%s := %s; %s; %s}" % (O, V, call, pr, V))
            F = self.fresh("F")
            lines.append("if (%s := %s?) then Print(%s) else Print(\"none\")" % (F, O, ty.show(F)))
            e = m.first(p.top(vals, V) + [("test", prm)])
            m.out.append(ty.mshow(e[V]) if e is not None else "none")
        elif form == "logic":
            L = self.fresh("L")
            lines.append("%s := logic{%s := %s; %s}" % (L, V, call, pr))
            lines.append("if (%s?) then Print(\"yes\") else Print(\"no\")" % L)
            e = m.first(p.top(vals, V) + [("test", prm)])
            m.out.append("yes" if e is not None else "no")
        elif form == "not":
            lines.append("if (not %s) then Print(\"not\") else Print(\"some\")" % ty.pred(call, k))
            snap = len(m.out)
            e = m.first(p.top(vals, V) + [("test", prm)])
            del m.out[snap:]
            m.out.append("some" if e is not None else "not")
        elif form == "forexp":
            Rn = self.fresh("R")
            usepred = R.random() < 0.5
            seq = p.top(vals, V) + ([("test", prm)] if usepred else [])
            lines.append("%s := for (%s := %s%s) { %s }" % (Rn, V, call, (", " + pr) if usepred else "", ty.show(V)))
            S = self.fresh("S")
            lines.append("Print(\"n {%s.Length}\")" % Rn)
            lines.append("for (%s : %s) { Print(%s) }" % (S, Rn, S))
            got = []
            m.forall(seq, lambda e: got.append(ty.mshow(e[V])))
            m.out.append("n %d" % len(got)); m.out.extend(got)
        elif form in ("gfor", "gif", "gopt", "gmv"):
            if form != "gmv":
                tells = [vals[nm].s for nm, _ in p.params if isinstance(vals[nm], ArgTell)]
                vals = {nm: plain(x) for nm, x in vals.items()}
            G = self.fresh("G" + form[1:].upper())
            ps = ", ".join("%s:%s" % (nm, {"t": "t", "arr": "[]t", "int": "int"}[kd]) for nm, kd in p.params)
            pas = [nm for nm, _ in p.params]
            inner = p.call(pas)
            if form == "gfor":
                self.consumers.append("%s(%s where t:%s):[]t = for (Zc := %s) { Zc }" %
                                      (G, ps, "subtype(comparable)" if p.cmp else "type", inner))
                Rn = self.fresh("R")
                lines.append("%s := %s(%s)" % (Rn, G, ", ".join(args)))
                lines.append("for (%s : %s) { Print(%s) }" % (V, Rn, ty.show(V)))
                got = []
                m.out.extend(tells)
                m.forall(p.top(vals, "Zc"), lambda e: got.append(e["Zc"]))
                m.out.extend(ty.mshow(x) for x in got)
            elif form == "gif":
                s, d = ty.value()
                if ty.name == "animal":
                    # (the default at the static class of the arguments:
                    # theirs if they agree, else animal through a variable)
                    if st in ("cat", "dog"):
                        d = ("obj", st, d[2]); s = "%s{N := %d}" % (st, d[2])
                self.consumers.append("%s(%s, Dflt:t where t:%s):t = if (Zc := %s) then Zc else Dflt" %
                                      (G, ps, "subtype(comparable)" if p.cmp else "type", inner))
                lines.append("%s := %s(%s, %s)" % (V, G, ", ".join(args), s))
                lines.append("Print(%s)" % ty.show(V))
                m.out.extend(tells)
                e = m.first(p.top(vals, "Zc"))
                m.out.append(ty.mshow(e["Zc"] if e is not None else d))
            elif form == "gopt":
                self.consumers.append("%s(%s where t:%s):?t = option{%s}" %
                                      (G, ps, "subtype(comparable)" if p.cmp else "type", inner))
                lines.append("if (%s := %s(%s)?) then Print(%s) else Print(\"none\")" % (V, G, ", ".join(args), ty.show(V)))
                # (the call is in the if's condition: its arguments' effects
                # are undone when the option is empty)
                snap = len(m.out)
                m.out.extend(tells)
                e = m.first(p.top(vals, "Zc"))
                if e is None: del m.out[snap:]
                m.out.append(ty.mshow(e["Zc"]) if e is not None else "none")
            else:   # gmv: a generic function with several values that takes another's
                spec = "<decides>" if p.decides else ""
                self.consumers.append("%s(%s where t:%s)%s:t =\n    Zc := %s\n    Zc" %
                                      (G, ps, "subtype(comparable)" if p.cmp else "type", spec, inner))
                gcall = ("%s[%s]" if p.decides else "%s(%s)") % (G, ", ".join(args))
                if R.random() < 0.5:
                    lines.append("for (%s := %s, %s) { Print(%s) }" % (V, gcall, pr, ty.show(V)))
                    m.forall(p.top(vals, V) + [("test", prm)], lambda e: m.out.append(ty.mshow(e[V])))
                else:
                    lines.append("if (%s := %s, %s) then Print(%s) else Print(\"none\")" % (V, gcall, pr, ty.show(V)))
                    e = m.first(p.top(vals, V) + [("test", prm)])
                    m.out.append(ty.mshow(e[V]) if e is not None else "none")
        elif form == "decides":
            # a <decides> function of its own, at the type argument: its body
            # takes the first success (first{}), called with []
            D = self.fresh("Dc")
            tyname = {"int": "int", "string": "string", "pt": "pt", "tup": "tuple(int, string)",
                      "animal": "animal", "arr": "[]int"}[ty.name]
            ps, inner_args, outer_args = [], [], []
            for (nm, kd), arg in zip(p.params, args):
                # Leave omitted arguments to the producer's default.
                inner_args.append(nm if arg is not None else None)
                if arg is not None:
                    ps.append("%s:%s" % (nm, {"t": tyname, "arr": "[]" + tyname, "int": "int"}[kd]))
                    outer_args.append(arg)
            self.consumers.append("%s(%s)<transacts><decides>:%s = first{Zc := %s; %s; Zc}" %
                                  (D, ", ".join(ps), tyname, p.call(inner_args), ty.pred("Zc", k)))
            lines.append("if (%s := %s[%s]) then Print(%s) else Print(\"none\")" %
                         (V, D, ", ".join(outer_args), ty.show(V)))
            e = m.first(p.top(vals, V) + [("test", prm)])
            m.out.append(ty.mshow(e[V]) if e is not None else "none")
        self.main.extend(lines)

    def program(self):
        kinds_i = ["I2", "I3", "IMeth", "IIf", "IArr", "IFx", "IFx2", "INest", "ILz", "ICmp", "IW", "IWArr", "IWOpt", "IWPair", "I2i", "I2i"]
        kinds_l = ["LElems", "LRep", "LTree", "LIf", "LFx", "LFx2", "LFxTree", "LCmp", "LW"]
        kinds_e = ["ERep", "ERev", "ETree", "EW"]
        # one of each path at least, then a few more
        # (#283: at times the lazy one has a return frame, LFr, from a stream of
        # its own, so seeds without it keep their programs)
        self.producer(R.choice(kinds_i))
        lazy = R.choice(kinds_l)
        if RFrame.random() < 0.3: lazy = "LFr" if RFrame.random() < 0.5 else "LFp"
        if RSeq.random() < 0.3: lazy = RSeq.choice(["LSq", "LSc", "LSb"])
        if RNest.random() < 0.3: lazy = RNest.choice(["LNc", "LNf"])
        if ROther.random() < 0.25: lazy = "LOt"
        if RInst.random() < 0.2: lazy = "LOt2"
        self.producer(lazy); self.producer(R.choice(kinds_e))
        for _ in range(R.randint(0, 2)):
            self.producer(R.choice(kinds_i + kinds_l + kinds_e))
        for _ in range(R.randint(3, 7)):
            self.stmt()
        self.for_continuations()
        self.first_searches()
        self.method_dispatch()
        self.recursive_named()
        self.mutual_generators()
        # (#283: a stream of its own, so seeds without it keep their programs)
        if random.Random(self.seed * 1000003 + 283290).random() < 0.3:
            self.mutual_sequence()
        if SHARED:
            self.main.append('Print("plain {plainvals{}.Vals()}")')
            self.m.out.append("plain 0")
        self.generic_overloads()
        self.bounded_generics()

    def bounded_generics(self):
        # (#502: type parameters with upper bounds, class, peer, container and numeric ones,
        # in functions with several values: members read through the bound dispatch to the
        # precise class, results keep the precise type, and where the first success is taken
        # a rejected alternative's output is rolled back; a stream of its own decides, so
        # seeds keep their other programs)
        rng = random.Random(self.seed * 1000003 + 502)
        if rng.random() >= 0.5:
            self.boundsrc = ""
            return
        self.boundsrc = (
            "bveh := class:\n"
            "    Speed:int = 1\n"
            "    Kind():string = \"veh\"\n"
            "bcar := class(bveh):\n"
            "    Doors:int = 4\n"
            "    Kind<override>():string = \"car\"\n"
            "btruck := class(bveh):\n"
            "    Load:int = 9\n"
            "    Kind<override>():string = \"truck\"\n"
            "BTag(X:t where t:subtype(bveh))<transacts>:t =\n"
            "    Print(\"tag {X.Kind()} {X.Speed}\")\n"
            "    X\n"
            "BBoth(X:t, Y:t where t:subtype(bveh))<transacts>:t = BTag(X) | BTag(Y)\n"
            "BUp(Base:t, V:u where t:subtype(bveh), u:subtype(t))<computes>:t = V\n"
            "BFast(Xs:[]t, Min:int where t:subtype(bveh))<transacts>:[]t = for (X:Xs, X.Speed > Min) { X }\n"
            "BHalf(X:t where t:subtype(rational))<computes><decides>:int = Floor[X / 2]\n"
            "BAll(Xs:t where t:subtype([]int))<transacts>:int = (if (F := Xs[0]) then F else -1) | Xs.Length\n"
            "bbox(t:subtype(bveh)) := class:\n"
            "    Item:t\n"
            "    Get()<transacts>:t = Item | Item\n"
            "    Pace()<computes>:int = Item.Speed\n")
        out = self.m.out
        # (what a for undoes, OV_FOR_BOOK: this stream's fors take calls of
        # functions with several values, kind `call`, or BFast's array, whose
        # source does nothing undoing would change, and none has a clause
        # between two generators: they print the same by either rule)
        def veh(kind):
            sp = rng.randint(0, 6)
            if kind == "bcar":
                d = rng.randint(1, 5)
                return ("bcar{Speed := %d, Doors := %d}" % (sp, d), sp, d)
            ld = rng.randint(1, 5)
            return ("btruck{Speed := %d, Load := %d}" % (sp, ld), sp, ld)
        own = {"bcar": "Doors", "btruck": "Load"}
        kindname = {"bcar": "car", "btruck": "truck"}
        for _ in range(rng.randint(1, 4)):
            k = rng.choice(["both", "first", "up", "fast", "half", "all", "box"])
            kind = rng.choice(["bcar", "btruck"])
            if k in ("both", "first"):
                a, b = veh(kind), veh(kind)
                if k == "both":
                    self.main.append('for (A := BBoth(%s, %s)) { Print("both {A.%s} {A.Kind()}") }' % (a[0], b[0], own[kind]))
                    for x in (a, b):
                        out += ["tag %s %d" % (kindname[kind], x[1]), "both %d %s" % (x[2], kindname[kind])]
                else:
                    cut = rng.randint(0, 6)
                    self.main.append('if (A := BBoth(%s, %s), A.Speed > %d) then Print("bfirst {A.%s}") else Print("bfirst none")'
                                     % (a[0], b[0], cut, own[kind]))
                    got = [x for x in (a, b) if x[1] > cut]
                    out += ["tag %s %d" % (kindname[kind], got[0][1]), "bfirst %d" % got[0][2]] if got else ["bfirst none"]
            elif k == "up":
                a = veh(kind)
                self.main.append('Print("up {BUp(bveh{}, %s).Kind()}")' % a[0])
                out.append("up %s" % kindname[kind])
            elif k == "fast":
                xs = [veh(kind) for _ in range(rng.randint(1, 3))]
                cut = rng.randint(0, 5)
                self.main.append('for (X : BFast(array{%s}, %d)) { Print("fast {X.%s}") }'
                                 % (", ".join(x[0] for x in xs), cut, own[kind]))
                out += ["fast %d" % x[2] for x in xs if x[1] > cut]
            elif k == "half":
                n = rng.randint(-9, 9)
                self.main.append('if (H := BHalf[%d]) { Print("half {H}") }' % n)
                out.append("half %d" % (n // 2))
            elif k == "all":
                xs = [rng.randint(-5, 9) for _ in range(rng.randint(1, 3))]
                self.main.append('for (V := BAll(array{%s})) { Print("ball {V}") }' % ", ".join(map(str, xs)))
                out += ["ball %d" % xs[0], "ball %d" % len(xs)]
            else:
                a = veh(kind)
                self.main.append('for (V := bbox(%s){Item := %s}.Get()) { Print("box {V.%s} {V.Kind()}") }' % (kind, a[0], own[kind]))
                out += ["box %d %s" % (a[2], kindname[kind])] * 2

    def generic_overloads(self):
        # (#283: generic overloads with several values or one, told apart by arity; their own
        # stream decides, so seeds keep their other programs)
        rng = random.Random(self.seed * 1000003 + 5692)
        if rng.random() >= 0.5:
            self.ovsrc = ""
            return
        self.ovsrc = (
            "Gov(X:t, Y:t where t:type)<transacts>:t = X | Y\n"
            "Gov(X:int)<transacts>:int = X * 7\n"
            "Gov(X:t, Y:t, Z:t where t:type)<transacts>:t = Gov(X, Z) | Y\n"
            "GovOne(X:int)<transacts>:int = Gov(X) + 1\n"
            "govbox(t:type) := class:\n"
            "    V:t\n"
            "    Get()<transacts>:t = V | V\n"
            "    Get(W:t, U:t)<transacts>:t = W | Get() | U\n")
        def lit(v):
            return '"%s"' % v if isinstance(v, str) else str(v)
        def pick():
            return rng.choice([lambda: rng.randint(-3, 9), lambda: rng.choice(["p", "qq", ""])])()
        out = self.m.out
        for _ in range(rng.randint(1, 4)):
            k = rng.choice(["two", "one", "three", "get", "get2", "first"])
            if k in ("two", "three", "get2", "first"):
                a = pick()
                b, c = [(rng.randint(-3, 9) if isinstance(a, int) else rng.choice(["p", "qq", ""])) for _ in range(2)]
            if k == "two":
                self.main.append('for (A := Gov(%s, %s)) { Print("gov2 {A}") }' % (lit(a), lit(b)))
                out += ["gov2 %s" % x for x in (a, b)]
            elif k == "one":
                n = rng.randint(-3, 9)
                self.main.append('Print("gov1 {GovOne(%d)}")' % n)
                out.append("gov1 %d" % (n * 7 + 1))
            elif k == "three":
                self.main.append('for (A := Gov(%s, %s, %s)) { Print("gov3 {A}") }' % (lit(a), lit(b), lit(c)))
                out += ["gov3 %s" % x for x in (a, c, b)]
            elif k == "get":
                v = pick()
                ty = "int" if isinstance(v, int) else "string"
                self.main.append('for (A := govbox(%s){V := %s}.Get()) { Print("get {A}") }' % (ty, lit(v)))
                out += ["get %s" % x for x in (v, v)]
            elif k == "get2":
                ty = "int" if isinstance(a, int) else "string"
                self.main.append('for (A := govbox(%s){V := %s}.Get(%s, %s)) { Print("get2 {A}") }' % (ty, lit(a), lit(b), lit(c)))
                out += ["get2 %s" % x for x in (b, a, a, c)]
            else:
                # (where the first success is taken: the first value other than the first argument)
                self.main.append('if (A := Gov(%s, %s, %s), A <> %s) then Print("govf {A}") else Print("govf none")'
                                 % (lit(a), lit(b), lit(c), lit(a)))
                rest = [x for x in (a, c, b) if x != a]
                out.append("govf %s" % rest[0] if rest else "govf none")

    def method_dispatch(self):
        # Every gate range covers each hierarchy, with the same independent
        # ordered-value oracle. Argument effects and rejected first searches
        # distinguish dispatch selection from an extra generator boundary.
        base_shapes = ['plain', 'added', 'fixed', 'repeat', 'reorder', 'wrapped', 'interface']
        shapes = base_shapes + ['own-' + s for s in base_shapes] + ['cross-' + s for s in base_shapes]
        rng = random.Random(self.seed * 1000003 + 28304102)
        p = Producer('IMeth', self.fresh('Dispatch'), shapes[self.seed % len(shapes)])
        self.prods.append(p)
        self.paths.add('inlined')
        x, y, cut = rng.randint(-3, 5), rng.randint(-3, 5), rng.randint(-3, 5)
        for first in [False, True]:
            call = f'{p.name}(Tell("method left",{x}),Tell("method right",{y}))'
            vals = {'X': ArgTell('method left',x), 'Y': ArgTell('method right',y)}
            seq = p.top(vals,'V') + [('test', lambda e: e['V'] > cut)]
            if first:
                self.main.append(f'if (V := {call}, V > {cut}) then Print("method first {{V}}") else Print("method none")')
                got = self.m.first(seq)
                self.m.out.append(f"method first {got['V']}" if got is not None else 'method none')
            else:
                self.main.append(f'for (V := {call}, V > {cut}) {{ Print("method all {{V}}") }}')
                self.m.forall(seq, lambda e: self.m.out.append(f"method all {e['V']}"))
        self.main.append(f'for (V := {p.name}("x","y")) {{ Print("method string {{V}}") }}')
        self.m.forall(p.top({'X':'x','Y':'y'},'V'), lambda e: self.m.out.append(f"method string {e['V']}"))
    def recursive_named(self):
        # Model named/default arguments at every recursive edge, independently
        # of the compiler's argument binder. Some seeds use a mutual group.
        # (A default cannot fail, the Book of Verse's tests, DefaultNamed.versetest:820:
        # the check that ends the recursion is the callee's first clause, after
        # its arguments and default are evaluated, so its failure rolls back
        # the edge as a failing default's did.)
        rng = random.Random(self.seed * 1000003 + 28307)
        tuple_rng = random.Random(self.seed * 1000003 + 246140)
        def positional(*args):
            text = ','.join(args)
            return f'({text})' if tuple_rng.random() < 0.5 else text
        meter, trace, even, odd, search, pair, eager, default, repeat, box, swap_all, swap_first = [self.fresh(n) for n in
            ('NamedMeter', 'NamedTrace', 'NamedEven', 'NamedOdd', 'NamedSearch', 'NamedPair', 'NamedEager', 'NamedDefault', 'NamedRepeat', 'NamedBox', 'NamedSwapAll', 'NamedSwapFirst')]
        mutual = rng.choice([False, True])
        limit, start, step = rng.randint(0, 3), rng.randint(-1, 1), rng.randint(1, 2)
        offsets, extra = [rng.randint(-2, 3), rng.randint(-2, 3)], rng.randint(1, 4)
        default_limit = rng.randint(-1, limit + 1)
        self.consumers.append(f'''{meter} := class:
    var N:int = 0
{trace}(H:{meter}, Label:string, Value:int)<transacts>:int =
    set H.N += 1
    Print("named {{Label}} {{Value}} {{H.N}}")
    Value
{default}(H:{meter}, N:int, Offset:int)<transacts>:int =
    {trace}(H,"default",N+Offset)''')
        for i, name in enumerate([even, odd] if mutual else [even]):
            target = [odd, even][i] if mutual else even
            edge = positional('H', f'{trace}(H,"pos",N+{step})')
            self.consumers.append(f'''{name}(H:{meter}, N:int, ?A:int={default}(H,N,{offsets[i]}), ?B:int=A+{extra})<transacts><decides>:int =
    N <= {default_limit}
    N <= {limit}
    Print("named visit {{N}} {{A}} {{B}} {{H.N}}")
    A | {target}[{edge},?B:={trace}(H,"arg",N+{extra})]''')
        if RECURSIVE_RETURNS and random.Random(self.seed * 1000033 + 467).random() < 0.5:
            for i in range(1 if not mutual else 2):
                at = -1 - i
                lines = self.consumers[at].splitlines()
                lines[-1] = "    return " + lines[-1].strip()
                self.consumers[at] = "\n".join(lines)
        generic_edge = positional('X', 'Other', 'N-1')
        self.consumers.append(f'''{search}(X:t, Y:t, H:{meter}, Cut:int where t:type)<transacts>:?t =
    var Current:t = X
    var Total:int = 0
    Result := if (V := {even}[H,{start}], set Current = Y, set Total += V,
        Print("named try {{V}} {{Total}}"), V >= Cut) then option{{Current}} else false
    Print("named state {{Total}} {{H.N}}")
    Result
{pair}(X:t, ?Y:t=X where t:type)<computes>:t = X | Y
{eager}(X:t, N:int, ?Y:t=X where t:type)<computes>:t =
    if (N>0) then ({pair}(X,?Y:=Y) | {pair}(X) | {eager}(X,N-1)) else X
{box}(t:type) := struct:
    E:[]t = Concatenate()
    V:t
{repeat}(X:a,Other:b,N:int,?Y:a=block{{ O:=option{{ B:{box}(a)={box}{{V:=X|X}}; B }}; if(B:=O?)then B.V else X }} where a:type,b:type)<transacts><decides>:a =
    N > 0
    Print("named generic {{N}}")
    Y | {repeat}[{generic_edge}]
{swap_all}(X:b,Y:b,Z:a,N:int where a:type,b:type)<transacts>:[]b = for(V:={repeat}[X,Z,N,?Y:=Y]): V
{swap_first}(X:b,Y:b,Z:a,N:int where a:type,b:subtype(comparable))<transacts>:?b =
    if(V:={repeat}[X,Z,N,?Y:=Y],V=X)then option{{V}}else false''')
        h = self.fresh('NamedHeap')
        self.main.append(f'{h} := {meter}{{}}')
        # Each call evaluates its arguments and default, then the callee's first
        # clauses, which may fail: in a for, what a lazily taken call of the
        # recursive group did stays when its clauses fail (LANGUAGE.md, #283).
        visits = 1
        a, b = start + offsets[0], start + offsets[0] + extra
        self.m.out.append(f'named default {a} {visits}')
        n, role = start, 0
        while n <= limit and n <= default_limit:
            self.m.out.append(f'named visit {n} {a} {b} {visits}')
            self.m.out.append(f'named all {a}')
            next_n, b = n + step, n + extra
            role = 1 - role if mutual else 0
            a = next_n + offsets[role]
            for label, value in [('pos', next_n), ('arg', b), ('default', a)]:
                visits += 1
                self.m.out.append(f'named {label} {value} {visits}')
            n = next_n
        self.main.append(f'for (V := {even}[{h},{start}]) {{ Print("named all {{V}}") }}')
        self.main.append(f'Print("named visits {{{h}.N}}")')
        self.m.out.append(f'named visits {visits}')
        for literal, other, value in [('1', '2', '2'), ('"old"', '"new"', 'new')]:
            cut = rng.randint(-2, limit + 5)
            result = self.fresh('NamedResult')
            self.main.append(f'if ({result} := {search}({literal},{other},{h},{cut})?) then Print("named value {{{result}}}") else Print("named none")')
            saved, saved_visits = len(self.m.out), visits
            n, role = start, 0
            a, b = n + offsets[0], n + offsets[0] + extra
            if n <= default_limit:
                visits += 1
                self.m.out.append(f'named default {a} {visits}')
            succeeded = False
            while n <= limit and n <= default_limit:
                self.m.out.append(f'named visit {n} {a} {b} {visits}')
                if a >= cut:
                    self.m.out.append(f'named try {a} {a}')
                    self.m.out.append(f'named state {a} {visits}')
                    self.m.out.append(f'named value {value}')
                    succeeded = True
                    break
                # (an edge whose callee fails ends the search: the if rolls it
                # back with the rest of the search when no value succeeded)
                next_n, b = n + step, n + extra
                if next_n > default_limit:
                    break
                role = 1 - role if mutual else 0
                a = next_n + offsets[role]
                for label, arg in [('pos', next_n), ('arg', b), ('default', a)]:
                    visits += 1
                    self.m.out.append(f'named {label} {arg} {visits}')
                n = next_n
            if not succeeded:
                del self.m.out[saved:]
                visits = saved_visits
                self.m.out.append('named none')
            depth = rng.randint(0, 3)
            self.main.append(f'for (V := {eager}({literal},{depth},?Y:={other})) {{ Print("named eager {{V}}") }}')
            x = literal.strip('"')
            values = [x] if depth == 0 else [x, value, x, x] + [x] * (4 * (depth - 1) + 1)
            self.m.out.extend(f'named eager {v}' for v in values)
            self.main.append(f'for (V := {repeat}[{literal},0,{depth},?Y:={other}]) {{ Print("named generic value {{V}}") }}')
            for n in range(depth, 0, -1):
                self.m.out.append(f'named generic {n}')
                self.m.out.append(f'named generic value {value if n == depth else x}')
            result = self.fresh('NamedGenericResult')
            self.main.append(f'if ({result} := {repeat}[{literal},0,{depth},?Y:={other}], {result}={literal}) then Print("named generic first {{{result}}}") else Print("named generic none")')
            if depth > 1:
                self.m.out.extend([f'named generic {depth}', f'named generic {depth-1}', f'named generic first {x}'])
            else:
                self.m.out.append('named generic none')
            opposite = '"unused"' if literal == '1' else '7'
            self.main.append(f'for(V:{swap_all}({literal},{other},{opposite},{depth})): Print("named swap value {{V}}")')
            self.m.out.extend(f'named generic {n}' for n in range(depth, 0, -1))
            if depth:
                self.m.out.extend(f'named swap value {v}' for v in [value] + [x] * (depth - 1))
            result = self.fresh('NamedSwapResult')
            self.main.append(f'if({result}:={swap_first}({literal},{other},{opposite},{depth})?)then Print("named swap first {{{result}}}")else Print("named swap none")')
            if depth > 1:
                self.m.out.extend([f'named generic {depth}', f'named generic {depth-1}', f'named swap first {x}'])
            else:
                self.m.out.append('named swap none')
        self.main.append(f'Print("named final {{{h}.N}}")')
        self.m.out.append(f'named final {visits}')

    def first_searches(self):
        # A separate stream covers nested effectful generic helpers and
        # mutable copy-out. Rejected inner searches roll back as a whole;
        # outer producer prefixes survive until the entire search fails.
        rng = random.Random(self.seed * 1000003 + 24603)
        meter, count, walk, search, witness = [self.fresh(n) for n in
                                             ('SearchMeter', 'SearchCount', 'SearchWalk', 'SearchGeneric', 'SearchWitness')]
        limit = rng.randint(0, 4)
        self.consumers.append(f'''{meter} := class:
    var N:int = 0
{count}(H:{meter}, I:int)<transacts><decides>:int =
    I <= {limit}
    set H.N += 1
    Print("search outer {{I}} {{H.N}}")
    I | {count}[H, I + 1]
{walk}(H:{meter}, A:[]t, I:int where t:type)<transacts><decides>:t =
    I < A.Length
    set H.N += 1
    Print("search inner {{I}} {{H.N}}")
    A[I] | {walk}[H, A, I + 1]
{search}(X:t, Y:t, H:{meter}, Cut:int where t:type)<transacts>:?t =
    var Current:t = X
    var Total:int = 0
    Result := if (I := {count}[H, 0], J := {walk}[H, array{{Y, Current}}, 0],
        set Total += I, set Current = J, Print("search try {{I}} {{Total}}"), I >= Cut):
        option{{Current}}
    else:
        false
    Print("search state {{Total}} {{H.N}}")
    Result
{witness}(Unused:t, H:{meter}, Cut:int where t:type)<transacts>:int =
    if (I := {count}[H, 0], block{{ E:[]t = array{{}}; E.Length = 0 }}, I >= Cut) then I else -1''')
        h = self.fresh('SearchHeap')
        self.main.append(f'{h} := {meter}{{}}')
        visits = 0
        for literal, other, value in [('1', '2', '2'), ('"old"', '"new"', 'new')]:
            cut = rng.randint(-1, limit + 2)
            result = self.fresh('SearchResult')
            self.main.append(f'if ({result} := {search}({literal}, {other}, {h}, {cut})?) then Print("search value {{{result}}}") else Print("search none")')
            selected = max(0, cut)
            if selected <= limit:
                for i in range(selected + 1):
                    visits += 1
                    self.m.out.append(f'search outer {i} {visits}')
                visits += 1
                self.m.out.append(f'search inner 0 {visits}')
                self.m.out.append(f'search try {selected} {selected}')
                self.m.out.append(f'search state {selected} {visits}')
                self.m.out.append(f'search value {value}')
            else:
                # The enclosing query also rolls back the wrapper's state
                # print when it returns an empty option.
                self.m.out.append('search none')
            cut = rng.randint(-1, limit + 2)
            self.main.append(f'Print("search witness {{{witness}({literal}, {h}, {cut})}}")')
            selected = max(0, cut)
            if selected <= limit:
                for i in range(selected + 1):
                    visits += 1
                    self.m.out.append(f'search outer {i} {visits}')
            self.m.out.append(f'search witness {selected if selected <= limit else -1}')
        self.main.append(f'Print("search visits {{{h}.N}}")')
        self.m.out.append(f'search visits {visits}')

    def for_continuations(self):
        # Keep the seed's earlier producers and consumers unchanged. Scalar B
        # belongs to A's filter; a choice B starts a new generator boundary.
        rng = random.Random(self.seed * 1000003 + 335)
        cut, limit, bound = rng.randint(0, 5), rng.randint(-1, 12), rng.randint(0, 5)
        name = self.fresh("ContValues")
        written = self.fresh("ContWritten")
        pair = self.fresh("ContPair")
        self.consumers.append(f'''{pair}(N:int)<computes>:int = N | N + 1
{name}(X:t, Limit:int where t:type)<transacts>:[]tuple(t, int) =
    var Total:int = 0
    Values := for (A := {pair}(1) | {pair}(3), set Total += A,
                   B := if (A > {cut}) then (10 | 11) else 0, B > Limit,
                   C := {pair}(1) | {pair}(3), C <= {bound}):
        set Total += B + C
        (X, A * 100 + B * 10 + C)
    Print("cont state {{Total}} {{Values.Length}}")
    Values
{written}(X:t where t:type):[][]t =
    for (A := {pair}(1) | {pair}(3), A <= {bound}, B := {pair}(1) | {pair}(3), B > {cut}):
        E:[]t = array{{}}
        E''')
        for literal in [str(rng.randint(-9, 9)), '"s"']:
            value = literal.strip('"')
            result = self.fresh("ContResult")
            self.main.append(f"{result} := {name}({literal}, {limit})")
            self.main.append(f'for (V : {result}) {{ Print("cont value {{V(0)}} {{V(1)}}") }}')
            total, values = 0, []
            for a in range(1, 5):
                before = total
                total += a
                generated = a > cut
                bs = [10, 11] if generated else [0]
                for b in bs:
                    if b <= limit:
                        if not generated:
                            total = before
                        continue
                    for c in range(1, 5):
                        if c <= bound:
                            total += b + c
                            values.append(a * 100 + b * 10 + c)
            self.m.out.append(f"cont state {total} {len(values)}")
            self.m.out.extend(f"cont value {value} {code}" for code in values)
            self.main.append(f'Print("cont written {{{written}({literal}).Length}}")')
            count = sum(a <= bound and b > cut for a in range(1, 5) for b in range(1, 5))
            self.m.out.append(f"cont written {count}")

    def mutual_sequence(self):
        """(#283) A generic mutual group whose second member is called only from the code after a
        choice point in the first (a continuation member's code), so its type instance is found
        there: A's values are its call of itself's, then the tuple of its arguments, each followed
        by a print, then B's values on it and it; B's the swapped tuple, then A's on it."""
        rng = random.Random(self.seed * 1000003 + 283291)
        a, b = self.fresh('SeqA'), self.fresh('SeqB')
        n, cut = rng.randint(1, 2), rng.randint(0, 25)
        (xs, xv), (ys, yv) = rng.choice([(('"s"', 's'), ('7', 7)), (('7', 7), ('"s"', 's'))])
        self.paths.add('lazy')
        self.consumers.append(f'''{a}(X:t, Y:u, N:int where t:type, u:type)<transacts><decides>:tuple(t, u, int) =
    N > 0
    Z := {a}[X, Y, N - 1] | (X, Y, N)
    Print("seq a {{N}} {{Z(2)}}")
    {b}[Z(1), Z(0), N - 1] | Z
{b}(Y:v, X:w, M:int where v:type, w:type)<transacts><decides>:tuple(w, v, int) =
    M >= 0
    (X, Y, M * 10) | {a}[X, Y, M]''')
        # (each call a generator of its own: what came before it stays when its clauses fail)
        def seq_a(x, y, k, var):
            if k <= 0:
                return [("cond", False)]
            z = var + "z"
            def after(env):
                zv = env[z]
                return [("print", f"seq a {k} {zv[2]}"),
                        ("choice", [[("choice", [seq_b(zv[1], zv[0], k - 1, var)])], [("val", var, zv)]])]
            return [("choice", [[("choice", [seq_a(x, y, k - 1, z)])], [("val", z, (x, y, k))]]), ("dyn", after)]
        def seq_b(y, x, m, var):
            if m < 0:
                return [("cond", False)]
            return [("choice", [[("val", var, (x, y, m * 10))], [("choice", [seq_a(x, y, m, var)])]])]
        m = self.m
        self.main += [f'for (V := {a}[{xs}, {ys}, {n}]) {{ Print("seq got {{V(0)}} {{V(1)}} {{V(2)}}") }}',
                      f'if (V := {a}[{xs}, {ys}, {n}], V(2) >= {cut}) then Print("seq first {{V(0)}} {{V(1)}} {{V(2)}}") else Print("seq none")']
        m.forall([("choice", [seq_a(xv, yv, n, "SQ")])], lambda e: m.out.append(f"seq got {e['SQ'][0]} {e['SQ'][1]} {e['SQ'][2]}"))
        e = m.first([("choice", [seq_a(xv, yv, n, "SQ")]), ("test", lambda env: env["SQ"][2] >= cut)])
        m.out.append("seq none" if e is None else f"seq first {e['SQ'][0]} {e['SQ'][1]} {e['SQ'][2]}")

    def mutual_generators(self):
        """Depth-first tree model with separate item and value transactions."""
        rng = random.Random(self.seed * 1000033 + 453)
        a, b, c, emit, cell, run = [self.fresh(n) for n in
                                  ('MutA', 'MutB', 'MutC', 'MutValue', 'MutCell', 'MutRun')]
        depth, first_depth = rng.randint(0, 3), rng.randint(0, 3)
        cut, first_cut = rng.randint(0, 35), rng.randint(0, 35)
        entry, first_entry = rng.randrange(3), rng.randrange(3)
        x, y = rng.choice([('7', '"s"'), ('"s"', '7')])
        payload = f'{x.strip(chr(34))} {y.strip(chr(34))}'
        call = lambda i, x, y, n, h: [f'{a}[({x},{y},{n},{h})]',
            f'{b}[({y},{x},{n},{h})]', f'{c}[(({x},{y}),{n},{h})]'][i]
        self.paths.add('lazy')
        self.consumers.append(f'''{cell} := class {{ var N:int=0 }}
{emit}(X:t,Y:u,N:int where t:type,u:type)<transacts>:tuple(t,u,int) =
    Print("mut value {{N}}")
    (X,Y,N)
{a}(X:a,Y:b,N:int,H:{cell} where a:type,b:subtype(comparable))<transacts><decides>:tuple(a,b,int) =
    set H.N+=1
    Print("mut visit 0 {{N}}")
    if(N>0)then ({emit}(X,Y,10*N) | {b}[(Y,X,N-1,H)] | {emit}(X,Y,10*N+1))else {emit}(X,Y,0)
{b}(Y:k,X:v,N:int,H:{cell},?E:[]v=Concatenate() where k:subtype(comparable),v:type)<transacts><decides>:tuple(v,k,int) =
    set H.N+=1
    Print("mut visit 1 {{N}}")
    M:[k]v=map{{Y=>X}}
    if(N>0)then ({emit}(X,Y,10*N+2) | {c}[((X,Y),N-1,H)] | {emit}(X,Y,10*N+3))else {emit}(X,Y,2)
{c}(Z:tuple(c,d),N:int,H:{cell} where c:type,d:subtype(comparable))<transacts><decides>:tuple(c,d,int) =
    set H.N+=1
    Print("mut visit 2 {{N}}")
    E:[]c=Concatenate()
    if(N>0)then ({emit}(Z(0),Z(1),10*N+4) | {a}[Z(0),Z(1),N-1,H] | {emit}(Z(0),Z(1),10*N+5))else {emit}(Z(0),Z(1),4)
{run}(X:b,Y:a,W:w where a:subtype(comparable),b:type,w:type):?tuple(b,a,int) =
    H:={cell}{{}}
    var Seen:int=0
    Result:=option{{V:={call(first_entry, 'X', 'Y', first_depth, 'H')}; E:[]w=Concatenate();set Seen+=V(2);V(2)>={first_cut};V}}
    Print("mut state {{H.N}} {{Seen}}")
    Result''')
        if RECURSIVE_RETURNS and random.Random(self.seed * 1000033 + 466).random() < 0.5:
            source = self.consumers[-1]
            for i in range(3):
                visit = f'    Print("mut visit {i} {{N}}")\n'
                source = source.replace(visit, "", 1)
            for i, line in enumerate([line for line in source.splitlines() if line.startswith("    if(N>0)then")]):
                tail, base = line.strip()[len("if(N>0)then "):].split("else ")
                tail = tail[1:-1].replace("N-1", "NextN")
                # (both returns in tail position, the branches of the body's
                # last if: the function is <decides>, Return.versetest:157)
                source = source.replace(line,
                    f'    if(N<=0):\n        Print("mut visit {i} {{N}}")\n'
                    f'        BaseN:={2*i}\n        return {base.replace(f",{2*i})", ",BaseN)")}\n'
                    f'    else:\n        Print("mut visit {i} {{N}}")\n        NextN:=N-1\n        return {tail}', 1)
            self.consumers[-1] = source
        h, option = self.fresh('MutState'), self.fresh('MutOption')
        self.main += [f'{h}:={cell}{{}}',
            f'for(V:={call(entry, x, y, depth, h)},set {h}.N+=V(2),V(2)>={cut}): Print("mut got {{V(0)}} {{V(1)}} {{V(2)}}")',
            f'Print("mut total {{{h}.N}}")', f'{option}:={run}({x},{y},option{{7}})',
            f'if(V:={option}?)then Print("mut first {{V(0)}} {{V(1)}} {{V(2)}}")else Print("mut none")']
        out, total = self.m.out, 0

        def all_values(member, n):
            nonlocal total
            total += 1
            out.append(f'mut visit {member} {n}')
            codes = [10*n+2*member, None, 10*n+2*member+1] if n else [2*member]
            for code in codes:
                if code is None:
                    all_values((member+1) % 3, n-1)
                elif code >= cut:
                    total += code
                    out.extend([f'mut value {code}', f'mut got {payload} {code}'])
        all_values(entry, depth)
        out.append(f'mut total {total}')
        total, seen = 0, 0

        def search(member, n):
            nonlocal total, seen
            start, old_total, old_seen = len(out), total, seen
            total += 1
            out.append(f'mut visit {member} {n}')
            codes = [10*n+2*member, None, 10*n+2*member+1] if n else [2*member]
            for code in codes:
                if code is None:
                    found = search((member+1) % 3, n-1)
                    if found is not None:
                        return found
                elif code >= first_cut:
                    seen += code
                    out.append(f'mut value {code}')
                    return code
            del out[start:]
            total, seen = old_total, old_seen
            return None
        found = search(first_entry, first_depth)
        out.append(f'mut state {total} {seen}')
        out.append('mut none' if found is None else f'mut first {payload} {found}')

    def text(self):
        pre = """pt := struct:
    A:int
    B:int
pair(t:type, u:type) := struct:
    First:t
    Second:u
animal := class:
    N:int = 0
    Name():string = "animal"
cat := class(animal):
    Name<override>():string = "cat"
dog := class(animal):
    Name<override>():string = "dog"
ShowArr(Arr:[]int):string =
    var Acc:string = "["
    for (E : Arr) { set Acc = Acc + "{E}," }
    Acc + "]"
Id(Y:t where t:type)<computes>:t = Y
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
"""
        if SHARED:
            pre += "plainvals := class:\n    Vals()<transacts>:int = 0\n"
        body = pre + "\n".join(p.src for p in self.prods) + "\n"
        if self.consumers: body += "\n".join(self.consumers) + "\n"
        body += getattr(self, "ovsrc", "")
        body += getattr(self, "boundsrc", "")
        body += "Main():void =\n" + "".join("    %s\n" % l for l in self.main)
        return body

def main():
    seed = int(sys.argv[1]); outdir = sys.argv[2]
    g = Gen(seed)
    g.program()
    src = g.text()
    if g.refusals:
        exp = "\n".join(sorted(g.refusals)) + "\nexit=4\n"
    else:
        exp = "".join(l + "\n" for l in g.m.out) + "exit=0\n"
    with open(os.path.join(outdir, "p.verse"), "w") as f: f.write(src)
    with open(os.path.join(outdir, "p.expected"), "w") as f: f.write(exp)
    with open(os.path.join(outdir, "p.meta"), "w") as f:
        f.write("paths=%s kinds=%s methods=%s bounds=%s\n" % (",".join(sorted(g.paths)), ",".join(p.kind for p in g.prods),
                ",".join(getattr(p, "method_shape", "direct") for p in g.prods if p.kind == "IMeth"),
                "yes" if getattr(g, "boundsrc", "") else "no"))

if __name__ == "__main__":
    main()
