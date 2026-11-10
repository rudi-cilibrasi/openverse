#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by a review agent of the upkeep session,
# independently of the front end's code, for the review of #282 (generic functions with
# several values, #235).
"""Random programs with generic functions with several values (#235, PR #282),
with a model of their output, written from docs/LANGUAGE.md ("Choice",
"Functions with several values", "Parametric functions", the readings table).

    usage: generic_mv.py SEED OUTDIR -> OUTDIR/p.verse, OUTDIR/p.expected, OUTDIR/p.meta

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
  * an effectful generator where the first success is taken inside a generic
    consumer is refused (exit 4).
"""
import random, sys, os

R = None
# (#387: an overridden method of a generic class; a generator of its own decides, so seeds keep
# their other programs)
R387 = None

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
    def __init__(self, kind, name):
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
            self.ovr = R387.random() < 0.5
            if self.ovr:
                # (#387: overridden in a generic subclass, which reaches it with (super:); the
                # receiver is typed at the base class, so the call dispatches: Y, then X | Y)
                self.src = ("c%s(t:type) := class:\n    X:t\n    Y:t\n    M%s()<transacts>:t = X | Y\n"
                            "d%s(t:type) := class(c%s(t)):\n    M%s<override>()<transacts>:t = Y | (super:)M%s()\n"
                            "%s(X:t, Y:t where t:type)<transacts>:t =\n    R:c%s(t) = d%s(t){X := X, Y := Y}\n    R.M%s()"
                            ) % (n, n, n, n, n, n, n, n, n, n)
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

    def bind_helper(self, h):
        """INest / ILz: an inlined generic function calling another."""
        self.helper = h
        n = self.name
        if self.kind == "INest":
            self.src = ("%s(X:t, Y:t, Z:t where t:type):t =\n"
                        "    W := %s(X, Y)\n    W | Z") % (n, h.name)
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
class Machine:
    def __init__(self):
        self.out = []

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
            elif op in ("choice", "choice2"):
                if op == "choice":
                    alts = ins[1]
                else:   # (W | Z: the value of W, then Z)
                    _, var, w, z = ins
                    alts = [[("val", var, env[w])], [("val", var, z)]]
                for alt in alts:
                    snap = len(self.out)
                    cont = (lambda e, s, seq=seq, i=i: self.run(seq, i + 1, e, k, mode, s))
                    if self.run(alt, 0, env, cont, mode, snap): return True
                    if mode == "first": del self.out[snap:]
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

    def forall(self, seq, body, env=None):
        env = env or {}
        snap = len(self.out)
        def k(e, s):
            body(e); return False
        self.run(seq, 0, env, k, "for", snap)

# ---------------------------------------------------------------- the program
class Gen:
    def __init__(self, seed):
        global R, R387
        R = random.Random(seed)
        R387 = random.Random(seed * 1000003 + 387)
        self.seed = seed
        self.prods = []
        self.consumers = []    # source of generic consumers
        self.main = []
        self.m = Machine()
        self.refuse = None
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
    def args(self, p, ty, mode, choices=True):
        """mode (for classes): same (one class), mixed (any classes), parent
        (the first argument that gives t through a variable of the parent's
        type). Returns the arguments, their values, the lines declaring such
        variables, and whether a plain generic call refuses them (inference
        binds t from the first argument; later ones must convert to it)."""
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
        bad = bool(st) and any(c != st[0] and st[0] != "animal" for c in st[1:])
        self.lastst = st[0] if st else None
        return out, vals, pre, bad

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
        args, vals, pre, mixed = self.args(p, ty, mode, choices=form not in ("gfor", "gif", "gopt", "decides"))
        st = self.lastst
        self.main.extend(pre)
        call = p.call(args)
        if form == "not" and ty.name == "tup": form = "for"
        fxlazy = (p.fx and p.path == "lazy") or (p.kind == "ILz" and p.helper.fx)
        if form in ("gif", "gopt") and fxlazy and R.random() < 0.85:
            form = "gfor"   # (mostly avoid a known refusal that discards the program)
        if mixed and form != "decides":
            # (a call types as a plain generic call: t from the first
            # argument, which a sibling class's object does not convert to)
            self.refuse = self.refuse or "sibling classes for one t (%s path)" % p.path
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
            args2, vals2, pre2, _ = self.args(q, ty2, "same")
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
                if p.fx and p.path == "lazy" or (p.kind == "ILz" and p.helper.fx):
                    self.refuse = self.refuse or "effectful generator, first success, in a generic function"
                m.out.extend(tells)
                e = m.first(p.top(vals, "Zc"))
                m.out.append(ty.mshow(e["Zc"] if e is not None else d))
            elif form == "gopt":
                self.consumers.append("%s(%s where t:%s):?t = option{%s}" %
                                      (G, ps, "subtype(comparable)" if p.cmp else "type", inner))
                lines.append("if (%s := %s(%s)?) then Print(%s) else Print(\"none\")" % (V, G, ", ".join(args), ty.show(V)))
                if p.fx and p.path == "lazy" or (p.kind == "ILz" and p.helper.fx):
                    self.refuse = self.refuse or "effectful generator, first success, in a generic function"
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
            ps = []
            for (nm, kd) in p.params:
                ps.append("%s:%s" % (nm, {"t": tyname, "arr": "[]" + tyname, "int": "int"}[kd]))
            self.consumers.append("%s(%s)<transacts><decides>:%s = first{Zc := %s; %s; Zc}" %
                                  (D, ", ".join(ps), tyname, p.call([nm for nm, _ in p.params]), ty.pred("Zc", k)))
            lines.append("if (%s := %s[%s]) then Print(%s) else Print(\"none\")" % (V, D, ", ".join(args), ty.show(V)))
            e = m.first(p.top(vals, V) + [("test", prm)])
            m.out.append(ty.mshow(e[V]) if e is not None else "none")
        self.main.extend(lines)

    def program(self):
        kinds_i = ["I2", "I3", "IMeth", "IIf", "IArr", "IFx", "IFx2", "INest", "ILz", "ICmp", "IW", "IWArr", "IWOpt", "IWPair", "I2i", "I2i"]
        kinds_l = ["LElems", "LRep", "LTree", "LIf", "LFx", "LFx2", "LFxTree", "LCmp", "LW"]
        kinds_e = ["ERep", "ERev", "ETree", "EW"]
        # one of each path at least, then a few more
        self.producer(R.choice(kinds_i)); self.producer(R.choice(kinds_l)); self.producer(R.choice(kinds_e))
        for _ in range(R.randint(0, 2)):
            self.producer(R.choice(kinds_i + kinds_l + kinds_e))
        for _ in range(R.randint(3, 7)):
            self.stmt()

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
        body = pre + "\n".join(p.src for p in self.prods) + "\n"
        if self.consumers: body += "\n".join(self.consumers) + "\n"
        body += "Main():void =\n" + "".join("    %s\n" % l for l in self.main)
        return body

def main():
    seed = int(sys.argv[1]); outdir = sys.argv[2]
    g = Gen(seed)
    g.program()
    src = g.text()
    if g.refuse:
        exp = "exit=4\n"
    else:
        exp = "".join(l + "\n" for l in g.m.out) + "exit=0\n"
    with open(os.path.join(outdir, "p.verse"), "w") as f: f.write(src)
    with open(os.path.join(outdir, "p.expected"), "w") as f: f.write(exp)
    with open(os.path.join(outdir, "p.meta"), "w") as f:
        f.write("paths=%s kinds=%s refuse=%s\n" % (",".join(sorted(g.paths)),
                ",".join(p.kind for p in g.prods), g.refuse or "-"))

if __name__ == "__main__":
    main()
