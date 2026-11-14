#!/usr/bin/env python3
"""Random openverse programs that stress the class features of the front end.

usage: gen.py SEED   (deterministic per seed; prints one program)

A program combines
  - a class hierarchy: 1-2 trees of 2-3 levels, <abstract>, <unique> and <final>
    classes, interfaces with fields and default methods (some extending others,
    overriding nothing, as the Book has it), <override> of methods and field
    defaults, (super:), <final> methods, var fields and set, fields holding objects,
    options, arrays and maps of objects, block: clauses, <decides> methods, method
    parameters of class and interface types, named parameters with defaults,
    methods returning objects with covariant overrides, casts of Self in bodies,
    return inside for, defer: in methods, blocks, constructors and loops;
  - heap effect specifiers (<computes> <reads> <writes> <allocates> <transacts>) on
    methods and constructors, consistent with the bodies and with what they override;
  - method names shared by two roots (two interfaces, or a class and an
    interface), implemented plainly or by qualified (i:)M implementations;
  - constructor functions: field initializers, let:, block:, named parameters,
    one-line and braced bodies, <decides>, overloads with disjoint parameters,
    delegation to an earlier overload or to an ancestor's constructor;
  - a stand-alone qualified (i:)M module;
  - a field two parametric interfaces declare, as the type parameter and as
    int, in classes that fix it to int (#205);
  - function values: functions and methods passed, stored and called (#210);
  - a parametric hierarchy pb(t) with renaming, fixing and extending subclasses,
    and a two-parameter class with subclasses that repeat or relate its type
    arguments (#209),
    a parametric interface, generic and fixed constructors, generic methods with
    overrides, generic functions;
  - overloaded top-level functions over disjoint types;
  - casts c[X], upcasts c(X), arrays of class and interface type iterated with
    for, set paths through arrays, options and object fields, rollback in failure
    contexts, a loop that allocates and links many objects.
Main prints everything it computes.  The first line lists the types that no
concrete class is below (drive.sh uses it to tag the known internal error).

Recursion is impossible by construction: every method root has a rank, and a
body calls only roots of lower rank (on any receiver), plus (super:) of its own
root, which goes up the hierarchy.  Method bodies never construct objects.
"""
import random
import sys

R = None  # the random.Random of this seed
NAMES = [0]


def chance(p):
    return R.random() < p


def lit(lo=0, hi=9):
    return str(R.randint(lo, hi))


def tmpname(p):
    NAMES[0] += 1
    return '%s%d' % (p, NAMES[0])


# ---------------------------------------------------------------- model

ALL = frozenset('rwa')   # heap effects: reads, writes, allocates


def pick_eff():
    """A declared heap effect set for a new method root."""
    k = R.random()
    if k < 0.5:
        return ALL
    if k < 0.65:
        return frozenset()
    if k < 0.8:
        return frozenset('r')
    if k < 0.87:
        return frozenset('w')
    if k < 0.94:
        return frozenset('rw')
    return frozenset('ra')


def narrow(eff):
    """The effects of an override: those of the declaration, or fewer."""
    if eff and chance(0.2):
        return frozenset(x for x in sorted(eff) if chance(0.5))
    return eff


def efftext(eff):
    if eff == ALL:
        return R.choice(['', '', '', '<transacts>'])
    if not eff:
        return '<computes>'
    return ''.join(t for x, t in (('r', '<reads>'), ('w', '<writes>'), ('a', '<allocates>')) if x in eff)

def tytext(ty):
    if isinstance(ty, tuple):
        return {'opt': '?%s', 'arr': '[]%s', 'map': '[string]%s'}[ty[0]] % ty[1].name
    if isinstance(ty, str):
        return ty
    return ty.name


class Field:
    def __init__(self, name, ty, var, default, owner):
        # ty: 'int' | 'string' | ('opt', T) | ('arr', T) | ('map', T) | a class T
        self.name, self.ty, self.var, self.default, self.owner = name, ty, var, default, owner
        self.constructs = False   # the default constructs an object

    def tytext(self):
        return tytext(self.ty)


def scalar(f):
    return f.ty in ('int', 'string')


class Root:
    """A method declaration that overrides nothing (a slot)."""
    def __init__(self, name, ptypes, ret, rank, decides, owner):
        self.name, self.ptypes, self.ret, self.rank = name, ptypes, ret, rank
        self.decides, self.owner = decides, owner
        self.pnames = []
        self.eff = ALL
        self.named = []   # names of ?N:int parameters, after the positional ones

    def sig(self, override=False, final=False, eff=None, ret=None, defaults=None):
        ps = ', '.join(['%s:%s' % (p, tytext(t)) for p, t in zip(self.pnames, self.ptypes)] +
                       ['?%s:int = %s' % (n, dv) for n, dv in zip(self.named, defaults or [])])
        spec = '<override>' if override else ''
        if final:
            spec += '<final>'
        dec = '<decides>' if self.decides else ''
        et = efftext(self.eff if eff is None else eff)
        if chance(0.5):
            dec = dec + et
        else:
            dec = et + dec
        return '%s%s(%s)%s:%s' % (self.name, spec, ps, dec, tytext(ret or self.ret))


class Impl:
    def __init__(self, owner, abstract, final=False, qual=None, eff=ALL):
        self.owner, self.abstract, self.final, self.qual = owner, abstract, final, qual
        self.eff = eff
        self.ret = None   # a covariant result type, when the implementation narrows it


def good(im):
    return isinstance(im, Impl) and not im.abstract


class Iface:
    is_iface = True
    abstract = True

    def __init__(self, name, parents):
        self.name, self.parents = name, parents
        self.fields = []
        self.roots = []
        self.impls = {}  # Root -> Impl (defaults and overrides)
        self.lines = []

    def closure(self):
        out = []
        for p in self.parents:
            for q in p.closure():
                if q not in out:
                    out.append(q)
        if self not in out:
            out.append(self)
        return out

    def below(self, other):
        return other.is_iface and other in self.closure()


class Cls:
    is_iface = False

    def __init__(self, name, parent, ifaces, abstract):
        self.name, self.parent, self.ifaces, self.abstract = name, parent, ifaces, abstract
        self.fields = []        # own new fields
        self.over = {}          # field name -> default expr (overrides)
        self.roots = []
        self.impls = {}         # Root -> Impl
        self.plain = {}         # name -> plain Impl given here
        self.children = []
        self.ctors = []
        self.lines = []
        self.items = []
        self.final = False
        self.unique = False
        self.has_block = False

    def chain(self):
        c, out = self, []
        while c:
            out.append(c)
            c = c.parent
        return out

    def all_ifaces(self):
        out = []
        for c in reversed(self.chain()):
            for i in c.ifaces:
                for q in i.closure():
                    if q not in out:
                        out.append(q)
        return out

    def below(self, other):
        if other.is_iface:
            return other in self.all_ifaces()
        return other in self.chain()

    def all_fields(self):
        out, seen = [], set()
        for c in reversed(self.chain()):
            for i in c.ifaces:
                for q in i.closure():
                    for f in q.fields:
                        if f.name not in seen:
                            seen.add(f.name)
                            out.append(f)
            for f in c.fields:
                if f.name not in seen:
                    seen.add(f.name)
                    out.append(f)
        return out

    def has_default(self, f):
        if f.default is not None:
            return True
        if any(f.name in c.over for c in self.chain()):
            return True
        # an interface's default for the field counts where the field enters the chain
        # (a class inherits an interface's fields that are not there yet)
        top = [c for c in self.chain() if f.name in [g.name for g in c.all_fields()]][-1]
        return any(f.name in getattr(i, 'fover', {}) for i in top.all_ifaces())

    def all_roots(self):
        out = []
        for c in reversed(self.chain()):
            for i in c.ifaces:
                for q in i.closure():
                    for r in q.roots:
                        if r not in out:
                            out.append(r)
            for r in c.roots:
                if r not in out:
                    out.append(r)
        return out

    def subtree(self):
        out = [self]
        for k in self.children:
            out += k.subtree()
        return out


def iface_default(ifaces, root):
    """The most specific interface implementation of root among ifaces, or None / 'ambig'."""
    cands = [i for i in ifaces if root in i.impls]
    if not cands:
        return None
    best = [i for i in cands if all(i.below(j) for j in cands)]
    if len(best) != 1:
        return 'ambig'
    return best[0].impls[root]


def resolve(cls, root, skip_own=False):
    """The implementation a class runs for slot root, or None / 'ambig'.

    The nearest qualified or plain implementation in the class chain wins.  Otherwise
    the candidates are the most specific interface default of root, and (as in Java)
    what the class above the one that introduced the slot has for the name; two
    different candidates are a conflict that the class must resolve by overriding."""
    full = cls.chain()
    chain = full[1:] if skip_own else full
    for c in chain:
        if root in c.impls:
            return c.impls[root]
        im = c.plain.get(root.name)
        if good(im):
            return im
    d1 = iface_default(cls.all_ifaces(), root)
    top = [c for c in full if root in c.all_roots()][-1]
    d2 = None
    if top.parent:
        rs = [resolve(top.parent, s) for s in top.parent.all_roots() if s.name == root.name]
        gs = [r for r in rs if good(r)]
        if len(set(id(r) for r in rs)) > 1:
            return 'ambig'   # the class above implements the name differently for its slots
        if gs:
            d2 = gs[0]
    if good(d1) and good(d2) and d1 is not d2:
        return 'ambig'
    if good(d1):
        return d1
    if good(d2):
        return d2
    return d1


def name_effs(cls, name, skip_own=False):
    """The effects of every implementation and declaration of name visible to cls."""
    out = []
    chain = cls.chain()[1:] if skip_own else cls.chain()
    for c in chain:
        out += [im.eff for r, im in c.impls.items() if r.name == name]
    for i in cls.all_ifaces():
        out += [im.eff for r, im in i.impls.items() if r.name == name]
        out += [r.eff for r in i.roots if r.name == name]
    return out


def meet(effs, base=ALL):
    out = base
    for e in effs:
        out = out & e
    return out


def roots_of_type(t):
    if t.is_iface:
        out = []
        for i in t.closure():
            for r in i.roots:
                if r not in out:
                    out.append(r)
        return out
    return t.all_roots()


def fields_of_type(t):
    if t.is_iface:
        out = []
        for i in t.closure():
            for f in i.fields:
                if f not in out:
                    out.append(f)
        return out
    return t.all_fields()


# ---------------------------------------------------------------- expressions

class Ctx:
    def __init__(self, ints=(), strs=(), maxrank=10 ** 9):
        self.ints = list(ints)    # int-valued atoms
        self.strs = list(strs)    # string-valued atoms
        self.calls = []           # (prefix, Root): callable as prefix + name(...)
        self.objs = []            # (expr, type): object values (arguments, cast sources)
        self.opts = []            # (expr, type): options of objects (fields)
        self.arrs = []            # (expr, type): arrays of objects (fields)
        self.maps = []            # (expr, type): maps from strings to objects (fields)
        self.casts = []           # (expr, type): an object and a type to cast it to
        self.maxrank = maxrank
        self.callable = GEN[0].callable if GEN else None
        self.allowed = ALL        # heap effects the code may have


GEN = []


def isobj(t):
    return not isinstance(t, (str, tuple))


def below(t, k):
    return t is k or t.below(k)


def args_text(root, ctx, d):
    out = []
    for t in root.ptypes:
        if t == 'int':
            out.append(iexpr(ctx, d - 1))
        else:
            cands = [e for (e, u) in ctx.objs if below(u, t)]
            if not cands:
                return None
            out.append(R.choice(cands))
    for n in root.named:
        if chance(0.5):
            out.append('?%s := %s' % (n, iexpr(ctx, d - 1)))
    return ', '.join(out)


def call_text(prefix, root, ctx, d, bracket=False):
    a = args_text(root, ctx, d)
    if a is None:
        return None
    o, c = ('[', ']') if bracket else ('(', ')')
    return '%s%s%s%s%s' % (prefix, root.name, o, a, c)


def shown(p, r, ctx, d):
    """A call usable in an interpolation: an int or string, or a read on the object it returns."""
    t = call_text(p, r, ctx, d)
    if t and isobj(r.ret):
        c = on_object(ctx, t, r.ret, d)
        return c[0] if c else None
    return t


def callable_now(ctx, decides=False):
    return [(p, r) for (p, r) in ctx.calls
            if r.rank < ctx.maxrank and r.decides == decides and r.eff <= ctx.allowed]


def on_object(ctx, e, t, d, want='int'):
    """An int (or string) read from the object e of type t: a call or a field."""
    sub = sub_ctx(ctx, t, e + '.')
    if GEN and '(' in e:
        sub.calls = [(p, r) for (p, r) in sub.calls if r.name not in GEN[0].shared or p.endswith(':)')]
    c = some_call(sub, d - 1, want) if d > 0 else None
    if c:
        return c
    fs = [f for f in fields_of_type(t) if f.ty == want and (not f.var or 'r' in ctx.allowed)]
    if fs:
        return ('%s.%s' % (e, R.choice(fs).name), want)
    return None


def some_call(ctx, d, want=None):
    """A call giving want ('int', 'string', or None for either): (text, type) or None.
    A call returning an object is followed by a call or a field read on it."""
    cs = [(p, r) for (p, r) in callable_now(ctx)
          if want is None or r.ret == want or (isobj(r.ret) and d > 1)]
    R.shuffle(cs)
    for p, r in cs[:4]:
        t = call_text(p, r, ctx, d)
        if not t:
            continue
        if isobj(r.ret):
            c = on_object(ctx, t, r.ret, d - 1, want or 'int')
            if c:
                return c
            continue
        return t, r.ret
    return None


def sub_ctx(ctx, t, prefix):
    sub = Ctx(ctx.ints, ctx.strs, ctx.maxrank)
    sub.calls = ctx.callable(t, prefix)
    sub.objs = ctx.objs
    sub.allowed = ctx.allowed
    return sub


def via_object(ctx, d):
    """An int computed through a field holding objects, or through a cast."""
    if ctx.callable is None:
        return None
    k = R.random()
    if ctx.casts and k < 0.3:
        e, t = R.choice(ctx.casts)
        n = tmpname('Q')
        c = on_object(ctx, n, t, d)
        if c:
            return '(if (%s := %s[%s]) then %s else %s)' % (n, t.name, e, c[0], lit())
    if ctx.opts and k < 0.55:
        e, t = R.choice(ctx.opts)
        n = tmpname('N')
        c = on_object(ctx, n, t, d)
        if c:
            return '(if (%s := %s?) then %s else %s)' % (n, e, c[0], lit())
    if ctx.maps and k < 0.75:
        e, t = R.choice(ctx.maps)
        if chance(0.3):
            return '%s.Length' % e
        n = tmpname('G')
        c = on_object(ctx, n, t, d)
        if c:
            return '(if (%s := %s["%s"]) then %s else %s)' % (n, e, R.choice('ab'), c[0], lit())
    if ctx.arrs:
        e, t = R.choice(ctx.arrs)
        if chance(0.3):
            return '%s.Length' % e
        n = tmpname('E')
        c = on_object(ctx, n, t, d)
        if c:
            return '(if (%s := %s[%s]) then %s else %s)' % (n, e, lit(0, 2), c[0], lit())
    return None


def iatom(ctx):
    k = R.random()
    if ctx.ints and k < 0.55:
        return R.choice(ctx.ints)
    if ctx.strs and k < 0.65:
        return '%s.Length' % R.choice(ctx.strs)
    return lit()


def iexpr(ctx, d=2):
    if d <= 0 or chance(0.3):
        return iatom(ctx)
    k = R.random()
    if k < 0.3:
        c = some_call(ctx, d)
        if c:
            return c[0] if c[1] == 'int' else '%s.Length' % c[0]
    if k < 0.38:
        v = via_object(ctx, d)
        if v:
            return v
    if k < 0.55:
        return '%s + %s' % (iexpr(ctx, d - 1), iexpr(ctx, d - 1))
    if k < 0.66:
        return '%s - %s' % (iexpr(ctx, d - 1), iatom(ctx))
    if k < 0.74:
        return '%s * %s' % (iatom(ctx), lit(1, 3))
    if k < 0.84:
        op = R.choice(['>', '<', '>=', '<=', '=', '<>'])
        return '(if (%s %s %s) then %s else %s)' % (iatom(ctx), op, iatom(ctx), iexpr(ctx, d - 1), iexpr(ctx, d - 1))
    dec = callable_now(ctx, decides=True)
    if dec and k < 0.92:
        p, r = R.choice(dec)
        t = call_text(p, r, ctx, d, bracket=True)
        if t:
            return '(if (%s) then %s else %s)' % (t, iexpr(ctx, d - 1), iatom(ctx))
    return '%s(%s, %s)' % (R.choice(['Max', 'Min']), iexpr(ctx, d - 1), iatom(ctx))


def sparts(ctx, d=2):
    """The inside of a string literal with interpolations (no quotes inside)."""
    parts = []
    for _ in range(R.randint(1, 3)):
        j = R.random()
        if j < 0.4:
            parts.append(R.choice(['a', '-', ' ', 'q', ':']))
        elif j < 0.75 or not ctx.strs:
            parts.append('{%s}' % iexpr(ctx, d - 1))
        else:
            parts.append('{%s}' % R.choice(ctx.strs))
    if chance(0.3):
        c = some_call(ctx, d, 'string')
        if c:
            parts.append('{%s}' % c[0])
    return ''.join(parts)


def sexpr(ctx, d=2):
    k = R.random()
    if ctx.strs and k < 0.3:
        return R.choice(ctx.strs)
    if k < 0.45:
        return '"%s"' % R.choice(['a', 'bb', 'ccc', 'x', 'yz', ''])
    return '"%s"' % sparts(ctx, d)


# ---------------------------------------------------------------- the generator

class Gen:
    def __init__(self):
        self.n = 0
        self.rank = 0
        self.ifaces = []
        self.classes = []
        self.trees = []
        self.out = []
        self.main = []
        self.pmain = []
        self.omain = []
        self.susp_main = False  # Main suspends (gen_existential's <suspends> Ev, #251)
        self.shared = set()     # method names with several roots
        self.fovered = set()    # fields an interface gives a new default
        self.phase = 'decl'     # 'decl' while generating bodies, 'main' after
        self.helpers = []
        self.extended_defaults = False

    def fresh(self, p):
        self.n += 1
        return '%s%d' % (p, self.n)

    def types(self):
        return self.ifaces + self.classes

    # --- calls

    def ambiguous(self, t, name):
        """Whether a plain call of name through type t could reach different code."""
        if t.is_iface:
            return False
        if self.phase != 'main':
            return True
        slots = [s for s in t.all_roots() if s.name == name]
        for d in t.subtree():
            if len(set(id(resolve(d, s)) for s in slots)) > 1:
                return True
        return False

    def callable(self, t, prefix):
        out, plain = [], set()
        for r in roots_of_type(t):
            if r.name in self.shared:
                if r.name not in plain and not self.ambiguous(t, r.name):
                    plain.add(r.name)
                    out.append((prefix, r))
                out.append((prefix + '(%s:)' % r.owner.name, r))
            else:
                out.append((prefix, r))
        return out

    def new_root(self, owner, decides=False):
        self.rank += 1
        name = self.fresh('D' if decides else 'M')
        n = R.choice([0, 0, 1, 1, 2]) if not decides else 1
        ptypes = []
        for _ in range(n):
            if not decides and chance(0.2):
                cands = list(self.ifaces) + ([] if owner.is_iface else self.classes)
                if owner not in cands:
                    cands.append(owner)
                ptypes.append(R.choice(cands))
            else:
                ptypes.append('int')
        ret = 'int' if decides or chance(0.75) else 'string'
        if not decides and chance(0.12):
            ups = [owner] + (owner.closure() if owner.is_iface else owner.chain() + owner.all_ifaces())
            ret = R.choice(ups)
        root = Root(name, ptypes, ret, self.rank, decides, owner)
        root.pnames = [self.fresh('P') for _ in range(n)]
        if not decides and chance(0.15):
            root.named = [self.fresh('Nm')]
        root.eff = pick_eff()
        return root

    def copy_root(self, r, owner):
        s = Root(r.name, list(r.ptypes), r.ret, r.rank, r.decides, owner)
        s.pnames = list(r.pnames)
        s.eff = r.eff
        return s

    # --- bodies

    def member_ctx(self, t, root, eff=ALL):
        """Context of a method body (or of a block: when root is None) of class or interface t,
        with the heap effects eff."""
        fs = fields_of_type(t)
        if 'r' not in eff:
            fs = [f for f in fs if not f.var]
        ctx = Ctx(ints=[f.name for f in fs if f.ty == 'int'],
                  strs=[f.name for f in fs if f.ty == 'string'],
                  maxrank=root.rank if root else 10 ** 9)
        ctx.allowed = eff
        ctx.callable = self.callable
        ctx.calls = self.callable(t, '')
        ctx.objs = [('Self', t)]
        if root:
            ctx.ints += root.named
            for p, ty in zip(root.pnames, root.ptypes):
                if ty == 'int':
                    ctx.ints.append(p)
                else:
                    ctx.objs.append((p, ty))
                    ctx.calls += self.callable(ty, p + '.')
        ctx.opts = [(f.name, f.ty[1]) for f in fs if isinstance(f.ty, tuple) and f.ty[0] == 'opt']
        ctx.arrs = [(f.name, f.ty[1]) for f in fs if isinstance(f.ty, tuple) and f.ty[0] == 'arr']
        ctx.maps = [(f.name, f.ty[1]) for f in fs if isinstance(f.ty, tuple) and f.ty[0] == 'map']
        for f in fs:
            if isobj(f.ty):
                ctx.objs.append((f.name, f.ty))
                ctx.calls += self.callable(f.ty, f.name + '.')
        for e, u in ctx.objs:
            for k in self.cast_targets(u):
                ctx.casts.append((e, k))
        return ctx

    def cast_targets(self, t):
        """Types a value of type t may be cast to without always failing."""
        out = [c for c in self.classes if c is not t and c.below(t)]
        out += [i for i in self.ifaces if i is not t and not below(t, i)
                and any(c.below(t) and c.below(i) for c in self.classes)]
        return out

    def body(self, t, root, sup, eff, ret=None):
        """Lines of a method body (after the signature's =); sup is a (super:) call or None."""
        ctx = self.member_ctx(t, root, eff)
        if sup and not chance(0.75):
            sup = None
        vars_ = [f.name for f in fields_of_type(t) if f.var and f.ty == 'int'] if 'w' in eff else []
        rw = 'r' in eff
        self.rw = rw
        if isobj(root.ret):
            cands = [e for e, u in ctx.objs if below(u, ret or root.ret)]
            e = R.choice(cands)
            if len(cands) > 1 and chance(0.6):
                e = 'if (%s %s %s) then %s else %s' % (iatom(ctx), R.choice(['>', '<']), iatom(ctx),
                                                     R.choice(cands), R.choice(cands))
            lines = [e]
            if vars_ and chance(0.3):
                lines = ['set %s = %s' % (R.choice(vars_), iexpr(ctx, 1))] + lines
            return self.with_defer(lines, root.name, vars_)
        if root.decides:
            lines = ['%s %s %s' % (root.pnames[0], R.choice(['>', '<', '>=', '<>']), iatom(ctx))]
            if sup:
                v = tmpname('L')
                lines.append('%s := %s' % (v, sup))
                ctx.ints.append(v)
            lines.append(iexpr(ctx))
            return self.with_defer(lines, root.name, vars_)
        if root.ret == 'string':
            e = sexpr(ctx)
            if sup:
                e = '"%s{%s}"' % (R.choice(['<', '+', '']), sup) if chance(0.5) else sup
            if vars_ and chance(0.25):
                return self.with_defer(['set %s %s 1' % (R.choice(vars_), '+=' if rw else '='), e],
                                       root.name, vars_)
            return self.with_defer([e], root.name, vars_)
        if sup:
            ctx.ints.append(sup)
        lines = []
        if chance(0.35):
            v = tmpname('L')
            lines.append('%s := %s' % (v, iexpr(ctx)))
            ctx.ints.append(v)
        if ctx.arrs and chance(0.3):
            e, k = R.choice(ctx.arrs)
            acc, it = tmpname('Acc'), tmpname('K')
            c = some_call(sub_ctx(ctx, k, it + '.'), 1, 'int')
            if c:
                lines.append('var %s:int = 0' % acc)
                lines.append('for (%s : %s) { set %s += %s }' % (it, e, acc, c[0]))
                ctx.ints.append(acc)
        if vars_ and chance(0.4):
            f = R.choice(vars_)
            lines.append('set %s %s %s' % (f, R.choice(['=', '+=', '-=', '+=']) if rw else '=', iexpr(ctx, 1)))
        if chance(0.12):
            lines += ['if (%s %s %s):' % (iatom(ctx), R.choice(['>', '<', '=']), iatom(ctx)),
                      '    return %s' % iexpr(ctx, 1)]
        if ctx.arrs and chance(0.3):
            e, k = R.choice(ctx.arrs)
            it = tmpname('K')
            c = some_call(sub_ctx(ctx, k, it + '.'), 1, 'int')
            if c:
                lines += ['for (%s : %s):' % (it, e),
                          '    if (%s %s %s):' % (c[0], R.choice(['>', '<', '>=']), iatom(ctx)),
                          '        return %s' % c[0]]
        e = iexpr(ctx)
        if sup and sup not in e and chance(0.8):
            e = '%s + %s' % (sup, e)
        lines.append(e)
        return self.with_defer(lines, root.name, vars_)

    def with_defer(self, lines, what, vars_):
        if not chance(0.15):
            return lines
        dl = ['defer:']
        if vars_ and chance(0.5):
            dl.append('    set %s %s %s' % (R.choice(vars_), '+=' if self.rw else '=', lit(1, 3)))
        else:
            dl.append('    Print("defer %s")' % what)
        at = R.choice([k for k, l in enumerate(lines) if not l.startswith(' ')])
        return lines[:at] + dl + lines[at:]

    def super_call(self, t, root, eff=ALL):
        ctx = self.member_ctx(t, root, eff)
        a = args_text(root, ctx, 1)
        if a is None:
            return None
        o, c = ('[', ']') if root.decides else ('(', ')')
        return '(super:)%s%s%s%s' % (root.name, o, a, c)

    def emit_method(self, lines, t, root, override, superok, qual=None, final=False, eff=ALL, im=None):
        sup = self.super_call(t, root, eff) if superok else None
        ret = None
        if override and isobj(root.ret) and not t.is_iface:
            above = resolve(t, root, skip_own=True)
            base = above.ret if isinstance(above, Impl) and above.ret else None
            ret = base
            if t is not root.ret and below(t, root.ret) and (base is None or below(t, base)) and chance(0.5):
                ret = t
            if im is not None:
                im.ret = ret
        b = self.body(t, root, sup, eff, ret)
        # defaults of named parameters: the positional parameters, immutable int fields, literals
        dctx = Ctx(ints=[p for p, ty in zip(root.pnames, root.ptypes) if ty == 'int'] +
                   [f.name for f in fields_of_type(t) if f.ty == 'int' and not f.var])
        dctx.callable = None
        defaults = [iexpr(dctx, 1) for _ in root.named]
        sig = ('(%s:)' % qual.owner.name if qual else '') + root.sig(override, final, eff, ret, defaults)
        if len(b) == 1 and chance(0.6):
            lines.append('    %s = %s' % (sig, b[0]))
        else:
            lines.append('    %s =' % sig)
            for l in b:
                lines.append('        ' + l)

    def field_default(self, ty):
        if isinstance(ty, tuple):
            return {'opt': 'false', 'arr': 'array{}', 'map': 'map{}'}[ty[0]]
        if ty == 'int':
            if self.helpers and chance(0.2):
                self.extended_defaults = True
                return '%s(%s)' % (R.choice(self.helpers), lit())
            return lit(0, 20)
        return '"%s"' % R.choice(['red', 'blue', 'n', 'ok', ''])

    def gen_field(self, owner):
        k = R.random()
        objtys = [t for t in self.types() if t is not owner] + [owner]
        earlier = [c for c in self.classes if c is not owner and not c.abstract and not owner.is_iface]
        if k < 0.05 and earlier:
            ty = R.choice(earlier)
            f = Field(self.fresh('B'), ty, chance(0.5), self.construct_plain(ty), owner)
            f.constructs = True
            return f
        if k < 0.14:
            ty = (R.choice(['opt', 'opt', 'arr', 'map']), R.choice(objtys))
            return Field(self.fresh({'opt': 'O', 'arr': 'A', 'map': 'T'}[ty[0]]), ty, True,
                         self.field_default(ty), owner)
        ty = 'int' if k < 0.75 else 'string'
        var = ty == 'int' and chance(0.35)
        default = None if (not var and chance(0.3)) else self.field_default(ty)
        return Field(self.fresh('F' if ty == 'int' else 'S'), ty, var, default, owner)

    def field_line(self, f):
        s = '    %s%s:%s' % ('var ' if f.var else '', f.name, f.tytext())
        if f.default is not None:
            s += ' = %s' % f.default
        return s

    # --- interfaces

    def gen_ifaces(self):
        for _ in range(R.choice([0, 1, 1, 2, 2, 3, 3])):
            parents = [R.choice(self.ifaces)] if self.ifaces and chance(0.35) else []
            i = Iface(self.fresh('i'), parents)
            self.ifaces.append(i)
            for _ in range(R.choice([0, 0, 1, 2])):
                i.fields.append(self.gen_field(i))
            for _ in range(R.randint(1, 3)):
                r = self.new_root(i)
                i.roots.append(r)
                i.impls[r] = Impl(i, chance(0.5), eff=r.eff)
        # a method name shared by two unrelated interfaces
        if len(self.ifaces) >= 2 and chance(0.7):
            a, b = R.sample(self.ifaces, 2)
            unrelated = not a.below(b) and not b.below(a) and \
                not any(a in j.closure() and b in j.closure() for j in self.ifaces)
            rs = [r for r in a.roots if not r.decides and all(t == 'int' for t in r.ptypes) and not isobj(r.ret)
                  and not r.named]
            if unrelated and rs:
                r = R.choice(rs)
                s = self.copy_root(r, b)
                b.roots.append(s)
                b.impls[s] = Impl(b, chance(0.5), eff=s.eff)
                self.shared.add(r.name)

    def decide_iface(self, i):
        """An interface's overrides of its parents' methods and field defaults
        (before the classes): none, as an interface overrides nothing (the Book's
        tests, Interface.versetest: "Interfaces can not override anything"). The
        draws an override took are taken still, and their results dropped, so the
        random stream is the one it was."""
        i.pending = []
        i.fover = {}
        for p in i.parents:
            for r in roots_of_type(p):
                if r.name in self.shared or not chance(0.25):
                    continue
                narrow(meet([im.eff for j in p.closure() for x, im in j.impls.items() if x is r], r.eff))
            for f in fields_of_type(p):
                if scalar(f) and f.name not in self.fovered and chance(0.2):
                    self.fovered.add(f.name)
                    extended = self.extended_defaults
                    self.field_default(f.ty)
                    self.extended_defaults = extended

    def emit_iface(self, i):
        """An interface's text (after the classes, so that its bodies may cast Self to them)."""
        hdr = '%s := interface%s:' % (i.name, '(%s)' % ', '.join(p.name for p in i.parents) if i.parents else '')
        lines = [hdr]
        for f in i.fields:
            lines.append(self.field_line(f))
        for name, (f, dflt) in i.fover.items():
            lines.append('    %s%s<override>:%s = %s' % ('var ' if f.var else '', name, f.tytext(), dflt))
        for r in i.roots:
            if i.impls[r].abstract:
                lines.append('    ' + r.sig(defaults=[lit() for _ in r.named]))
            else:
                self.emit_method(lines, i, r, False, False, eff=r.eff)
        for r, superok, eff in i.pending:
            self.emit_method(lines, i, r, True, superok, eff=eff)
        return lines

    # --- classes

    def gen_class(self, parent, depth):
        nkids = 0
        if depth < 3:
            nkids = R.choice([0, 1, 1, 2, 2, 3]) if depth == 1 else R.choice([0, 0, 1, 2])
        abstract = nkids > 0 and chance(0.4)
        have = parent.all_ifaces() if parent else []
        mine = set(r.name for r in parent.all_roots()) if parent else set()
        ifs = [i for i in self.ifaces if i not in have and
               chance(0.6 if mine & set(r.name for r in i.roots) else (0.3 if parent else 0.45))]
        c = Cls(self.fresh('c'), parent, ifs, abstract)
        self.classes.append(c)
        if parent is None and chance(0.15):
            c.unique = True
        for _ in range(R.choice([0, 1, 1, 2, 3])):
            c.fields.append(self.gen_field(c))
        for f in [f for f in c.all_fields() if f.owner is not c]:
            if scalar(f) and chance(0.2):
                c.over[f.name] = self.field_default(f.ty)
        items = []   # (root, override, superok, qual, final)
        done = set()
        for r in c.all_roots():
            if r.name in done:
                continue
            if r.name in self.shared:
                done.add(r.name)
                self.shared_impls(c, r.name, items)
                continue
            above = resolve(c, r, skip_own=True)
            if isinstance(above, Impl) and above.final:
                continue
            need = (not abstract) and not good(above)
            inherited = [im.eff for a in c.chain()[1:] for x, im in a.impls.items() if x is r]
            added = [im.eff for i in c.all_ifaces() for x, im in i.impls.items() if x is r]
            need = need or any(not (e <= f) for e in inherited for f in added)
            if need or chance(0.35):
                im = Impl(c, False, eff=narrow(meet(name_effs(c, r.name), r.eff)), final=nkids == 0 and chance(0.1))
                c.impls[r] = im
                c.plain[r.name] = im
                items.append((r, True, good(above) and above.eff <= im.eff, None, im.final))
        # new roots
        for _ in range(R.choice([0, 1, 1, 2])):
            r = None
            if chance(0.3):
                # a class root named like a method of an interface the class does not have
                mine = [x.name for x in c.all_roots()]
                cands = [q for i in self.ifaces if i not in c.all_ifaces()
                         for q in i.roots if q.name not in mine
                         and not q.decides and all(t == 'int' for t in q.ptypes) and not isobj(q.ret)
                         and not q.named]
                if cands:
                    q = R.choice(cands)
                    r = self.copy_root(q, c)
                    r.eff = meet([im.eff for i in self.ifaces for x, im in i.impls.items() if x.name == q.name], q.eff)
                    self.shared.add(r.name)
            if r is None:
                r = self.new_root(c, decides=chance(0.12))
            c.roots.append(r)
            ab = abstract and chance(0.4)
            fin = (not ab) and nkids == 0 and chance(0.1) and r.name not in self.shared
            im = Impl(c, ab, fin, eff=r.eff)
            c.impls[r] = im
            c.plain[r.name] = im
            items.append((r, False, False, None, fin))
        R.shuffle(items)
        hdr_parents = ([parent.name] if parent else []) + [i.name for i in ifs]
        spec = ''
        if c.unique:
            spec += '<unique>'
        if abstract:
            spec += '<abstract>'
        if nkids == 0 and not abstract and chance(0.08):
            spec += '<final>'
            c.final = True
        lines = ['%s := class%s%s:' % (c.name, spec, '(%s)' % ', '.join(hdr_parents) if hdr_parents else '')]
        for f in c.fields:
            lines.append(self.field_line(f))
        for fname, d in c.over.items():
            f = [g for g in c.all_fields() if g.name == fname][0]
            lines.append('    %s%s<override>:%s = %s' % ('var ' if f.var else '', fname, f.tytext(), d))
        c.items = items
        c.lines = lines
        if len(lines) == 1 and not items:
            f = Field(self.fresh('F'), 'int', False, lit(), c)
            c.fields.append(f)
            lines.append(self.field_line(f))
        for _ in range(nkids):
            c.children.append(self.gen_class(c, depth + 1))
        return c

    def shared_impls(self, c, name, items):
        """Implementations in class c of the slots named name."""
        slots = [s for s in c.all_roots() if s.name == name]
        above = {s: resolve(c, s, skip_own=True) for s in slots}
        if any(isinstance(a, Impl) and a.final for a in above.values()):
            return
        needs = [s for s in slots if not good(above[s])] if not c.abstract else []
        from_chain = any(good(above[s]) and not above[s].owner.is_iface for s in slots)
        distinct = set(id(above[s]) for s in slots if good(above[s]))
        must = bool(needs) or (len(slots) >= 2 and not from_chain and len(distinct) >= 2)
        inherited = [im.eff for a in c.chain()[1:] for r, im in a.impls.items() if r.name == name]
        added = [im.eff for i in c.all_ifaces() for r, im in i.impls.items() if r.name == name]
        conflict = any(not (e <= f) for e in inherited for f in added)
        if not must and not conflict and not chance(0.45):
            return
        if len(slots) >= 2 and chance(0.65) and not conflict:
            qs = [s for s in slots if s in needs or chance(0.6)]
            if not qs:
                qs = [R.choice(slots)]
            for s in qs:
                im = Impl(c, False, qual=s, eff=narrow(meet(name_effs(c, name), s.eff)))
                c.impls[s] = im
                items.append((s, True, good(above[s]) and above[s].eff <= im.eff, s, False))
        else:
            im = Impl(c, False, eff=narrow(meet(name_effs(c, name), slots[0].eff)))
            for s in slots:
                c.impls[s] = im
            c.plain[name] = im
            same = len(set(id(above[s]) for s in slots)) == 1
            ok = same and good(above[slots[0]]) and above[slots[0]].eff <= im.eff
            items.append((slots[0], True, ok, None, False))

    def emit_class_bodies(self, c):
        for (r, override, superok, qual, final) in c.items:
            im = c.impls[r]
            if im.abstract:
                c.lines.append('    ' + r.sig(defaults=[lit() for _ in r.named]))
            else:
                self.emit_method(c.lines, c, r, override, superok, qual=qual, final=final, eff=im.eff, im=im)
        if chance(0.2):
            c.lines += self.class_block(c)
            c.has_block = True

    def class_block(self, c):
        ctx = self.member_ctx(c, None)
        lines = ['    block:']
        if chance(0.3):
            lines += ['        defer:', '            Print("block defer %s")' % c.name]
        vars_ = [f.name for f in c.all_fields() if f.var and f.ty == 'int']
        if vars_ and chance(0.5):
            lines.append('        set %s += %s' % (R.choice(vars_), iexpr(ctx, 1)))
        lines.append('        Print("block %s %s")' % (c.name, sparts(ctx, 1)))
        return lines

    # --- constructors

    SIGS = [[], ['int'], ['string'], ['int', 'int'], ['string', 'int'], ['int', 'string']]

    def gen_ctors(self):
        """Constructor families: one name, one class, overloads with disjoint parameters."""
        for c in self.classes:
            nfam = 0
            if chance(0.55):
                nfam = 2 if chance(0.15) else 1
            for _ in range(nfam):
                name = self.fresh('Mk%s_' % c.name)
                k = 1 if chance(0.65) else R.choice([2, 2, 3])
                sigs = R.sample(self.SIGS, k)
                fam = []
                for j, sig in enumerate(sigs):
                    fam.append(self.ctor(c, name, sig, fam, alone=(k == 1)))
                c.ctors += fam

    def ctor_call(self, k, ctx, delegate=False):
        args = [iexpr(ctx, 1) if t == 'int' else sexpr(ctx, 1) for t in k['ptypes']]
        for (n, t) in k['named']:
            if chance(0.5):
                args.append('?%s := %s' % (n, iexpr(ctx, 1) if t == 'int' else sexpr(ctx, 1)))
        o, cl = ('[', ']') if k['decides'] else ('(', ')')
        return '%s%s%s%s%s' % (k['name'], '<constructor>' if delegate else '', o, ', '.join(args), cl)

    def ctor_min_eff(self, c, delegate):
        """The heap effects a constructor of c has, or None when not modelled."""
        chain = c.chain()
        if any(a.has_block for a in chain):
            return None
        defaults = [f.default or '' for f in c.all_fields()] + [v for a in chain for v in a.over.values()] + \
            [dv for i in c.all_ifaces() for (_, dv) in getattr(i, 'fover', {}).values()]
        if any(h in d for h in self.helpers for d in defaults) or any(f.constructs for f in c.all_fields()):
            return None
        eff = c.construction_eff
        if delegate:
            if delegate['eff'] is None:
                return None
            eff = eff | delegate['eff']
        return eff

    def construction_eff(self, data):
        """Declare data budgets before making constructors with narrow effects.

        Parents precede children. Defaults using helpers/constructed objects
        and class blocks retain the conservative full budget; simple data
        preserves allocation-only and computes constructor coverage.
        """
        if data.is_iface:
            fields = fields_of_type(data)
            chain, ifaces, parents = [], data.closure(), data.parents
        else:
            fields, chain, ifaces = data.all_fields(), data.chain(), data.all_ifaces()
            parents = ([data.parent] if data.parent else []) + data.ifaces
        defaults = [f.default or '' for f in fields] + [v for a in chain for v in a.over.values()] + \
            [dv for i in ifaces for (_, dv) in getattr(i, 'fover', {}).values()]
        unknown = (any(a.has_block for a in chain) or any(f.constructs for f in fields) or
                   any(h in d for h in self.helpers for d in defaults))
        eff = ALL if unknown else (frozenset('a') if any(f.var for f in fields) or
                                   any(a.unique for a in chain) else frozenset())
        for parent in parents:
            eff |= parent.construction_eff
        return eff

    def ctor(self, c, name, ptypes, earlier, alone):
        named = [(self.fresh('Opt'), R.choice(['int', 'string']))] if alone and chance(0.2) else []
        decides = chance(0.12) and 'int' in ptypes
        ps = [(self.fresh('Arg'), t) for t in ptypes]
        ctx = Ctx(ints=[p for p, t in ps if t == 'int'] + [n for n, t in named if t == 'int'],
                  strs=[p for p, t in ps if t == 'string'] + [n for n, t in named if t == 'string'])
        params = ['%s:%s' % p for p in ps] + \
                 ['?%s:%s = %s' % (n, t, lit() if t == 'int' else '"d"') for n, t in named]
        items = []
        if chance(0.3):
            v = tmpname('K')
            items.append(['let:', '    %s := %s' % (v, iexpr(ctx, 1))])
            ctx.ints.append(v)
        if decides:
            p = [p for p, t in ps if t == 'int'][0]
            items.append(['let:', '    %s := %s > %s' % (tmpname('Ok'), p, lit(0, 3))])
        if chance(0.25):
            blk = ['block:']
            if chance(0.3):
                blk += ['    defer:', '        Print("ctor defer %s")' % name]
            blk.append('    Print("ctor %s %s")' % (c.name, sparts(ctx, 1)))
            items.append(blk)
        # delegate to an earlier overload of the family, or to a constructor of a class above
        own = [k for k in earlier if not k['decides'] or decides]
        ups = [a for a in c.chain()[1:] if [k for k in a.ctors if not k['decides'] or decides]]
        delegate, dcls = None, None
        if own and chance(0.35):
            delegate, dcls = R.choice(own), c
        elif ups and chance(0.7):
            dcls = ups[0] if chance(0.7) else R.choice(ups)
            delegate = R.choice([k for k in dcls.ctors if not k['decides'] or decides])
        dfields = set(f.name for f in dcls.all_fields()) if dcls else set()
        eff = self.ctor_min_eff(c, delegate)
        spec = '<decides>' if decides else ''
        if eff is not None and chance(0.5):
            if chance(0.3):
                eff = eff | frozenset(R.sample('rwa', R.randint(1, 3)))
            spec = spec + efftext(eff) if chance(0.5) else efftext(eff) + spec
            if eff == ALL:
                eff = None
        else:
            if chance(0.2):
                spec += '<transacts>'
            eff = None
        hdr = '%s<constructor>(%s)%s := %s' % (name, ', '.join(params), spec, c.name)
        sets = []
        for f in c.all_fields():
            if f.name in dfields:
                continue
            if not scalar(f):
                if chance(0.2):
                    sets.append(f)
                continue
            if not c.has_default(f) or chance(0.4):
                sets.append(f)
        R.shuffle(sets)
        for f in sets:
            if not scalar(f):
                e = f.default
            else:
                e = iexpr(ctx, 2) if f.ty == 'int' else sexpr(ctx, 1)
            items.append(['%s := %s' % (f.name, e)])
        if delegate:
            items.append([self.ctor_call(delegate, ctx, delegate=True)])
        form = R.random()
        flat = all(len(it) == 1 for it in items)
        if not items:
            if chance(0.5):
                lines = [hdr + '{}']
            else:
                lines = [hdr + ':', '    block:', '        Print("empty ctor")']
        elif flat and form < 0.25:
            lines = [hdr + ': ' + '; '.join(it[0] for it in items)]
        elif flat and form < 0.45:
            lines = [hdr + ' { ' + '; '.join(it[0] for it in items) + ' }']
        else:
            lines = [hdr + ':']
            for it in items:
                lines += ['    ' + l for l in it]
        return {'name': name, 'ptypes': ptypes, 'named': named, 'lines': lines, 'decides': decides,
                'eff': eff}

    # --- construction expressions

    def construct(self, c, ctx, allow_fail=False):
        """An expression constructing the concrete class c; (text, failable)."""
        ks = [k for k in c.ctors if allow_fail or not k['decides']]
        if ks and chance(0.6):
            k = R.choice(ks)
            return self.ctor_call(k, ctx), k['decides']
        sets = []
        for f in c.all_fields():
            if not scalar(f):
                continue
            if not c.has_default(f) or chance(0.3):
                e = iexpr(ctx, 1) if f.ty == 'int' else sexpr(ctx, 1)
                sets.append('%s := %s' % (f.name, e))
        R.shuffle(sets)
        return '%s{%s}' % (c.name, ', '.join(sets)), False

    def construct_plain(self, c):
        sets = []
        for f in c.all_fields():
            if not c.has_default(f):
                sets.append('%s := %s' % (f.name, lit() if f.ty == 'int' else '"z"'))
        return '%s{%s}' % (c.name, ', '.join(sets))

    # --- the stand-alone qualified module

    def gen_qualified(self):
        L, M = [], []
        qa, qb = self.fresh('qa'), self.fresh('qb')
        m = self.fresh('Qm')
        da, db = chance(0.5), chance(0.5)
        L.append('%s := interface:' % qa)
        L.append('    %s():int%s' % (m, (' = %s' % lit(1, 50)) if da else ''))
        other = None
        if chance(0.5):
            other = self.fresh('Qo')
            L.append('    %s():int = %s() * %s' % (other, m, lit(1, 3)))
        L.append('%s := interface:' % qb)
        L.append('    %s():int%s' % (m, (' = %s' % lit(1, 50)) if db else ''))
        qs = self.fresh('qs')
        vfield = self.fresh('QV')
        L.append('%s := class(%s, %s):' % ((qs, qa, qb) if chance(0.5) else (qs, qb, qa)))
        L.append('    var %s:int = %s' % (vfield, lit(0, 9)))
        give_a = (not da) or chance(0.7)
        give_b = (not db) or chance(0.7) or not give_a
        if give_a:
            e = '%s + %s' % (vfield, lit(100, 199))
            if da and chance(0.5):
                e += ' + (super:)%s()' % m
            L.append('    (%s:)%s<override>():int = %s' % (qa, m, e))
        if give_b:
            e = '%s + %s' % (vfield, lit(200, 299))
            if db and chance(0.5):
                e += ' + (super:)%s()' % m
            L.append('    (%s:)%s<override>():int =' % (qb, m))
            L.append('        set %s += 1' % vfield)
            L.append('        %s' % e)
        use = self.fresh('QUse')
        L.append('    %s():int = (%s:)%s() * 1000 + (%s:)%s()' % (use, qa, m, qb, m))
        qd = None
        if chance(0.6):
            qd = self.fresh('qd')
            L.append('%s := class(%s):' % (qd, qs))
            which = R.choice([qa, qb])
            e = lit(1000, 1999)
            if chance(0.7):
                e += ' + (super:)%s()' % m
            L.append('    (%s:)%s<override>():int = %s' % (which, m, e))
        qp = self.fresh('qp')
        L.append('%s := class(%s, %s):' % (qp, qa, qb))
        L.append('    %s<override>():int = %s' % (m, lit(3000, 3999)))
        qe = qf = None
        if chance(0.5):
            qe, qf = self.fresh('qe'), self.fresh('qf')
            L.append('%s := class(%s):' % (qe, qa))
            L.append('    %s<override>():int = %s' % (m, lit(4000, 4999)))
            L.append('%s := class(%s, %s):' % (qf, qe, qb))
            L.append('    (%s:)%s<override>():int = %s' % (qb, m, lit(5000, 5999)))
        self.out += L
        x = tmpname('Q')
        M.append('%s := %s{}' % (x, qs))
        M.append('Print("qs {%s.(%s:)%s()} {%s.(%s:)%s()} {%s.%s()}")' % (x, qa, m, x, qb, m, x, use))
        if other:
            M.append('Print("other {%s.%s()}")' % (x, other))
        M.append('set %s.%s += %s' % (x, vfield, lit(1, 5)))
        As = [x, '%s{}' % qp] + (['%s{}' % qd] if qd else []) + (['%s{}' % qe, '%s{}' % qf] if qe else [])
        Bs = [x, '%s{}' % qp] + (['%s{}' % qd] if qd else []) + (['%s{}' % qf] if qe else [])
        R.shuffle(As)
        R.shuffle(Bs)
        a, b = tmpname('QA'), tmpname('QB')
        M.append('%s:[]%s = array{%s}' % (a, qa, ', '.join(As)))
        M.append('%s:[]%s = array{%s}' % (b, qb, ', '.join(Bs)))
        y = tmpname('X')
        M.append('for (%s : %s) { Print("qa {%s.%s()}") }' % (y, a, y, m))
        y = tmpname('X')
        M.append('for (%s : %s) { Print("qb {%s.%s()} {%s.(%s:)%s()}") }' % (y, b, y, m, y, qb, m))
        y, z = tmpname('X'), tmpname('Y')
        M.append('for (%s : %s, %s := %s[%s]) { Print("cast {%s.%s()}") }' % (y, a, z, qs, y, z, use))
        if qd:
            M.append('Print("qd {%s{}.(%s:)%s()} {%s{}.(%s:)%s()}")' % (qd, qa, m, qd, qb, m))
        M.append('Print("qp {%s{}.%s()} {%s{}.(%s:)%s()}")' % (qp, m, qp, qb, m))
        if qe:
            M.append('Print("qe {%s{}.%s()} {%s{}.(%s:)%s()}")' % (qe, m, qf, qa, m))
        self.main += M

    # --- a field two parametric interfaces declare (#205)

    def gen_shared_field(self):
        """A var field declared as the type parameter by one interface and as
        int by another, in classes that fix the parameter to int (listed in
        either order), and in a generic class below the second whose subclass
        also implements the first: read and set through each type."""
        L, M = [], []
        sx, sy, sb = self.fresh('sx'), self.fresh('sy'), self.fresh('sb')
        f = self.fresh('SF')
        L.append('%s(t:type) := interface:' % sx)
        L.append('    var %s:t' % f)
        L.append('%s(t:type) := interface:' % sy)
        L.append('    var %s:int' % f)
        sc = self.fresh('sc')
        L.append('%s := class(%s):' % (sc, '%s(int), %s(int)' % ((sx, sy) if chance(0.5) else (sy, sx))))
        L.append('    %s:int = %s' % (self.fresh('SG'), lit()))
        L.append('%s(t:type) := class(%s(t)):' % (sb, sy))
        L.append('    %s:int = %s' % (self.fresh('SK'), lit()))
        sd = self.fresh('sd')
        L.append('%s := class(%s(int), %s(int)):' % (sd, sb, sx))
        L.append('    %s:int = %s' % (self.fresh('SL'), lit()))
        # (classes that fix t and take the field from sy alone)
        sf = sg = None
        if chance(0.5):
            sf = self.fresh('sf')
            L.append('%s := class(%s(int)):' % (sf, sy))
            L.append('    %s:int = %s' % (self.fresh('SJ'), lit()))
        if chance(0.5):
            sg = self.fresh('sg')
            L.append('%s := class(%s(int)):' % (sg, sb))
            L.append('    %s:int = %s' % (self.fresh('SM'), lit()))
        gx, gy, gb = self.fresh('SFx'), self.fresh('SFy'), self.fresh('SFb')
        L.append('%s(N:%s(t) where t:type):t = N.%s' % (gx, sx, f))
        L.append('%s(N:%s(t) where t:type):int = N.%s' % (gy, sy, f))
        L.append('%s(N:%s(t) where t:type):int = N.%s' % (gb, sb, f))
        tx, ty, tb = self.fresh('SSx'), self.fresh('SSy'), self.fresh('SSb')
        for (fn, iface, vt) in ((tx, sx, 't'), (ty, sy, 'int'), (tb, sb, 'int')):
            L.append('%s(N:%s(t), V:%s where t:type):void =' % (fn, iface, vt))
            L.append('    set N.%s = V' % f)
        self.out += L
        c, d = tmpname('SC'), tmpname('SD')
        M.append('%s := %s{%s := %s}' % (c, sc, f, lit()))
        M.append('%s := %s{%s := %s}' % (d, sd, f, lit()))
        ys, bs = [c, d], [d]
        if sf:
            v = tmpname('SFv')
            M.append('%s := %s{%s := %s}' % (v, sf, f, lit()))
            ys.append(v)
        if sg:
            v = tmpname('SG')
            M.append('%s := %s{%s := %s}' % (v, sg, f, lit()))
            ys.append(v)
            bs.append(v)
        for _ in range(R.randint(2, 6)):
            k = R.randrange(5)
            o = R.choice([c, d])
            if k == 4:
                o = R.choice(ys)
                b = R.choice(bs)
                M.append('%s(%s, %s)' % (ty, o, lit(10, 99)))
                M.append('Print("sy {%s(%s)} {%s(%s)}")' % (gy, o, gb, b))
                continue
            if k == 0:
                M.append('Print("sf {%s(%s)} {%s(%s)} {%s.%s}")' % (gx, o, gy, o, o, f))
            elif k == 1:
                M.append('Print("sb {%s(%s)} {%s(%s{%s := %s})}")' % (gb, d, gb, sb + '(string)', f, lit()))
            elif k == 2:
                fn = R.choice([tx, ty] + ([tb] if o == d else []))
                M.append('%s(%s, %s)' % (fn, o, lit(10, 99)))
            else:
                M.append('set %s.%s = %s' % (o, f, lit(100, 199)))
        M.append('Print("sf end {%s.%s} {%s.%s}")' % (c, f, d, f))
    # --- function values (#210)

    def gen_fn_values(self):
        """Top-level functions passed, stored and called as values: a generic
        map over a function type (called under the refinement), a <decides>
        function type that also takes plain functions, a function-typed
        field, an array and an option of functions."""
        L, M = [], []
        fs = []
        for _ in range(R.randint(2, 4)):
            f = self.fresh('Fv')
            k = R.randrange(3)
            if k == 0:
                L.append('%s(X:int):int = X * %s + %s' % (f, lit(1, 3), lit()))
            elif k == 1:
                L.append('%s(X:int):int = X - %s' % (f, lit()))
            else:
                L.append('%s(X:int):int = if (X > %s) then X else %s' % (f, lit(), lit()))
            fs.append(f)
        d = self.fresh('Fd')
        L.append('%s(X:int)<decides>:int =' % d)
        L.append('    X > %s' % lit(0, 5))
        L.append('    X + 100')
        sh = self.fresh('Fshow')
        L.append('%s(X:int):string = "s{X}"' % sh)
        mp, fl, tw = self.fresh('FMap'), self.fresh('FKeep'), self.fresh('FTwice')
        L.append('%s(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }' % mp)
        L.append('%s(Xs:[]int, F:type{_(:int)<decides>:int}):[]int = for (X : Xs, Y := F[X]) { Y }' % fl)
        L.append('%s(F:int->int, X:int):int = F(F(X))' % tw)
        pu = self.fresh('Fpure')
        L.append('%s(X:int)<computes>:int = X + %s' % (pu, lit()))
        # (methods as values: an override through the base class, a generic
        # class's method, a <decides> method)
        fb, fs2, fbx, fpk = self.fresh('fbase'), self.fresh('fsub'), self.fresh('fbox'), self.fresh('fpick')
        L.append('%s := class:' % fb)
        L.append('    Val():int = %s' % lit())
        L.append('%s := class(%s):' % (fs2, fb))
        L.append('    Val<override>():int = %s' % lit(10, 19))
        L.append('%s(t:type) := class:' % fbx)
        L.append('    V:t')
        L.append('    Get():t = V')
        L.append('%s := class:' % fpk)
        L.append('    Min:int')
        L.append('    Keep(X:int)<decides>:int =')
        L.append('        X >= Min')
        L.append('        X')
        # (#214: by variance, and a generic function at closed types)
        fid, fdesc, fon = self.fresh('FId'), self.fresh('FDesc'), self.fresh('FOnSub')
        L.append('%s(X:t where t:type):t = X' % fid)
        L.append('%s(B:%s):int = B.Val() + %s' % (fdesc, fb, lit()))
        L.append('%s(F:type{_(:%s):int}, B:%s):int = F(B)' % (fon, fs2, fs2))
        fcnt = self.fresh('FCnt')
        L.append('%s():int = %s' % (fcnt, lit()))
        fr, fg = self.fresh('FRun0'), self.fresh('FGet')
        L.append('%s(F:type{_():int}):int = F()' % fr)
        L.append('%s(F:type{_():t} where t:type):t = F()' % fg)
        hc = self.fresh('fholder')
        L.append('%s := class:' % hc)
        L.append('    var Op:int->int = %s' % R.choice(fs))
        L.append('    Run(X:int):int = Op(X)')
        self.out += L
        xs = 'array{%s}' % ', '.join(lit() for _ in range(R.randint(1, 4)))
        for _ in range(R.randint(2, 6)):
            k = R.randrange(11)
            if k == 10:
                M.append('Print("fva {%s(%s, %s{})} {%s(%s, %s)}")' % (fon, fdesc, fs2, tw, fid, lit()))
                v = tmpname('FW')
                M.append('%s:type{_():rational} = %s' % (v, fcnt))
                M.append('Print("fw {Floor(%s())}")' % v)
                continue
            if k == 9:
                b = tmpname('FB')
                M.append('%s:%s = %s{}' % (b, fb, R.choice([fb, fs2])))
                M.append('Print("fov {%s(%s.Val)}")' % (fr, b))
                M.append('Print("fgb {%s(%s(int){V := %s}.Get)} {%s(%s(string){V := \"g\"}.Get)}")' % (fg, fbx, lit(), fg, fbx))
                y = tmpname('FY')
                M.append('for (%s : %s(%s, %s{Min := %s}.Keep)) { Print("fpk {%s}") }' % (y, fl, xs, fpk, lit(0, 6), y))
                continue
            if k == 6:
                # (effect subtyping between variables)
                a, b, c = tmpname('FP'), tmpname('FR'), tmpname('FQ')
                M.append('%s:type{_(:int)<computes>:int} = %s' % (a, pu))
                M.append('%s:type{_(:int)<reads>:int} = %s' % (b, a))
                M.append('%s:type{_(:int)<decides>:int} = %s' % (c, b))
                M.append('if (V := %s[%s]) then Print("fe {%s(1)} {V}")' % (c, lit(), a))
                continue
            if k == 7:
                # (a var holding a function, rolled back)
                v = tmpname('FV')
                M.append('var %s:int->int = %s' % (v, R.choice(fs)))
                M.append('if (set %s = %s, %s[%s]) then Print("fs") else Print("fr")' % (v, R.choice(fs + [pu]), d, lit(0, 6)))
                M.append('Print("fv {%s(%s)}")' % (v, lit()))
                continue
            if k == 8:
                # (options and maps of functions, joined whatever the order)
                o, m = tmpname('FO'), tmpname('FM')
                M.append('%s:?(int->int) = option{%s}' % (o, R.choice(fs)))
                M.append('if (G := %s?) then Print("fo {G(%s)}")' % (o, lit()))
                ks = R.sample(fs + [pu], 2)
                M.append('%s := map{1 => %s, 2 => %s}' % (m, ks[0], ks[1]))
                M.append('if (G := %s[%s]) then Print("fq {G(%s)}")' % (m, R.choice(['1', '2']), lit()))
                continue
            if k == 0:
                y = tmpname('FY')
                M.append('for (%s : %s(%s, %s)) { Print("fm {%s}") }' % (y, mp, xs, R.choice(fs), y))
            elif k == 1:
                y = tmpname('FY')
                M.append('for (%s : %s(%s, %s)) { Print(%s) }' % (y, mp, xs, sh, y))
            elif k == 2:
                y = tmpname('FY')
                M.append('for (%s : %s(%s, %s)) { Print("fk {%s}") }' % (y, fl, xs, R.choice([d] + fs), y))
            elif k == 3:
                M.append('Print("ft {%s(%s, %s)}")' % (tw, R.choice(fs), lit()))
            elif k == 4:
                h = tmpname('FH')
                M.append('%s := %s{}' % (h, hc))
                M.append('set %s.Op = %s' % (h, R.choice(fs)))
                M.append('Print("fh {%s.Run(%s)} {%s.Op(%s)}")' % (h, lit(), h, lit()))
                # (a method as a value, holding its receiver)
                M.append('Print("fmv {%s(%s.Run, %s)}")' % (tw, h, lit()))
            else:
                a, y = tmpname('FA'), tmpname('FY')
                M.append('%s:[](int->int) = array{%s}' % (a, ', '.join(R.sample(fs, min(len(fs), 2)))))
                M.append('for (%s : %s) { Print("fa {%s(%s)}") }' % (y, a, y, lit()))
        self.main += M

    # --- the parametric hierarchy

    def gen_parametric(self):
        L, M = [], []
        g = self.fresh('pg') if chance(0.5) else None
        pb, pr, pr2, pf, pw = (self.fresh(x) for x in ['pb', 'pr', 'prr', 'pf', 'pw'])
        V, N, S, X, A = (self.fresh(x) for x in ['PV', 'PN', 'PS', 'PX', 'PA'])
        get, cnt, desc, pick, score, both, twice, gtag = (
            self.fresh(x) for x in ['Get', 'Cnt', 'Desc', 'Pick', 'Score', 'Both', 'Twice', 'GTag'])
        abstract = chance(0.4)
        have_pr2 = chance(0.5)
        have_pf = not abstract or chance(0.3)
        have_pw = (not abstract or chance(0.3)) and not g
        if g:
            L.append('%s(t:type) := interface:' % g)
            L.append('    %s():t' % get)
            L.append('    %s():string = "pg"' % gtag)
        L.append('%s(t:type) := class%s%s:' % (pb, '<abstract>' if abstract else '', '(%s(t))' % g if g else ''))
        L.append('    %s:t' % V)
        L.append('    var %s:int = %s' % (N, lit(0, 5)))
        L.append('    %s:string = "%s"' % (S, R.choice(['s', 'pb', ''])))
        L.append('    %s%s():t = %s' % (get, '<override>' if g else '', V))
        L.append('    %s():int =' % cnt)
        L.append('        set %s += %s' % (N, lit(1, 3)))
        L.append('        %s' % N)
        L.append('    %s():string = "pb {%s} {%s}"' % (desc, N, S))
        L.append('    %s(Y:t):t = if (%s > %s) then Y else %s' % (pick, N, lit(2, 6), V))
        L.append('    %s(O:u where u:type):tuple(t, u, int) = (%s, O, %s)' % (both + 'G', V, N))
        if abstract:
            L.append('    %s():int' % score)
        else:
            L.append('    %s():int = %s + %s' % (score, N, lit()))
        if g and chance(0.5):
            L.append('    %s<override>():string = "pb-g {(super:)%s()}"' % (gtag, gtag))
        L.append('%s(t:type) := class(%s(t)):' % (pr, pb))
        L.append('    %s:t' % X)
        L.append('    %s<override>():string = "pr {%s()} {(super:)%s()}"' % (desc, score, desc))
        L.append('    %s<override>():int = %s%s' % (score, lit(10, 20), '' if abstract else ' + (super:)%s()' % score))
        if chance(0.5):
            L.append('    %s<override>():t = %s' % (get, X))
        if chance(0.5):
            L.append('    %s<override>(Y:t):t = (super:)%s(%s)' % (pick, pick, X))
        if chance(0.6):
            L.append('    %s<override>(O:u where u:type):tuple(t, u, int) =' % (both + 'G'))
            L.append('        set %s += %s' % (N, lit(1, 9)))
            L.append('        (super:)%s(O)' % (both + 'G'))
        if have_pr2:
            L.append('%s(u:type) := class(%s(u)):' % (pr2, pr))
            L.append('    %s<override>():int = %s * (super:)%s()' % (score, lit(2, 3), score))
            L.append('    %s<override>():int =' % cnt)
            L.append('        set %s += 100' % N)
            L.append('        (super:)%s()' % cnt)
        if have_pf:
            L.append('%s := class%s(%s(int)):' % (pf, '<abstract>' if abstract else '', pb))
            L.append('    %s():int = %s * 2 + %s' % (twice, V, N))
        if have_pw:
            L.append('%s(a:type, b:type) := class%s(%s(b)):' % (pw, '<abstract>' if abstract else '', pb))
            L.append('    %s:a' % A)
            L.append('    %s():tuple(b, a) = (%s, %s)' % (both, V, A))
        mb, mr, mr2, mf, mfx, mw, mo = (self.fresh(x) for x in
                                        ['MkPb', 'MkPr', 'MkPrr', 'MkPf', 'MkFix', 'MkPw', 'MkOpt'])
        L.append('%s<constructor>(Y:t where t:type) := %s(t):' % (mb, pb))
        L.append('    %s := Y' % V)
        if chance(0.5):
            L.append('    %s := %s' % (N, lit(5, 9)))
        L.append('%s<constructor>(Y:t, Z:t where t:type) := %s(t):' % (mr, pr))
        L.append('    %s := Z' % X)
        L.append('    %s<constructor>(Y)' % mb)
        if have_pr2:
            L.append('%s<constructor>(Y:u where u:type) := %s(u):' % (mr2, pr2))
            L.append('    %s := "prr"' % S)
            L.append('    %s<constructor>(Y, Y)' % mr)
        if not abstract:
            L.append('%s<constructor>(Y:int) := %s(int):' % (mfx, pb))
            L.append('    %s := Y * %s' % (V, lit(2, 4)))
            L.append('%s<constructor>(Y:t where t:type) := %s(?t):' % (mo, pb))
            L.append('    %s := option{Y}' % V)
        if have_pf and not abstract:
            L.append('%s<constructor>(Y:int) := %s:' % (mf, pf))
            L.append('    %s<constructor>(Y + %s)' % (mb, lit(1, 5)))
        if have_pw and not abstract:
            L.append('%s<constructor>(Y:a, Z:b where a:type, b:type) := %s(a, b):' % (mw, pw))
            L.append('    %s := Y' % A)
            L.append('    %s<constructor>(Z)' % mb)
        alls, tot = self.fresh('PAll'), self.fresh('PTot')
        et = g or pb
        L.append('%s(Xs:[]%s(t) where t:type):[]t = for (X : Xs) { X.%s() }' % (alls, et, get))
        L.append('%s(Xs:[]%s(t) where t:type):int =' % (tot, pb))
        L.append('    var T:int = 0')
        L.append('    for (X : Xs) { set T += X.%s() + X.%s() }' % (score, cnt))
        L.append('    T')
        self.out += L

        def items(ty):
            lv = lit() if ty == 'int' else '"%s"' % R.choice(['a', 'b', 'c'])
            lv2 = lit() if ty == 'int' else '"%s"' % R.choice(['d', 'e'])
            out = ['%s(%s, %s)' % (mr, lv, lv2), '%s(%s){%s := %s, %s := %s}' % (pr, ty, V, lv, X, lv2)]
            if have_pr2:
                out.append('%s(%s)' % (mr2, lv))
            if not abstract:
                out += ['%s(%s)' % (mb, lv), '%s(%s){%s := %s}' % (pb, ty, V, lv)]
                if ty == 'int':
                    out.append('%s(%s)' % (mfx, lv))
                    if have_pf:
                        out += ['%s(%s)' % (mf, lv), '%s{%s := %s}' % (pf, V, lv)]
                if have_pw:
                    out += ['%s("w", %s)' % (mw, lv), '%s(int, %s){%s := %s, %s := 1}' % (pw, ty, V, lv, A)]
            R.shuffle(out)
            return out[:R.randint(2, len(out))]
        for ty in (['int', 'string'] if chance(0.5) else ['int']):
            xs = tmpname('Ps')
            M.append('%s:[]%s(%s) = array{%s}' % (xs, pb, ty, ', '.join(items(ty))))
            x = tmpname('X')
            M.append('for (%s : %s) { Print("{%s.%s()} {%s.%s()} {%s.%s()} {%s.%s(%s.%s)}") }' %
                     (x, xs, x, get, x, desc, x, cnt, x, pick, x, V))
            M.append('Print("tot {%s(%s)}")' % (tot, xs))
            x = tmpname('X')
            M.append('for (%s : %s) { Print("gen {%s.%s("o")(1)} {%s.%s(%s)(2)}") }' %
                     (x, xs, x, both + 'G', x, both + 'G', lit()))
            x = tmpname('X')
            M.append('for (%s : %s(%s)) { Print("all {%s}") }' % (x, alls, xs, x))
            x, y = tmpname('X'), tmpname('Y')
            M.append('for (%s : %s, %s := %s[%s]) { Print("pr {%s.%s} {%s.%s()}") }' % (x, xs, y, pr, x, y, X, y, score))
            if have_pr2:
                x, y = tmpname('X'), tmpname('Y')
                M.append('for (%s : %s):' % (x, xs))
                M.append('    if (%s := %s[%s]) then Print("prr {%s.%s()}") else Print("not prr")' % (y, pr2, x, y, cnt))
            if ty == 'int' and have_pf and not abstract:
                x, y = tmpname('X'), tmpname('Y')
                M.append('for (%s : %s, %s := %s[%s]) { Print("pf {%s.%s()}") }' % (x, xs, y, pf, x, y, twice))
            if g:
                gs = tmpname('Gs')
                M.append('%s:[]%s(%s) = %s' % (gs, g, ty, xs))
                x = tmpname('X')
                M.append('for (%s : %s) { Print("g {%s.%s()} {%s.%s()}") }' % (x, gs, x, get, x, gtag))
                x = tmpname('X')
                M.append('for (%s : %s(%s)) { Print("gall {%s}") }' % (x, alls, gs, x))
                x, y = tmpname('X'), tmpname('Y')
                M.append('for (%s : %s, %s := %s[%s]) { Print("g->pr {%s.%s}") }' % (x, gs, y, pr, x, y, X))
        if have_pw and not abstract:
            w = tmpname('W')
            M.append('%s := %s(%s, "z")' % (w, mw, lit()))
            M.append('Print("pw {%s.%s()(0)} {%s.%s()(1)} {%s.%s}")' % (w, both, w, both, w, A))
        if not abstract:
            o, z = tmpname('Op'), tmpname('Z')
            M.append('%s := %s(%s)' % (o, mo, lit()))
            M.append('if (%s := %s.%s()?) then Print("opt {%s}")' % (z, o, get, z))
        # a parametric class holding hierarchy objects
        conc = [c for c in self.classes if not c.abstract]
        if conc:
            c = R.choice(conc)
            e, _ = self.construct(c, Ctx())
            b = tmpname('Bo')
            M.append('%s := %s(%s, %s)' % (b, mr, e, e))
            sub = Ctx()
            sub.calls = self.callable(c, '%s.%s().' % (b, get))
            ct = some_call(sub, 1)
            if ct:
                M.append('Print("held {%s} {%s.%s()}")' % (ct[0], b, desc))
        self.pmain = M

    # --- classes that repeat or relate type arguments (#209)

    def gen_relational(self):
        """A two-parameter class q2(t, u) and subclasses whose pins relate its
        type arguments: qd(t) := class(q2(t, t)) repeats them, qo(t) and qn(t)
        fix the first to ?t and []t, qi := class(qd(int)) fixes both below
        qd. Each overrides some of q2's methods; generic functions over
        q2(t, u) and q2(t, t) call them, so dispatch is typed under the
        refinement that unifies the receiver's type arguments with the pins."""
        L, M = [], []
        q2, qd, qo, qn, qi = (self.fresh(x) for x in ['q2', 'qd', 'qo', 'qn', 'qi'])
        qp, qs, qw = (self.fresh(x) for x in ['qp', 'qs', 'qw'])
        C = self.fresh('QC')
        A, B, N = (self.fresh(x) for x in ['QA', 'QB', 'QN'])
        g1, g2, tag, mix, pk = (self.fresh(x) for x in ['G1', 'G2', 'QTag', 'Mix', 'Pk'])
        fs, ss, sw = (self.fresh(x) for x in ['Firsts', 'Sames', 'Swaps'])
        k = lit(1, 4)
        L.append('%s(t:type, u:type) := class:' % q2)
        L.append('    %s:t' % A)
        L.append('    %s:u' % B)
        L.append('    var %s:int = %s' % (N, lit(0, 3)))
        L.append('    %s():t = %s' % (g1, A))
        L.append('    %s():u = %s' % (g2, B))
        L.append('    %s():string = "q2"' % tag)
        L.append('    %s(X:t, Y:u):tuple(t, u) = (X, Y)' % mix)
        L.append('    %s(X:t):t =' % pk)
        L.append('        set %s += 1' % N)
        L.append('        if (%s > %s) then X else %s' % (N, k, A))
        have_qo, have_qn, have_qi = chance(0.7), chance(0.5), chance(0.6)
        have_qp, have_qw = chance(0.5), chance(0.5)
        L.append('%s(t:type) := class(%s(t, t)):' % (qd, q2))
        if chance(0.7):
            L.append('    %s<override>():t = %s' % (g1, B))
        if chance(0.5):
            L.append('    %s<override>():t = %s' % (g2, A))
        L.append('    %s<override>():string = "qd"' % tag)
        if chance(0.6):
            L.append('    %s<override>(X:t, Y:t):tuple(t, t) = (Y, X)' % mix)
        if chance(0.5):
            L.append('    %s<override>(X:t):t = if (%s > 0) then %s else (super:)%s(X)' % (pk, N, B, pk))
        if have_qi:
            L.append('%s := class(%s(int)):' % (qi, qd))
            L.append('    %s<override>():int = %s + %s * %s' % (g1, A, B, lit(2, 5)))
            L.append('    %s<override>():string = "qi {(super:)%s()}"' % (tag, tag))
            if chance(0.5):
                L.append('    %s<override>(X:int):int = X + %s' % (pk, A))
        if have_qo:
            L.append('%s(t:type) := class(%s(?t, t)):' % (qo, q2))
            L.append('    %s<override>():?t = %s' % (
                g1, R.choice(['option{%s}' % B, 'if (%s > 1) then option{%s} else %s' % (N, B, A)])))
            L.append('    %s<override>():string = "qo"' % tag)
            if chance(0.5):
                L.append('    %s<override>(X:?t, Y:t):tuple(?t, t) = (option{Y}, Y)' % mix)
        if have_qn:
            L.append('%s(t:type) := class(%s([]t, t)):' % (qn, q2))
            L.append('    %s<override>():[]t = array{%s, %s}' % (g1, B, B))
            L.append('    %s<override>():string = "qn"' % tag)
        if have_qp:
            # a class below a closed fixer that wraps its own parameter (it
            # takes the fixer's pins where its own would point past them)
            L.append('%s(u:type) := class(%s(int, u)):' % (qp, q2))
            L.append('    %s<override>():string = "qp {%s}"' % (tag, A))
            L.append('%s(w:type) := class(%s([]w)):' % (qs, qp))
            L.append('    %s:w' % C)
            if chance(0.5):
                # (it overrides too: a dispatch on q2 opens w, #209 step 2)
                L.append('    %s<override>():string = "qs {%s}"' % (tag, A))
        if have_qw:
            # a class below a repeating one that wraps its own parameter
            L.append('%s(u:type) := class(%s(?u)):' % (qw, qd))
            L.append('    %s:u' % C)
        L.append('%s(Xs:[]%s(t, u) where t:type, u:type):[]t = for (X : Xs) { X.%s() }' % (fs, q2, g1))
        L.append('%s(Xs:[]%s(t, t) where t:type):[]t = for (X : Xs) { X.%s() }' % (ss, q2, g2))
        L.append('%s(Xs:[]%s(t, u), Y:t, Z:u where t:type, u:type):[]tuple(t, u) =' % (sw, q2))
        L.append('    for (X : Xs) { X.%s(X.%s(Y), Z) }' % (mix, pk))
        self.out += L

        def ints():
            out = ['%s(int, int){%s := %s, %s := %s}' % (q2, A, lit(), B, lit()),
                   '%s(int){%s := %s, %s := %s}' % (qd, A, lit(), B, lit())]
            if have_qi:
                out.append('%s{%s := %s, %s := %s}' % (qi, A, lit(), B, lit()))
            R.shuffle(out)
            return out[:R.randint(1, len(out))]
        xs = tmpname('Qs')
        M.append('%s:[]%s(int, int) = array{%s}' % (xs, q2, ', '.join(ints())))
        x = tmpname('X')
        M.append('for (%s : %s) { Print("{%s.%s()} {%s.%s()} {%s.%s()} {%s.%s(%s)}") }' %
                 (x, xs, x, tag, x, g1, x, g2, x, pk, lit()))
        x = tmpname('X')
        M.append('for (%s : %s(%s)) { Print("f {%s}") }' % (x, fs, xs, x))
        x = tmpname('X')
        M.append('for (%s : %s(%s)) { Print("s {%s}") }' % (x, ss, xs, x))
        x = tmpname('X')
        M.append('for (%s : %s(%s, %s, %s)) { Print("w {%s(0)} {%s(1)}") }' % (x, sw, xs, lit(), lit(), x, x))
        if chance(0.5):
            ys = tmpname('Qs')
            M.append('%s:[]%s(string, string) = array{%s(string){%s := "a", %s := "b"}, %s(string, string){%s := "c", %s := "d"}}' %
                     (ys, q2, qd, A, B, q2, A, B))
            x = tmpname('X')
            M.append('for (%s : %s(%s)) { Print("fs {%s}") }' % (x, fs, ys, x))
        if have_qo:
            os_ = tmpname('Qo')
            M.append('%s:[]%s(?int, int) = array{%s(int){%s := false, %s := %s}, %s(?int, int){%s := option{%s}, %s := %s}}' %
                     (os_, q2, qo, A, B, lit(), q2, A, lit(), B, lit()))
            x, v = tmpname('X'), tmpname('V')
            M.append('for (%s : %s) { Print(if (%s := %s.%s()?) then "o {%s.%s()} {%s}" else "o {%s.%s()} none") }' %
                     (x, os_, v, x, g1, x, tag, v, x, tag))
            x, v = tmpname('X'), tmpname('V')
            M.append('for (%s : %s(%s)) { Print(if (%s := %s?) then "of {%s}" else "of none") }' % (x, fs, os_, v, x, v))
        if have_qp:
            ps_ = tmpname('Qp')
            M.append('%s:[]%s(int, []int) = array{%s(int){%s := %s, %s := array{%s}, %s := %s}, %s([]int){%s := %s, %s := array{}}}' %
                     (ps_, q2, qs, A, lit(), B, lit(), C, lit(), qp, A, lit(), B))
            x = tmpname('X')
            M.append('for (%s : %s) { Print("p {%s.%s()} {%s.%s()} {%s.%s().Length}") }' % (x, ps_, x, tag, x, g1, x, g2))
            x = tmpname('X')
            M.append('for (%s : %s(%s)) { Print("pf {%s}") }' % (x, fs, ps_, x))
        if have_qw:
            ws = tmpname('Qw')
            M.append('%s:[]%s(?int, ?int) = array{%s(int){%s := false, %s := option{%s}, %s := %s}, %s(?int){%s := option{%s}, %s := false}}' %
                     (ws, q2, qw, A, B, lit(), C, lit(), qd, A, lit(), B))
            x, v = tmpname('X'), tmpname('V')
            M.append('for (%s : %s) { Print(if (%s := %s.%s()?) then "wq {%s.%s()} {%s}" else "wq {%s.%s()} none") }' %
                     (x, ws, v, x, g1, x, tag, v, x, tag))
        if have_qn:
            ns = tmpname('Qn')
            M.append('%s:[]%s([]int, int) = array{%s(int){%s := array{}, %s := %s}, %s([]int, int){%s := array{%s}, %s := 0}}' %
                     (ns, q2, qn, A, B, lit(), q2, A, lit(), B))
            x = tmpname('X')
            M.append('for (%s : %s) { Print("n {%s.%s()} {%s.%s().Length}") }' % (x, ns, x, tag, x, g1))
        self.main += M

    # --- classes with type parameters a dispatch opens (#209 step 2)

    def gen_existential(self):
        """A GADT-style hierarchy: xe(t) with Ev():t; xl := class(xe(int));
        xp(a, b) := class(xe(tuple(a, b))), whose a and b only occur inside
        the type argument it gives xe; xf(a, b) := class(xe(a)), whose b
        does not occur at all; maybe xt(a, b, n) below xp, with a type
        parameter of its own. Code generic over xe(t) dispatches to them,
        opening their type parameters; their methods use locals of those
        types, whose initial values come from the object. Sometimes Ev is
        <suspends> throughout (#251), and Main then suspends too."""
        L, M = [], []
        su = chance(0.4)
        if su:
            self.susp_main = True
        sx = '<suspends>' if su else ''
        def pause():
            return ['        Sleep(0.01)'] if su and chance(0.5) else []
        xe, xl, xa, xp, xf, xt = (self.fresh(x) for x in ['xe', 'xl', 'xa', 'xp', 'xf', 'xt'])
        ev, nm, run = (self.fresh(x) for x in ['Ev', 'Nm', 'XRun'])
        V, L1, R1, P1, T1 = (self.fresh(x) for x in ['XV', 'XL', 'XR', 'XP', 'XT'])
        have_xt = chance(0.5)
        L.append('%s(t:type) := class<abstract>:' % xe)
        L.append('    %s()%s:t' % (ev, sx))
        L.append('    %s():string = "xe"' % nm)
        L.append('%s := class(%s(int)):' % (xl, xe))
        L.append('    %s:int' % V)
        L.append('    %s<override>()%s:int =' % (ev, sx))
        L += pause()
        L.append('        %s' % V)
        if chance(0.6):
            L.append('    %s<override>():string = "xl {%s}"' % (nm, V))
        L.append('%s := class(%s(int)):' % (xa, xe))
        L.append('    %s:%s(int)' % (L1, xe))
        L.append('    %s:%s(int)' % (R1, xe))
        L.append('    %s<override>()%s:int = %s.%s() + %s.%s()' % (ev, sx, L1, ev, R1, ev))
        L.append('%s(a:type, b:type) := class(%s(tuple(a, b))):' % (xp, xe))
        L.append('    %s:%s(a)' % (L1, xe))
        L.append('    %s:%s(b)' % (R1, xe))
        if chance(0.5):
            L.append('    %s<override>()%s:tuple(a, b) =' % (ev, sx))
            L += pause()
            L.append('        var X:a = %s.%s()' % (L1, ev))
            L.append('        Y:b = %s.%s()' % (R1, ev))
            L.append('        set X = %s.%s()' % (L1, ev))
            L.append('        (X, Y)')
        else:
            if su and chance(0.5):
                # (a spawned dispatch at the opened type parameters, #209)
                L.append('    %s<override>()%s:tuple(a, b) =' % (ev, sx))
                L.append('        TL := spawn{%s.%s()}' % (L1, ev))
                L.append('        Y:b = %s.%s()' % (R1, ev))
                L.append('        (TL.Await(), Y)')
            else:
                L.append('    %s<override>()%s:tuple(a, b) = (%s.%s(), %s.%s())' % (ev, sx, L1, ev, R1, ev))
        if chance(0.6):
            L.append('    %s<override>():string = "xp({%s.%s()}, {%s.%s()})"' % (nm, L1, nm, R1, nm))
        L.append('%s(a:type, b:type) := class(%s(a)):' % (xf, xe))
        L.append('    %s:%s(tuple(a, b))' % (P1, xe))
        L.append('    %s<override>()%s:a = %s.%s()(0)' % (ev, sx, P1, ev))
        if have_xt:
            L.append('%s(a:type, b:type, n:type) := class(%s(a, b)):' % (xt, xp))
            L.append('    %s:n' % T1)
            L.append('    %s<override>():string = "xt {(super:)%s()}"' % (nm, nm))
        L.append('%s(E:%s(t) where t:type)%s:t = E.%s()' % (run, xe, sx, ev))
        self.out += L

        def iexp(d):
            r = R.random()
            if d <= 0 or r < 0.35:
                return '%s{%s := %s}' % (xl, V, lit())
            if r < 0.6:
                return '%s{%s := %s, %s := %s}' % (xa, L1, iexp(d - 1), R1, iexp(d - 1))
            return '%s(int, int){%s := %s}' % (xf, P1, pexp(d - 1))

        def pexp(d):
            if have_xt and chance(0.3):
                return '%s(int, int, string){%s := %s, %s := %s, %s := "t"}' % (xt, L1, iexp(d - 1), R1, iexp(d - 1), T1)
            return '%s(int, int){%s := %s, %s := %s}' % (xp, L1, iexp(d - 1), R1, iexp(d - 1))
        for _ in range(R.randint(1, 3)):
            M.append('Print("x {%s(%s)}")' % (run, iexp(3)))
        ps = tmpname('Xp')
        M.append('%s:[]%s(tuple(int, int)) = array{%s, %s}' % (ps, xe, pexp(2), pexp(2)))
        x = tmpname('X')
        M.append('for (%s : %s) { Print("xp {%s.%s()} {%s(%s)(0)} {%s(%s)(1)}") }' % (x, ps, x, nm, run, x, run, x))
        self.main += M

    def gen_param_iface(self):
        """Parametric classes below a plain interface (#276): pi(t) with a
        field of type t below ni, maybe also below a parametric interface
        ci(t) listed before or after ni, or below ci(t) extending ni; maybe a
        subclass fixing t and one keeping it; code over ni (and ci) dispatches
        to their overrides, opening t."""
        L, M = [], []
        ni, pc, ipc, kpc = (self.fresh(x) for x in ['ni', 'pc', 'ipc', 'kpc'])
        nm, sz, lb = (self.fresh(x) for x in ['INm', 'ISz', 'ILb'])
        V, N = self.fresh('PV'), self.fresh('PN')
        L.append('%s := interface:' % ni)
        L.append('    %s:string = "%s"' % (lb, lb.lower()))
        L.append('    %s():string' % nm)
        L.append('    %s():int' % sz)
        ci, cg = self.fresh('ci'), self.fresh('ICg')
        # ('sub': pc implements ci(t) only, and its subclasses add ni, #209)
        mode = R.choice(['plain', 'plain', 'before', 'after', 'extends', 'sub'])
        if mode != 'plain':
            L.append('%s(t:type) := interface%s:' % (ci, '(%s)' % ni if mode == 'extends' else ''))
            L.append('    %s():int' % cg)
        parents = {'plain': ni, 'before': '%s(t), %s' % (ci, ni), 'after': '%s, %s(t)' % (ni, ci),
                   'extends': '%s(t)' % ci, 'sub': '%s(t)' % ci}[mode]
        L.append('%s(t:type) := class(%s):' % (pc, parents))
        L.append('    %s:[]t' % V)
        L.append('    %s:int' % N)
        if mode != 'sub':
            L.append('    %s<override>():string = "%s {%s} {%s.Length}"' % (nm, pc, N, V))
            L.append('    %s<override>():int = %s.Length + %s' % (sz, V, N))
        if mode != 'plain':
            L.append('    %s<override>():int = %s * 10' % (cg, N))
        have_i, have_k = chance(0.6), chance(0.5)
        if mode == 'sub':
            have_i, have_k = True, True
            L.append('%s := class(%s(int), %s):' % (ipc, pc, ni))
            L.append('    %s<override>():string = "%s {%s} {%s.Length}"' % (nm, ipc, N, V))
            L.append('    %s<override>():int = %s.Length + %s' % (sz, V, N))
            L.append('%s(t:type) := class(%s(t), %s):' % (kpc, pc, ni))
            L.append('    %s<override>():string = "%s {%s.Length}"' % (nm, kpc, V))
            L.append('    %s<override>():int = %s.Length * 2' % (sz, V))
        else:
            if have_i:
                L.append('%s := class(%s(int)):' % (ipc, pc))
                L.append('    %s<override>():string = "%s {%s}"' % (nm, ipc, N))
            if have_k:
                L.append('%s(t:type) := class(%s(t)):' % (kpc, pc))
                L.append('    %s<override>():int = %s.Length * 2' % (sz, V))
        self.out += L
        def obj():
            r = R.random()
            if mode == 'sub':
                if r < 0.5:
                    return '%s{%s := array{%s}, %s := %s}' % (ipc, V, lit(), N, lit())
                return '%s(string){%s := array{"a", "b"}, %s := %s}' % (kpc, V, N, lit())
            if have_i and r < 0.3:
                return '%s{%s := array{%s}, %s := %s}' % (ipc, V, lit(), N, lit())
            if have_k and r < 0.55:
                return '%s(string){%s := array{"a", "b"}, %s := %s}' % (kpc, V, N, lit())
            return '%s(logic){%s := array{true}, %s := %s}' % (pc, V, N, lit())
        xs = tmpname('Ni')
        M.append('%s:[]%s = array{%s}' % (xs, ni, ', '.join(obj() for _ in range(R.randint(1, 4)))))
        x = tmpname('X')
        M.append('for (%s : %s) { Print("ni {%s.%s} {%s.%s()} {%s.%s()}") }' % (x, xs, x, lb, x, nm, x, sz))
        if mode != 'plain':
            cs = tmpname('Ci')
            M.append('%s:[]%s(logic) = array{%s(logic){%s := array{false}, %s := %s}}' % (cs, ci, pc, V, N, lit()))
            y = tmpname('Y')
            M.append('for (%s : %s) { Print("ci {%s.%s()}") }' % (y, cs, y, cg))
        self.main += M

    # --- overloads

    def gen_overloads(self):
        name = self.fresh('Show')
        L, M = [], []
        opt = chance(0.4)
        L.append('%s(X:int):string = "int {X}"' % name)
        if opt:
            L.append('%s(X:?int):string = if (V := X?) then "some {V}" else "none"' % name)
        else:
            L.append('%s(X:string):string = "str {X}"' % name)
        two = chance(0.5)
        option_tag = opt and two
        if two:
            L.append('%s(X:int, Y:int):string = "two {X + Y}"' % name)
        tup = chance(0.3)
        # tuple(char) both unpacks for char and converts to string ([]char).
        char_tag = tup and not opt
        if tup:
            tag = ',?Character:logic' if char_tag else ''
            L.append('%s(X:char%s):string = "char {X}"' % (name, tag))
        used = []
        objtypes = self.trees[:2]
        inh = [i for i in self.ifaces if any(c.below(i) and not c.abstract for c in self.classes)]
        if inh and chance(0.35):
            objtypes = [R.choice(inh)]
        for t in objtypes:
            sub = Ctx()
            sub.calls = self.callable(t, 'X.')
            c = some_call(sub, 1)
            body = '"%s {%s}"' % (t.name, c[0]) if c else '"%s"' % t.name
            L.append('%s(X:%s):string = %s' % (name, t.name, body))
            used.append(t)
        if len(used) == 1 and chance(0.5):
            option_tag = opt
            L.append('%s(X:%s, Y:int):string = "%s and {Y}"' % (name, used[0].name, used[0].name))
            if not used[0].abstract:
                M.append('Print(%s(%s, %s))' % (name, self.construct_plain(used[0]), lit()))
        # A whole tuple accepted by a multi-positional sibling overlaps ?int
        # under the pinned tuple/option admission rule. Keep generating both
        # families, distinguishing the option with a required name.
        if option_tag:
            L = [line.replace('(X:?int):', '(X:?int,?Option:logic):') for line in L]
        self.out += L
        M.append('Print(%s(%s))' % (name, lit()))
        if opt:
            tag = ',?Option:=true' if option_tag else ''
            M.append('Print(%s(option{%s}%s))' % (name, lit(), tag))
            M.append('Print(%s(false%s))' % (name, tag))
        else:
            M.append('Print(%s("%s"))' % (name, R.choice(['a', 'b'])))
            M.append('Print(%s(%s(%s)))' % (name, name, lit()))
        if two:
            M.append('Print(%s(%s, %s))' % (name, lit(), lit()))
        if tup:
            tag = ',?Character:=true' if char_tag else ''
            M.append("Print(%s('%s'%s))" % (name, R.choice('abz'), tag))
        for t in used:
            for c in (t.subtree() if not t.is_iface else [c for c in self.classes if c.below(t)]):
                if not c.abstract and chance(0.5):
                    e, failable = self.construct(c, Ctx())
                    if not failable:
                        M.append('Print(%s(%s))' % (name, e))
        self.omain = M

    # --- Main for the hierarchy

    def main_ctx(self, objs, t=None, prefix=None):
        ctx = Ctx()
        ctx.objs = list(objs)
        ctx.callable = self.callable
        if t is not None:
            ctx.calls = self.callable(t, prefix)
        return ctx

    def gen_main_hierarchy(self):
        M = []
        objs = []
        for c in self.classes:
            if c.abstract:
                continue
            for _ in range(R.choice([1, 1, 2])):
                v = tmpname('O')
                e, failable = self.construct(c, Ctx(), allow_fail=True)
                if failable:
                    w = tmpname('W')
                    M.append('%s:%s = if (%s := %s) then %s else %s' % (v, c.name, w, e, w, self.construct_plain(c)))
                else:
                    M.append('%s := %s' % (v, e))
                objs.append((v, c))
        R.shuffle(objs)
        # links through option and array fields
        for v, c in objs:
            for f in c.all_fields():
                if scalar(f) or not chance(0.7) or (isobj(f.ty) and not f.var):
                    continue
                fty = f.ty if isinstance(f.ty, tuple) else ('obj', f.ty)
                cands = [w for w, d in objs if below(d, fty[1])]
                if not cands:
                    continue
                if fty[0] == 'opt':
                    M.append('set %s.%s = option{%s}' % (v, f.name, R.choice(cands)))
                elif fty[0] == 'obj':
                    M.append('set %s.%s = %s' % (v, f.name, R.choice(cands)))
                    vs = [g for g in fty[1].all_fields() if g.var and g.ty == 'int']
                    if vs:
                        M.append('set %s.%s.%s += %s' % (v, f.name, R.choice(vs).name, lit(1, 9)))
                elif fty[0] == 'map':
                    for key in R.sample('abc', R.randint(1, 3)):
                        # (a set through a map's key is in a failure context: its key's
                        # reference is <decides>, the Book of Verse's API reference)
                        M.append('if (set %s.%s["%s"] = %s) {}' % (v, f.name, key, R.choice(cands)))
                else:
                    ws = [R.choice(cands) for _ in range(R.randint(1, 3))]
                    M.append('set %s.%s = %s.%s + array{%s}' % (v, f.name, v, f.name, ', '.join(ws)))
        mctx = self.main_ctx(objs)
        # show each object
        for v, c in objs:
            parts = []
            for f in c.all_fields():
                if scalar(f) and chance(0.5):
                    parts.append('{%s.%s}' % (v, f.name))
            calls = self.callable(c, v + '.')
            for p, r in calls:
                if r.decides or not chance(0.6):
                    continue
                t = shown(p, r, mctx, 2)
                if t:
                    parts.append('{%s}' % t)
            if parts:
                M.append('Print("%s: %s")' % (c.name, ' '.join(parts)))
            for p, r in calls:
                if r.decides and chance(0.7):
                    w = tmpname('W')
                    t = call_text(p, r, mctx, 1, bracket=True)
                    M.append('if (%s := %s) then Print("%s yes {%s}") else Print("%s no")' % (w, t, r.name, w, r.name))
            vars_ = [f for f in c.all_fields() if f.var and f.ty == 'int']
            if vars_ and chance(0.6):
                f = R.choice(vars_)
                M.append('set %s.%s %s %s' % (v, f.name, R.choice(['=', '+=', '-=', '*=']), lit(1, 4)))
                if chance(0.5):
                    a = tmpname('Al')
                    M.append('%s := %s' % (a, v))
                    M.append('set %s.%s += %s' % (a, f.name, lit(1, 4)))
                if chance(0.5):
                    M.append('if (set %s.%s = %s, %s.%s > %s) then Print("kept {%s.%s}") else Print("rolled back {%s.%s}")'
                             % (v, f.name, lit(0, 20), v, f.name, lit(5, 15), v, f.name, v, f.name))
                M.append('Print("%s.%s = {%s.%s}")' % (v, f.name, v, f.name))
            for f in c.all_fields():
                if isinstance(f.ty, tuple) and f.ty[0] == 'opt' and chance(0.5):
                    vs = [g for g in fields_of_type(f.ty[1]) if g.var and g.ty == 'int']
                    if vs:
                        g = R.choice(vs)
                        z = tmpname('Z')
                        M.append('if (set %s.%s?.%s += %s, %s := %s.%s?) then Print("through {%s.%s}") else Print("empty %s")'
                                 % (v, f.name, g.name, lit(1, 9), z, v, f.name, z, g.name, f.name))
        # unique classes compare by identity
        for t in self.trees:
            if t.unique:
                os_ = [v for v, c in objs if c.below(t)]
                if len(os_) >= 2:
                    a, b = R.sample(os_, 2)
                    M.append('if (%s = %s) then Print("eq") else Print("ne")' % (a, b))
                    M.append('if (%s <> %s) then Print("ne") else Print("eq")' % (a, a))
        # arrays of a class or interface type above several objects
        types = list(self.types())
        R.shuffle(types)
        narr = 0
        for t in types:
            below_ = [(v, c) for v, c in objs if c.below(t)]
            if len(below_) < 2 or narr >= 4:
                continue
            narr += 1
            arr = tmpname('Xs')
            R.shuffle(below_)
            M.append('%s:[]%s = array{%s}' % (arr, t.name, ', '.join(v for v, _ in below_)))
            x = tmpname('X')
            ictx = self.main_ctx(objs + [(x, t)])
            parts = []
            for p, r in self.callable(t, x + '.'):
                if not r.decides and chance(0.7):
                    ct = shown(p, r, ictx, 1)
                    if ct:
                        parts.append('{%s}' % ct)
            fs = fields_of_type(t)
            for f in fs:
                if scalar(f) and chance(0.5):
                    parts.append('{%s.%s}' % (x, f.name))
            if not parts:
                parts = ['?']
            vf = [f for f in fs if f.var and f.ty == 'int']
            if chance(0.3):
                i = tmpname('I')
                M.append('for (%s -> %s : %s) { Print("%s {%s} %s") }' % (i, x, arr, t.name, i, ' '.join(parts)))
            else:
                M.append('for (%s : %s):' % (x, arr))
                if chance(0.25):
                    M.append('    defer:')
                    M.append('        Print("after %s")' % ' '.join(parts[:1]))
                M.append('    Print("%s %s")' % (t.name, ' '.join(parts)))
                if vf and chance(0.5):
                    M.append('    set %s.%s += %s' % (x, vf[0].name, lit(1, 3)))
            if vf and chance(0.4):
                y = tmpname('Y')
                M.append('if (set %s[%s].%s *= %s, %s := %s[0]) then Print("path {%s.%s}") else Print("no path")' %
                         (arr, lit(0, 3), vf[0].name, lit(2, 3), y, arr, y, vf[0].name))
            # casts down to a class below t, or to an interface
            subs = [c for c in self.classes if c.below(t) and c is not t]
            subs += [i for i in self.ifaces if i is not t and chance(0.3)
                     and any(d.below(t) and d.below(i) for d in self.classes)]
            if subs:
                s = R.choice(subs)
                x, y = tmpname('X'), tmpname('Y')
                ct = some_call(self.main_ctx(objs, s, y + '.'), 1)
                show = s.name + (' {%s}' % ct[0] if ct else '')
                if chance(0.5):
                    M.append('for (%s : %s, %s := %s[%s]) { Print("as %s") }' % (x, arr, y, s.name, x, show))
                else:
                    M.append('for (%s : %s):' % (x, arr))
                    M.append('    if (%s := %s[%s]) then Print("is %s") else Print("not %s")' % (y, s.name, x, show, s.name))
            # a function over the array
            tot = [(p, r) for (p, r) in self.callable(t, 'X.') if r.ret == 'int' and not r.decides
                   and all(q == 'int' for q in r.ptypes)]
            if tot and chance(0.5):
                p, r = R.choice(tot)
                fn = self.fresh('Total')
                self.out.append('%s(Xs:[]%s):int =' % (fn, t.name))
                self.out.append('    var N:int = 0')
                self.out.append('    for (X : Xs) { set N += %s }' % call_text(p, r, Ctx(ints=['N']), 1))
                self.out.append('    N')
                M.append('Print("total {%s(%s)}")' % (fn, arr))
            # a var of the array's type, reassigned (it starts as the first element)
            if chance(0.35):
                cur, x = tmpname('Cur'), tmpname('X')
                c1 = some_call(self.main_ctx(objs, t, x + '.'), 1, 'int')
                c2 = some_call(self.main_ctx(objs, t, cur + '.'), 1)
                if c1 and c2:
                    M.append('var %s:%s = %s' % (cur, t.name, below_[0][0]))
                    M.append('for (%s : %s, %s > %s) { set %s = %s }' % (x, arr, c1[0], lit(0, 30), cur, x))
                    M.append('Print("cur {%s}")' % c2[0])
            # an upcast
            if chance(0.3):
                v, c = R.choice(below_)
                u = tmpname('U')
                M.append('%s := %s(%s)' % (u, t.name, v))
                ct = some_call(self.main_ctx(objs, t, u + '.'), 1)
                if ct:
                    M.append('Print("up {%s}")' % ct[0])
        if chance(0.5):
            M += self.gen_stress(objs)
        # show objects again (var fields changed)
        for v, c in objs[:3]:
            ct = some_call(self.main_ctx(objs, c, v + '.'), 2)
            if ct:
                M.append('Print("again {%s}")' % ct[0])
        self.main = M + self.main

    def gen_stress(self, objs):
        """A loop that constructs many objects, links some, rolls some back (GC pressure)."""
        conc = [c for c in self.classes if not c.abstract]
        if not conc:
            return []
        M = []
        c = R.choice(conc)
        ups = [t for t in self.types() if below(c, t)]
        t = R.choice(ups)
        kept, acc, i, v = tmpname('Kept'), tmpname('Acc'), tmpname('I'), tmpname('V')
        n = R.choice([50, 200, 600])
        M.append('var %s:[]%s = array{}' % (kept, t.name))
        M.append('var %s:int = 0' % acc)
        M.append('for (%s := 1..%d):' % (i, n))
        ctx = Ctx(ints=[i])
        e, failable = self.construct(c, ctx)
        if failable:
            e = self.construct_plain(c)
        M.append('    %s := %s' % (v, e))
        vars_ = [f for f in c.all_fields() if f.var and f.ty == 'int']
        if vars_ and chance(0.6):
            M.append('    set %s.%s += %s' % (v, R.choice(vars_).name, i))
        M.append('    if (Mod[%s, %d] = 0) then set %s = %s + array{%s}' % (i, R.choice([3, 7, 13]), kept, kept, v))
        if vars_ and chance(0.5):
            f = R.choice(vars_).name
            M.append('    if (set %s.%s = 1000, set %s = %s + array{%s}, %s > %d) then set %s += 1' %
                     (v, f, kept, kept, v, i, n - 3, acc))
        holders = [(w, f) for w, d in objs for f in d.all_fields()
                   if isinstance(f.ty, tuple) and below(c, f.ty[1])]
        if holders and chance(0.6):
            w, f = R.choice(holders)
            if f.ty[0] == 'opt':
                M.append('    if (Mod[%s, 5] = 0) then set %s.%s = option{%s}' % (i, w, f.name, v))
            elif f.ty[0] == 'map':
                M.append('    if (Q := Mod[%s, 4], set %s.%s["k{Q}"] = %s) {}' % (i, w, f.name, v))
            else:
                M.append('    if (Mod[%s, 50] = 0) then set %s.%s = %s.%s + array{%s}' % (i, w, f.name, w, f.name, v))
        sub = self.main_ctx(objs + [(v, c)], c, v + '.')
        sub.ints = [i]
        ct = some_call(sub, 1, 'int')
        if ct:
            M.append('    if (R := Mod[%s, 1000]) then set %s += R' % (ct[0], acc))
        M.append('Print("stress {%s} {%s.Length}")' % (acc, kept))
        x = tmpname('X')
        sub = self.main_ctx(objs + [(x, t)], t, x + '.')
        ct = some_call(sub, 1)
        if ct:
            M.append('for (%s : %s, Mod[%s.Length, 2] = 0) { Print("kept {%s}") }' % (x, kept, kept, ct[0]))
        return M

    # --- program

    def gen(self):
        if chance(0.5):
            h = self.fresh('Helper')
            self.helpers.append(h)
            self.out.append('%s(X:int):int = X * %s + %s' % (h, lit(1, 3), lit()))
        self.gen_ifaces()
        for i in self.ifaces:
            self.decide_iface(i)
        for _ in range(R.choice([1, 2, 2])):
            self.trees.append(self.gen_class(None, 1))
        self.phase = 'main'
        for i in self.ifaces:
            i.lines = self.emit_iface(i)
        for c in self.classes:
            self.emit_class_bodies(c)
        # The heap contract is a declaration: descendants include every
        # parent's budget even when they override a field default.
        for data in self.ifaces + self.classes:
            data.construction_eff = self.construction_eff(data)
            tag = '<transacts>' if data.construction_eff == ALL else efftext(data.construction_eff)
            keyword = 'interface' if data.is_iface else 'class'
            data.lines[0] = data.lines[0].replace(' := ' + keyword, ' := ' + keyword + tag, 1)
        self.gen_ctors()
        for i in self.ifaces:
            self.out += i.lines
        for c in self.classes:
            self.out += c.lines
        for c in self.classes:
            for k in c.ctors:
                self.out += k['lines']
        if chance(0.4):
            self.gen_qualified()
        if chance(0.3):
            self.gen_shared_field()
        if chance(0.3):
            self.gen_fn_values()
        if chance(0.5):
            self.gen_parametric()
        if chance(0.5):
            self.gen_overloads()
        self.gen_main_hierarchy()
        self.main += self.pmain + self.omain
        if chance(0.4):
            self.gen_relational()
        if chance(0.4):
            self.gen_existential()
        if chance(0.3):
            self.gen_param_iface()
        # types with no concrete class below them (for triage: see drive.sh)
        empty = [t.name for t in self.types()
                 if not any((c is t or c.below(t)) and not c.abstract for c in self.classes)]
        lines = ['# uninhabited: %s' % ' '.join(empty)] + list(self.out)
        lines.append('Main()<suspends>:void =' if self.susp_main else 'Main():void =')
        if chance(0.25):
            lines += ['    defer:', '        Print("main done")']
        for m in self.main:
            lines.append('    ' + m)
        return '\n'.join(lines) + '\n'


def main():
    global R
    seed = int(sys.argv[1])
    R = random.Random(seed)
    g = Gen()
    GEN.append(g)
    source = g.gen()
    if g.extended_defaults:
        sys.stdout.write('# openverse: extended-defaults\n')
    sys.stdout.write(source)


if __name__ == '__main__':
    main()
