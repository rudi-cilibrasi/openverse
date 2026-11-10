#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the reviews of #234, #239 and #245 (choice and functions with several values, #208, #235),
# laziness from the review of #267 (generators taken where they are consumed, #246),
# exact effects where the first success is taken from the review of #275,
# consumers in methods from the review of #279, a return in a test's clauses from #284 and #287,
# alternatives with several values from the review of #296, blocks and constructions from #302,
# named arguments from #305, functions with several values and named parameters from #307,
# methods with several values from #310 (overridden from #328), returns in functions with several values from #312,
# and a choice after such a return's if, or in its value, from #318.
"""Random programs with choices INSIDE expressions (PR #234, phase 2), and an
independent model written from docs/LANGUAGE.md's "Choice" section (not from
scripts/gen-choice.py, and not from the lifting code).

The model is a continuation-passing evaluator: operands are evaluated left to
right, as ordinary expressions are, and a choice is a choice point where it
is written. That is what "the code before a choice runs once; each
alternative then runs the rest", "spatial order" and "lifting ... in the order
they are evaluated" say, without reference to how lifting is done.

- first-success contexts (if condition, first{}, if{}, option{}, logic{},
  not, left of or): depth-first; an alternative leading to no success is
  rolled back to the state the choice was reached in; no success at all:
  everything since the context began is rolled back;
- a for / for{}: a choice is a generator; a failure rolls back to the most
  recent generator (its alternative's own clauses failed); effects of
  segments that succeeded are kept, even if later generators give nothing;
- set L op= e: L's indices, then (op=) L's old value, then e;
- comparison chains: each pair is checked as soon as both operands are
  evaluated (the choice-free order: `0 > 1 < X` never evaluates X).

PR #237 (phase 3a) adds, under the flag `bif`, an `if ... else if ... else`
whose branches are choices or plain values, anywhere a choice may be. The
model, from LANGUAGE.md and the PR text only: its conditions run where the if
is written, once, each a first-success context of its own (kept if it
succeeds, rolled back if it fails), in order; the first that succeeds picks
its branch (else the last); the if then gives the picked branch's
alternatives, each evaluated in the state the condition left, seeing its
names. Since #331 the if adds no choice of its own: a branch with one
alternative is no generator, as an if with a return is not (#314); only
the choices the program reaches count.

usage: gen-ex.py SEED OUTDIR [flags...]   -> OUTDIR/p.verse, OUTDIR/p.expected
flags: heavy     (with bif: more of them, longer chains, longer conditions)
       bif       (branchy ifs; without it the programs are #234's, seed for seed)
       cf        (the choice-free twin: each choice is its first alternative)
       nochain   (no choice in operand >= 2 of a comparison chain: known bug)
       lazy      (recursive generators taken lazily, #246/#267; on by default
                  with mv, rec and bif; nolazy turns it off)
       noforset  (no op= / indexed set in a for)
       noret     (no `if (A op B) then return else true` among a test's clauses,
                  on with lazy otherwise, #284/#287)
       nort      (no call of RT, a function with several values with an early return
                  whose value is a choice; on with lazy otherwise, #312)
       nomvm     (no bare call, in a test that runs as a method, of that class's own
                  method with several values; on with meth otherwise, #310)
       nonam     (no call of NAM(NU, ?NV := …), a function with several values and a
                  named parameter whose default prints; on with lazy otherwise)
       nona      (no call of NA(A, ?P := …, ?Q := …) with named arguments in a test's
                  expressions, #305; on with lazy otherwise)
       nocb      (no block{B := e1; e2} or construction pt{Y := e2, X := e1} in a
                  test's expressions, #302; on with lazy otherwise)
       noaltch   (no alternative of a choice with several values of its own: a
                  choice, a call of a function with several values or of a
                  generator, #296; on with lazy otherwise)
"""
import copy
import os
import random
import sys

seed = int(sys.argv[1])
outdir = sys.argv[2]
flags = set(sys.argv[3:])


def _skip_eager_overflow(exc_type, exc, tb):
    # (a program whose recursive values would overflow when all computed at
    # the call, #246: marked SKIP for the driver, not modelled)
    if exc_type.__name__ == 'EagerOverflow':
        open(f"{outdir}/p.verse", "w").write("Main():void = {}\n")
        open(f"{outdir}/p.expected", "w").write("SKIP overflow (not modelled; #246 for one in a value never taken)\n")
        sys.exit(0)
    sys.__excepthook__(exc_type, exc, tb)


sys.excepthook = _skip_eager_overflow

# (the CPS model recurses deeply: Python 3.11's calls of Python functions do
# not use the C stack, so a high limit is enough)
sys.setrecursionlimit(1000000)
R = random.Random(seed)

PRE = '''Pos(X:int)<decides>:int =
    X > 0
    X
Even(X:int)<decides>:int =
    Mod[X, 2] = 0
    X
Tw(A:int, B:int):int = A * 10 + B
Tell(S:string, X:int):int =
    Print(S)
    X
ctr := class:
    var C:int = 0
    Next()<transacts>:int =
        set C += 1
        C - 1
    Add(X:int)<transacts>:int =
        set C += X
        C
'''


class EagerOverflow(Exception):
    """An int leaves 64-bit range: the program stops with an overflow, which
    is not modelled (where it stops, which prints a failure context keeps).
    A recursive function's values are all computed at the call (#245), so
    this also covers one in a value a first success would not reach (#246)."""


class StOverflow(Exception):
    """An int leaves 64-bit range where the program computes it (not an
    eager F$all value): the program stops there with an overflow (exit 2),
    having printed what the path it is on printed, those of failure contexts
    still open included."""

    def __init__(self, st):
        self.st = st


def chks(v, st):
    if not (-(1 << 63) <= v < (1 << 63)):
        raise StOverflow(st)
    return v


def chk(v):
    if not (-(1 << 63) <= v < (1 << 63)):
        raise EagerOverflow()
    return v


class Fail(Exception):
    pass


class St:
    def __init__(self):
        self.vars = {}
        self.binds = {}
        self.A = [0, 0, 0, 0]
        self.F = 1.0
        self.out = []

    def copy(self):
        # (vars and binds hold ints and strings only: shallow copies suffice)
        n = St.__new__(St)
        n.vars = dict(self.vars)
        n.binds = dict(self.binds)
        n.A = list(self.A)
        n.F = self.F
        n.out = list(self.out)
        return n


uid = [0]


def fresh(p):
    uid[0] += 1
    return f"{p}{uid[0]}"


def lookup(st, n):
    return st.binds[n] if n in st.binds else st.vars[n]


# ----------------------------------------------------------------- generation
# expression nodes:
#  ('lit',k) ('ref',n) ('tell',s,e) ('bprint',s,e) ('bset',v,op,k,e)
#  ('bin',op,a,b) ('tw',a,b) ('twt',a,b) ('pos',e) ('even',e) ('next',) ('add',e)
#  ('idx',[e1,e2,e3],i) ('cmp',e0,[(op,e)...]) ('choice',[alts])
#  ('optor', clauses, default) ('orx', e1, e2) ('ifx', clauses, then, else)
OPS = ['>', '<', '<>', '=', '>=', '<=']
CHAIN = [False]
NCH = [0]   # choices generated in the current test (bounded)

# ---- PR #239 (phase 3b), flag `mv`: functions with several values, inlined
# at their calls. LANGUAGE.md: "a call of it is a choice: it goes where a
# choice can go, and its values come in the callee's spatial order, at the
# call's place. Such a call is inlined: its arguments are evaluated first, in
# order, then its body runs in the caller's clauses, so the body's effects are
# rolled back or kept as the caller's are." The model inlines: a call
# evaluates its arguments left to right (CPS), binds them to the parameters,
# then runs the body's statements and value as the caller's own code, with
# every name the body binds renamed for that (dynamic) call site.
MV = 'mv' in flags
# ---- PR #245 (phase 3c), flag `rec`: effect-free recursive functions with
# several values. LANGUAGE.md: their values are computed at the call, all of
# them, in order; for finite ones that is the same as taking them one by
# one. The model is a separate list-monad evaluator (values in spatial
# order: a choice concatenates, operands combine left to right with the
# leftmost varying slowest, failure gives none), written from that text; a
# call is then a choice point over the list, in the caller's context.
REC = 'rec' in flags
# ---- PR #267 (#246 step 1), flag `lazy` (on with mv, rec and bif): recursive
# functions shaped as generators, taken lazily. From LANGUAGE.md: values one
# at a time as the consumer asks, in spatial order (depth first); in a for,
# the generator's clauses run between iterations and stay, a value's effects
# go with a rejected iteration, and a call whose clauses fail gives no values
# but keeps what its arguments did (as an eager one, #245); where the first
# success is taken, effects are undone as the Verse Calculus undoes them
# (#275): a value's with that value, also when a later choice is exhausted
# and the context comes back for the next value, and what a call's clauses,
# last if's conditions and arguments do (print, change an object, set a
# name) with all the values that call leads to, when the context rejects
# them all; the path to the value taken keeps its effects, in order (not yet
# in a method, where it is refused: the generated consumers are top-level
# functions; flag nofirstfx takes such a generator in a for only). The model inlines
# each call, recursively and lazily (CPS): a call evaluates its arguments,
# then its clauses as the caller's code, then its last choice as a choice
# point whose alternatives are values or calls of itself. A value never taken
# is never computed, so an overflow in one does not happen; one taken stops
# the program there (exit 2), and only eager F$all values are SKIPped.
LAZY = 'lazy' in flags or ('nolazy' not in flags and bool({'mv', 'rec', 'bif'} & flags))
GFUNCS = []
GFRAME = [0]
FXFIRST = [0]
# ---- #279, flag meth (on with lazy; nometh turns it off): some tests run in
# a method, Run, of a class of their own whose var fields are the test's two
# variables (one of them <private> at times), read and set bare there, and
# which inherits a method Nx from tbase (overridden at times) that counts in
# a var field Cn, called bare. Where the first success is taken, a set of
# such a field after a generator call keeps only the successful attempt's
# value, as a local's would: the model treats the fields as the test's vars.
METH = LAZY and 'nometh' not in flags
# ---- #284/#287, flag ret (on with lazy; noret turns it off): a test's if or
# for has a clause `if (A op B) then return else true` (A, B names bound before
# it, the test's vars, literals). A return inside a failure context leaves the
# function, and nothing the condition did is rolled back (LANGUAGE.md); the
# test prints its state in a defer:, so it is still checked. After a call of a
# generator with effects where the first success is taken (run as a function
# of its own, #275), such a clause is refused (#287), and so is the program.
RET = LAZY and 'noret' not in flags
# ---- #296, flag altch (on with lazy; noaltch turns it off): an alternative
# of a choice in a test's code may have several values of its own (a choice
# inside an expression, a call of a function with several values or of a
# generator). Its values come in order, alternative by alternative, with the
# usual undo rules: the CPS model needs nothing new. Not in a set's value nor
# in a branchy if, where it is still refused, nor in the generated functions.
ALTCH = LAZY and 'noaltch' not in flags and 'cf' not in flags
# ---- #302, flag cb (on with lazy; nocb turns it off): a test's expression may be
# block{B := e1; e2} (B is the block's own name, e2 may use it) or
# PS(pt{Y := e2, X := e1}), a construction of pt := struct{X, Y} written against
# its declaration order at times. A construction evaluates its fields in
# declaration order, not as written (LANGUAGE.md), so the model evaluates e1,
# then e2, as Tw(e1, e2); a block's clauses are the context's own. Choices may be
# inside both. Not in a set's value, a branchy if, nor the generated functions.
CB = LAZY and 'nocb' not in flags and 'cf' not in flags
# ---- #305, flag na (on with lazy; nona turns it off): a test's expression may call
# NA(A:int, ?P:int = Tell("dp", A), ?Q:int = P + 1):int = A * 100 + P * 10 + Q
# with some of its named arguments, in either order, the positional one written
# before or after them. A call evaluates its positional arguments, then its named
# ones as written, then the defaults of those omitted, in order (LANGUAGE.md); a
# default may use the parameters before it, and its effects are the caller's.
NA = LAZY and 'nona' not in flags and 'cf' not in flags
# ---- flag nam (on with lazy; nonam turns it off): a test's expression may call
# NAM(NU:int, ?NV:int = Tell("dv", NU)):int = NU + NV | NV * 2, a function with
# several values and a named parameter (inlined): its argument, then ?NV's if given,
# else the default (printing dv), then a choice of its two values.
NAM = LAZY and 'nonam' not in flags and 'cf' not in flags
# ---- #310, flag mvm (on with meth; nomvm turns it off): a test that runs as a
# method may call, bare, its class's own method with several values,
#   MvT(MpT:int):int = MpT + Nx() | MpT + HpT(NTa),  HpT(HqT:int):int = HqT * 2
# (unique names, as #310 requires): the first alternative calls Self's Nx,
# overridden at times, so it counts in Cn only when that alternative runs; the
# second reads the var field NTa where it is evaluated, as a bare call's
# argument in the body. At times a top-level constant has the field's name
# (NTa:int = 100 + T), and the call's argument is the field itself: the
# argument and the body must both read the field (the silent bug #310's review
# found).
MVM = 'nomvm' not in flags
# ---- #338 (with altch): at times a test that takes the first success starts with two composed
# choices, X := T | (C + L) with a choice C inside an alternative, the second in the rest of
# the first, so the front end compiles that rest once as a continuation ($cont, #335). A
# separate generator decides, so seeds keep their other choices.
R5 = random.Random(seed * 1000003 + 338)
# ---- #342: the same in a for (two composed choices first, so the clauses after the first and
# the body become one continuation, $contf); a generator of its own keeps the rest as they were.
R6 = random.Random(seed * 1000003 + 342)
# ---- #360 (#283): a branch of a branchy if may be a call with several values, recursive (taken
# lazily, one generator at the call) or not (inlined: its clauses plain, its choices generators);
# the if adds no choice of its own (#331), so a branch with one alternative is evaluated as it is.
# A generator of its own decides, so seeds keep their other choices.
R9 = random.Random(seed * 1000003 + 360)
# (branchy ifs in mv and rec modes too, half the programs, so their branches can call them)
BIF = 'bif' in flags or ((MV or REC) and R9.random() < 0.5)
# ---- #361 (#283): a choice in a set's path, set A[Mod[J.Next() + (0 | 2), 4]] op= e: the index's
# J.Next() runs once, before the choice; each index value is an alternative, reading its old value
# and then running e (its effects once per index value). A generator of its own decides.
R10 = random.Random(seed * 1000003 + 361)
# ---- #364 (#335 phase 2b): at times a for test starts with an exclusive choice, X := RT2(..) or
# RT3(..) (a return with a choice after it), and then a composed choice, so the front end calls
# one continuation from each path instead of copying the rest. A generator of its own decides.
R11 = random.Random(seed * 1000003 + 364)
# ---- #371 (#283): at times two of the lazily taken generators (Gz) call each other instead of
# themselves: a mutually recursive group, taken lazily as one. A generator of its own decides.
R12 = random.Random(seed * 1000003 + 371)
# ---- #328 (with mvm): at times the test's class overrides Mv with several values of its own,
#   MvT<override>(MpT:int):int = MpT * 3 | (super:)MvT(MpT) | MpT - 1
# Run, the fields and the base MvT are then in a parent class, so the bare MvT(..) in Run
# dispatches on Self, the test's class: the override's alternatives, the middle one the base's
# two. A second generator decides, so seeds keep their other choices.
R4 = random.Random(seed * 1000003 + 328)
# ---- #312, flag rt (on with lazy; nort turns it off): a test's expression may call
#   RT(RTa:int):int =
#       RTy := RTa | RTa + 1 | RTa + 2
#       Print("p{RTy}")
#       if (RTy = RTa + 1):
#           Print("rt")
#           return 99
#       else:
#           RTd := RTy * 2
#           Print("e{RTd}")
#       RTd := RTy * 10
#       RTd
# Each alternative prints p{RTy} first, before the if (#312's review: no hidden
# choice may keep it when a for rejects the value).
# A return gives the value of the alternative it is reached in: (after e{2 RTa})
# RTa * 10, then (after rt) 99, then (after e{2 (RTa + 2)}) (RTa + 2) * 10. (#312
# takes only the exact subset: every choice before the if, none in a return's
# value or after the if.)
# The else's RTd is its own; the one after the if is another (#312's review).
RT = LAZY and 'nort' not in flags and 'cf' not in flags
# ---- #314, with rt: two more functions with a return, where the if is an exclusive
# choice in a for (no generator boundary of its own):
#   RT2(RTa:int):int =                    RT3(RTa:int):int =
#       RTy := RTa | RTa + 1 | RTa + 2        RTy := RTa | RTa + 1 | RTa + 2
#       Print("p{RTy}")                       Print("p{RTy}")
#       if (RTy = RTa + 1):                   if (RTy = RTa + 1):
#           Print("rt")                           Print("rt")
#           return 99 | 98                        return 99
#       else:                                 else:
#           Print("e{RTy}")                       Print("e{RTy}")
#       Print("q{RTy}")                       Print("q{RTy}")
#       RTy * 10 | RTy * 10 + 1               RTy * 10 | RTy * 10 + 1
# In a for, a rejected value undoes what came after the last choice reached on its
# path: RT2's rt and p{..} stay when 99 and 98 are both rejected (the return's
# choice was reached), RT3's do not; p, e and q stay when both of a fall-through's
# values are rejected (the choice after the if was reached).
RT2 = RT and 'nort2' not in flags
REFUSED = [False]


class Return(Exception):
    def __init__(self, st):
        self.st = st


# the kinds of node whose insides are failure contexts of their own (or an
# inlined function's arguments), where a lifted call's clauses are not the test's
NESTED = ('not', 'logic', 'optor', 'orx', 'ifx', 'bif', 'mcall', 'choice', 'blk', 'cons', 'na', 'nam', 'mvm', 'rt', 'rt2', 'rt3')


def lift_pos(x):
    """'top' if x has a call of a lifted generator outside NESTED nodes, else
    'nested' if it has one inside them, else None."""
    if isinstance(x, tuple) and x and isinstance(x[0], str):
        if x[0] == 'gcall' and GFUNCS[x[1]]['lifted']:
            return 'top'
        if x[0] in NESTED:
            return 'nested' if has_lifted(x) else None
    if isinstance(x, (tuple, list)):
        rs = [lift_pos(y) for y in x]
        return 'top' if 'top' in rs else ('nested' if 'nested' in rs else None)
    return None


def has_lifted(x):
    if isinstance(x, tuple) and x and isinstance(x[0], str) and x[0] == 'gcall' and GFUNCS[x[1]]['lifted']:
        return True
    if isinstance(x, (tuple, list)):
        return any(has_lifted(y) for y in x)
    return False
SNX = {'inc': 1, 'ovm': False}
RFUNCS = []
RX = {'fi': None}
FUNCS = []
CTX = {'ctrs': None, 'nofail': False, 'fmax': None, 'plim': 64, 'take': None, 'noprint': False, 'nochoice': False}
PROD = [1]          # upper bound of the number of values (bounded)
SITE = [0]


def leaf(scope, vars_):
    k = R.random()
    if scope and k < 0.4:
        return ('ref', R.choice(scope))
    if vars_ and k < 0.55:
        return ('ref', R.choice(vars_))
    return ('lit', R.randint(-1, 5))


def gen_e(scope, vars_, d, ch):
    """an int expression; ch: whether a choice may be inside (liftably)."""
    if CTX['nochoice']:
        ch = False
    # (#314: returns in functions with several values, often enough that two calls of one
    # land in one first-success context, as in #318's review)
    if (RT2 and ch and NCH[0] < 4 and CTX['fmax'] is None and not CTX.get('inset') and not CTX.get('inbif')
            and R.random() < 0.12 and (not MV or PROD[0] * 6 <= CTX['plim'])):
        NCH[0] += 1
        if MV:
            PROD[0] *= 6
        return (R.choice(['rt2', 'rt3']), gen_e(scope, vars_, d + 1, ch))
    if LAZY and ch and NCH[0] < 4 and GFUNCS and CTX['fmax'] is None and R.random() < 0.25:
        m = gen_gcall(scope, vars_, d)
        if m is not None:
            return m
    if BIF and ch and NCH[0] < 4 and d < 3 and R.random() < (0.4 if 'heavy' in flags else 0.14) \
            and (not MV or PROD[0] * 3 <= CTX['plim']) and not lift_block():
        NCH[0] += 1
        if MV:
            PROD[0] *= 3
        return gen_bif(scope, vars_, d)
    if REC and ch and NCH[0] < 4 and RFUNCS and R.random() < 0.2 and not lift_block():
        m = gen_rcall(scope, vars_, d)
        if m is not None:
            return m
    if MV and ch and NCH[0] < 4 and not CTX.get('nomcall') and FUNCS[:CTX['fmax'] if CTX['fmax'] is not None else len(FUNCS)] and R.random() < 0.25:
        m = gen_mcall(scope, vars_, d)
        if m is not None:
            return m
    k = R.random()
    if ch and NCH[0] < 4 and k < 0.22 and (not MV or PROD[0] * 3 <= CTX['plim']):
        NCH[0] += 1
        n = R.randint(2, 3)
        if MV:
            PROD[0] *= n
        alts = []
        altch = (ALTCH and CTX['fmax'] is None and not CTX['nochoice'] and not CTX.get('inset')
                 and not CTX.get('inbif'))
        for _ in range(n):
            if R.random() < 0.08 and d < 3:
                # a directly nested choice is spliced
                alts.append(('choice', [gen_e(scope, vars_, d + 2, False) for _ in range(2)]))
            elif altch and d < 3 and R.random() < 0.3:
                alts.append(gen_e(scope, vars_, d + 1, True))     # (with several values of its own, #296)
            else:
                alts.append(gen_e(scope, vars_, d + 1, False))
        return ('choice', alts)
    if d >= 3 or k < 0.32:
        return leaf(scope, vars_)
    k = R.random()
    if CTX['noprint'] and (k < 0.16 or 0.59 <= k < 0.69):
        return leaf(scope, vars_)     # (no print, no object change)
    if CTX.get('big') and k < 0.03:
        return ('big', leaf(scope, vars_))
    if k < 0.10:
        return ('tell', fresh("t"), gen_e(scope, vars_, d + 1, ch))
    if k < 0.16:
        return ('bprint', fresh("p"), gen_e(scope, vars_, d + 1, False))
    if k < 0.22 and vars_ and not CTX.get('nobset'):
        return ('bset', R.choice(vars_), R.choice(['=', '+=']), R.randint(-1, 7), gen_e(scope, vars_, d + 1, False))
    if k < 0.40:
        op = R.choice(['+', '-', '+', '*'])
        a = gen_e(scope, vars_, d + 1, ch)
        b = gen_e(scope, vars_, d + 1, ch) if op != '*' else ('lit', R.randint(-1, 3))
        if op == '*' and R.random() < 0.5:
            a, b = b, a
        return ('bin', op, a, b)
    if (k < 0.48 and RT and ch and NCH[0] < 4 and CTX['fmax'] is None and not CTX['nochoice']
            and not CTX.get('inset') and not CTX.get('inbif') and R.random() < 0.3
            and (not MV or PROD[0] * 3 <= CTX['plim'])):
        NCH[0] += 1
        if RT2 and R.random() < 0.6 and (not MV or PROD[0] * 6 <= CTX['plim']):
            if MV:
                PROD[0] *= 6
            return (R.choice(['rt2', 'rt3']), gen_e(scope, vars_, d + 1, ch))
        if MV:
            PROD[0] *= 3
        return ('rt', gen_e(scope, vars_, d + 1, ch))
    if (k < 0.48 and MVM and CTX.get('meth') and METH and ch and NCH[0] < 4 and CTX['fmax'] is None
            and not CTX['nochoice'] and not CTX.get('inset') and not CTX.get('inbif') and R.random() < 0.9
            and (not MV or PROD[0] * 2 <= CTX['plim'])):
        NCH[0] += 1
        if MV:
            PROD[0] *= 2
        CTX['mvm_used'] = True
        arg = ('ref', CTX['mvm'][1]) if R.random() < 0.4 else gen_e(scope, vars_, d + 1, ch)
        return ('mvm', arg, CTX['mvm'])
    if (k < 0.48 and NAM and ch and NCH[0] < 4 and CTX['fmax'] is None and not CTX['nochoice']
            and not CTX.get('inset') and not CTX.get('inbif') and R.random() < 0.5
            and (not MV or PROD[0] * 2 <= CTX['plim'])):
        NCH[0] += 1
        if MV:
            PROD[0] *= 2
        named = [('NV', gen_e(scope, vars_, d + 1, ch))] if R.random() < 0.5 else []
        return ('nam', gen_e(scope, vars_, d + 1, ch), named, R.randint(0, len(named)))
    if (k < 0.48 and NA and CTX['fmax'] is None and not CTX['nochoice'] and not CTX.get('inset')
            and not CTX.get("inbif") and R.random() < 0.4):
        named = [(n, gen_e(scope, vars_, d + 1, ch)) for n in ('P', 'Q') if R.random() < 0.6]
        R.shuffle(named)
        return ('na', gen_e(scope, vars_, d + 1, ch), named, R.randint(0, len(named)))
    if (k < 0.48 and CB and CTX['fmax'] is None and not CTX['nochoice'] and not CTX.get('inset')
            and not CTX.get('inbif') and R.random() < 0.4):
        if R.random() < 0.5:
            return ('cons', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch), R.random() < 0.6)
        x = fresh("B")
        e1 = gen_e(scope, vars_, d + 1, ch)
        return ('blk', x, e1, gen_e(scope + [x], vars_, d + 1, ch))
    if k < 0.48:
        return ('tw', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch))
    if k < 0.51:
        return ('twt', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch))
    if CTX['nofail'] and (0.51 <= k < 0.59 or 0.69 <= k < 0.83):
        return leaf(scope, vars_)     # (a body without <decides> cannot fail)
    if k < 0.59:
        return (R.choice(['pos', 'even']), gen_e(scope, vars_, d + 1, ch))
    if k < 0.64:
        if CTX['ctrs'] is not None:
            return ('cnext', R.choice(CTX['ctrs'])) if CTX['ctrs'] else leaf(scope, vars_)
        if CTX.get('meth') and CTX['fmax'] is None and R.random() < 0.5:
            return ('snx',)        # (Self's Nx, called bare)
        return ('next',)
    if k < 0.69:
        if CTX['ctrs'] is not None:
            return ('cadd', R.choice(CTX['ctrs']), gen_e(scope, vars_, d + 1, ch)) if CTX['ctrs'] else leaf(scope, vars_)
        return ('add', gen_e(scope, vars_, d + 1, ch))
    if k < 0.75:
        return ('idx', [gen_e(scope, vars_, d + 2, ch) for _ in range(3)], gen_e(scope, vars_, d + 2, ch))
    if k < 0.83:
        return gen_cmp(scope, vars_, d + 1, ch)
    saved = CTX['nofail']
    CTX['nofail'] = False      # (a nested failure context may fail inside)
    savedt = CTX['take']
    CTX['take'] = 'first'      # (and takes the first success)
    try:
        if k < 0.89:
            cl, _ = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True, lastval=True)
            return ('optor', cl, leaf(scope, vars_))
        if k < 0.94:
            return ('orx', gen_e(scope, vars_, d + 1, True), leaf(scope, vars_))
        cl, sc2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
        cl.append(failable(sc2, vars_))
        return ('ifx', cl, leaf(sc2, vars_), leaf(scope, vars_))
    finally:
        CTX['nofail'] = saved
        CTX['take'] = savedt


def lift_block():
    """(known bugs in #275: where the first success is taken, after a call of
    a generator whose clauses, conditions or arguments have effects (run as a
    function of its own), a later generator without them, an eager call or a
    branchy if is a name clash ('$c… is already defined'), and so is one in
    its arguments; a call with effects in such a call's arguments followed by
    another is refused with 'internal: name $c…'. Flag fxsteer avoids them (fixed in 9bff543))"""
    return CTX['take'] != 'for' and 'fxsteer' in flags and bool(FXFIRST[0] or CTX.get('liftargs'))


def gub(fi, n):
    """an upper bound of the number of values of Gz_fi with N = n."""
    f = GFUNCS[fi]
    if f['decides'] and n < f['lo']:
        return 0
    if n < -1:
        return 0
    if f['decides']:
        alts = f['val'][1]
    else:
        alts = f['val'][2] if n <= f['lo'] else f['val'][3]
    if 'cf' in flags:
        alts = alts[:1]
    return sum(gub(a[1], n - 1) if a[0] == 'gself' else 1 for a in alts)     # (the callee's, #371)


def gen_gcall(scope, vars_, d):
    cands = [(i, n) for i in range(len(GFUNCS)) for n in range(0, 4)
             if 1 <= gub(i, n) and gub(i, n) * PROD[0] <= CTX['plim']
             and not (CTX['nofail'] and GFUNCS[i]['decides'])
             # (one whose clauses, conditions or arguments of its calls of itself
             # print, change an object or set a local: anywhere since #275;
             # flag nofirstfx, the rule of #267, takes it in a for only)
             and (GFUNCS[i]['first_ok'] or CTX['take'] == 'for' or 'nofirstfx' not in flags)
             # (known bug in #275: where the first success is taken, a call of a
             # generator without effects after one with effects is a name
             # clash; so none after one there, with flag fxsteer)
             and not (not GFUNCS[i]['lifted'] and lift_block())
             and not (GFUNCS[i]['lifted'] and CTX.get('liftargs') and CTX['take'] != 'for' and 'fxsteer' in flags)
             # (nor a second one in a clause after a clause that had one)
             and not (GFUNCS[i]['lifted'] and CTX['take'] != 'for' and 'fxsteer' in flags
                      and CTX.get('fx_before', 0) > 0 and CTX.get('clause_lifts', 0) >= 1)
             # (nor one with effects in the arguments of one without, which run first)
             and not (GFUNCS[i]['lifted'] and CTX['take'] != 'for' and CTX.get('loopargs') and 'fxsteer' in flags)]
    if not cands:
        return None
    i, n = R.choice(cands)
    f = GFUNCS[i]
    if f['lifted'] and CTX['take'] != 'for':
        FXFIRST[0] += 1
        CTX['clause_lifts'] = CTX.get('clause_lifts', 0) + 1
    NCH[0] += 1
    PROD[0] *= gub(i, n)
    saved = (CTX.get('loopargs'), CTX.get('liftargs'))
    if not f['lifted'] and CTX['take'] != 'for':
        CTX['loopargs'] = True
    if f['lifted'] and CTX['take'] != 'for':
        CTX['liftargs'] = True
    try:
        args = [('lit', n), gen_e(scope, vars_, d + 1, True)]
    finally:
        CTX['loopargs'], CTX['liftargs'] = saved
    if f['ctr']:
        args.append(('obj', R.choice(['K', 'J'])) if CTX['ctrs'] is None else ('ref', R.choice(CTX['ctrs'])))
    return ('gcall', i, args)


def gen_gfunc(i):
    fx = R.random() < 0.5          # may print or change an object in clauses, conditions, arguments
    dec = R.random() < 0.7
    ctr = R.random() < 0.4
    f = {'name': f"Gz{i}", 'decides': dec, 'ctr': ctr, 'first_ok': not fx, 'lo': R.choice([0, 1]),
         'params': [('N', 'int'), ('A', 'int')] + ([('C', 'ctr')] if ctr else [])}
    CTX.update(ctrs=['C'] if ctr else [], nofail=not dec, nochoice=True, noprint=not fx, fmax=-1, take=None)
    sc, vs = ['N', 'A'], []
    stmts = []
    if dec:
        stmts.append(('sfilt', ('cmp', ('ref', 'N'), [('>=', ('lit', f['lo']))])))
    names = R.sample(['Y', 'Q', 'V', 'W', 'Z', 'B'], 6)
    for _ in range(R.randint(0, 3)):
        k = R.random()
        if k < 0.25 and fx:
            stmts.append(('sprint', fresh("g")))
        elif k < 0.5:
            x = names.pop()
            stmts.append(('slet', x, gen_e(sc, vs, 1, False)))
            sc = sc + [x]
        elif k < 0.7:
            v = names.pop()
            stmts.append(('svar', v, gen_e(sc, vs, 1, False)))
            vs = vs + [v]
        elif k < 0.85 and vs:
            stmts.append(('sset', R.choice(vs), R.choice(['=', '+=']), gen_e(sc, vs, 1, False)))
        elif ctr and fx:
            stmts.append(('snext', 'C'))
    allsc = sc + vs

    def value():
        # (a value may print, change an object and set a local anywhere:
        # undone with it where it is rejected; one that overflows only does
        # where it is taken)
        CTX['noprint'] = False
        CTX['big'] = True
        try:
            return gen_e(sc, vs, 1, False)
        finally:
            CTX['noprint'] = not fx
            CTX['big'] = False

    def selfcall():
        # (the arguments of a call of itself print, change an object or set a
        # local in a generator with effects, fx; in the others they are pure)
        CTX['nobset'] = not fx
        a = gen_e(sc, vs, 1, False)
        CTX['nobset'] = False
        args = [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else [])
        return ('gself', i, args)

    def alts(withself):
        out = [value() for _ in range(R.randint(1, 2))]
        if withself:
            for _ in range(R.choice([1, 1, 2])):
                out.insert(R.randint(0, len(out)), selfcall())
        if len(out) == 1 and not withself and R.random() < 0.5:
            out.append(value())
        return out
    if dec:
        f['val'] = ('gchoice', alts(True))
    else:
        conds = [('filter', ('cmp', ('ref', 'N'), [('<=', ('lit', f['lo']))]))]
        # (a condition that always succeeds, so that N <= lo picks the base:
        # a print where the generator may print there)
        if fx and R.random() < 0.5:
            c2 = [('print', fresh("c"))]
            conds = c2 + conds if R.random() < 0.5 else conds + c2
        f['val'] = ('gbif', conds, alts(False), alts(True))
    f['stmts'] = stmts
    f['lifted'] = lifted(f)
    CTX.update(ctrs=None, nofail=False, nochoice=False, noprint=False, fmax=None, take=None)
    return f


FX_NODES = ('sprint', 'snext', 'tell', 'bprint', 'cnext', 'cadd', 'print', 'next', 'add', 'seti', 'setf')


def has_node(x, kinds):
    if isinstance(x, tuple):
        if x and isinstance(x[0], str) and x[0] in kinds:
            return True
        return any(has_node(y, kinds) for y in x)
    if isinstance(x, list):
        return any(has_node(y, kinds) for y in x)
    return False


def lifted(f):
    """whether a call of f where the first success is taken runs as a function
    of its own (#275): its clauses, last if's conditions or self-call
    arguments print or change an object, or those arguments set a name."""
    v = f['val']
    alts = v[1] if v[0] == 'gchoice' else v[2] + v[3]
    args = [a[2] for a in alts if a[0] == 'gself']
    conds = v[1] if v[0] == 'gbif' else []
    return (has_node(f['stmts'], FX_NODES) or has_node(conds, FX_NODES) or has_node(args, FX_NODES)
            or has_node(args, ('bset', 'setv')))


def show_galts(alts):
    if 'cf' in flags:
        return "(" + show(alts[0]) + ")"
    return "(" + " | ".join(show(a) for a in alts) + ")"


def show_gfunc(f):
    ps = ", ".join(f"{p}:{t}" for p, t in f['params'])
    L = [f"{f['name']}({ps}){'<decides>' if f['decides'] else ''}:int ="]
    L += ["    " + show_s(c) for c in f['stmts']]
    v = f['val']
    if v[0] == 'gchoice':
        L.append("    " + show_galts(v[1]))
    else:
        L.append(f"    if ({show_cl(v[1], ', ')}) then {show_galts(v[2])} else {show_galts(v[3])}")
    return L


def gen_call(fi, vals, st, k, mode):
    GFRAME[0] += 1
    fr = f"g{GFRAME[0]}"
    f = GFUNCS[fi]
    own = set(p for p, _ in f['params']) | binders_of(f['stmts'], set()) | binders_of(f['val'], set())
    stmts = rename(f['stmts'], own, fr)
    val = rename(f['val'], own, fr)
    for (p, _), v in zip(f['params'], vals):
        st.binds[f"{fr}.{p}"] = v
    LASTG[0] = f.get('lifted', False)
    if mode == 'all':
        # (in a for, a call whose clauses fail gives no values: what its
        # arguments and the clauses before it did stays, and its clauses' own
        # effects go, LANGUAGE.md, as for an eager one)
        s0 = st.copy()
        try:
            return run_body(stmts, val, st, k, mode)
        except Fail:
            return s0
    return run_body(stmts, val, st, k, mode)


def gen_rcall(scope, vars_, d):
    cands = [(i, n) for i in range(len(RFUNCS)) for n in range(0, 4)
             if rub(i, n) * PROD[0] <= CTX['plim'] and rub(i, n) >= 1
             and not (CTX['nofail'] and RFUNCS[i]['decides'])]
    if not cands:
        return None
    i, n = R.choice(cands)
    NCH[0] += 1
    PROD[0] *= rub(i, n)
    # (known bug: a choice or a call with several values in the argument of a
    # recursive one is refused or miscompiled; flag argbug keeps them)
    if True:
        # (a call with effects where the first success is taken cannot be in
        # the arguments of an eager call: see lift_block)
        saved = CTX.get('loopargs')
        if CTX['take'] != 'for':
            CTX['loopargs'] = True
        try:
            return ('rcall', i, n, gen_e(scope, vars_, d + 1, True))
        finally:
            CTX['loopargs'] = saved
    # (known bugs: a failing argument of a recursive call loses the other
    # alternatives in a body, and keeps the effects before it in a for)
    saved = CTX['nofail']
    CTX['nofail'] = True
    try:
        return ('rcall', i, n, gen_e(scope, vars_, d + 1, False))
    finally:
        CTX['nofail'] = saved


# the bodies of recursive functions: effect-free expressions over N, A, Y
def rleaf(sc):
    return ('ref', R.choice(sc)) if R.random() < 0.6 else ('lit', R.randint(-1, 4))


def gen_rx(sc, d, fi, dec):
    k = R.random()
    if d >= 2 or k < 0.35:
        return rleaf(sc)
    if k < 0.6:
        return ('bin', R.choice(['+', '-', '*']), gen_rx(sc, d + 1, fi, dec), gen_rx(sc, d + 1, fi, dec))
    if k < 0.72:
        return ('ctw', gen_rx(sc, d + 1, fi, dec), gen_rx(sc, d + 1, fi, dec))
    if k < 0.82 and dec and not RX.get('inarg'):
        return ('cpos', gen_rx(sc, d + 1, fi, dec))
    if k < 0.9 and dec and not RX.get('inarg'):
        return ('cmpf', gen_rx(sc, d + 1, fi, dec), R.choice(OPS), gen_rx(sc, d + 1, fi, dec))
    js = [j for j in range(fi) if dec or not RFUNCS[j]['decides']]
    if js and R.random() < 0.5 and not RX.get('inarg'):
        j = R.choice(js)
        return ('rrec', j, gen_rarg(sc, d + 1, fi, dec))
    return rleaf(sc)


def gen_rarg(sc, d, fi, dec):
    if True:
        return gen_rx(sc, d, fi, dec)
    RX['inarg'] = True
    try:
        return gen_rx(sc, d, fi, dec)
    finally:
        RX['inarg'] = False


def gen_ralts(sc, fi, dec):
    alts = [gen_rx(sc, 1, fi, dec) for _ in range(R.randint(1, 2))]
    for _ in range(R.choice([1, 1, 2])):
        alts.insert(R.randint(0, len(alts)), ('rrec', fi, gen_rarg(sc, 1, fi, dec)))
    return alts


def gen_rfunc(fi):
    dec = R.random() < 0.7
    f = {'name': f"Rq{fi}", 'decides': dec, 'lo': R.choice([0, 1]), 'locals': [], 'shape': None}
    sc = ['N', 'A']
    if dec:
        if R.random() < 0.4:
            f['locals'].append(('Y', gen_rx(sc, 1, fi, dec)))
            sc = sc + ['Y']
        alts = gen_ralts(sc, fi, dec)
        if R.random() < 0.6:
            f['shape'] = ('plain', alts)
        else:
            f['shape'] = ('operand', R.choice(['+', '*', '-']), gen_rx(sc, 1, fi, dec), alts, R.random() < 0.5)
    else:
        f['shape'] = ('branchy', gen_rx(sc, 1, fi, dec), gen_ralts(sc, fi, dec))
    return f


def show_rx(e, f):
    t = e[0]
    if t == 'lit':
        return str(e[1])
    if t == 'ref':
        return e[1]
    if t == 'bin':
        return f"({show_rx(e[2], f)} {e[1]} {show_rx(e[3], f)})"
    if t == 'ctw':
        return f"CTw({show_rx(e[1], f)}, {show_rx(e[2], f)})"
    if t == 'cpos':
        return f"CPos[{show_rx(e[1], f)}]"
    if t == 'cmpf':
        return f"({show_rx(e[1], f)} {e[2]} {show_rx(e[3], f)})"
    if t == 'rrec':
        g = RFUNCS[e[1]] if e[1] < len(RFUNCS) else f
        a = show_rx(e[2], f)
        return f"{g['name']}[N - 1, {a}]" if g['decides'] else f"{g['name']}(N - 1, {a})"
    raise AssertionError(e)


def show_ralts(alts, f):
    if 'cf' in flags:
        return "(" + show_rx(alts[0], f) + ")"
    return "(" + " | ".join(show_rx(a, f) for a in alts) + ")"


def show_rfunc(f):
    if f['decides']:
        L = [f"{f['name']}(N:int, A:int)<computes><decides>:int =", f"    N >= {f['lo']}"]
        L += [f"    {x} := {show_rx(e, f)}" for x, e in f['locals']]
        sh = f['shape']
        if sh[0] == 'plain':
            L.append("    " + show_ralts(sh[1], f))
        else:
            o, x, alts, left = sh[1], show_rx(sh[2], f), show_ralts(sh[3], f), sh[4]
            L.append(f"    {alts} {o} {x}" if left else f"    {x} {o} {alts}")
        return L
    base, alts = f['shape'][1], f['shape'][2]
    return [f"{f['name']}(N:int, A:int)<computes>:int = if (N <= {f['lo']}) then {show_rx(base, f)} else {show_ralts(alts, f)}"]


def rvals(e, env, f):
    """the values of e, in order (list monad)."""
    t = e[0]
    if t == 'lit':
        return [e[1]]
    if t == 'ref':
        return [env[e[1]]]
    if t in ('bin', 'ctw'):
        a, b = (e[2], e[3]) if t == 'bin' else (e[1], e[2])
        out = []
        for x in rvals(a, env, f):
            for y in rvals(b, env, f):
                out.append(chk(x * 10 + y if t == 'ctw' else {'+': x + y, '-': x - y, '*': x * y}[e[1]]))
        return out
    if t == 'cpos':
        return [x for x in rvals(e[1], env, f) if x > 0]
    if t == 'cmpf':
        return [x for x in rvals(e[1], env, f) for y in rvals(e[3], env, f) if cmpf(x, e[2], y)]
    if t == 'rrec':
        return [v for av in rvals(e[2], env, f) for v in rcall_vals(e[1] if e[1] < len(RFUNCS) else f['idx'], env['N'] - 1, av)]
    raise AssertionError(e)


def ralts_vals(alts, env, f):
    if 'cf' in flags:
        alts = alts[:1]
    return [v for a in alts for v in rvals(a, env, f)]


RMEMO = {}


def rcall_vals(fi, n, a):
    key = (fi, n, a)
    if key in RMEMO:
        return RMEMO[key]
    f = RFUNCS[fi]
    env = {'N': n, 'A': a}
    out = []
    if f['decides']:
        if n >= f['lo']:
            envs = [env]
            for x, e in f['locals']:
                envs = [dict(en, **{x: v}) for en in envs for v in rvals(e, en, f)]
            sh = f['shape']
            for en in envs:
                if sh[0] == 'plain':
                    out += ralts_vals(sh[1], en, f)
                else:
                    o, xe, alts, left = sh[1], sh[2], sh[3], sh[4]
                    ops = {'+': lambda p, q: p + q, '*': lambda p, q: p * q, '-': lambda p, q: p - q}[o]
                    if left:
                        out += [chk(ops(p, q)) for p in ralts_vals(alts, en, f) for q in rvals(xe, en, f)]
                    else:
                        out += [chk(ops(p, q)) for p in rvals(xe, en, f) for q in ralts_vals(alts, en, f)]
    else:
        out = rvals(f['shape'][1], env, f) if n <= f['lo'] else ralts_vals(f['shape'][2], env, f)
    RMEMO[key] = out
    return out


def rub_e(e, n, f):
    t = e[0]
    if t in ('lit', 'ref'):
        return 1
    if t in ('bin', 'ctw', 'cmpf'):
        return rub_e(e[2] if t == 'bin' else e[1], n, f) * rub_e(e[3] if t in ('bin', 'cmpf') else e[2], n, f)
    if t == 'cpos':
        return rub_e(e[1], n, f)
    if t == 'rrec':
        return rub_e(e[2], n, f) * rub(e[1] if e[1] < len(RFUNCS) else f['idx'], n - 1)
    raise AssertionError(e)


RUB = {}


def rub(fi, n):
    """an upper bound of the number of values of R_fi with N = n."""
    if (fi, n) in RUB:
        return RUB[(fi, n)]
    f = RFUNCS[fi]
    if n < -1:
        return 0
    if f['decides']:
        if n < f['lo']:
            u = 0
        else:
            u = 1
            for _, e in f['locals']:
                u *= rub_e(e, n, f)
            sh = f['shape']
            alts = sh[1] if sh[0] == 'plain' else sh[3]
            a = sum(rub_e(x, n, f) for x in (alts[:1] if 'cf' in flags else alts))
            u *= a * (1 if sh[0] == 'plain' else rub_e(sh[2], n, f))
    else:
        if n <= f['lo']:
            u = rub_e(f['shape'][1], n, f)
        else:
            alts = f['shape'][2]
            u = sum(rub_e(x, n, f) for x in (alts[:1] if 'cf' in flags else alts))
    RUB[(fi, n)] = u
    return u


def gen_mcall(scope, vars_, d):
    lim = CTX['fmax'] if CTX['fmax'] is not None else len(FUNCS)
    cands = [i for i in range(lim)
             if FUNCS[i]['count'] * PROD[0] <= CTX['plim']
             and not (CTX['nofail'] and FUNCS[i]['decides'])
             and not (CTX['ctrs'] is not None and not CTX['ctrs'] and FUNCS[i]['nctr'])]
    if not cands:
        return None
    fi = R.choice(cands)
    f = FUNCS[fi]
    NCH[0] += 1
    PROD[0] *= f['count']
    args = []
    for _, t in f['params']:
        if t == 'ctr':
            args.append(('obj', R.choice(['K', 'J'])) if CTX['ctrs'] is None else ('ref', R.choice(CTX['ctrs'])))
        else:
            args.append(gen_e(scope, vars_, d + 1, True))
    SITE[0] += 1
    return ('mcall', fi, args, f"s{SITE[0]}")


def gen_alts(scope, vars_, d):
    return [gen_e(scope, vars_, d + 1, False) for _ in range(R.choice([1, 2, 2, 3]))]


def is_call(e):
    return isinstance(e, tuple) and e and e[0] in ('mcall', 'rcall')


def unblock(e):
    while isinstance(e, tuple) and e and e[0] in ('bset', 'bprint', 'blk'):
        e = e[2] if e[0] == 'blk' else e[-1]      # (blk: its bound value, which needs no name)
    return e


def branch_alts(scope, vars_, d):
    """a branch's alternatives: at times one call with several values (#360)."""
    # (where a lifted choice may go: not in a block with a defer: of its own, lift_block)
    if R9.random() < 0.3 and NCH[0] < 4 and not lift_block():
        m = None
        if MV and FUNCS and not CTX.get('nomcall'):
            m = gen_mcall(scope, vars_, d)
        elif REC and RFUNCS:
            m = gen_rcall(scope, vars_, d)
        if m is not None:
            return [m]
    return gen_alts(scope, vars_, d)


def gen_bif(scope, vars_, d):
    saved_inbif = CTX.get('inbif')
    CTX['inbif'] = True       # (no alternative with values of its own in a branchy if, #296)
    try:
        return gen_bif0(scope, vars_, d)
    finally:
        CTX['inbif'] = saved_inbif


def gen_bif0(scope, vars_, d):
    arms = []
    for _ in range(R.choice([1, 1, 2, 3, 4] if 'heavy' in flags else [1, 1, 2, 3])):
        saved = CTX['nofail']
        savedt = CTX['take']
        CTX['nofail'] = False
        CTX['take'] = 'first'
        cl, sc2 = gen_clauses(list(scope), vars_, d + 1, R.randint(0, 3 if 'heavy' in flags else 2), allow_gen=False, inner=True)
        CTX['nofail'] = saved
        CTX['take'] = savedt
        cl.append(failable(sc2, vars_))
        arms.append((cl, branch_alts(sc2, vars_, d)))
    els = branch_alts(scope, vars_, d)
    if all(len(a) == 1 and not is_call(a[0]) for _, a in arms) and len(els) == 1 and not is_call(els[0]):
        els.append(gen_e(scope, vars_, d + 1, False))
    if any(is_call(x) for _, a in arms for x in a) or any(is_call(x) for x in els):
        # (an if with a call in a branch converts as a whole, and no branch may then be a block,
        # as LANGUAGE.md says: a set's, a Print's or a block's value is taken instead)
        arms = [(cl, [unblock(x) for x in a]) for cl, a in arms]
        els = [unblock(x) for x in els]
    return ('bif', arms, els, R.random() < 0.5)


def gen_cmp(scope, vars_, d, ch):
    if CTX['fmax'] is not None and 'nocmpcall' in flags:
        # (a call of a function with several values in a comparison in a
        # function's statement hung the compiler, #239, fixed since: flag
        # nocmpcall leaves it out)
        saved = CTX.get('nomcall', False)
        CTX['nomcall'] = True
        try:
            return gen_cmp0(scope, vars_, d, ch)
        finally:
            CTX['nomcall'] = saved
    return gen_cmp0(scope, vars_, d, ch)


def gen_cmp0(scope, vars_, d, ch):
    n = R.choice([1, 1, 1, 2])
    e0 = gen_e(scope, vars_, d + 1, ch)
    rest = []
    for i in range(n):
        c2 = ch and not ('nochain' in flags and i >= 1)
        x = gen_e(scope, vars_, d + 1, c2)
        if i >= 1 and top_choice_e(x):
            CHAIN[0] = True
        rest.append((R.choice(OPS), x))
    return ('cmp', e0, rest)


def show(e):
    t = e[0]
    if t == 'lit':
        return str(e[1])
    if t == 'ref':
        return e[1]
    if t == 'tell':
        return f'Tell("{e[1]}", {show(e[2])})'
    if t == 'bprint':
        return f'(Print("{e[1]}"); {show(e[2])})'
    if t == 'bset':
        return f'(set {e[1]} {e[2]} {e[3]}; {show(e[4])})'
    if t == 'bin':
        return f'({show(e[2])} {e[1]} {show(e[3])})'
    if t == 'tw':
        return f'Tw({show(e[1])}, {show(e[2])})'
    if t == 'cons':
        if e[3]:
            return f'PS(pt{{Y := {show(e[2])}, X := {show(e[1])}}})'
        return f'PS(pt{{X := {show(e[1])}, Y := {show(e[2])}}})'
    if t == 'blk':
        return f'block{{ {e[1]} := {show(e[2])}; {show(e[3])} }}'
    if t == 'mvm':
        return f'Mv{e[2][0]}({show(e[1])})'
    if t == 'rt':
        return f'RT({show(e[1])})'
    if t in ('rt2', 'rt3'):
        return f'{t.upper()}({show(e[1])})'
    if t in ('na', 'nam'):
        items = [f'?{n} := {show(x)}' for n, x in e[2]]
        items.insert(e[3], show(e[1]))
        return f'{"NA" if t == "na" else "NAM"}({", ".join(items)})'
    if t == 'twt':
        return f'Tw(({show(e[1])}, {show(e[2])}))'
    if t == 'pos':
        return f'Pos[{show(e[1])}]'
    if t == 'even':
        return f'Even[{show(e[1])}]'
    if t == 'snx':
        return 'Nx()'
    if t == 'next':
        return 'K.Next()'
    if t == 'add':
        return f'K.Add({show(e[1])})'
    if t == 'idx':
        return 'array{' + ", ".join(show(x) for x in e[1]) + '}[' + show(e[2]) + ']'
    if t == 'cmp':
        return '(' + show(e[1]) + "".join(f' {op} {show(x)}' for op, x in e[2]) + ')'
    if t == 'choice':
        if 'cf' in flags:
            return '(' + show(alts_of(e)[0]) + ')'
        return '(' + " | ".join(show(a) for a in e[1]) + ')'
    if t == 'optor':
        return f'(option{{{show_cl(e[1], "; ")}}}? or {show(e[2])})'
    if t == 'orx':
        return f'({show(e[1])} or {show(e[2])})'
    if t == 'ifx':
        return f'(if ({show_cl(e[1], ", ")}) then {show(e[2])} else {show(e[3])})'
    if t in ('gcall', 'gself'):
        f = GFUNCS[e[1]]
        a = ", ".join(show(x) for x in e[2])
        return f"{f['name']}[{a}]" if f['decides'] else f"{f['name']}({a})"
    if t == 'big':
        return f"(9223372036854775807 + {show(e[1])} * 0 + 1)"
    if t == 'rcall':
        f = RFUNCS[e[1]]
        return f"{f['name']}[{e[2]}, {show(e[3])}]" if f['decides'] else f"{f['name']}({e[2]}, {show(e[3])})"
    if t == 'mcall':
        f = FUNCS[e[1]]
        a = ", ".join(show(x) for x in e[2])
        return f"{f['name']}[{a}]" if f['decides'] else f"{f['name']}({a})"
    if t == 'obj':
        return e[1]
    if t == 'cnext':
        return f"{e[1]}.Next()"
    if t == 'cadd':
        return f"{e[1]}.Add({show(e[2])})"
    if t == 'bif':
        out = ''
        for i, (cl, alts) in enumerate(e[1]):
            out += ('if' if i == 0 else ' else if') + f' ({show_cl(cl, ", ")}) then {show_alts(alts)}'
        return '(' + out + f' else {show_alts(e[2])})'
    raise AssertionError(e)


def show_alts(alts):
    if 'cf' in flags or len(alts) == 1:
        return '(' + show(alts[0]) + ')'
    return '(' + " | ".join(show(a) for a in alts) + ')'


def alts_of(e):
    if 'cf' in flags:   # the choice-free twin: each choice is its first alternative
        a = e[1][0]
        return alts_of(a) if a[0] == 'choice' else [a]
    out = []
    for a in e[1]:
        out += alts_of(a) if a[0] == 'choice' else [a]
    return out


# clause nodes:
#  ('bind',x,e) ('sbind',x,[e1,e2]) ('filter',cmp) ('setv',v,op,e) ('seti',op,e)
#  ('setf',e) ('print',s) ('range',x,lo,hi) ('not',clauses) ('logic',clauses)
def gen_clauses(scope, vars_, d, n, allow_gen, inner=False, lastval=False, isfor=False):
    cl = []
    for i in range(n):
        CTX['fx_before'], CTX['clause_lifts'] = FXFIRST[0], 0
        k = R.random()
        last = lastval and i == n - 1
        if k < 0.33 or last:
            if last and R.random() < 0.4 and scope:
                cl.append(('filter', gen_cmp(scope, vars_, d, True)))
            else:
                x = fresh("X")
                cl.append(('bind', x, gen_e(scope, vars_, d, True)))
                scope = scope + [x]
        elif k < 0.38 and not inner:
            x = fresh("S")
            cl.append(('sbind', x, [gen_e(scope, vars_, d + 1, True) for _ in range(2)]))
        elif k < 0.55:
            cl.append(('filter', gen_cmp(scope, vars_, d, True)))
        elif k < 0.64 and vars_ and not CTX.get('nobset'):
            op = '=' if (isfor and 'noforset' in flags) else R.choice(['=', '+=', '*='])
            CTX['inset'] = True
            cl.append(('setv', R.choice(vars_), op, gen_e(scope, vars_, d, True)))
            CTX['inset'] = False
        elif k < 0.69 and not inner:
            op = '=' if (isfor and 'noforset' in flags) else R.choice(['=', '+='])
            if not (isfor and 'noforset' in flags):
                CTX['inset'] = True
                cl.append(('setc' if R10.random() < 0.4 else 'seti', op, gen_e(scope, vars_, d, True)))
                CTX['inset'] = False
        elif k < 0.73 and not inner and not (isfor and 'noforset' in flags):
            CTX['inset'] = True
            cl.append(('setf', gen_e(scope, vars_, d + 1, True)))
            CTX['inset'] = False
        elif k < 0.79:
            if not CTX['noprint']:
                cl.append(('print', fresh("c")))
        elif k < 0.85 and not inner:
            savedt = CTX['take']
            CTX['take'] = 'first'
            c2, s2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
            CTX['take'] = savedt
            cl.append(('not', c2 + [failable(s2, vars_)]))
        elif k < 0.90 and not inner:
            savedt = CTX['take']
            CTX['take'] = 'first'
            c2, s2 = gen_clauses(list(scope), vars_, d + 1, R.randint(1, 2), allow_gen=False, inner=True)
            CTX['take'] = savedt
            cl.append(('logic', c2 + [failable(s2, vars_)]))
        elif allow_gen:
            x = fresh("R")
            lo = R.randint(0, 2)
            cl.append(('range', x, lo, lo + R.randint(0, 2)))
            scope = scope + [x]
        elif not CTX['noprint']:
            cl.append(('print', fresh("c")))
    return cl, scope


def failable(scope, vars_):
    return ('filter', ('cmp', leaf(scope, vars_), [(R.choice(OPS), leaf(scope, vars_))]))


def top_choice_e(e):
    t = e[0]
    if t in ('choice', 'bif', 'mcall', 'rcall', 'gcall', 'nam', 'mvm', 'rt', 'rt2', 'rt3'):
        return True
    if t in ('lit', 'ref', 'next', 'bprint', 'bset', 'optor', 'orx', 'ifx', 'obj', 'cnext', 'big', 'snx'):
        return False
    if t == 'cadd':
        return top_choice_e(e[2])
    if t in ('tell', 'pos', 'even', 'add'):
        return top_choice_e(e[-1])
    if t == 'bin':
        return top_choice_e(e[2]) or top_choice_e(e[3])
    if t in ('tw', 'twt', 'cons'):
        return top_choice_e(e[1]) or top_choice_e(e[2])
    if t == 'blk':
        return top_choice_e(e[2]) or top_choice_e(e[3])
    if t == 'na':
        return top_choice_e(e[1]) or any(top_choice_e(x) for _, x in e[2])
    if t == 'idx':
        return any(top_choice_e(x) for x in e[1]) or top_choice_e(e[2])
    if t == 'cmp':
        return top_choice_e(e[1]) or any(top_choice_e(x) for _, x in e[2])
    raise AssertionError(e)


def top_choice_c(c):
    t = c[0]
    if t == 'bind':
        return top_choice_e(c[2])
    if t == 'sbind':
        return any(top_choice_e(x) for x in c[2])
    if t == 'filter':
        return top_choice_e(c[1])
    if t == 'setv':
        return top_choice_e(c[3])
    if t == 'setc':
        return True          # (the index's choice is at the top)
    if t in ('seti', 'setf'):
        return top_choice_e(c[-1])
    return False


def show_c(c):
    t = c[0]
    if t == 'bind':
        e = c[2]
        if e[0] == 'bif' and e[3]:
            return f"{c[1]} := " + show(e)[1:-1]
        return f"{c[1]} := " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'sbind':
        return f'{c[1]} := "<{{{show(c[2][0])}}}-{{{show(c[2][1])}}}>"'
    if t == 'filter':
        s = show(c[1])
        return s[1:-1]
    if t == 'setv':
        e = c[3]
        return f"set {c[1]} {c[2]} " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'seti':
        e = c[2]
        return f"set A[Mod[J.Next(), 4]] {c[1]} " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'setc':
        return f"set A[Mod[J.Next() + (0 | 2), 4]] {c[1]} " + show(c[2])
    if t == 'setf':
        e = c[1]
        return "set F *= " + (show(e) if e[0] == 'choice' else show(e))
    if t == 'print':
        return f'Print("{c[1]}")'
    if t == 'range':
        return f"{c[1]} := {c[2]}..{c[3]}"
    if t == 'not':
        return f"not ({show_cl(c[1], '; ')})"
    if t == 'logic':
        return f"logic{{{show_cl(c[1], '; ')}}}?"
    if t == 'ret':
        return f"if ({show(c[1])[1:-1]}) then return else true"
    raise AssertionError(c)


def show_cl(cl, sep):
    return sep.join(show_c(c) for c in cl)


# ---------------------------------------------------------------- the model
STATS = {'cp': 0, 'gfirst': 0, 'gback': 0, 'gfor': 0, 'lfirst': 0, 'lback': 0, 'lmeth': 0}
LASTG = [False]


def choice_point(thunks, st, k, mode, gen=False):
    """thunks: f(s, k) for each alternative, in spatial order. (gen: a
    generator's; counted for the statistics MVSTATS asks for)"""
    STATS['cp'] += 1
    lift = gen and LASTG[0]
    if gen:
        STATS['gfirst' if mode == 'first' else 'gfor'] += 1
        if lift and mode == 'first':
            STATS['lfirst'] += 1
            if CTX.get('meth'):
                STATS['lmeth'] += 1
    if mode == 'first':
        for th in thunks:
            s1 = st.copy()
            before = STATS['cp']
            try:
                return th(s1, k)
            except Fail:
                if gen and STATS['cp'] > before:
                    STATS['gback'] += 1    # (a later choice exhausted, back into the generator)
                    if lift:
                        STATS['lback'] += 1
                continue
        raise Fail()
    cur = st
    for th in thunks:
        s1 = cur.copy()
        try:
            cur = th(s1, k)
        except Fail:
            pass
    return cur


def first_inner(run, st):
    """a nested first-success context: (value, state) or None; st untouched."""
    s0 = st.copy()
    try:
        return run(s0, lambda v, s: (v, s))
    except Fail:
        return None


def cmpf(a, op, b):
    return {'>': a > b, '<': a < b, '<>': a != b, '=': a == b, '>=': a >= b, '<=': a <= b}[op]


def ev(e, st, k, mode):
    t = e[0]
    if t == 'lit':
        return k(e[1], st)
    if t == 'ref':
        return k(lookup(st, e[1]), st)
    if t == 'tell':
        def k2(v, s):
            s.out.append(e[1])
            return k(v, s)
        return ev(e[2], st, k2, mode)
    if t == 'bprint':
        st.out.append(e[1])
        return ev(e[2], st, k, mode)
    if t == 'bset':
        st.vars[e[1]] = e[3] if e[2] == '=' else chks(st.vars[e[1]] + e[3], st)
        return ev(e[4], st, k, mode)
    if t == 'rt':
        def krt(v, s0):
            def val(x):
                return lambda s1, k2: k2(chks(x, s1), s1)

            def alt_ret(s1, k2):
                s1.out.append(f"p{chks(v + 1, s1)}")
                s1.out.append('rt')
                return k2(99, s1)
            def fall(y):
                def th(s1, k2):
                    s1.out.append(f"p{y}")
                    s1.out.append(f"e{chks(y * 2, s1)}")
                    return k2(chks(y * 10, s1), s1)
                return th
            return choice_point([fall(v), alt_ret, fall(v + 2)], s0, k, mode)
        return ev(e[1], st, krt, mode)
    if t in ('rt2', 'rt3'):
        def krt2(v, s0):
            def val(x):
                return lambda s1, k2: k2(x, s1)
            def alt_ret(s1, k2):
                s1.out.append(f"p{chks(v + 1, s1)}")
                s1.out.append('rt')
                if t == 'rt2':
                    return choice_point([val(99), val(98)], s1, k2, mode)
                return k2(99, s1)
            def fall(y):
                def th(s1, k2):
                    yy = chks(y, s1)
                    s1.out.append(f"p{yy}")
                    s1.out.append(f"e{yy}")
                    s1.out.append(f"q{yy}")
                    y10 = chks(yy * 10, s1)
                    return choice_point([val(y10), lambda s2, k3: k3(chks(y10 + 1, s2), s2)], s1, k2, mode)
                return th
            return choice_point([fall(v), alt_ret, fall(v + 2)], s0, k, mode)
        return ev(e[1], st, krt2, mode)
    if t == 'mvm':
        def kmvm(v, s0):
            def alt1(s1, k2):
                c = s1.vars['S.Cn']
                s1.vars['S.Cn'] = c + SNX['inc']
                return k2(chks(v + c, s1), s1)

            def alt2(s1, k2):
                return k2(chks(v + 2 * s1.vars[e[2][1]], s1), s1)
            if SNX['ovm']:
                return choice_point([lambda s1, k2: k2(chks(v * 3, s1), s1),
                                     lambda s1, k2: choice_point([alt1, alt2], s1, k2, mode),
                                     lambda s1, k2: k2(chks(v - 1, s1), s1)], s0, k, mode)
            return choice_point([alt1, alt2], s0, k, mode)
        return ev(e[1], st, kmvm, mode)
    if t == 'nam':
        def knam(vu, s0):
            def finish(nv, s):
                vals = [chks(vu + nv, s), chks(nv * 2, s)]
                return choice_point([(lambda v: (lambda s1, k2: k2(v, s1)))(v) for v in vals], s, k, mode)
            if e[2]:
                return ev(e[2][0][1], s0, lambda nv, s: finish(nv, s), mode)
            s0.out.append('dv')
            return finish(vu, s0)
        return ev(e[1], st, knam, mode)
    if t == 'na':
        # positional, then the named ones as written, then the omitted defaults
        def kna(va, s0):
            vals = {}

            def step(i, s):
                if i < len(e[2]):
                    n, x = e[2][i]

                    def kn(v, s2):
                        vals[n] = v
                        return step(i + 1, s2)
                    return ev(x, s, kn, mode)
                p = vals['P'] if 'P' in vals else None
                if p is None:
                    s.out.append('dp')
                    p = va
                q = vals['Q'] if 'Q' in vals else p + 1
                return k(chks(chks(chks(va * 100, s) + chks(p * 10, s), s) + q, s), s)
            return step(0, s0)
        return ev(e[1], st, kna, mode)
    if t == 'blk':
        def kblk(v, s):
            s.binds[e[1]] = v
            return ev(e[3], s, k, mode)
        return ev(e[2], st, kblk, mode)
    if t in ('bin', 'tw', 'twt', 'cons'):
        # (a construction: its fields in declaration order, X then Y, as written or not)
        a, b = (e[2], e[3]) if t == 'bin' else (e[1], e[2])

        def ka(va, s1):
            def kb(vb, s2):
                if t != 'bin':
                    return k(chks(chks(va * 10, s2) + vb, s2), s2)
                return k(chks({'+': va + vb, '-': va - vb, '*': va * vb}[e[1]], s2), s2)
            return ev(b, s1, kb, mode)
        return ev(a, st, ka, mode)
    if t in ('pos', 'even'):
        def kp(v, s):
            if (v > 0) if t == 'pos' else (v % 2 == 0):
                return k(v, s)
            raise Fail()
        return ev(e[1], st, kp, mode)
    if t == 'snx':
        v = st.vars['S.Cn']
        st.vars['S.Cn'] += SNX['inc']
        return k(v, st)
    if t == 'next':
        v = st.vars['K.C']
        st.vars['K.C'] += 1
        return k(v, st)
    if t == 'add':
        def kadd(v, s):
            s.vars['K.C'] = chks(s.vars['K.C'] + v, s)
            return k(s.vars['K.C'], s)
        return ev(e[1], st, kadd, mode)
    if t == 'idx':
        elems = e[1] + [e[2]]

        def go(i, acc, s):
            if i == len(elems):
                j = acc[-1]
                if 0 <= j < 3:
                    return k(acc[j], s)
                raise Fail()
            return ev(elems[i], s, lambda v, s2: go(i + 1, acc + [v], s2), mode)
        return go(0, [], st)
    if t == 'cmp':
        def go(i, prev, first, s):
            if i == len(e[2]):
                return k(first, s)
            op, x = e[2][i]

            def kc(v, s2):
                if not cmpf(prev, op, v):
                    raise Fail()
                return go(i + 1, v, first, s2)
            return ev(x, s, kc, mode)
        return ev(e[1], st, lambda v0, s: go(0, v0, v0, s), mode)
    if t == 'obj':
        return k(e[1], st)
    if t == 'cnext':
        o = lookup(st, e[1]) + '.C'
        v = st.vars[o]
        st.vars[o] += 1
        return k(v, st)
    if t == 'cadd':
        o = lookup(st, e[1]) + '.C'

        def kca(v, s):
            s.vars[o] = chks(s.vars[o] + v, s)
            return k(s.vars[o], s)
        return ev(e[2], st, kca, mode)
    if t in ('gcall', 'gself'):
        args = e[2]

        def gog(i, vals, s):
            if i == len(args):
                return gen_call(e[1], vals, s, k, mode)
            return ev(args[i], s, lambda v, s2: gog(i + 1, vals + [v], s2), mode)
        return gog(0, [], st)
    if t == 'gchoice':
        if 'cf' in flags:
            return ev(e[1][0], st, k, mode)
        return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in e[1]], st, k, mode, True)
    if t == 'gbif':
        res = first_inner(lambda s, kk: run_clauses(e[1], s, lambda s2: kk(None, s2), 'first'), st)
        alts, s0 = (e[2], res[1]) if res is not None else (e[3], st)
        if 'cf' in flags:
            return ev(alts[0], s0, k, mode)
        return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in alts], s0, k, mode, True)
    if t == 'big':
        return ev(e[1], st, lambda v, s: k(chks(9223372036854775807 + v * 0 + 1, s), s), mode)
    if t == 'rcall':
        def krc(av, s):
            vs = rcall_vals(e[1], e[2], av)
            if 'cf' in flags:
                if not vs:
                    raise Fail()
                return k(vs[0], s)
            return choice_point([(lambda s2, k2, v=v: k2(v, s2)) for v in vs], s, k, mode)
        return ev(e[3], st, krc, mode)
    if t == 'mcall':
        body = inst(e[1], e[3])
        args = e[2]

        def go(i, vals, s):
            if i == len(args):
                for p, v in zip(body['params'], vals):
                    s.binds[p] = v
                return run_body(body['stmts'], body['val'], s, k, mode)
            return ev(args[i], s, lambda v, s2: go(i + 1, vals + [v], s2), mode)
        return go(0, [], st)
    if t == 'choice' and 'cf' in flags:
        return ev(alts_of(e)[0], st, k, mode)
    if t == 'choice':
        return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in alts_of(e)], st, k, mode)
    if t == 'optor':
        res = first_inner(lambda s, kk: run_clauses(e[1], s, lambda s2: kk(clause_value(e[1], s2), s2), 'first'), st)
        if res is not None:
            return k(res[0], res[1])
        return ev(e[2], st, k, mode)
    if t == 'orx':
        res = first_inner(lambda s, kk: ev(e[1], s, kk, 'first'), st)
        if res is not None:
            return k(res[0], res[1])
        return ev(e[2], st, k, mode)
    if t == 'bif':
        for cl, alts in e[1]:
            res = first_inner(lambda s, kk, cl=cl: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
            if res is not None:
                return bif_alts(alts, res[1], k, mode)
        return bif_alts(e[2], st, k, mode)
    if t == 'ifx':
        res = first_inner(lambda s, kk: run_clauses(e[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            return ev(e[2], res[1], k, mode)
        return ev(e[3], st, k, mode)
    raise AssertionError(e)


def binders_of(x, acc):
    """every name a callee's body binds (parameters aside)."""
    if isinstance(x, tuple):
        if x and x[0] in ('bind', 'sbind', 'range', 'slet', 'svar') and isinstance(x[1], str):
            acc.add(x[1])
        for y in x:
            binders_of(y, acc)
    elif isinstance(x, list):
        for y in x:
            binders_of(y, acc)
    return acc


def rename(x, own, site):
    if isinstance(x, list):
        return [rename(y, own, site) for y in x]
    if not isinstance(x, tuple) or not x:
        return x
    if not isinstance(x[0], str):
        return tuple(rename(y, own, site) for y in x)
    t = x[0]
    if t == 'mcall':
        return ('mcall', x[1], rename(x[2], own, site), f"{site}/{x[3]}")
    if t in ('ref', 'cnext', 'snext', 'bind', 'sbind', 'range', 'slet', 'svar', 'sset', 'bset', 'cadd', 'setv') and isinstance(x[1], str) and x[1] in own:
        return (t, f"{site}.{x[1]}") + tuple(rename(y, own, site) for y in x[2:])
    return (t,) + tuple(rename(y, own, site) for y in x[1:])


INST = {}


def inst(fi, site):
    """the body of FUNCS[fi] for the call site `site`: its names renamed."""
    key = (fi, site)
    if key not in INST:
        f = FUNCS[fi]
        own = set(p for p, _ in f['params']) | binders_of(f['stmts'], set()) | binders_of(f['val'], set())
        INST[key] = {'params': [f"{site}.{p}" for p, _ in f['params']],
                     'stmts': rename(f['stmts'], own, site), 'val': rename(f['val'], own, site)}
    return INST[key]


def run_body(stmts, val, st, k, mode):
    if not stmts:
        return ev(val, st, k, mode)
    c = stmts[0]

    def nxt(s):
        return run_body(stmts[1:], val, s, k, mode)
    t = c[0]
    if t == 'sprint':
        st.out.append(c[1])
        return nxt(st)
    if t == 'slet':
        def kl(v, s):
            s.binds[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kl, mode)
    if t == 'svar':
        def kv(v, s):
            s.vars[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kv, mode)
    if t == 'sset':
        old = st.vars[c[1]]

        def kss(x, s):
            s.vars[c[1]] = x if c[2] == '=' else chks(old + x, s)
            return nxt(s)
        return ev(c[3], st, kss, mode)
    if t == 'sfilt':
        return ev(c[1], st, lambda _, s: nxt(s), mode)
    if t == 'snext':
        o = lookup(st, c[1]) + '.C'
        st.vars[o] += 1
        return nxt(st)
    raise AssertionError(c)


def bif_alts(alts, st, k, mode):
    if 'cf' in flags:
        return ev(alts[0], st, k, mode)
    if len(alts) == 1:     # (#331: a branch without a choice of its own is no generator)
        return ev(alts[0], st, k, mode)
    return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in alts], st, k, mode)


def clause_value(cl, s):
    c = cl[-1]
    if c[0] == 'bind':
        return s.binds[c[1]]
    if c[0] == 'filter':
        return s.binds['$last']
    raise AssertionError(c)


def run_clauses(cl, st, k, mode):
    """k(state) after the last clause; returns what k returns."""
    if not cl:
        return k(st)
    c = cl[0]

    def nxt(s):
        return run_clauses(cl[1:], s, k, mode)
    t = c[0]
    if t == 'bind':
        def kb(v, s):
            s.binds[c[1]] = v
            return nxt(s)
        return ev(c[2], st, kb, mode)
    if t == 'sbind':
        def ka(va, s1):
            def kb2(vb, s2):
                s2.binds[c[1]] = f"<{va}-{vb}>"
                return nxt(s2)
            return ev(c[2][1], s1, kb2, mode)
        return ev(c[2][0], st, ka, mode)
    if t == 'filter':
        def kf(v, s):
            s.binds['$last'] = v
            return nxt(s)
        return ev(c[1], st, kf, mode)
    if t == 'setv':
        v, op = c[1], c[2]
        old = st.vars[v]

        def ks(x, s):
            s.vars[v] = x if op == '=' else chks(old + x if op == '+=' else old * x, s)
            return nxt(s)
        return ev(c[3], st, ks, mode)
    if t == 'setc':
        op = c[1]
        base = st.vars['J.C']
        st.vars['J.C'] += 1

        def idx(k):
            def th(s1, k2):
                i = (base + k) % 4
                old = s1.A[i]

                def ksc(x, s):
                    s.A[i] = x if op == '=' else chks(old + x, s)
                    return k2(None, s)
                return ev(c[2], s1, ksc, mode)
            return th
        return choice_point([idx(0), idx(2)], st, lambda _v, s: nxt(s), mode)
    if t == 'seti':
        op = c[1]
        i = st.vars['J.C'] % 4
        st.vars['J.C'] += 1
        old = st.A[i]

        def ksi(x, s):
            s.A[i] = x if op == '=' else chks(old + x, s)
            return nxt(s)
        return ev(c[2], st, ksi, mode)
    if t == 'setf':
        old = st.F

        def ksf(x, s):
            s.F = old * x
            return nxt(s)
        return ev(c[1], st, ksf, mode)
    if t == 'print':
        st.out.append(c[1])
        return nxt(st)
    if t == 'range':
        def mk(v):
            def th(s, k2):
                s.binds[c[1]] = v
                return k2(None, s)
            return th
        return choice_point([mk(v) for v in range(c[2], c[3] + 1)], st, lambda _, s: nxt(s), mode)
    if t == 'not':
        res = first_inner(lambda s, kk: run_clauses(c[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is not None:
            raise Fail()
        return nxt(st)
    if t == 'ret':
        if first_inner(lambda s, kk: ev(c[1], s, kk, 'first'), st) is not None:
            raise Return(st)       # (leaves the test with the state as it is)
        return nxt(st)
    if t == 'logic':
        res = first_inner(lambda s, kk: run_clauses(c[1], s, lambda s2: kk(None, s2), 'first'), st)
        if res is None:
            raise Fail()
        return nxt(res[1])
    raise AssertionError(c)


def fmt_float(f):
    # (openverse floats have no negative zero: LANGUAGE.md, float)
    f = float(f) + 0.0
    if f != f:
        return "NaN"
    if f in (float('inf'), float('-inf')):
        return "Inf" if f > 0 else "-Inf"
    return repr(f)


# ---------------------------------------------------------------- programs
POOL = ['Y', 'Q', 'K', 'J', 'A', 'F', 'N0c', 'N1b', 'V', 'W', 'Z', 'X', 'B', 'S', 'O', 'Lg']


def top_choice_s(c):
    t = c[0]
    if t in ('slet', 'svar'):
        return top_choice_e(c[2])
    if t == 'sset':
        return top_choice_e(c[3])
    if t == 'sfilt':
        return top_choice_e(c[1])
    return False


def show_s(c):
    t = c[0]
    if t == 'sprint':
        return f'Print("{c[1]}")'
    if t == 'slet':
        return f"{c[1]} := {show(c[2])}"
    if t == 'svar':
        return f"var {c[1]}:int = {show(c[2])}"
    if t == 'sset':
        return f"set {c[1]} {c[2]} {show(c[3])}"
    if t == 'sfilt':
        return show(c[1])[1:-1]
    if t == 'snext':
        return f"{c[1]}.Next()"
    raise AssertionError(c)


def gen_func(i):
    decides = R.random() < 0.3
    names = R.sample(POOL, len(POOL))
    params = [(names.pop(), 'int') for _ in range(R.randint(0, 2))]
    if R.random() < 0.3:
        params.insert(R.randint(0, len(params)), (names.pop(), 'ctr'))
    ctrs = [p for p, t in params if t == 'ctr']
    CTX.update(ctrs=ctrs, nofail=not decides, fmax=i, plim=12)
    NCH[0] = 0
    PROD[0] = 1
    scope = [p for p, t in params if t == 'int']
    vars_ = []
    stmts = []
    for _ in range(R.randint(0, 3)):
        k = R.random()
        if k < 0.2:
            stmts.append(('sprint', fresh("m")))
        elif k < 0.5:
            x = names.pop()
            stmts.append(('slet', x, gen_e(scope, vars_, 1, True)))
            scope = scope + [x]
        elif k < 0.65:
            v = names.pop()
            stmts.append(('svar', v, gen_e(scope, vars_, 1, True)))
            vars_ = vars_ + [v]
        elif k < 0.8 and vars_:
            stmts.append(('sset', R.choice(vars_), R.choice(['=', '+=']), gen_e(scope, vars_, 1, True)))
        elif k < 0.9 and decides and scope:
            stmts.append(('sfilt', gen_cmp(scope, vars_, 1, True)))
        elif ctrs:
            stmts.append(('snext', R.choice(ctrs)))
        else:
            stmts.append(('sprint', fresh("m")))
    val = gen_e(scope, vars_, 1, True)
    if not (any(top_choice_s(c) for c in stmts) or top_choice_e(val)):
        val = ('bin', '+', val, ('choice', [('lit', R.randint(0, 3)), leaf(scope, vars_)]))
        PROD[0] *= 2
    f = {'name': f"M{i}", 'params': params, 'decides': decides, 'stmts': stmts, 'val': val,
         'count': PROD[0], 'nctr': len(ctrs)}
    CTX.update(ctrs=None, nofail=False, fmax=None, plim=64)
    return f


def show_func(f):
    ps = ", ".join(f"{p}:{t}" for p, t in f['params'])
    L = [f"{f['name']}({ps}){'<decides>' if f['decides'] else ''}:int ="]
    L += ["    " + show_s(c) for c in f['stmts']]
    L.append("    " + show(f['val']))
    return L


lines = []
out = []
tests = []
OVERFLOW = [False]
SKIPRET = [False]
if REC:
    lines += ["CTw(A:int, B:int)<computes>:int = A * 10 + B",
              "CPos(X:int)<computes><decides>:int =", "    X > 0", "    X"]
    for i in range(R.randint(1, 3)):
        f = gen_rfunc(i)
        f['idx'] = i
        RFUNCS.append(f)
        RUB.clear()
        if rub(i, 3) > 200:   # (keep the arrays small)
            pass
    for f in RFUNCS:
        lines += show_rfunc(f)
if LAZY:
    for i in range(R.randint(1, 3)):
        GFUNCS.append(gen_gfunc(i))
    # (#371: a pair of compatible generators call each other: the same parameters, failing or
    # not, with or without effects, run apart or not where the first success is taken)
    def retarget(f, j):
        v = f['val']
        fix = lambda alts: [('gself', j, a[2]) if a[0] == 'gself' else a for a in alts]
        f['val'] = ('gchoice', fix(v[1])) if v[0] == 'gchoice' else ('gbif', v[1], fix(v[2]), fix(v[3]))
    pairs = [(a, b) for a in range(len(GFUNCS)) for b in range(a + 1, len(GFUNCS))
             if all(GFUNCS[a][x] == GFUNCS[b][x] for x in ('decides', 'ctr', 'first_ok', 'lifted'))]
    if pairs and R12.random() < 0.8:
        a, b = R12.choice(pairs)
        retarget(GFUNCS[a], b)
        retarget(GFUNCS[b], a)
    for f in GFUNCS:
        lines += show_gfunc(f)
if MV:
    for i in range(R.randint(1, 4)):
        FUNCS.append(gen_func(i))
    for f in FUNCS:
        lines += show_func(f)
NT = R.randint(2, 5)
for ti in range(NT):
    name = f"T{ti}"
    NCH[0] = 0
    PROD[0] = 1
    FXFIRST[0] = 0
    vars_ = [f"N{ti}a", f"N{ti}b"]
    st = St()
    st.vars = {v: 0 for v in vars_}
    st.vars['K.C'] = 0
    st.vars['J.C'] = 0
    meth = METH and R.random() < 0.4
    if meth:
        ovr, priv = R.random() < 0.5, R.random() < 0.5
        SNX['inc'] = 2 if ovr else 1
        SNX['ovm'] = MVM and R4.random() < 0.5
        st.vars['S.Cn'] = 0
    CTX['meth'] = meth
    CTX['mvm'] = (ti, f"N{ti}a")
    CTX['mvm_used'] = False
    CTX['mvm_const'] = R.random() < 0.5
    L = [f"{name}():void ="]
    for v in vars_:
        L.append(f"    var {v}:int = 0")
    L.append("    K := ctr{}")
    L.append("    J := ctr{}")
    L.append("    var A:[]int = array{0, 0, 0, 0}")
    L.append("    var F:float = 1.0")
    kind = R.choice(['if', 'if', 'for', 'for', 'first', 'formacro', 'ifmacro', 'option', 'logic', 'not', 'or'])
    isfor = kind in ('for', 'formacro')
    CTX['take'] = 'for' if isfor else 'first'
    n = R.randint(1, 4)
    lastval = kind in ('first', 'formacro', 'ifmacro', 'option', 'or')
    cl, scope = gen_clauses([], vars_, 0, n, allow_gen=isfor, lastval=lastval, isfor=isfor)
    if isfor and RT2 and R11.random() < 0.2:
        # (one exclusive choice, then a composed one: two constructs, as small as can be)
        comp = ('choice', [('tell', fresh("t"), leaf([], vars_)),
                           ('bin', '+', ('choice', [leaf([], vars_), leaf([], vars_)]), leaf([], vars_))])
        cl = [('bind', fresh("X"), (R11.choice(['rt2', 'rt3']), leaf([], vars_))), ('bind', fresh("X"), comp)] + cl
    if ALTCH and ((not isfor and R5.random() < 0.35) or (isfor and R6.random() < 0.35)):
        two = []
        for _ in range(2):
            alt1 = ('tell', fresh("t"), leaf([], vars_))
            alt2 = ('bin', '+', ('choice', [leaf([], vars_), leaf([], vars_)]), leaf([], vars_))
            two.append(('bind', fresh("X"), ('choice', [alt1, alt2])))
        cl = two + cl
    if kind not in ('for', 'formacro', 'option'):
        cl.append(('filter', ('cmp', leaf(scope, vars_), [(R.choice(OPS), leaf(scope, vars_))])))
    if not any(top_choice_c(c) for c in cl):
        # make sure there is a choice inside an expression, lifted at the top
        x = fresh("X")
        e = ('bin', '+', ('tell', fresh("t"), leaf([], vars_)), ('choice', [('lit', 1), ('lit', 2)]))
        cl.insert(0, ('bind', x, e))
        scope = [x] + scope
    has_ret = False
    if RET and kind in ('if', 'for') and R.random() < 0.35:
        # where: before the first clause with a lifted call (it runs), or, at
        # times, after one whose call is at the clause's top (refused, #287)
        lp = [lift_pos(c) if kind == 'if' else None for c in cl]
        j = next((i for i, x in enumerate(lp) if x), len(cl))
        if j < len(cl) and lp[j] == "top" and R.random() < 0.4:
            pos = R.randint(j + 1, len(cl))
            REFUSED[0] = True
        else:
            pos = R.randint(0, j)
        sc = [c[1] for c in cl[:pos] if c[0] in ('bind', 'range')]
        cl.insert(pos, ('ret', ('cmp', leaf(sc, vars_), [(R.choice(OPS), leaf(sc, vars_))])))
        has_ret = True
    show_state = ('Print("st {' + vars_[0] + '} {' + vars_[1] + '} {K.C} {J.C} '
                  '{A[0] or 9}{A[1] or 9}{A[2] or 9}{A[3] or 9} {F}' + (' {Cn}' if meth else '') + '")')

    def state_line(s):
        return (f"st {s.vars[vars_[0]]} {s.vars[vars_[1]]} {s.vars['K.C']} {s.vars['J.C']} "
                + "".join(str(x) for x in s.A) + " " + fmt_float(s.F) + (f" {s.vars['S.Cn']}" if meth else ""))

    def as_method(L):
        """the test as the method Run of a class of its own, its vars fields."""
        if not meth:
            return L
        split = CTX.get('mvm_used') and SNX['ovm']     # (#328: Run in a parent class)
        top = f"{name}b" if split else f"{name}c"
        M = [f"{top} := class(tbase):", f"    var {vars_[0]}:int = 0",
             f"    var {vars_[1]}{'<private>' if priv else ''}:int = 0"]
        if ovr and not split:
            M += ["    Nx<override>()<transacts>:int =", "        set Cn += 2", "        Cn - 2"]
        if CTX.get('mvm_used'):
            M.append(f"    Hp{ti}(Hq{ti}:int):int = Hq{ti} * 2")
            M.append(f"    Mv{ti}(Mp{ti}:int):int = Mp{ti} + Nx() | Mp{ti} + Hp{ti}(N{ti}a)")
        M.append("    Run():void =")
        M += ["    " + l for l in L[3:]]
        if split:
            M.append(f"{name}c := class({name}b):")
            if ovr:
                M += ["    Nx<override>()<transacts>:int =", "        set Cn += 2", "        Cn - 2"]
            M.append(f"    Mv{ti}<override>(Mp{ti}:int):int = Mp{ti} * 3 | (super:)Mv{ti}(Mp{ti}) | Mp{ti} - 1")
        M.append(f"{name}():void = {name}c{{}}.Run()")
        if CTX.get('mvm_used') and CTX.get('mvm_const'):
            M.insert(0, f"N{ti}a:int = {100 + ti}")    # (a constant named like the field)
        return M
    binds = [c[1] for c in cl if c[0] in ('bind', 'range', 'sbind')]
    vals_str = " ".join("{" + b + "}" for b in binds)

    def vals(s):
        return " ".join(str(s.binds[b]) for b in binds)
    tout = []
    body_first = lambda s2: s2
    try:
        if kind == 'if':
            L.append(f"    if ({show_cl(cl, ', ')}):")
            L.append(f'        Print("then {vals_str}")')
            L.append("    else:")
            L.append('        Print("else")')
            try:
                res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
                if res is not None:
                    st = res[1]
                    st.out.append(f"then {vals(st)}")
                else:
                    st.out.append("else")
            except Return as r:
                st = r.st
        elif kind in ('first', 'ifmacro', 'option', 'or'):
            body = show_cl(cl, '; ')
            if kind == 'first':
                L.append(f'    if (V := first{{{body}}}) then Print("first {{V}}") else Print("none")')
            elif kind == 'ifmacro':
                L.append(f'    V := if{{{body}}} else -7')
                L.append('    Print("v {V}")')
            elif kind == 'option':
                L.append(f'    O := option{{{body}}}')
                L.append('    if (V := O?) then Print("o {V}") else Print("o none")')
            else:
                L.append(f'    W := ({body}) or -7')
                L.append('    Print("w {W}")')
            res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(clause_value(cl, s2), s2), 'first'), st)
            if res is not None:
                v, st = res
                st.out.append({'first': f"first {v}", 'ifmacro': f"v {v}", 'option': f"o {v}", 'or': f"w {v}"}[kind])
            else:
                st.out.append({'first': "none", 'ifmacro': "v -7", 'option': "o none", 'or': "w -7"}[kind])
        elif kind == 'logic':
            L.append(f"    Lg := logic{{{show_cl(cl, '; ')}}}")
            L.append('    if (Lg?) then Print("l true") else Print("l false")')
            res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
            if res is not None:
                st = res[1]
                st.out.append("l true")
            else:
                st.out.append("l false")
        elif kind == 'not':
            L.append(f"    if (not ({show_cl(cl, '; ')})) then Print(\"not ok\") else Print(\"not fail\")")
            res = first_inner(lambda s, kk: run_clauses(cl, s, lambda s2: kk(None, s2), 'first'), st)
            st.out.append("not fail" if res is not None else "not ok")
        elif kind == 'for':
            L.append(f"    for ({show_cl(cl, ', ')}):")
            L.append(f'        Print("body {vals_str}")')

            def fbody(s):
                s.out.append(f"body {vals(s)}")
                return s
            s0 = st.copy()
            try:
                st = run_clauses(cl, s0, fbody, 'all')
            except Fail:
                pass
            except Return as r:
                st = r.st
        else:  # formacro
            last = cl[-1]
            L.append(f"    Vs := for{{{show_cl(cl, '; ')}}}")
            L.append('    for (V : Vs) { Print("e {V}") }')
            vs = []

            def fbody2(s):
                vs.append(clause_value(cl, s))
                return s
            s0 = st.copy()
            try:
                st = run_clauses(cl, s0, fbody2, 'all')
            except Fail:
                pass
            st.out += [f"e {v}" for v in vs]
    except StOverflow as ov:
        # (the program stops in this test: the later ones never run)
        if has_ret:
            SKIPRET[0] = True    # (whether its defer runs then is not modelled)
        L.append("    " + show_state)
        lines += as_method(L)
        tests.append(name)
        out += [f"== {name}"] + ov.st.out
        OVERFLOW[0] = True
        break
    if has_ret:
        L[7:7] = ["    defer:", "        " + show_state]     # (after F's declaration)
    else:
        L.append("    " + show_state)
    tout = st.out + [state_line(st)]
    lines += as_method(L)
    tests.append(name)
    out += [f"== {name}"] + tout

src_main = ["Main():void ="] + [f'    Print("== {n}")\n    {n}()' for n in tests]
if METH:
    PRE += """tbase := class:
    var Cn:int = 0
    Nx()<transacts>:int =
        set Cn += 1
        Cn - 1
"""
if RT:
    PRE += ('RT(RTa:int):int =\n    RTy := RTa | RTa + 1 | RTa + 2\n    Print("p{RTy}")\n    if (RTy = RTa + 1):\n'
            '        Print("rt")\n        return 99\n    else:\n        RTd := RTy * 2\n'
            '        Print("e{RTd}")\n    RTd := RTy * 10\n    RTd\n')
if RT2:
    for nm, ret in (('RT2', '99 | 98'), ('RT3', '99')):
        PRE += (f'{nm}(RTa:int):int =\n    RTy := RTa | RTa + 1 | RTa + 2\n    Print("p{{RTy}}")\n'
                f'    if (RTy = RTa + 1):\n        Print("rt")\n        return {ret}\n    else:\n'
                f'        Print("e{{RTy}}")\n    Print("q{{RTy}}")\n    RTy * 10 | RTy * 10 + 1\n')
if NAM:
    PRE += 'NAM(NU:int, ?NV:int = Tell("dv", NU)):int = NU + NV | NV * 2\n'
if NA:
    PRE += 'NA(A:int, ?P:int = Tell("dp", A), ?Q:int = P + 1):int = A * 100 + P * 10 + Q\n'
if CB:
    PRE += "pt := struct:\n    X:int = 0\n    Y:int = 0\nPS(P:pt)<computes>:int = P.X * 10 + P.Y\n"
if LAZY:
    PRE = PRE.replace("Pos(X:int)<decides>", "Pos(X:int)<computes><decides>").replace(
        "Even(X:int)<decides>", "Even(X:int)<computes><decides>").replace("Tw(A:int, B:int):int", "Tw(A:int, B:int)<computes>:int")
open(f"{outdir}/p.verse", "w").write(PRE + "\n".join(lines) + "\n" + "\n".join(src_main) + "\n")
open(f"{outdir}/p.chain", "w").write("1" if CHAIN[0] else "0")
if os.environ.get('MVSTATS'):
    print(f"stats gens={len(GFUNCS)} gfor={STATS['gfor']} gfirst={STATS['gfirst']} gback={STATS['gback']} lfirst={STATS['lfirst']} lback={STATS['lback']} lmeth={STATS['lmeth']}", file=sys.stderr)
if SKIPRET[0]:
    open(f"{outdir}/p.expected", "w").write("SKIP (a return in a test that overflows)\n")
elif REFUSED[0]:
    open(f"{outdir}/p.expected", "w").write("exit=4\n")
else:
    open(f"{outdir}/p.expected", "w").write("".join(l + "\n" for l in out) + ("exit=2\n" if OVERFLOW[0] else "exit=0\n"))
