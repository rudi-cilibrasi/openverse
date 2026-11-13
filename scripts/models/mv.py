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
# methods with several values from #310 (overridden from #328, of one name in unrelated classes from #283's
# shared families), returns in functions with several values from #312,
# and a choice after such a return's if, or in its value, from #318;
# return frames (a recursive call with code after it) from #283, and a generator's call of itself
# in a failure context of its own code (a consumer of it there) from #283's nested consumers.
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
       noshared  (no program whose tests' methods with several values all have one
                  name, which mvm and meth give at times otherwise, #283)
       nonam     (no call of NAM(NU, ?NV := …), a function with several values and a
                  named parameter whose default prints; on with lazy otherwise)
       nona      (no call of NA(A, ?P := …, ?Q := …) with named arguments in a test's
                  expressions, #305; on with lazy otherwise)
       nocb      (no block{B := e1; e2} or construction pt{Y := e2, X := e1} in a
                  test's expressions, #302; on with lazy otherwise)
       noaltch   (no alternative of a choice with several values of its own: a
                  choice, a call of a function with several values or of a
                  generator, #296; on with lazy otherwise)
       retdefer-control (emit an equivalent pre-change layout of returning
                  cleanup scopes, with the same independent trace oracle)
       (a branchy generator's base branch is at times one if with a print in its
                  condition, a value whose condition is undone with it, #283)
       noframes  (no return frame: a generator's call of itself with code after
                  it, or its choice bound with plain code after it, #283; on with
                  lazy otherwise)
       noseq     (no choice points in sequence in a generator: a call of itself
                  followed by a choice or by another call, a choice followed by a
                  call, a choice bound in a branch with code after it, #283; on
                  with frames otherwise)
       notyped   (no choice of strings in a generator with a choice point after it,
                  #283; on with seq otherwise)
       noenter   (no alternative, one of several, with code before a choice in it,
                  #283; on with seq otherwise)
       nolifted  (no call of a generator of itself where the lifter takes it, after
                  its bound choice: a named argument, a construction's field, a
                  comparison's later operand, a set's value, an if's branch, or's
                  right, #283; on with seq otherwise)
       nonested  (no call of a generator of itself in a failure context of its own
                  code, which consumes it: an if's condition, or's left, option{},
                  not, logic{}, a for, #283; on with seq otherwise)
       noother   (no call of another function with several values as a choice point in a
                  generator's code: Oxv, Oyv, or another generator, #283; on with seq
                  otherwise)
       nocls     (no call of a generator of itself in a field of a class's construction,
                  ocls{A := …, B := …}, whose superclass's field B is evaluated first,
                  #283; on with seq otherwise)
       noovw     (no overloads Ow of one name with one value or several, OwOne calling
                  the one with one value, OwR recursive, owc/owd's overloaded method Om,
                  #283's overloads picked in rounds; on in half the programs otherwise)
       noovm     (no second list, of one value, of a test's class's method with several
                  values; on in half the programs with mvm and meth otherwise)
       nohm      (no test HetMethods: methods of one name of unrelated classes, called on the
                  value of a choice whose alternatives are of those classes, #283, #335; on in
                  a third of the programs otherwise)
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
    if exc_type.__name__ == 'ModelBudget':
        open(f"{outdir}/p.verse", "w").write("Main():void = {}\n")
        open(f"{outdir}/p.expected", "w").write(f"SKIP long ({exc})\n")
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


class ForBodyFail(Exception):
    """(#283) a for's body failed: the for fails, not only that iteration."""


# (a path that prints over OUT_MAX lines, a model that takes over EV_MAX steps, or one that
# copies over WORK_MAX entries with its states (each choice point copies the path's output):
# the program would print more than the driver's 12000 lines, or the model would run for
# minutes. Without a bound it copied an ever longer output at each choice point, for hours
# at seed 770157 in bif mode. Marked SKIP long, which the driver skips as over 12000 lines.)
OUT_MAX = 12000
EV_MAX = 10_000_000
EV_STEPS = [0]
WORK_MAX = 5_000_000_000
WORK = [0]


class ModelBudget(Exception):
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
        if len(self.out) > OUT_MAX:
            raise ModelBudget(f"a path prints over {OUT_MAX} lines")
        WORK[0] += len(self.out) + len(self.vars) + len(self.binds)
        if WORK[0] > WORK_MAX:
            raise ModelBudget(f"over {WORK_MAX} entries copied with states")
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
# of its own, #275), a return now uses an explicit source exit. The legacy
# refusal flag preserves older source/oracle pairs for baseline controls.
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
# Recursive tuple spelling changes only argument grouping. The CPS model
# still evaluates the same arguments once, left to right, on self/mutual edges.
RRecursiveTuple = random.Random(seed * 1000003 + 246140)
# ---- #328 (with mvm): at times the test's class overrides Mv with several values of its own,
#   MvT<override>(MpT:int):int = MpT * 3 | (super:)MvT(MpT) | MpT - 1
# Run, the fields and the base MvT are then in a parent class, so the bare MvT(..) in Run
# dispatches on Self, the test's class: the override's alternatives, the middle one the base's
# two. A second generator decides, so seeds keep their other choices.
R4 = random.Random(seed * 1000003 + 328)
# ---- #372 (#283): at times (with mvm) an interface declares Mv, i<T> := interface: MvT(MpT:int):int,
# and the class that gives it Run implements it, so the bare MvT(..) dispatches from the interface,
# the family's root. The output is the same. A generator of its own decides, so seeds keep the rest.
R13 = random.Random(seed * 1000003 + 372)
# ---- #375 (#283): at times (with mvm) the interface gives Mv a default with several values,
#   i<T> := interface: MvT(MpT:int):int = MpT * 5 | MpT + 7
# and the class that gives Run has no MvT of its own: a bare MvT(..) gets the default, and an
# override in a subclass (#328) reaches it with (super:). Its own generator decides, before the
# test runs (it changes the values); the interface form is then taken whatever R13 draws.
R14 = random.Random(seed * 1000003 + 375)
# ---- #380 (#283): at times a test's expression calls Ov, overloaded by arity and by type, each
# overload with several values:
#   Ov(OA:int):int = OA + 1 | OA * 2
#   Ov(OA:int, OB:int):int = OA - OB | OB * 3
#   Ov(OS:string):int = OS.Length | 0          (called with a string literal)
# The arguments pick the overload; they run once, left to right, before its choice, and each
# alternative is a value. A generator of its own decides, so seeds keep their other programs.
R15 = random.Random(seed * 1000003 + 380)
OVL = 'noovl' not in flags and R15.random() < 0.5
# ---- #283's overloads picked in rounds: at times overloads of one name where some have one value
# and others several, a function calling only one with one value, one calling its own name, a
# recursive one calling an overload, and an overloaded method with several values:
#   Ow(OA:int)<computes>:int = OA * 5                         (one value)
#   Ow(OS:string)<computes>:int = OS.Length | 9               (called with a string literal)
#   Ow(OA:int, OB:int)<computes>:int = Ow(OA) | Ow("{OB}")    (its own name: OA * 5, then the
#                                                               length of OB written, its sign too, then 9)
#   OwOne(OA:int)<computes>:int = Ow(OA) + 1                  (one value, so also outside a failure
#                                                               context: Main prints one first)
#   OwR(N:int)<computes><decides>:int = (N > 0; Ow(N, N) | OwR[N - 1])
#                                                             (recursive, so computed at the call)
#   owc := class: Om()<computes>:int = 3 | 6, Om(X:int)<computes>:int = X + 3
#   owd := class(owc): Om<override>()<computes>:int = 103 | (super:)Om()
# A call takes the overload its arguments fit; they run first, left to right. A generator of its
# own decides, so seeds keep their other programs.
R19 = random.Random(seed * 1000003 + 569)
OVW = 'noovw' not in flags and R19.random() < 0.5
# ---- the same (with mvm and meth; noovm turns it off): at times a test's class whose method with
# several values its test calls (#310, MvT, or Mv when they share the name) also declares it with
# another list, of one value, MvT(MpT:int, MqT:int):int = MpT * 10 + MqT, which the test calls at
# times, bare or through Self. A call of either then takes its list first (then its family, when
# the classes share the name). A generator of its own decides, so seeds keep their other programs.
R20 = random.Random(seed * 1000003 + 5690)
OVM = METH and MVM and 'noovm' not in flags and R20.random() < 0.5
# ---- #383 (#283): at times a branch of a branchy if is a block whose bound value has several
# values, a choice or a call with several values, and whose value uses the bound name:
#   if (…) then block{ BT := (a | b); BT + e } else …
# The block's name is its own (fresh, so it shadows nothing and is not seen after the if). Its
# choice is a generator as a branch's is (#360); the if adds none (#331). A generator of its own
# decides, so seeds keep their other programs.
R16 = random.Random(seed * 1000003 + 383)
# ---- #391 (#283): at times a function with several values (mv mode) has a defer: of its own
# that prints, just before its value: it runs as each value leaves the function, after the value is
# computed and before the caller's clauses after it; a value whose clauses fail rolls it back with
# the rest of its effects. A generator of its own decides, so seeds keep their other programs.
R17 = random.Random(seed * 1000003 + 391)
# ---- #283 (with mvm and meth; noshared turns it off): at times the tests' methods with several
# values all have one name, Mv, instead of MvT: each test's class (or interface) declares it apart,
# the root of a family of its own, and a call's receiver picks the family. A call is bare, as
# before, or through Self, both of the enclosing class, or through MeT, a local of the class Run
# is in (or of the interface) bound to Self, whose family only its type tells: the same values
# either way. An unrelated class has an ordinary Mv,
#   pmv := class: Mv(Mp:int):int = Mp * 1000
# called at times on a new pmv in a test that runs as a method: one value, its argument's times
# 1000, with nothing to undo. A generator of its own decides, so seeds keep their other programs.
R18 = random.Random(seed * 1000003 + 2833)
SHARED = METH and MVM and 'noshared' not in flags and R18.random() < 0.4
# ---- #283, #335 (nohm turns it off): at times a test of its own, HetMethods, after the others,
# calls Hm, a method of one name in two or three unrelated classes (each the root of a family of
# its own when Hm has several values there, or an ordinary method), on the value of a choice whose
# alternatives are of those classes, so the clauses after it are copied for each and the receiver's
# class picks the family (gen_hetero_methods). A generator of its own decides, and another makes
# the test, so seeds keep their other programs.
HM = 'nohm' not in flags and random.Random(seed * 1000003 + 283335).random() < 0.34
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
# Cleanup executes before each value leaves a returning scope. A branch
# that falls through cleans up once before the later choice; registrations
# after its returning path are reached only on fallthrough. Keep this draw
# independent of the expression generator and its existing seed streams.
RET_DEFER = RT2 and random.Random(seed * 1000003 + 283391).random() < 0.5
# ---- #283, with ret: at times the test's return is in a block of its own with a choice of its
# own and a defer: (its clauses lifted into the test's), returning on some of its values:
#   Xn := block{ defer: Print("rbN"); Wn := a | b; if (Wn op L) then return else true; Wn }
# The defer: runs as each value leaves the block, and at the return, which leaves it, before the
# test's own: LANGUAGE.md's rule for any scope, whether its clauses are lifted or not. A
# generator of its own decides, so seeds keep their other programs.
RRB = random.Random(seed * 1000003 + 283392)
# ---- #283, flag frames (on with lazy; noframes turns it off): a generator's call of
# itself may have code after it, which runs on each of the call's values (a return
# frame): an alternative `Gz0(N - 1, A) + e` (e any value, with no var), `L + Gz0(…)`
# (L a literal or name, read where it is written), or `Tell("fN", Gz0(…))`; and a
# <decides> one may bind its choice and have plain code after it,
#   Gz0(N:int, A:int)<decides>:int =
#       …clauses…
#       Wf := (A | Gz0(N - 1, A) | …)
#       Print("fN")         (statements with no var, set or choice)
#       Wf + A              (a value)
# which is the choice of `Wf := a; …; Wf + A` for each alternative a. The model is
# the same CPS inlining: the frame's code runs on each value as the caller's own
# code after the call returns it, so where a value is rejected what the frames did
# with it is undone with it (in a for: the frames are part of the value's segment,
# as the code after the last choice reached is). A generator of its own decides, so
# seeds keep their other programs.
RFR = random.Random(seed * 1000003 + 283283)
# ---- #283: at times a branchy generator's base branch is one value that is an if with a
# print in its condition, `if (N <= 1) then ((if (Print("frN"), A > k) then x else y)) else …`:
# that if is the value (it has no choice), so its condition runs with the value and is undone
# with it where the consumer rejects it, as any value's code is. A stream of its own, so seeds
# without it keep their programs.
RIFV = random.Random(seed * 1000003 + 283284)
RPRE = random.Random(seed * 1000003 + 283285)
# ---- #283: at times the code after a bound choice sets a var of the generator (`set V += Wf`)
# and its value reads it: every later value and alternative sees what a kept value set, a
# rejected one's write is undone; a stream of its own.
RVAR = random.Random(seed * 1000003 + 283286)
# ---- #283, flag seq (on with frames; noseq turns it off): choice points in sequence in a
# generator, a stream of its own, applied to a generator once it is made, so seeds where it does
# not fire keep their programs: a call of itself followed by another, `Gz0(N - 1, A) + Gz0(N - 1, 2)`;
# a <decides> one's bound choice with a choice after it, `Wf := (A | Gz0[N - 1, A]); …; (Wf | Wf + 2)`,
# or with values only and a call after it, `Wf := (1 | A); …; (Gz0[N - 1, Wf] + Wf | N)`, or a call
# bound after it, `Wq := Gz0[N - 1, Wf]`; and a choice bound in a branchy one's else, with code after
# it, `else: Wb := (…); …; Wb + 1` (a `gblk`). The model is the same CPS inlining: the code after a
# choice point runs on each of its values, the code before the next one once for each of them.
RSEQ = random.Random(seed * 1000003 + 283287)
# ---- #283, flag typed (on with seq; notyped turns it off): a <decides> generator's bound choice
# of strings, `Ws := ("a" | "{Gz0[N - 1, A]}" | "bb")` (a call of itself in it, whose value the
# string's code takes), with a choice point after it that reads `Ws.Length`, and an alternative
# with a choice of strings in its expression, `(("a" | "bb").Length + 2)`: the code after a choice
# whose values are not the generator's type; a stream of its own.
RTY = random.Random(seed * 1000003 + 283288)
# (and at times an empty string in place of one of those literals, `("" | "bb")`, `("" | "")`,
# which has no type of its own in Verse Core: a stream of its own, drawn after RTY's, so that a
# program is RTY's but for its empty strings)
REMPTY = random.Random(seed * 1000003 + 283293)
# ---- #283, flag enter (on with seq; noenter turns it off): an alternative, one of several, with
# code before a choice in it, `Tell("sqN", 2) + (Gz0(N - 1, A) | 3)`: that code runs after the
# generator's choice point and before the alternative's own, once for each time the alternative
# is taken; a stream of its own.
RENT = random.Random(seed * 1000003 + 283289)
# ---- #283, flag lifted (on with seq; nolifted turns it off): after a generator's bound choice,
# a statement with a call of itself where the lifter takes it. In a <decides> one's, guarded by N
# so that its calls end: `or`'s right, `Wl := (N = 0 or Gz0[N - 1, A] > 1)`, a comparison's
# later operand in it, `Wl := (N = 0 or 5 > Gz0[N - 1, A])`, an `if`'s branch, `Wl := (if (N > 0)
# then Gz0[N - 1, A] else (1 | 5))`. In the block of another's else: a named argument,
# `Wl := NA(N, ?P := Gz0(N - 1, A))`; a construction's field, in its type's order whatever the
# written one, `Wl := PS(pt{Y := Gz0(N - 1, A), X := 2})`; `set Vl += Gz0(N - 1, A)`, its old
# value read before the call, or `set Vl = Gz0(N - 1, A) + Vl`; an `if`'s branch. A stream of
# its own.
RLIFT = random.Random(seed * 1000003 + 283292)
# ---- #283, flag nested (on with seq; nonested turns it off): a call of a generator of itself in a
# failure context of its own code, which consumes it there, taking its first success (or a for all
# its values) while the generator's own values are taken: an if's condition, `Wn := (if (N > lo,
# Gz[N - 1, a] > k) then x else y)`; or's left, `Wn := (Gz[N - 1, a] > k or x)`; option{},
# `Wn := (option{Gz[N - 1, a] > k}? or x)`; in a <decides> one, not and logic{} as clauses,
# `not (Gz[N - 1, a] > k)`, `logic{Gz[N - 1, a] > k}?`; and a for over its values that sets a var
# of the generator, `for (N > lo, Xn := Gz[N - 1, a]) { set Vn += Xn }`, in a <decides> one at times
# with a body that may fail, `{ set Vn += Xn; Xn < k }`, which fails the for. Its place: the code after
# the generator's bound choice (a <decides> one's), or after the choice bound in its else's block,
# whose value then reads the result, with that choice's name at times in the call; or its clauses,
# before its choice, guarded by N so that its calls end (an if with a print in each branch, or a
# for with one in its body). The model is the same CPS: the context runs the call as it would
# anywhere, each call's code taking its own in turn. A stream of its own.
RNEST = random.Random(seed * 1000003 + 283293)
# ---- #283, flag other (on with seq; noother turns it off): a call of another function with several
# values as a choice point in a generator's code, alone as an alternative of its choice or after a
# call of itself (`Gz0(N - 1, 2) + Oyv(A)`): Oxv, <decides>, whose clauses print and may fail,
#   Oxv(OxA:int)<transacts><decides>:int =
#       Print("ox {OxA}")
#       OxA > 0
#       OxA | OxA + 3
# (in a <decides> generator), Oyv(OyA:int)<transacts>:int = Tell("oy", OyA) | OyA + 3, or an earlier
# generator. The callee is taken with the generator, a choice point as a call of the generator is:
# in a for, when its clauses fail it has no values and what came before the call stays, as at a
# call of a generator (`gen_call`), not undone as at an inlined call. A stream of its own.
ROTH = random.Random(seed * 1000003 + 283294)
# ---- #283, flag cls (on with seq; nocls turns it off): in the block of a generator's else, a call
# of itself in a field of a class's construction, `Wc := OC(ocls{A := …, B := …})` with
#   obase := class:  B:int = 0
#   ocls := class(obase):  A:int = 0
#   OC(P:ocls)<computes>:int = P.A * 10 + P.B
# whose fields are evaluated in its order, the superclass's B first, whatever the written one. A
# stream of its own.
RCLS = random.Random(seed * 1000003 + 283295)
OTHERS = set()
USES_CC = [False]
SQN = [0]
USED = set()     # (generator, in a for): the calls the tests make, for MVSEQ's statistics
FRN = [0]


def sqfresh():
    """a name for a print of the choice points in sequence, a counter of its own (#283)."""
    SQN[0] += 1
    return f"sq{SQN[0]}"


def ffresh():
    """a name for a frame's print, from a counter of its own (#283)."""
    FRN[0] += 1
    return f"fr{FRN[0]}"
FRAMES = LAZY and 'noframes' not in flags and 'cf' not in flags
SEQ = FRAMES and 'noseq' not in flags
TYPED = SEQ and 'notyped' not in flags
ENTER = SEQ and 'noenter' not in flags
LIFTED = SEQ and 'nolifted' not in flags
NEST = SEQ and 'nonested' not in flags
OTHER = SEQ and 'noother' not in flags
CLS = SEQ and 'nocls' not in flags
REFUSED = [False]


class Return(Exception):
    def __init__(self, st):
        self.st = st


# the kinds of node whose insides are failure contexts of their own (or an
# inlined function's arguments), where a lifted call's clauses are not the test's
NESTED = ('not', 'logic', 'optor', 'orx', 'ifx', 'bif', 'mcall', 'choice', 'blk', 'cons', 'ccons', 'na', 'nam', 'mvm', 'rt', 'rt2', 'rt3', 'ovl',
          'ow2')


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
SNX = {'inc': 1, 'ovm': False, 'dflt': False}
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


def mvm_ok(ch):
    """whether a call of the test's class's own method with several values may be here
    (its values' count aside, `mvm_fits`)."""
    return (MVM and CTX.get('meth') and METH and ch and NCH[0] < 4 and CTX['fmax'] is None
            and not CTX['nochoice'] and not CTX.get('inset') and not CTX.get('inbif'))


def mvm_fits():
    return not MV or PROD[0] * 2 <= CTX['plim']


def gen_mvm(scope, vars_, d, ch):
    if OVM and R20.random() < 0.35:
        # (the method's other list, of one value: an ordinary call, after its arguments)
        CTX['mvm_used'] = True
        return ('mvm2', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch), CTX['mvm'],
                R20.choice(['bare', 'self']))
    NCH[0] += 1
    if MV:
        PROD[0] *= 2
    CTX['mvm_used'] = True
    arg = ('ref', CTX['mvm'][1]) if R.random() < 0.4 else gen_e(scope, vars_, d + 1, ch)
    # (#283: in a program whose methods share a name, through a receiver at times)
    form = R18.choice(['bare', 'self', 'me']) if SHARED else 'bare'
    if form == 'me':
        CTX['mvm_me'] = True
    return ('mvm', arg, CTX['mvm'], form)


def gen_e(scope, vars_, d, ch):
    """an int expression; ch: whether a choice may be inside (liftably)."""
    if CTX['nochoice']:
        ch = False
    # (#283: in a program whose methods share a name, such calls more often)
    if SHARED and mvm_ok(ch) and mvm_fits() and R18.random() < 0.2:
        return gen_mvm(scope, vars_, d, ch)
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
    if (OVL and ch and NCH[0] < 4 and CTX['fmax'] is None and not CTX['nochoice']
            and not CTX.get('inset') and not CTX.get('inbif') and R15.random() < 0.1
            and (not MV or PROD[0] * 2 <= CTX['plim'])):
        NCH[0] += 1
        if MV:
            PROD[0] *= 2
        kind = R15.choice([1, 2, 's'])
        if kind == 's':
            return ('ovl', 's', [], R15.choice(['', 'a', 'xyz', 'hello']))
        return ('ovl', kind, [gen_e(scope, vars_, d + 1, ch) for _ in range(kind)], None)
    if (OVW and CTX['fmax'] is None and not CTX.get('inset') and not CTX.get('inbif')
            and R19.random() < 0.1):
        kind = R19.choice(['owone', 'ow1', 'om1', 'ows', 'ow2', 'om', 'owr'])
        if kind in ('owone', 'ow1', 'om1'):
            return (kind, gen_e(scope, vars_, d + 1, ch))     # (one value)
        n = 6 if kind == 'owr' else 3
        if ch and NCH[0] < 4 and not CTX['nochoice'] and (not MV or PROD[0] * n <= CTX['plim']):
            NCH[0] += 1
            if MV:
                PROD[0] *= n
            if kind == 'ows':
                return ('ows', R19.choice(['', 'a', 'xyz']))
            if kind == 'ow2':
                return ('ow2', gen_e(scope, vars_, d + 1, ch), gen_e(scope, vars_, d + 1, ch))
            if kind == 'om':
                return ('om', R19.choice(['c', 'd']))
            return ('owr', R19.randint(0, 2))
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
    if k < 0.48 and mvm_ok(ch) and R.random() < 0.9 and mvm_fits():
        return gen_mvm(scope, vars_, d, ch)
    if SHARED and CTX.get('meth') and CTX['fmax'] is None and R18.random() < 0.06:
        return ('pmv', gen_e(scope, vars_, d + 1, ch))
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
    total = sum(ub_e(a, n) for a in alts)     # (the callee's, #371)
    if f.get('bound'):
        total *= ub_e(f['bound'][1], n) * ub_e(f['bound'][2], n)
    return total


def ub_e(e, n):
    """an upper bound of the number of values of e, code of a generator with N = n: a call of a
    generator (with N - 1) has its values, a choice its alternatives', anything else the product
    of its parts' (#283: so choice points in sequence multiply)."""
    if isinstance(e, tuple) and e and isinstance(e[0], str):
        if e[0] in ('gself', 'gcall'):
            return gub(e[1], n - 1)
        if e[0] == 'slet' and e[1] == 'Wl' and e[2][0] in ('orx', 'ifx'):
            # (#283, flag lifted: or's values its left's or its right's, an if's one branch's,
            # so that a call guarded by N, which ends, has a bound that does not)
            x = e[2]
            return ub_e(x[1], n) + ub_e(x[2], n) if x[0] == 'orx' else ub_e(x[2], n) + ub_e(x[3], n)
        if e[0] == 'choice':
            return sum(ub_e(a, n) for a in e[1])
        if e[0] == 'snest':
            # (#283, flag nested: a consumer, one value whatever its call's)
            return 1
        if e[0] == 'gx':
            # (#283, flag other: Oxv's or Oyv's two)
            return 2
        if e[0] == 'gblk':
            return sum(ub_e(a, n) for a in e[2]) * ub_e(e[3], n) * ub_e(e[4], n)
    if isinstance(e, (tuple, list)):
        r = 1
        for y in e:
            r *= ub_e(y, n)
        return r
    return 1


def frame_call(a):
    """the call of a generator in alternative a: the whole alternative, or the
    one in a return frame after it (#283), else None."""
    if a[0] == 'gself':
        return a
    if a[0] == 'bin':
        c = frame_call(a[2])
        return c if c is not None else frame_call(a[3])
    if a[0] == 'tell':
        return frame_call(a[2])
    return None


def frame_prefix(a):
    """what alternative a evaluates before the call in its return frame (#283),
    which runs with the call's arguments."""
    if a[0] == 'bin' and frame_call(a) is not None:
        if frame_call(a[2]) is None:
            return [a[2]] + frame_prefix(a[3])
        return frame_prefix(a[2])
    if a[0] == 'tell':
        return frame_prefix(a[2])
    return []


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
    USED.add((i, CTX['take'] == 'for'))
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
    # (#283: at times a var the code after a bound call sets, RVAR)
    want_var = dec and FRAMES and RVAR.random() < 0.3
    if want_var and not vs:
        stmts.append(('svar', 'Vk', ('lit', RVAR.randint(0, 3))))
        vs = vs + ['Vk']
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

    def simple():
        # (a literal or a name; RFR only, so seeds keep their other programs)
        return ('lit', RFR.randint(-1, 3)) if RFR.random() < 0.5 else ('ref', RFR.choice(sc))

    def framed(c):
        # (#283: code after the call, which runs on each of its values; no var
        # in it, which it would run on a copy of)
        k = RFR.random()
        if k < 0.3:
            f = ('bin', RFR.choice(['+', '-', '*']), c, simple())
        elif k < 0.5:
            f = ('bin', RFR.choice(['+', '*']), simple(), c)
        elif k < 0.7:
            f = ('tell', ffresh(), c)
        elif k < 0.85:
            f = ('bin', '+', ('tell', ffresh(), c), ('tell', ffresh(), simple()))
        else:
            f = c
        # (#283: what the alternative reads before the call that may not read
        # the same after it, a call that prints or changes an object, runs
        # once before it; a stream of its own)
        if RPRE.random() < 0.35:
            pre = ('cnext', 'C') if ctr and RPRE.random() < 0.5 else ('tell', ffresh(), simple())
            return ('bin', RPRE.choice(['+', '*']), pre, f)
        return f

    def alts(withself):
        out = [value() for _ in range(R.randint(1, 2))]
        if withself:
            for _ in range(R.choice([1, 1, 2])):
                out.insert(R.randint(0, len(out)), selfcall())
        if len(out) == 1 and not withself and R.random() < 0.5:
            out.append(value())
        if FRAMES and withself and RFR.random() < 0.5:
            out = [framed(a) if a[0] == 'gself' else a for a in out]
        return out
    if dec:
        f['val'] = ('gchoice', alts(True))
        if FRAMES and (want_var or RFR.random() < 0.3):
            # (#283: the choice bound, plain code after it, then a value)
            post = []
            for j in range(RFR.randint(0, 2)):
                k = RFR.random()
                if k < 0.4:
                    post.append(('sprint', ffresh()))
                elif k < 0.7:
                    post.append(('slet', f"Wp{j}", ('bin', RFR.choice(['+', '*']), ('ref', 'Wf'), simple())))
                elif ctr:
                    post.append(('snext', 'C'))
                else:
                    post.append(('sfilt', ('cmp', ('ref', 'Wf'), [(RFR.choice(['>', '<>']), ('lit', RFR.randint(-2, 2)))])))
            names = ['Wf'] + [c[1] for c in post if c[0] == 'slet']
            last = ('bin', RFR.choice(['+', '-', '*']), ('ref', RFR.choice(names)), simple())
            if vs and (want_var or RVAR.random() < 0.5):
                v = RVAR.choice(vs)
                post.append(('sset', v, '+=', ('ref', 'Wf')))
                last = ('bin', '+', ('ref', v), last)
            f['bound'] = ('Wf', post, ('tell', ffresh(), last) if RFR.random() < 0.3 else last)
    else:
        conds = [('filter', ('cmp', ('ref', 'N'), [('<=', ('lit', f['lo']))]))]
        # (a condition that always succeeds, so that N <= lo picks the base:
        # a print where the generator may print there)
        if fx and R.random() < 0.5:
            c2 = [('print', fresh("c"))]
            conds = c2 + conds if R.random() < 0.5 else conds + c2
        base = alts(False)
        if LAZY and RIFV.random() < 0.5:
            cond = [('print', ffresh()), ('filter', ('cmp', ('ref', 'A'), [(RIFV.choice(['>', '<']), ('lit', RIFV.randint(-1, 2)))]))]
            pick = lambda: ('lit', RIFV.randint(-1, 4)) if RIFV.random() < 0.5 else ('ref', RIFV.choice(['N', 'A']))
            base = [('ifx', cond, pick(), pick())]
        f['val'] = ('gbif', conds, base, alts(True))
    if SEQ:
        seq_shapes(f, i, sc, ctr)
    if TYPED:
        typed_shapes(f, i, sc, ctr)
    if ENTER:
        enter_shapes(f, i, sc, ctr)
    if LIFTED:
        lifted_shapes(f, i, sc, ctr, stmts)
    if NEST:
        nested_shapes(f, i, sc, ctr, stmts)
    if OTHER:
        other_shapes(f, i, sc, ctr)
    if CLS:
        class_shapes(f, i, sc, ctr)
    f['stmts'] = stmts
    f['lifted'] = lifted(f)
    CTX.update(ctrs=None, nofail=False, nochoice=False, noprint=False, fmax=None, take=None)
    return f


def seq_call(i, sc, ctr):
    """(#283) a call of generator i, of its own, its second argument a literal or one of the
    names `sc` (RSEQ)."""
    a = ('lit', RSEQ.randint(-1, 3)) if RSEQ.random() < 0.5 else ('ref', RSEQ.choice(sc))
    return ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else []))


def seq_shapes(f, i, sc, ctr):
    """(#283, flag seq) choice points in sequence in generator f, made already, from RSEQ alone:
    an alternative that calls itself followed by another call of itself; a <decides> one's bound
    choice followed by a choice, or made of values and followed by a call; a branchy one's else a
    block that binds a choice, with code after it."""
    v = f['val']
    small = lambda: ('lit', RSEQ.randint(0, 3))
    if RSEQ.random() < 0.3:
        alts = v[1] if v[0] == 'gchoice' else v[3]
        idx = [j for j, a in enumerate(alts) if frame_call(a) is not None]
        if idx:
            j = RSEQ.choice(idx)
            second = seq_call(i, sc, ctr)
            if RSEQ.random() < 0.4:
                second = ('tell', sqfresh(), second)
            alts[j] = ('bin', RSEQ.choice(['+', '-', '*']), alts[j], second)
            f['seq'] = f.get('seq', set()) | {'two-calls'}
    if f['decides'] and RSEQ.random() < 0.35:
        post0 = [('sprint', sqfresh())] if RSEQ.random() < 0.5 else []
        if RSEQ.random() < 0.5:
            # (a call followed by a choice)
            x, post, last = f.get('bound') or ('Wf', post0, ('ref', 'Wf'))
            f['bound'] = (x, post, ('choice', [last, ('bin', '+', ('ref', x), small())]))
            f['seq'] = f.get('seq', set()) | {'call-then-choice'}
        else:
            # (a choice before a call: the bound choice's alternatives are values)
            vals = [a for a in v[1] if frame_call(a) is None][:2]
            while len(vals) < 2:
                vals.append(small())
            v[1][:] = vals
            if RSEQ.random() < 0.5:
                last = ('choice', [('bin', '+', seq_call(i, sc + ['Wf'], ctr), ('ref', 'Wf')), ('ref', 'N')])
                post = post0
            else:
                post = post0 + [('slet', 'Wq', seq_call(i, sc + ['Wf'], ctr))]
                last = ('choice', [('bin', '+', ('ref', 'Wq'), ('ref', 'Wf')), ('ref', 'Wf')])
            f['bound'] = ('Wf', post, last)
            f['seq'] = f.get('seq', set()) | {'choice-then-call'}
    if not f['decides'] and RSEQ.random() < 0.3:
        # (a choice bound in the else branch, with code after it)
        post = [('sprint', sqfresh())] if RSEQ.random() < 0.5 else []
        r = RSEQ.random()
        if r < 0.4:
            last = ('bin', '+', ('ref', 'Wb'), small())
        elif r < 0.7:
            last = ('choice', [('ref', 'Wb'), ('bin', '*', ('ref', 'Wb'), small())])
        else:
            last = ('bin', '+', seq_call(i, sc + ['Wb'], ctr), ('ref', 'Wb'))
        f['val'] = ('gbif', v[1], v[2], [('gblk', 'Wb', v[3], post, last)])
        f['seq'] = f.get('seq', set()) | {'branch-block'}


def typed_shapes(f, i, sc, ctr):
    """(#283, flag typed) choices of strings in generator f, made already, from RTY alone: its
    bound choice of strings (a <decides> one), and an alternative with a choice of strings in
    its expression."""
    def call(a):
        return ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else []))
    def lit():
        s = RTY.choice(['a', 'bb', 'ccc', 'dddd'])
        return ('str', '' if REMPTY.random() < 0.3 else s)
    v = f['val']
    if f['decides'] and RTY.random() < 0.25:
        strs = [lit() for _ in range(RTY.randint(1, 2))]
        if RTY.random() < 0.5:
            strs.insert(RTY.randint(0, len(strs)), ('sfmt', call(('ref', RTY.choice(sc)))))
        v[1][:] = strs if len(strs) > 1 else strs + [lit()]
        post = [('sprint', sqfresh())] if RTY.random() < 0.6 else []
        n = ('slen', ('ref', 'Ws'))
        if RTY.random() < 0.5:
            last = ('choice', [('bin', '+', call(n), n), ('ref', 'N')])
        else:
            last = ('bin', '*', call(('ref', 'A')), n)
        f['bound'] = ('Ws', post, last)
        f['seq'] = f.get('seq', set()) | {'typed-choice'}
    if RTY.random() < 0.2:
        alts = v[1] if v[0] == 'gchoice' else v[3]
        # (in the generator's own choice, not in a bound one, whose values
        # the code after it takes)
        if alts and alts[0][0] != 'gblk' and not f.get('bound'):
            alts.insert(RTY.randint(0, len(alts)),
                        ('bin', '+', ('slen', ('choice', [lit(), lit()])), ('lit', RTY.randint(0, 3))))
            f['seq'] = f.get('seq', set()) | {'typed-expr'}


def enter_shapes(f, i, sc, ctr):
    """(#283, flag enter) an alternative, one of several, in generator f, made already, with code
    before a choice of its own (RENT alone): a call, then a choice of a call of itself or of
    values."""
    v = f['val']
    if RENT.random() < 0.25:
        alts = v[1] if v[0] == 'gchoice' else v[3]
        if alts and alts[0][0] != 'gblk' and not f.get('bound'):
            a = ('ref', RENT.choice(sc)) if RENT.random() < 0.5 else ('lit', RENT.randint(0, 3))
            inner = [('lit', RENT.randint(0, 4)), ('lit', RENT.randint(0, 4))]
            if RENT.random() < 0.6:
                inner[RENT.randint(0, 1)] = ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] +
                                             ([('ref', 'C')] if ctr else []))
            # (the code before the choice a call that prints, or one of a function with no effects,
            # which is still read once, before it)
            pre = (('tell', sqfresh(), ('lit', RENT.randint(1, 3))) if RENT.random() < 0.6 else
                   ('tw', ('lit', RENT.randint(0, 2)), a))
            alts.insert(RENT.randint(0, len(alts)), ('bin', RENT.choice(['+', '*']), pre, ('choice', inner)))
            f['seq'] = f.get('seq', set()) | {'enter'}


def lifted_shapes(f, i, sc, ctr, stmts):
    """(#283, flag lifted) after a generator's bound choice, a statement with a call of itself
    where the lifter takes it (RLIFT alone): in a <decides> one's, guarded by N so that the
    calls end (`or`'s right, a later comparison operand in it, an `if`'s branch); in the block of
    another's else, where N - 1 is at least its base's (a named argument, a struct's field, a
    `set`'s value, an `if`'s branch)."""
    v = f['val']
    blk = not f['decides'] and v[0] == 'gbif' and v[3] and v[3][0][0] == 'gblk'
    # (more often in an else's block, which is rarer)
    if RLIFT.random() >= (0.7 if blk else 0.25) or not (f['decides'] or blk):
        return
    a = ('ref', RLIFT.choice(sc)) if RLIFT.random() < 0.5 else ('lit', RLIFT.randint(0, 3))
    call = ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else []))
    lo = f['lo']
    other = (('lit', RLIFT.randint(0, 3)) if RLIFT.random() < 0.5 else
             ('choice', [('lit', RLIFT.randint(0, 3)), ('lit', RLIFT.randint(4, 7))]))
    if f['decides']:
        kind = RLIFT.choice(['cmp', 'if', 'or'])
        base = ('cmp', ('ref', 'N'), [('=', ('lit', lo))])
        if kind == 'cmp':
            # (N = lo or K > call: the call a comparison's later operand, in or's right)
            e = ('orx', base, ('cmp', ('lit', RLIFT.randint(1, 6)), [(RLIFT.choice(['>', '>=']), call)]))
        elif kind == 'or':
            e = ('orx', base, ('cmp', call, [(RLIFT.choice(['>', '>=']), ('lit', RLIFT.randint(0, 3)))]))
        else:
            e = (('ifx', [('filter', ('cmp', ('ref', 'N'), [('>', ('lit', lo))]))], call, other)
                 if RLIFT.random() < 0.5 else
                 ('ifx', [('filter', ('cmp', ('ref', 'N'), [('<=', ('lit', lo))]))], other, call))
        st = ('slet', 'Wl', e)
        x, post, last = f.get('bound') or ('Wf', [], ('ref', 'Wf'))
    else:
        kinds = (['na'] if NA else []) + (['cons'] if CB else []) + ['set', 'set=', 'if']
        kind = RLIFT.choice(kinds)
        if kind == 'na':
            st = ('slet', 'Wl', ('na', ('ref', 'N'), [('P', call)], RLIFT.randint(0, 1)))
        elif kind == 'cons':
            st = ('slet', 'Wl', ('cons', ('lit', RLIFT.randint(0, 3)), call, RLIFT.random() < 0.5))
        elif kind == 'if':
            # (in the else, N > lo: either branch may be taken)
            cond = [('filter', ('cmp', ('ref', 'N'), [(RLIFT.choice(['>', '<']), ('lit', RLIFT.randint(lo, lo + 2)))]))]
            st = ('slet', 'Wl', ('ifx', cond, call, other) if RLIFT.random() < 0.5 else ('ifx', cond, other, call))
        else:
            if not any(c[0] == 'svar' and c[1] == 'Vl' for c in stmts):
                stmts.append(('svar', 'Vl', ('lit', RLIFT.randint(0, 3))))
            # (`set +=` reads the old value before the call, `set =` after it, from the var each
            # value of it has set)
            st = (('sset', 'Vl', '+=', call) if kind == 'set' else
                  ('sset', 'Vl', '=', ('bin', '+', call, ('ref', 'Vl'))))
        _, x, galts, post, last = v[3][0]
    post = post + [st]
    last = ('bin', '+', ('ref', 'Vl' if kind in ('set', 'set=') else 'Wl'), last)
    if f['decides']:
        f['bound'] = (x, post, last)
    else:
        v[3][0] = ('gblk', x, galts, post, last)
    f['seq'] = f.get('seq', set()) | {'lifted-' + kind}


def nested_shapes(f, i, sc, ctr, stmts):
    """(#283, flag nested) a call of generator f of itself in a failure context of its own code,
    which consumes it there (RNEST alone): after its bound choice (a <decides> one's) or after the
    choice bound in its else's block, its value then reading the result; or in its clauses, guarded
    by N so that its calls end."""
    if RNEST.random() >= 0.35:
        return
    v = f['val']
    blk = not f['decides'] and v[0] == 'gbif' and v[3] and v[3][0][0] == 'gblk'
    lo = f['lo']
    where = RNEST.choice(['clauses', 'after']) if (f['decides'] or blk) else 'clauses'
    if where == 'after':
        if f['decides']:
            x, post, last = f.get('bound') or ('Wf', [], ('ref', 'Wf'))
        else:
            _, x, galts, post, last = v[3][0]
        # (not a bound choice of strings, `Ws`, typed_shapes': the call's argument is an int)
        names = sc + ([x] if x != 'Ws' else [])
        kinds = ['if', 'or', 'opt', 'for'] + (['not', 'logic'] if f['decides'] else [])
    else:
        names = sc
        kinds = ['if', 'for']
    kind = RNEST.choice(kinds)
    a = ('ref', RNEST.choice(names)) if RNEST.random() < 0.5 else ('lit', RNEST.randint(0, 3))
    call = ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else []))
    test = ('cmp', call, [(RNEST.choice(['>', '<', '>=', '<>']), ('lit', RNEST.randint(-1, 3)))])
    guard = [('filter', ('cmp', ('ref', 'N'), [('>', ('lit', lo))]))] if where == 'clauses' else []
    w, xn, vn = f"Wn{i}", f"Xn{i}", f"Vn{i}"

    def val():
        n = ('lit', RNEST.randint(0, 4))
        return ('tell', sqfresh(), n) if where == 'clauses' or RNEST.random() < 0.4 else n
    if kind == 'if':
        st = ('slet', w, ('ifx', guard + [('filter', test)], val(), val()))
    elif kind == 'or':
        st = ('slet', w, ('orx', test, val()))
    elif kind == 'opt':
        st = ('slet', w, ('optor', [('filter', test)], val()))
    elif kind == 'not':
        st = ('sclause', ('not', [('filter', test)]))
    elif kind == 'logic':
        st = ('sclause', ('logic', [('filter', test)]))
    else:
        stmts.append(('svar', vn, ('lit', RNEST.randint(0, 3))))
        pr = sqfresh() if RNEST.random() < 0.6 else None
        # (a body that may fail, which fails the for and so the generator's value: a <decides> one's)
        lim = RNEST.randint(1, 6) if f['decides'] and RNEST.random() < 0.4 else None
        st = ('sfor', guard + [('bind', xn, call)], ('ref', vn), pr, lim)
    st = ('snest', kind, st)
    if where == 'clauses':
        stmts.append(st)
    else:
        post = post + [st]
        if kind in ('if', 'or', 'opt', 'for'):
            last = ('bin', '+', ('ref', vn if kind == 'for' else w), last)
        if f['decides']:
            f['bound'] = (x, post, last)
        else:
            v[3][0] = ('gblk', x, galts, post, last)
    f['seq'] = f.get('seq', set()) | {f'nested-{kind}'}


def other_shapes(f, i, sc, ctr):
    """(#283, flag other) a call of another function with several values as a choice point in
    generator f, made already (ROTH alone): an alternative of its own choice that is that call, or a
    call of itself followed by it."""
    if ROTH.random() >= 0.3:
        return
    v = f['val']
    alts = v[1] if v[0] == 'gchoice' else v[3]
    # (not a branch's block, `gblk`, nor a bound choice of strings, typed_shapes')
    if not alts or alts[0][0] == 'gblk' or (f.get('bound') or ('',))[0] == 'Ws':
        return
    cands = [j for j in range(i) if (f['decides'] or not GFUNCS[j]['decides']) and (ctr or not GFUNCS[j]['ctr'])]
    a = ('ref', ROTH.choice(sc)) if ROTH.random() < 0.5 else ('lit', ROTH.randint(-1, 3))
    if cands and ROTH.random() < 0.4:
        j = ROTH.choice(cands)
        callee = ('gcall', j, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if GFUNCS[j]['ctr'] else []))
        kind = 'other-gen'
    else:
        x = 'x' if f['decides'] else 'y'
        OTHERS.add(x)
        callee = ('gx', x, a)
        kind = 'other-fn'
    if ROTH.random() < 0.5:
        own = ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), ('lit', ROTH.randint(0, 3))] +
               ([('ref', 'C')] if ctr else []))
        callee = ('bin', ROTH.choice(['+', '*']), own, callee)
    alts.insert(ROTH.randint(0, len(alts)), callee)
    f['seq'] = f.get('seq', set()) | {kind}


def class_shapes(f, i, sc, ctr):
    """(#283, flag cls) in the block of generator f's else, made already (RCLS alone), a call of
    itself in a field of a class's construction, its fields evaluated in the class's order."""
    v = f['val']
    blk = not f['decides'] and v[0] == 'gbif' and v[3] and v[3][0][0] == 'gblk'
    if not blk or RCLS.random() >= 0.6:
        return
    a = ('ref', RCLS.choice(sc)) if RCLS.random() < 0.5 else ('lit', RCLS.randint(0, 3))
    call = ('gself', i, [('bin', '-', ('ref', 'N'), ('lit', 1)), a] + ([('ref', 'C')] if ctr else []))
    other = (('lit', RCLS.randint(0, 3)) if RCLS.random() < 0.5 else
             ('choice', [('lit', RCLS.randint(0, 3)), ('lit', RCLS.randint(4, 7))]))
    st = ('slet', 'Wc', ('ccons', call, other) if RCLS.random() < 0.5 else ('ccons', other, call))
    _, x, galts, post, last = v[3][0]
    v[3][0] = ('gblk', x, galts, post + [st], ('bin', '+', ('ref', 'Wc'), last))
    USES_CC[0] = True
    f['seq'] = f.get('seq', set()) | {'class-cons'}


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
    arguments print or change an object, or those arguments set a name. (#283) One with choice
    points in sequence also where its values or the code after its calls do: they may run before
    a choice point, once for the values after it."""
    if f.get('seq'):
        return has_node((f['stmts'], f['val'], f.get('bound')), FX_NODES + ('sset', 'bset', 'setv'))
    v = f['val']
    alts = v[1] if v[0] == 'gchoice' else v[2] + v[3]
    args = [c[2] for a in alts if (c := frame_call(a)) is not None] + [x for a in alts for x in frame_prefix(a)]
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
    if v[0] == 'gchoice' and f.get('bound'):
        x, post, last = f['bound']
        L.append(f"    {x} := " + show_galts(v[1]))
        L += ["    " + show_s(c) for c in post]
        L.append("    " + show(last))
    elif v[0] == 'gchoice':
        L.append("    " + show_galts(v[1]))
    elif v[3] and v[3][0][0] == 'gblk':
        # (#283: the else a block that binds a choice, with code after it)
        _, x, galts, post, last = v[3][0]
        L.append(f"    if ({show_cl(v[1], ', ')}) then {show_galts(v[2])} else:")
        L.append(f"        {x} := " + show_galts(galts))
        L += ["        " + show_s(c) for c in post]
        L.append("        " + show(last))
    else:
        L.append(f"    if ({show_cl(v[1], ', ')}) then {show_galts(v[2])} else {show_galts(v[3])}")
    return L


def gen_call(fi, vals, st, k, mode):
    GFRAME[0] += 1
    fr = f"g{GFRAME[0]}"
    f = GFUNCS[fi]
    stmts, val = f['stmts'], f['val']
    if f.get('bound'):
        # (#283: its choice bound, the code after it run on each of its values)
        x, post, last = f['bound']
        stmts, val = stmts + [('slet', x, val)] + post, last
    own = set(p for p, _ in f['params']) | binders_of(stmts, set()) | binders_of(val, set())
    stmts = rename(stmts, own, fr)
    val = rename(val, own, fr)
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
    while isinstance(e, tuple) and e and e[0] in ('bset', 'bprint'):
        e = e[-1]
    return e


def branch_alts(scope, vars_, d):
    """a branch's alternatives: at times one call with several values (#360), or a block
    whose bound value has several values (#383)."""
    # (where a lifted choice may go: not in a block with a defer: of its own, lift_block)
    if R16.random() < 0.35 and NCH[0] < 4 and not lift_block() and (not MV or PROD[0] * 2 <= CTX['plim']):
        x = fresh("BT")
        e1 = None
        if MV and FUNCS and not CTX.get('nomcall') and R16.random() < 0.5:
            e1 = gen_mcall(scope, vars_, d)
        if e1 is None:
            NCH[0] += 1
            if MV:
                PROD[0] *= 2
            e1 = ('choice', [gen_e(scope, vars_, d + 1, False) for _ in range(2)])
        return [('blk', x, e1, ('bin', '+', ('ref', x), gen_e(scope + [x], vars_, d + 1, False)))]
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
        # (an if with a call in a branch converts as a whole, and no branch may then be a set or
        # a Print, as LANGUAGE.md says: its value is taken instead; a block may be one, #383)
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
    if t == 'str':
        return f'"{e[1]}"'
    if t == 'sfmt':
        return '"{' + show(e[1]) + '}"'
    if t == 'slen':
        return f'{show(e[1])}.Length'
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
    if t == 'gx':
        return f"Oxv[{show(e[2])}]" if e[1] == 'x' else f"Oyv({show(e[2])})"
    if t == 'ccons':
        return f'OC(ocls{{A := {show(e[1])}, B := {show(e[2])}}})'
    if t == 'cons':
        if e[3]:
            return f'PS(pt{{Y := {show(e[2])}, X := {show(e[1])}}})'
        return f'PS(pt{{X := {show(e[1])}, Y := {show(e[2])}}})'
    if t == 'blk':
        return f'block{{ {e[1]} := {show(e[2])}; {show(e[3])} }}'
    if t == 'mvm':
        recv = {'bare': '', 'self': 'Self.', 'me': f'Me{e[2][0]}.'}[e[3]]
        return f'{recv}Mv{"" if SHARED else e[2][0]}({show(e[1])})'
    if t == 'pmv':
        return f'pmv{{}}.Mv({show(e[1])})'
    if t == 'mvm2':
        return f'{"Self." if e[4] == "self" else ""}Mv{"" if SHARED else e[3][0]}({show(e[1])}, {show(e[2])})'
    if t == 'rt':
        return f'RT({show(e[1])})'
    if t in ('rt2', 'rt3'):
        return f'{t.upper()}({show(e[1])})'
    if t == 'ovl':
        return f'Ov("{e[3]}")' if e[1] == 's' else f'Ov({", ".join(show(x) for x in e[2])})'
    if t in ('owone', 'ow1'):
        return f'{"OwOne" if t == "owone" else "Ow"}({show(e[1])})'
    if t == 'om1':
        return f'owc{{}}.Om({show(e[1])})'
    if t == 'ows':
        return f'Ow("{e[1]}")'
    if t == 'ow2':
        return f'Ow({show(e[1])}, {show(e[2])})'
    if t == 'om':
        return f'ow{e[1]}{{}}.Om()'
    if t == 'owr':
        return f'OwR[{e[1]}]'
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
        if t == 'gself' and RRecursiveTuple.random() < 0.5:
            a = f"({a})"
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
    if t in ('choice', 'bif', 'mcall', 'rcall', 'gcall', 'nam', 'mvm', 'rt', 'rt2', 'rt3', 'ovl', 'ows', 'ow2', 'om', 'owr'):
        return True
    if t in ('owone', 'ow1', 'om1'):
        return top_choice_e(e[1])
    if t in ('lit', 'ref', 'next', 'bprint', 'bset', 'optor', 'orx', 'ifx', 'obj', 'cnext', 'big', 'snx'):
        return False
    if t == 'cadd':
        return top_choice_e(e[2])
    if t in ('tell', 'pos', 'even', 'add', 'pmv'):
        return top_choice_e(e[-1])
    if t == 'bin':
        return top_choice_e(e[2]) or top_choice_e(e[3])
    if t in ('tw', 'twt', 'cons', 'mvm2'):
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
    if t == 'rblk':
        return (f'{c[1]} := block{{ defer: Print("{c[5]}"); {c[2]} := {show(c[3])}; '
                f'if ({show(c[4])[1:-1]}) then return else true; {c[2]} }}')
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
    EV_STEPS[0] += 1
    if EV_STEPS[0] > EV_MAX:
        raise ModelBudget(f"over {EV_MAX} steps of the model")
    t = e[0]
    if t == 'lit':
        return k(e[1], st)
    if t == 'ref':
        return k(lookup(st, e[1]), st)
    if t == 'str':
        return k(e[1], st)
    if t == 'sfmt':
        return ev(e[1], st, lambda v, s: k(str(v), s), mode)
    if t == 'slen':
        return ev(e[1], st, lambda v, s: k(len(v), s), mode)
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
                def leave(x, s):
                    if RET_DEFER:
                        s.out.extend([f'branch b {t.upper()}', f'branch a {t.upper()}', f'outer {t.upper()}'])
                    return k2(x, s)
                if t == 'rt2':
                    return choice_point([val(99), val(98)], s1, leave, mode)
                return leave(99, s1)
            def fall(y):
                def th(s1, k2):
                    yy = chks(y, s1)
                    s1.out.append(f"p{yy}")
                    s1.out.append(f"e{yy}")
                    if RET_DEFER and y == v:
                        s1.out.extend([f'branch b {t.upper()}', f'branch a {t.upper()}'])
                    s1.out.append(f"q{yy}")
                    y10 = chks(yy * 10, s1)
                    def leave(x, s):
                        if RET_DEFER:
                            s.out.extend([f'late {t.upper()}', f'outer {t.upper()}'])
                        return k2(x, s)
                    return choice_point([val(y10), lambda s2, k3: k3(chks(y10 + 1, s2), s2)], s1, leave, mode)
                return th
            return choice_point([fall(v), alt_ret, fall(v + 2)], s0, k, mode)
        return ev(e[1], st, krt2, mode)
    if t == 'pmv':
        return ev(e[1], st, lambda v, s: k(chks(v * 1000, s), s), mode)
    if t == 'mvm2':
        return ev(e[1], st, lambda a, s0: ev(e[2], s0, lambda b, s1: k(chks(chks(a * 10, s1) + b, s1), s1), mode),
                  mode)
    if t == 'mvm':
        def kmvm(v, s0):
            def alt1(s1, k2):
                c = s1.vars['S.Cn']
                s1.vars['S.Cn'] = chks(c + SNX['inc'], s1)
                return k2(chks(v + c, s1), s1)

            def alt2(s1, k2):
                return k2(chks(v + 2 * s1.vars[e[2][1]], s1), s1)
            base = [alt1, alt2]
            if SNX['dflt']:
                # (#375: the interface's default, MpT * 5 | MpT + 7)
                base = [lambda s1, k2: k2(chks(v * 5, s1), s1), lambda s1, k2: k2(chks(v + 7, s1), s1)]
            if SNX['ovm']:
                return choice_point([lambda s1, k2: k2(chks(v * 3, s1), s1),
                                     lambda s1, k2: choice_point(base, s1, k2, mode),
                                     lambda s1, k2: k2(chks(v - 1, s1), s1)], s0, k, mode)
            return choice_point(base, s0, k, mode)
        return ev(e[1], st, kmvm, mode)
    if t == 'ovl':
        # (#380: the overload its arguments pick; they run first, then its two alternatives)
        def kargs(i, got, s0):
            if i < len(e[2]):
                return ev(e[2][i], s0, lambda v, s: kargs(i + 1, got + [v], s), mode)
            if e[1] == 's':
                alts = [lambda s1, k2: k2(len(e[3]), s1), lambda s1, k2: k2(0, s1)]
            elif e[1] == 1:
                alts = [lambda s1, k2: k2(chks(got[0] + 1, s1), s1), lambda s1, k2: k2(chks(got[0] * 2, s1), s1)]
            else:
                alts = [lambda s1, k2: k2(chks(got[0] - got[1], s1), s1), lambda s1, k2: k2(chks(got[1] * 3, s1), s1)]
            return choice_point(alts, s0, k, mode)
        return kargs(0, [], st)
    if t in ('owone', 'ow1', 'om1'):
        # (an overload with one value: an ordinary call, after its argument)
        def kow(v, s):
            if t == 'om1':
                return k(chks(v + 3, s), s)
            w = chks(v * 5, s)
            return k(chks(w + 1, s) if t == 'owone' else w, s)
        return ev(e[1], st, kow, mode)
    if t == 'ows':
        return choice_point([lambda s1, k2: k2(len(e[1]), s1), lambda s1, k2: k2(9, s1)], st, k, mode)
    if t == 'ow2':
        # (its arguments, then Ow(OA) | Ow("{OB}"): OA * 5, then OB's length written, then 9)
        def kow2(a, s0):
            def kb(b, s1):
                return choice_point([lambda s2, k2: k2(chks(a * 5, s2), s2),
                                     lambda s2, k2: choice_point([lambda s3, k3: k3(len(str(b)), s3),
                                                                  lambda s3, k3: k3(9, s3)], s2, k2, mode)],
                                    s1, k, mode)
            return ev(e[2], s0, kb, mode)
        return ev(e[1], st, kow2, mode)
    if t == 'om':
        base = [lambda s1, k2: k2(3, s1), lambda s1, k2: k2(6, s1)]
        if e[1] == 'c':
            return choice_point(base, st, k, mode)
        return choice_point([lambda s1, k2: k2(103, s1), lambda s1, k2: choice_point(base, s1, k2, mode)],
                            st, k, mode)
    if t == 'owr':
        # (OwR[N]: Ow(N, N)'s values, then OwR[N - 1]'s; none from 0)
        vs = [x for n in range(e[1], 0, -1) for x in (n * 5, len(str(n)), 9)]
        return choice_point([(lambda x: lambda s1, k2: k2(x, s1))(x) for x in vs], st, k, mode)
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
    if t == 'gx':
        # (#283: Oxv or Oyv, taken with the generator whose code calls it: in a for, when its
        # clauses fail, no values, and what came before the call stays, as at `gen_call`)
        def kgx(a, s):
            def body(s1, k1):
                if e[1] == 'x':
                    s1.out.append(f"ox {a}")
                    if not a > 0:
                        raise Fail()
                    return choice_point([(lambda s2, k2: k2(a, s2)), (lambda s2, k2: k2(chks(a + 3, s2), s2))],
                                        s1, k1, mode, True)

                def told(s2, k2):
                    s2.out.append("oy")
                    return k2(a, s2)
                return choice_point([told, (lambda s2, k2: k2(chks(a + 3, s2), s2))], s1, k1, mode, True)
            if mode == 'all':
                s0 = s.copy()
                try:
                    return body(s, k)
                except Fail:
                    return s0
            return body(s, k)
        return ev(e[2], st, kgx, mode)
    if t == 'ccons':
        # (#283: a class's construction, the superclass's field B first, then A: A * 10 + B)
        def kcb(vb, s1):
            def kca(va, s2):
                return k(chks(chks(va * 10, s2) + vb, s2), s2)
            return ev(e[1], s1, kca, mode)
        return ev(e[2], st, kcb, mode)
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
    # (a counter's `set C += 1` is checked addition, as any: it stops the
    # program there, before the method returns: fuzz-model-mv seed 4594)
    if t == 'snx':
        v = st.vars['S.Cn']
        st.vars['S.Cn'] = chks(v + SNX['inc'], st)
        return k(v, st)
    if t == 'next':
        v = st.vars['K.C']
        st.vars['K.C'] = chks(v + 1, st)
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
        st.vars[o] = chks(v + 1, st)
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
    if t == 'gblk':
        # (#283: a choice bound in a branch, then the code after it, on each of its values)
        def kgb(v, s):
            s.binds[e[1]] = v
            return run_body(e[3], e[4], s, k, mode)
        if len(e[2]) == 1:
            return ev(e[2][0], st, kgb, mode)
        return choice_point([(lambda s, k2, a=a: ev(a, s, k2, mode)) for a in e[2]], st, kgb, mode, True)
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

        dfr = FUNCS[e[1]].get('defer')

        def kd(v, s):
            # (#391: the function's own defer: runs as this value leaves it)
            s.out.append(dfr)
            return k(v, s)

        def go(i, vals, s):
            if i == len(args):
                for p, v in zip(body['params'], vals):
                    s.binds[p] = v
                return run_body(body['stmts'], body['val'], s, kd if dfr else k, mode)
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
        if x and x[0] in ('bind', 'sbind', 'range', 'slet', 'svar', 'gblk') and isinstance(x[1], str):
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
    if t in ('ref', 'cnext', 'snext', 'bind', 'sbind', 'range', 'slet', 'svar', 'sset', 'bset', 'cadd', 'setv', 'gblk') and isinstance(x[1], str) and x[1] in own:
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
    if t == 'snest':
        # (#283: a consumer in a generator's code, as anywhere)
        return run_body([c[2]] + stmts[1:], val, st, k, mode)
    if t == 'sclause':
        return run_clauses([c[1]], st, nxt, mode)
    if t == 'sfor':
        # (all the values its clauses give, what each iteration does kept, as any for's; a body
        # that fails fails the for, LANGUAGE.md's reading, so the code it is in)
        def kfor(s):
            x = c[1][-1][1]
            o = c[2][1]
            s.vars[o] = chks(s.vars[o] + s.binds[x], s)
            if c[3]:
                s.out.append(c[3])
            if c[4] is not None and not s.binds[x] < c[4]:
                raise ForBodyFail()
            return s
        s0 = st.copy()
        try:
            st = run_clauses(c[1], s0, kfor, 'all')
        except ForBodyFail:
            raise Fail()
        except Fail:
            pass
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
    if t == 'rblk':
        # (each value of the block's choice: its return leaves the block, running its
        # defer:, else the value does as it leaves the block)
        def krb(v, s):
            s.binds[c[2]] = v
            leaving = first_inner(lambda s2, kk: ev(c[4], s2, kk, 'first'), s) is not None
            s.out.append(c[5])
            if leaving:
                raise Return(s)
            s.binds[c[1]] = v
            return nxt(s)
        return ev(c[3], st, krb, mode)
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
    if t == 'snest':
        return show_s(c[2])
    if t == 'sclause':
        return show_c(c[1])
    if t == 'sfor':
        body = (f"set {c[2][1]} += {c[1][-1][1]}" + (f'; Print("{c[3]}")' if c[3] else "") +
                (f"; {c[1][-1][1]} < {c[4]}" if c[4] is not None else ""))
        return f"for ({show_cl(c[1], ', ')}) {{ {body} }}"
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
         'count': PROD[0], 'nctr': len(ctrs), 'defer': f"df{i}" if R17.random() < 0.35 else None}
    CTX.update(ctrs=None, nofail=False, fmax=None, plim=64)
    return f


def show_func(f):
    ps = ", ".join(f"{p}:{t}" for p, t in f['params'])
    L = [f"{f['name']}({ps}){'<decides>' if f['decides'] else ''}:int ="]
    L += ["    " + show_s(c) for c in f['stmts']]
    if f.get('defer'):
        L += ["    defer:", f'        Print("{f["defer"]}")']
    L.append("    " + show(f['val']))
    return L


def gen_hetero_methods(rng):
    """(#283, #335) Hm in two or three unrelated classes, with several values or one, at times
    overridden in a class below (whose override reaches the root's with (super:)), at times with
    a second list that no call takes (so that hierarchy's lists have names of their own), the
    classes at times below a base class without Hm; called on the value of a choice whose
    alternatives are those classes' objects, each twice through HmDup or once as written (one at
    least twice, so the alternatives have values of their own and the clauses after the choice
    are copied for each): in a for, with a filter at times, in a for's body, with a later clause
    that takes each alternative's own type (HmTag, overloaded by class), and, under the base
    class (where the names the condition binds join), where the first success is taken.
    Returns the declarations, the test and its output."""
    n = rng.randint(2, 3)
    base = rng.random() < 0.5
    names = ['hma', 'hmb', 'hmc'][:n]
    vals = {}
    decls = (['hmbase := class:', '    Hk:int = 0'] if base else [])
    kinds = [rng.choice(['multi', 'multi', 'one']) for _ in names]
    if 'multi' not in kinds:
        kinds[rng.randrange(n)] = 'multi'
    below = {}
    for c, kind in zip(names, kinds):
        k1, k2 = rng.randint(1, 6), rng.randint(-3, 9)
        decls.append(f"{c} := class{'(hmbase)' if base else ''}:")
        if kind == 'multi':
            decls.append(f"    Hm(Hx:int):int = Hx * {k1} | Hx + {k2}")
            vals[c] = (lambda k1, k2: lambda x: [x * k1, x + k2])(k1, k2)
        else:
            decls.append(f"    Hm(Hx:int):int = Hx * {k1} + {k2}")
            vals[c] = (lambda k1, k2: lambda x: [x * k1 + k2])(k1, k2)
        if rng.random() < 0.3:
            decls.append("    Hm(Hs:string):int = Hs.Length")
        if kind == 'multi' and rng.random() < 0.35:
            k3 = rng.randint(1, 5)
            decls += [f"{c}s := class({c}):", f"    Hm<override>(Hx:int):int = Hx - {k3} | (super:)Hm(Hx)"]
            vals[c + 's'] = (lambda k3, up: lambda x: [x - k3] + up(x))(k3, vals[c])
            below[c] = c + 's'
    decls.append("HmDup(V:t where t:type):t = V | V")
    decls += [f'HmTag(V:{c}):string = "{c}"' for c in names]

    def alts():
        """a choice of receivers: its source, and the objects' classes (static, and the root's for HmTag)"""
        cs = [rng.choice(names) for _ in range(rng.randint(2, 3))]
        twice = [rng.random() < 0.6 for _ in cs]
        if not any(twice):
            twice[rng.randrange(len(cs))] = True
        src, objs = [], []
        for c, t in zip(cs, twice):
            cl = below[c] if c in below and rng.random() < 0.5 else c
            src.append(f"HmDup({cl}{{}})" if t else f"{cl}{{}}")
            objs += [(cl, c)] * (2 if t else 1)
        return "(" + " | ".join(src) + ")", objs
    test, out = ["HetMethods():void ="], []
    for _ in range(rng.randint(2, 4)):
        forms = ['for', 'filter', 'body', 'tag'] + (['first'] if base else [])
        form = rng.choice(forms)
        src, objs = alts()
        x = rng.randint(-2, 6)
        t = rng.randint(-2, 12)
        if form == 'for':
            test.append(f'    for (A := {src}, X := A.Hm({x})) {{ Print("h {{X}}") }}')
            out += [f"h {v}" for cl, _ in objs for v in vals[cl](x)]
        elif form == 'filter':
            test.append(f'    for (A := {src}, X := A.Hm({x}), X > {t}) {{ Print("g {{X}}") }}')
            out += [f"g {v}" for cl, _ in objs for v in vals[cl](x) if v > t]
        elif form == 'body':
            test.append(f'    for (A := {src}) {{ for (X := A.Hm({x})) {{ Print("b {{X}}") }} }}')
            out += [f"b {v}" for cl, _ in objs for v in vals[cl](x)]
        elif form == 'tag':
            test.append(f'    for (A := {src}, X := A.Hm({x}), T := HmTag(A)) {{ Print("t {{X}} {{T}}") }}')
            out += [f"t {v} {c}" for cl, c in objs for v in vals[cl](x)]
        else:
            test.append(f'    if (A := {src}, X := A.Hm({x}), X > {t}) {{ Print("f {{X}}") }} else {{ Print("f none") }}')
            first = next((v for cl, _ in objs for v in vals[cl](x) if v > t), None)
            out.append("f none" if first is None else f"f {first}")
    return decls, test, out


def gen_incomplete_if(rng):
    """A conditional chooses a branch once and discards each yielded value."""
    arms = [rng.sample(range(1, 9), rng.randint(2, 4)) for _ in range(rng.randint(1, 2))]
    cond = " else ".join(
        f'if (Tell("guard {i}", K) = {i}) then (' +
        " | ".join(f"(set Score = {v}; {v})" for v in values) + ")"
        for i, values in enumerate(arms))
    cutoff = rng.randrange(10)
    selector = rng.randrange(len(arms) + 1)
    source = [
        "IncompleteIf():void =",
        "    var Score:int = 0",
        f"    for (K := 0..{len(arms)}, {cond}, Score >= {cutoff}):",
        '        Print("void body {K} {Score}")',
        "    set Score = 0",
        f"    if (K := {selector}, {cond}, Score >= {cutoff}):",
        '        Print("void first {Score}")',
        '    else: Print("void none")',
    ]
    output = []
    score = 0
    for i, values in enumerate(arms):
        output.append(f"guard {i}")
        for v in values:
            if v >= cutoff:
                score = v
                output.append(f"void body {i} {score}")
    if score >= cutoff:
        output.append(f"void body {len(arms)} {score}")
    candidates = arms[selector] if selector < len(arms) else [0]
    first = next((v for v in candidates if v >= cutoff), None)
    if first is None:
        output.append("void none")
    else:
        if selector < len(arms):
            output.append(f"guard {selector}")
        output.append(f"void first {first}")
    return source, output


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
        def to_j(a):
            # (every call of it, in a return frame too, #283, and in choice points
            # in sequence, so that each is recursive through the other)
            if isinstance(a, tuple) and a and a[0] == 'gself':
                return ('gself', j, a[2])
            if isinstance(a, tuple):
                return tuple(to_j(x) for x in a)
            if isinstance(a, list):
                return [to_j(x) for x in a]
            return a
        f['val'] = to_j(f['val'])
        if f.get('bound'):
            f['bound'] = to_j(f['bound'])
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
        SNX['dflt'] = MVM and R14.random() < 0.4
        st.vars['S.Cn'] = 0
    CTX['meth'] = meth
    CTX['mvm'] = (ti, f"N{ti}a")
    CTX['mvm_used'] = False
    CTX['mvm_me'] = False
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
        # times, after one whose call is at the clause's top.
        lp = [lift_pos(c) if kind == 'if' else None for c in cl]
        j = next((i for i, x in enumerate(lp) if x), len(cl))
        if j < len(cl) and lp[j] == "top" and R.random() < 0.4:
            pos = R.randint(j + 1, len(cl))
            REFUSED[0] = 'legacy-first-return-refusal' in flags
        else:
            pos = R.randint(0, j)
        sc = [c[1] for c in cl[:pos] if c[0] in ('bind', 'range')]
        cl.insert(pos, ('ret', ('cmp', leaf(sc, vars_), [(R.choice(OPS), leaf(sc, vars_))])))
        has_ret = True
        if RRB.random() < 0.4 and not lift_block() and (not MV or PROD[0] * 2 <= CTX['plim']):
            if MV:
                PROD[0] *= 2
            w = fresh("W")
            alts = [('tell', fresh("t"), ('lit', RRB.randint(-1, 5))), ('lit', RRB.randint(-1, 5))]
            RRB.shuffle(alts)
            cl[pos] = ('rblk', fresh("X"), w, ('choice', alts),
                       ('cmp', ('ref', w), [(RRB.choice(OPS), ('lit', RRB.randint(-1, 5)))]), fresh("rb"))
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
        ifc = CTX.get('mvm_used') and R13.random() < 0.5
        dflt = CTX.get('mvm_used') and SNX['dflt']     # (#375: the interface's default)
        ifc = ifc or dflt
        mv = "Mv" if SHARED else f"Mv{ti}"         # (#283: one name for every test's)
        M = ([f"i{ti} := interface:", f"    {mv}(Mp{ti}:int):int" + (f" = Mp{ti} * 5 | Mp{ti} + 7" if dflt else "")]
             if ifc else []) + [
             f"{top} := class(tbase{f', i{ti}' if ifc else ''}):", f"    var {vars_[0]}:int = 0",
             f"    var {vars_[1]}{'<private>' if priv else ''}:int = 0"]
        if ovr and not split:
            M += ["    Nx<override>()<transacts>:int =", "        set Cn += 2", "        Cn - 2"]
        if CTX.get('mvm_used'):
            M.append(f"    Hp{ti}(Hq{ti}:int):int = Hq{ti} * 2")
            if OVM:
                M.append(f"    {mv}(Mp{ti}:int, Mq{ti}:int):int = Mp{ti} * 10 + Mq{ti}")
            if not dflt:
                M.append(f"    {mv}{'<override>' if ifc else ''}(Mp{ti}:int):int = Mp{ti} + Nx() | Mp{ti} + Hp{ti}(N{ti}a)")
        M.append("    Run():void =")
        if CTX.get('mvm_me'):
            # (#283: Self as the class Run is in, or as the interface, which only types tell)
            M.append(f"        Me{ti}:{f'i{ti}' if ifc and R18.random() < 0.5 else top} = Self")
        M += ["    " + l for l in L[3:]]
        if split:
            M.append(f"{name}c := class({name}b):")
            if ovr:
                M += ["    Nx<override>()<transacts>:int =", "        set Cn += 2", "        Cn - 2"]
            M.append(f"    {mv}<override>(Mp{ti}:int):int = Mp{ti} * 3 | (super:){mv}(Mp{ti}) | Mp{ti} - 1")
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

if HM and not OVERFLOW[0] and not REFUSED[0]:
    hm_decls, hm_test, hm_out = gen_hetero_methods(random.Random(seed * 1000003 + 283336))
    lines += hm_decls + hm_test
    tests.append("HetMethods")
    out += ["== HetMethods"] + hm_out

if BIF and not OVERFLOW[0] and not REFUSED[0]:
    incomplete_src, incomplete_out = gen_incomplete_if(random.Random(seed * 1000003 + 283))
    lines += incomplete_src
    tests.append("IncompleteIf")
    out += ["== IncompleteIf"] + incomplete_out

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
        if not RET_DEFER:
            PRE += (f'{nm}(RTa:int):int =\n    RTy := RTa | RTa + 1 | RTa + 2\n    Print("p{{RTy}}")\n'
                    f'    if (RTy = RTa + 1):\n        Print("rt")\n        return {ret}\n    else:\n'
                    f'        Print("e{{RTy}}")\n    Print("q{{RTy}}")\n    RTy * 10 | RTy * 10 + 1\n')
        else:
            header = [f'{nm}(RTa:int):int =', f'    defer: Print("outer {nm}")',
                      '    RTy := RTa | RTa + 1 | RTa + 2', '    Print("p{RTy}")']
            branch = [f'        defer: Print("branch a {nm}")', f'        defer: Print("branch b {nm}")']
            late = [f'    defer: Print("late {nm}")', '    Print("q{RTy}")', '    RTy * 10 | RTy * 10 + 1']
            if 'retdefer-control' in flags:
                # Ordinary pre-change scopes: a returning branch and an
                # else that cleans up its fallthrough branch before the tail.
                body = ['    if (RTy = RTa + 1):'] + branch + ['        Print("rt")', f'        return {ret}', '    else:',
                    '        if (RTy = RTa):', *('    ' + s for s in branch), '            Print("e{RTy}")',
                    '        else: Print("e{RTy}")', *('    ' + s for s in late[:-1]), '        return RTy * 10 | RTy * 10 + 1']
            else:
                body = ['    if (RTy <= RTa + 1):'] + branch + ['        if (RTy = RTa + 1):',
                    '            Print("rt")', f'            return {ret}', '        Print("e{RTy}")',
                    '    else: Print("e{RTy}")'] + late
            PRE += '\n'.join(header + body) + '\n'
if NAM:
    PRE += 'NAM(NU:int, ?NV:int = Tell("dv", NU)):int = NU + NV | NV * 2\n'
if SHARED:
    PRE += 'pmv := class:\n    Mv(Mp:int):int = Mp * 1000\n'
if OVL:
    PRE += ('Ov(OA:int):int = OA + 1 | OA * 2\nOv(OA:int, OB:int):int = OA - OB | OB * 3\n'
            'Ov(OS:string):int = OS.Length | 0\n')
if OVW:
    PRE += ('Ow(OA:int)<computes>:int = OA * 5\nOw(OS:string)<computes>:int = OS.Length | 9\n'
            'Ow(OA:int, OB:int)<computes>:int = Ow(OA) | Ow("{OB}")\nOwOne(OA:int)<computes>:int = Ow(OA) + 1\n'
            'OwR(N:int)<computes><decides>:int =\n    N > 0\n    Ow(N, N) | OwR[N - 1]\n'
            'owc := class:\n    Om()<computes>:int = 3 | 6\n    Om(X:int)<computes>:int = X + 3\n'
            'owd := class(owc):\n    Om<override>()<computes>:int = 103 | (super:)Om()\n')
    # (Main first prints a call of the function that reaches only an overload with one value,
    # outside a failure context)
    OWK = R19.randint(-3, 12)
    src_main.insert(1, f'    Print("ow {{OwOne({OWK})}}")')
    out.insert(0, f"ow {OWK * 5 + 1}")
if NA:
    PRE += 'NA(A:int, ?P:int = Tell("dp", A), ?Q:int = P + 1):int = A * 100 + P * 10 + Q\n'
if CB:
    PRE += "pt := struct:\n    X:int = 0\n    Y:int = 0\nPS(P:pt)<computes>:int = P.X * 10 + P.Y\n"
if 'x' in OTHERS:
    PRE += 'Oxv(OxA:int)<transacts><decides>:int =\n    Print("ox {OxA}")\n    OxA > 0\n    OxA | OxA + 3\n'
if 'y' in OTHERS:
    PRE += 'Oyv(OyA:int)<transacts>:int = Tell("oy", OyA) | OyA + 3\n'
if USES_CC[0]:
    PRE += ("obase := class:\n    B:int = 0\nocls := class(obase):\n    A:int = 0\n"
            "OC(P:ocls)<computes>:int = P.A * 10 + P.B\n")
if LAZY:
    PRE = PRE.replace("Pos(X:int)<decides>", "Pos(X:int)<computes><decides>").replace(
        "Even(X:int)<decides>", "Even(X:int)<computes><decides>").replace("Tw(A:int, B:int):int", "Tw(A:int, B:int)<computes>:int")
open(f"{outdir}/p.verse", "w").write(PRE + "\n".join(lines) + "\n" + "\n".join(src_main) + "\n")
open(f"{outdir}/p.chain", "w").write("1" if CHAIN[0] else "0")
if os.environ.get('MVSEQ'):
    # (#283: the generators with choice points in sequence; then each kind the tests call, in a
    # for or where the first success is taken, with effects run as a function of its own or not)
    used = [(k, 'for' if isfor else ('first-lifted' if GFUNCS[i]['lifted'] else 'first'))
            for i, isfor in sorted(USED) for k in sorted(GFUNCS[i].get('seq', ()))]
    made = sorted({k for f in GFUNCS for k in f.get('seq', ())})
    print(f"seq {sum(1 for f in GFUNCS if f.get('seq'))} " + " ".join(sorted({f"{k}/{c}" for k, c in used})) +
          f" made={','.join(made)}", file=sys.stderr)
if os.environ.get('MVSTATS'):
    print(f"stats gens={len(GFUNCS)} gfor={STATS['gfor']} gfirst={STATS['gfirst']} gback={STATS['gback']} lfirst={STATS['lfirst']} lback={STATS['lback']} lmeth={STATS['lmeth']}", file=sys.stderr)
if SKIPRET[0]:
    open(f"{outdir}/p.expected", "w").write("SKIP (a return in a test that overflows)\n")
elif REFUSED[0]:
    open(f"{outdir}/p.expected", "w").write("exit=4\n")
else:
    open(f"{outdir}/p.expected", "w").write("".join(l + "\n" for l in out) + ("exit=2\n" if OVERFLOW[0] else "exit=0\n"))
