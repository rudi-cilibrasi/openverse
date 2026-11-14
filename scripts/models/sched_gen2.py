#!/usr/bin/env python3
# A model-based generator for openverse's gate (scripts/fuzz-model-*.sh).
# Its model is written from docs/LANGUAGE.md by the upkeep session, independently of
# scripts/gen-choice.py, gen-conc.py and gen-classes.py and of the front end's code,
# for the review of #249 (generic task roots, #244). Since #316, every other spawn of Hd goes
# through SpH, a generic immediate function that spawns it, so its roots are at its caller's
# type arguments too (the statement's number picks the form, so seeds keep their programs).
# Since #419, half of this generator's seeds put F's top-level branch/rush
# starts under one or two refining casts. The casts finish before the source
# suffix. Both conditions always succeed; the independent source scheduler
# model stays unchanged, including function-owned tasks and cleanup order.
# Some seeds route Hd through a choice loop returning a waiting call. Its
# first iteration returns, so the independent scheduler model is unchanged.
"""Generator + reference model for concurrency in generic functions (PR #249).

usage: gen.py SEED OUTDIR   -> writes OUTDIR/gSEED.verse and OUTDIR/gSEED.expected
The model follows docs/LANGUAGE.md "Concurrency": polling scheduler, 30 ticks/s,
Main first then roots in start order, repass while something ended/was
cancelled/was signalled, arms in source order, race losers cancelled last
started first, rush losers become roots (stopped at function exit with the
branches, last started first, after the function's defers)."""
import random, sys, os
from collections import Counter

TICKS = {"0.0": 0, "0.1": 3, "0.2": 6, "0.3": 9, "0.5": 15, "1.0": 30}
DURS = list(TICKS)


class Deadlock(Exception):
    pass


# ---------------------------------------------------------------- scheduler
class Task:
    def __init__(self):
        self.done = False; self.cancelled = False; self.result = None; self.root = None
        # (a cancel of it while it runs, taken after that run, #253, #260)
        self.req = False


# (Main's code runs as a dummy task, which nothing can cancel)
MAIN_TASK = Task()


class Root:
    """A root of the scheduler: Main, a spawned task's call, a branch or a
    rush loser. Its owner is the task whose code it runs: a spawned task's
    own, or for a branch or loser the task running when it was made (#260).
    `cancel_req`: the root asked to be cancelled after its run (it awaited a
    cancelled task)."""
    def __init__(self, kind, gen, task=None, owner=None):
        self.kind = kind; self.gen = gen; self.task = task
        self.owner = owner if owner is not None else (task if task is not None else MAIN_TASK)
        self.done = False; self.cancel_req = False


class Event:
    def __init__(self, sticky):
        self.sticky = sticky; self.has = False; self.val = None; self.waiters = []


class Rec:
    def __init__(self):
        self.done = False; self.val = None


class Sched:
    def __init__(self):
        self.clock = 0; self.roots = []; self.out = []; self.progress = False
        self.sleepers = Counter(); self.running = []; self.main = None

    def p(self, s):
        self.out.append(s)

    def cur(self):
        return self.running[-1]

    def cur_task(self):
        return self.running[-1].owner if self.running else MAIN_TASK

    def task_running(self, t):
        # its root, or one of its branches or rush losers, runs (#260)
        return any(r.owner is t for r in self.running)

    def poll(self, root):
        if root.done:
            return
        was = self.task_running(root.owner)
        self.running.append(root)
        try:
            next(root.gen)
        except StopIteration as s:
            root.done = True; self.progress = True
            if root.task:
                root.task.done = True; root.task.result = s.value
        finally:
            self.running.pop()
        # the run that marked its owner running takes a cancel of the owner
        # asked meanwhile: a task's own run unless it ended in it (#253), a
        # branch's or loser's run its owner's (#260)
        t = root.owner
        if t is not MAIN_TASK and not was and t.req:
            t.req = False
            if root.kind == "spawn":
                if not root.done:
                    self.cancel_root(root)
            elif not t.done:
                self.cancel_root(t.root)
        if root.cancel_req and not root.done:
            root.cancel_req = False
            self.cancel_root(root)

    def cancel_root(self, root):
        if root.done:
            return
        if root in self.running:
            root.cancel_req = True
            return
        root.done = True
        if root.task:
            root.task.done = True; root.task.cancelled = True
        root.gen.close()
        self.progress = True

    def run(self, main_gen):
        self.main = Root("main", main_gen)
        while True:
            while True:
                self.progress = False
                self.poll(self.main)
                if self.main.done:
                    return 0
                i = 0
                while i < len(self.roots):
                    r = self.roots[i]
                    if not r.done:
                        self.poll(r)
                    i += 1
                if not self.progress:
                    break
            live = [t for t, c in self.sleepers.items() if c > 0 and t > self.clock]
            if not live:
                return 2
            self.clock = min(live)
            if self.clock > 30 * 3000:
                raise RuntimeError("model runaway")


S = None  # the scheduler of the current model run


def m_sleep(d):
    ticks = TICKS[d] if isinstance(d, str) else d
    # (Sleep(0.0) completes at once, without suspending: the Book's tested
    # examples in ch. 14; any positive duration waits at least one tick)
    if ticks == 0:
        return
    wake = S.clock + max(1, ticks)
    S.sleepers[wake] += 1
    try:
        while S.clock < wake:
            yield
    finally:
        S.sleepers[wake] -= 1


def m_await_task(task):
    if task.done and not task.cancelled:
        return task.result
    while True:
        if task.cancelled:
            S.cur().cancel_req = True
            yield
            continue
        if task.done:
            return task.result
        yield


def m_await_event(ev):
    if ev.sticky and ev.has:
        return ev.val
    rec = Rec(); ev.waiters.append(rec)
    try:
        while not rec.done:
            yield
        return rec.val
    finally:
        if rec in ev.waiters:
            ev.waiters.remove(rec)


def m_signal(ev, v):
    if ev.sticky:
        ev.has = True; ev.val = v
    if ev.waiters:
        S.progress = True
    for r in ev.waiters:
        r.done = True; r.val = v
    ev.waiters = []


class Frame:
    def __init__(self, env):
        self.env = env; self.starts = []; self.counter = 0


# (the documented stop order, #254; IMPL_ORDER=1 for the order before it)
IMPL_ORDER = os.environ.get("IMPL_ORDER", "") != ""


class ArmRef:
    """A rush arm, as stopped at its function's exit: (IMPL_ORDER) a pending
    arm of a rush that has not ended, stopped by its own start number; or
    (the documented order, #254) the arm all along, which owns what its code
    starts, and once its rush ended without it, its loser's root."""
    def __init__(self, gen):
        self.gen = gen; self.done = False; self.root = None


def stop_one(root):
    if isinstance(root, ArmRef):
        if root.root is None:
            if not root.done:
                root.done = True
                root.gen.close()
            return
        root = root.root
    if not root.done:
        if root in S.running:
            root.cancel_req = True
            return
        root.done = True
        root.gen.close()
        S.progress = True


def stop_tree(e, kids):
    # what its code started first, last started first, then it (#254)
    for sn, c in sorted(kids.get(id(e), []), key=lambda x: -x[0]):
        stop_tree(c, kids)
    stop_one(e)


def stop_all(fr):
    if not IMPL_ORDER:
        # each unwinding whole: the function's own last started first (#254)
        kids, tops = {}, []
        for sn, e, owner in fr.starts:
            if owner is None:
                tops.append((sn, e))
            else:
                kids.setdefault(id(owner), []).append((sn, e))
        for sn, e in sorted(tops, key=lambda x: -x[0]):
            stop_tree(e, kids)
        return
    # branches and rush losers, last started first
    for sn, root, _ in sorted(fr.starts, key=lambda x: -x[0]):
        if isinstance(root, ArmRef):
            if not root.done:
                root.done = True
                root.gen.close()
            continue
        if not root.done:
            if root in S.running:
                root.cancel_req = True
                continue
            root.done = True
            root.gen.close()
            S.progress = True


def m_call(fn, args):
    fr = Frame(dict(args))
    try:
        v = yield from exec_block(fn.body, fr)
        return fr.env[fn.ret] if fn.ret else v
    finally:
        stop_all(fr)


def m_spawn(gen):
    task = Task()

    def wrap():
        v = yield from gen
        return v
    root = Root("spawn", wrap(), task)
    task.root = root
    S.roots.append(root)
    S.poll(root)
    return task


def m_cancel(task):
    # a running task (its code, or a branch's or loser's of it, runs) is
    # cancelled after that run (#260); a task done, or unwinding (marked
    # done first, #261), is not changed
    if task.done:
        return
    if S.task_running(task):
        task.req = True
        return
    S.cancel_root(task.root)


def killer_gen(t, tag, k, d):
    try:
        if d != "-1.0":
            yield from m_sleep(d)
        m_cancel(t)
        S.p(f"{tag} k{k} cancelled")
        yield from m_sleep(3)
        S.p(f"{tag} k{k} end")
    finally:
        S.p(f"{tag} k{k} defer")


def awaiter_gen(t, tag, k):
    try:
        yield from m_await_task(t)
        S.p(f"{tag} a{k} got")
    finally:
        S.p(f"{tag} a{k} defer")


# ---------------------------------------------------------------- AST
class Fn:
    def __init__(self, name, body, ret):
        self.name = name; self.body = body; self.ret = ret


class St:
    def __init__(self, k, **kw):
        self.k = k; self.__dict__.update(kw)


def exec_block(stmts, fr, owner=None):
    """Run a scope: defers run at its end (or when unwound). `owner`: the
    branch or rush arm whose code it is, which owns what it starts (#254)."""
    for i, s in enumerate(stmts):
        if s.k == "defer":
            try:
                v = yield from exec_block(stmts[i + 1:], fr, owner)
                return v
            finally:
                S.p(f"{fr.env['Tag']} {s.label} {fr.env['N']}")
                if getattr(s, "kill", None):
                    m_spawn(killer_gen(fr.env[s.kill], fr.env["Tag"], s.kk, "-1.0"))
                if getattr(s, "aw", None):
                    m_spawn(awaiter_gen(fr.env[s.aw], fr.env["Tag"], s.kk2))
        yield from exec_stmt(s, fr, owner)
    return None


def run_arm(stmts, val, fr, owner=None):
    yield from exec_block(stmts, fr, owner)
    return fr.env[val] if val else None


def exec_conc(s, fr, owner=None):
    kind = s.kind
    pend = []   # (idx, startno, gen)
    results = [None] * len(s.arms)
    winner = None
    finished = False
    refs = {}
    for i, (stmts, val) in enumerate(s.arms):
        sn = fr.counter; fr.counter += 1
        # (a rush arm owns what its code starts, #254; a sync or race arm's
        # is its enclosing owner's)
        ref = ArmRef(None) if kind == "rush" and not IMPL_ORDER else None
        g = run_arm(stmts, val, fr, ref if ref is not None else owner)
        if ref is not None:
            ref.gen = g; refs[i] = ref; fr.starts.append((sn, ref, owner))
        try:
            next(g)
            pend.append((i, sn, g))
            if kind == "rush" and IMPL_ORDER:
                refs[i] = ArmRef(g); fr.starts.append((sn, refs[i], owner))
        except StopIteration as e:
            results[i] = e.value
            if kind != "sync":
                winner = e.value
                break
    try:
        if kind == "sync":
            while pend:
                yield
                for item in list(pend):
                    try:
                        next(item[2])
                    except StopIteration as e:
                        results[item[0]] = e.value
                        pend.remove(item)
            finished = True
            return tuple(results)
        if winner is None:
            while winner is None:
                yield
                for item in list(pend):
                    try:
                        next(item[2])
                    except StopIteration as e:
                        winner = e.value
                        pend.remove(item)
                        break
        finished = True
        for ref in refs.values():
            ref.done = True
        if kind == "race":
            for item in reversed(pend):
                item[2].close()
        else:  # rush: losers become roots
            for (i, sn, g) in pend:
                r = Root("rushloser", g, owner=S.cur_task())
                if IMPL_ORDER:
                    fr.starts.append((sn, r, owner))
                else:
                    refs[i].root = r   # (its arm's entry stands for it)
                S.roots.append(r)
        pend = []
        return winner
    finally:
        if not finished:
            for ref in refs.values():
                ref.done = True
            for item in reversed(pend):
                item[2].close()


def exec_stmt(s, fr, owner=None):
    env = fr.env
    k = s.k
    if k == "print":
        S.p(f"{env['Tag']} {s.label} {env['N']}")
    elif k == "sleep":
        yield from m_sleep(s.d)
    elif k == "branch":
        sn = fr.counter; fr.counter += 1
        r = Root("branch", None, owner=S.cur_task())
        r.gen = exec_block(s.body, fr, r)
        fr.starts.append((sn, r, owner))
        S.roots.append(r)
        S.poll(r)
    elif k == "conc":
        v = yield from exec_conc(s, fr, owner)
        if s.kind == "sync":
            env[s.var] = v[s.pick]
        else:
            env[s.var] = v
    elif k == "spawnh":
        env[s.tvar] = m_spawn(m_call(HD, {"X": env[s.val], "Tag": env["Tag"], "K": s.kk, "D": s.d, "N": env["N"]}))
    elif k == "callh":
        env[s.var] = yield from m_call(HD, {"X": env[s.val], "Tag": env["Tag"], "K": s.kk, "D": s.d, "N": env["N"]})
    elif k == "await":
        env[s.var] = yield from m_await_task(env[s.tvar])
    elif k == "cancel":
        m_cancel(env[s.tvar])
    elif k == "event":
        env[s.evar] = Event(s.sticky)
    elif k == "spawnw":
        env[s.tvar] = m_spawn(m_call(WS if s.sticky else WT, {"E": env[s.evar], "Tag": env["Tag"], "K": s.kk, "N": env["N"]}))
    elif k == "signal":
        m_signal(env[s.evar], env[s.val])
    elif k == "evawait":
        env[s.var] = yield from m_await_event(env[s.evar])
    elif k == "rec":
        env[s.var] = env["X"]
        if env["N"] > 0:
            args = {"X": env["X"], "Y": env["Y"], "Z": env["Z"], "Tag": env["Tag"] + ("t" if s.wrap == "tup" else WRAPS[s.wrap][0]), "N": env["N"] - 1}
            if s.spawn:
                t = m_spawn(m_call(FNS[s.fn], args))
                yield from exec_block(s.mid, fr, owner)
                if s.cancel:
                    m_cancel(t)
                else:
                    env[s.var] = yield from m_await_task(t)
            else:
                env[s.var] = yield from m_call(FNS[s.fn], args)
    elif k == "meawait":   # a task's own handle (#260)
        env[s.var] = yield from m_await_event(env["Me"])
    elif k == "hcancel":
        m_cancel(env[s.var])
    elif k == "spawnkill":
        m_spawn(killer_gen(env[s.var], env["Tag"], s.kk, s.d))
    elif k == "spawnawait":
        m_spawn(awaiter_gen(env[s.var], env["Tag"], s.kk))
    elif k == "gcall":
        env[s.var] = env["X"]
        if env["N"] > 0:
            env[s.var] = yield from m_call(GFNS[s.fn], {"X": env["X"], "Tag": env["Tag"] + "g", "N": env["N"] - 1,
                                                       "Me": env["Me"]})
    elif k == "fcall":
        env[s.var] = yield from m_call(FNS[s.fn], {"X": env["X"], "Y": env["X"], "Z": env["X"],
                                                   "Tag": env["Tag"] + "f", "N": s.n})
    elif k == "hdsleep":  # the helper's own body pieces
        yield from m_sleep(env["D"])
    elif k == "hprint":
        S.p(f"{env['Tag']} {s.fmt.format(K=env['K'])}")
    elif k == "hawait":
        env["V"] = yield from m_await_event(env["E"])
    elif k == "hdefer":
        pass
    else:
        raise ValueError(k)


# helpers' bodies (model side); their defers print "{Tag} h{K} defer"
def _hd_body():
    return [St("hdefer2", fmt="h{K} defer"), St("hprint", fmt="h{K} go"), St("hdsleep"),
            St("hprint", fmt="h{K} done")]


class HelperFn:
    def __init__(self, kind):
        self.kind = kind


def helper_gen(kind, env):
    fr = Frame(dict(env))
    e = fr.env
    try:
        if kind == "hd":
            S.p(f"{e['Tag']} h{e['K']} go")
            yield from m_sleep(e["D"])
            S.p(f"{e['Tag']} h{e['K']} done")
            return e["X"]
        else:
            v = yield from m_await_event(e["E"])
            S.p(f"{e['Tag']} w{e['K']} woke")
            return v
    finally:
        S.p(f"{e['Tag']} {'h' if kind == 'hd' else 'w'}{e['K']} defer")


HD = HelperFn("hd"); WT = HelperFn("wt"); WS = HelperFn("ws")
_orig_m_call = m_call


def m_call(fn, args):  # noqa: F811
    if isinstance(fn, HelperFn):
        return helper_gen(fn.kind, args)
    return _orig_m_call(fn, args)


WRAPS = {
    "opt": ("o", lambda v: f"option{{{v}}}", lambda i, w, v: f"if ({w} := {i}?) then set {v} = {w}"),
    "arr": ("a", lambda v: f"array{{{v}}}", lambda i, w, v: f"if ({w} := {i}[0]) then set {v} = {w}"),
    "box": ("b", lambda v: f"bx(t){{V := {v}}}", lambda i, w, v: f"set {v} = {i}.V"),
}
TUPWRAP = True  # tuple wrap handled specially (X,Y)/(Y,X)
FNS = {}
GFNS = {}

# instantiations: (type text, mk(k) expr, show(var) interpolation, model show)
INSTS = {
    "int": ("int", lambda k: f"{k}", lambda r: f"{{{r}}}", lambda k: f"{k}"),
    "string": ("string", lambda k: f'"s{k}"', lambda r: f"{{{r}}}", lambda k: f"s{k}"),
    "optint": ("?int", lambda k: f"option{{{k}}}", lambda r: f"{{ShO({r})}}", lambda k: f"o{k}"),
    "arrint": ("[]int", lambda k: f"array{{{k}, {k}}}", lambda r: f"{{ShA({r})}}", lambda k: f"a{k}x2"),
    "pt": ("pt", lambda k: f"pt{{K := {k}}}", lambda r: f"p{{{r}.K}}", lambda k: f"p{k}"),
    "tup": ("tuple(int, string)", lambda k: f'({k}, "q")', lambda r: f"t{{ShT({r})}}", lambda k: f"t{k}q"),
    "bxs": ("bx(string)", lambda k: f'bx(string){{V := "s{k}"}}', lambda r: f"b{{{r}.V}}", lambda k: f"bs{k}"),
}


# ---------------------------------------------------------------- generator
class Gen:
    def __init__(self, rng, nfns, maxdepth):
        self.r = rng; self.nfns = nfns; self.maxdepth = maxdepth
        self.n = 0
        self.evprof = False

    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

    def dur(self):
        return self.r.choice(DURS)

    def block(self, scope, depth, in_branch, length, need_wait=False):
        """scope: dict with 'vals' (t vars), 'tasks' (tvar, unawaited), 'events'."""
        r = self.r
        out = []
        scope = {"vals": list(scope["vals"]), "uvals": list(scope["uvals"]), "tasks": list(scope["tasks"]), "events": list(scope["events"])}
        if need_wait:
            out.append(St("sleep", d=self.dur()))
        for _ in range(length):
            out.extend(self.stmt(scope, depth, in_branch))
        return out, scope

    def stmt(self, scope, depth, in_branch):
        r = self.r
        choices = ["print", "sleep", "sleep", "defer", "callh"]
        if depth < 2:
            choices += ["branch", "branch", "race", "rush", "sync", "spawnh", "rec", "rec", "event"]
        if scope["tasks"]:
            choices += ["await", "await", "cancel"]
        if scope["events"]:
            choices += ["signal", "signal", "signal", "evawait", "evawait", "spawnw"]
            if self.evprof:
                choices += ["signal", "signal", "evawait", "spawnw", "spawnw", "branch", "sleep"]
        if self.evprof and depth < 2 and len(scope["events"]) < 2:
            choices += ["event"] * 4
        c = r.choice(choices)
        if c == "print":
            return [St("print", label=self.fresh("p"))]
        if c == "sleep":
            return [St("sleep", d=self.dur())]
        if c == "defer":
            return [St("defer", label=self.fresh("d"))]
        if c == "callh":
            v = self.fresh("V")
            s = St("callh", var=v, val=r.choice(scope["vals"]), kk=self.n, d=self.dur())
            scope["vals"].append(v)
            return [s]
        if c == "branch":
            body, _ = self.block(scope, depth + 1, True, r.randint(1, 3), need_wait=r.random() < 0.8)
            body.append(St("print", label=self.fresh("bp")))
            if r.random() < 0.6:
                body.insert(0, St("defer", label=self.fresh("bd")))
            return [St("branch", body=body)]
        if c in ("race", "rush", "sync"):
            na = r.choice([2, 2, 3])
            arms = []
            for ai in range(na):
                imm = (c != "sync" and ai == na - 1 and r.random() < 0.1)
                body, sc = self.block(scope, depth + 1, in_branch, r.randint(0, 2), need_wait=not imm)
                # (an arm that may end without waiting starts with Sleep(0.0),
                # which completes at once: every arm of a race or a rush can
                # suspend, the Book's tests, Concurrency.versetest:831)
                if imm:
                    body.insert(0, St("sleep", d="0.0"))
                if r.random() < 0.5:
                    body.insert(0, St("defer", label=self.fresh("ad")))
                body.append(St("print", label=self.fresh("ap")))
                arms.append((body, r.choice(sc["vals"])))
            v = self.fresh("V")
            s = St("conc", kind=c, var=v, arms=arms, pick=r.randrange(na))
            scope["vals"].append(v)
            return [s]
        if c == "spawnh":
            t = self.fresh("T")
            ty = r.choice("tu")
            scope["tasks"].append((t, ty))
            return [St("spawnh", tvar=t, val=r.choice(scope["vals" if ty == "t" else "uvals"]), kk=self.n, d=self.dur())]
        if c == "await":
            t = r.choice(scope["tasks"])
            if r.random() < 0.8:
                scope["tasks"].remove(t)
            v = self.fresh("V")
            scope["vals" if t[1] == "t" else "uvals"].append(v)
            return [St("await", var=v, tvar=t[0])]
        if c == "cancel":
            t = r.choice(scope["tasks"])
            if r.random() < 0.7:
                scope["tasks"].remove(t)
            return [St("cancel", tvar=t[0])]
        if c == "event":
            e = self.fresh("E")
            sticky = r.random() < 0.35
            ty = r.choice("tu")
            scope["events"].append((e, sticky, ty))
            out = [St("event", evar=e, sticky=sticky, ty=ty)]
            for _ in range(r.randint(0, 2)):
                t = self.fresh("T")
                out.append(St("spawnw", tvar=t, evar=e, kk=self.n, sticky=sticky))
                scope["tasks"].append((t, ty))
            return out
        if c == "spawnw":
            e, sticky, ty = r.choice(scope["events"])
            t = self.fresh("T")
            scope["tasks"].append((t, ty))
            return [St("spawnw", tvar=t, evar=e, kk=self.n, sticky=sticky)]
        if c == "signal":
            e, sticky, ty = r.choice(scope["events"])
            return [St("signal", evar=e, val=r.choice(scope["vals" if ty == "t" else "uvals"]))]
        if c == "evawait":
            e, sticky, ty = r.choice(scope["events"])
            v = self.fresh("V")
            scope["vals" if ty == "t" else "uvals"].append(v)
            return [St("evawait", var=v, evar=e)]
        if c == "rec":
            v = self.fresh("V")
            spawn = r.random() < 0.45
            mid = []
            if spawn:
                for _ in range(r.randint(0, 2)):
                    mid.append(r.choice([St("print", label=self.fresh("p")), St("sleep", d=self.dur())]))
            s = St("rec", var=v, fn=r.randrange(self.nfns), wrap=r.choice(["opt", "arr", "box", "tup"]), uwrap=r.choice(["opt", "arr", "box", "tup", "same"]),
                   spawn=spawn, mid=mid, cancel=spawn and r.random() < 0.3, idn=self.n)
            scope["vals"].append(v)
            return [s]
        raise ValueError(c)


class GGen:
    """Functions G(X:t, Tag, N, Me:sticky_event(task(t))) (and Gi, the same
    at int) run as tasks that Main gives their own handle: their code, their
    branches and rush losers, at several depths, take it (`Me.Await()`) and
    cancel it, or start tasks that cancel or await it, also from defers
    (#253, #260, #261)."""
    def __init__(self, g, ngf, nfns):
        self.g = g; self.r = g.r; self.ngf = ngf; self.nfns = nfns

    def block(self, scope, depth, length, lead_sleep=False):
        scope = {k: list(v) for k, v in scope.items()}
        out = []
        if lead_sleep:
            out.append(St("sleep", d=self.g.dur()))
        for _ in range(length):
            out.extend(self.stmt(scope, depth))
        return out, scope

    def stmt(self, scope, depth):
        r, g = self.r, self.g
        ch = ["print", "sleep", "sleep", "defer", "callh"]
        if not scope["handles"]:
            ch += ["meawait"] * 4
        else:
            ch += ["hcancel"] * 2 + ["spawnkill", "spawnkill", "spawnawait", "kdefer", "kdefer", "meawait"]
        if depth < 2:
            ch += ["branch"] * 3 + ["rush"] * 2 + ["race", "sync", "spawnh"]
        if scope["tasks"]:
            ch += ["await", "cancel"]
        if depth < 2:
            ch += ["gcall", "fcall"]
        c = r.choice(ch)
        if c == "print":
            return [St("print", label=g.fresh("p"))]
        if c == "sleep":
            return [St("sleep", d=g.dur())]
        if c == "defer":
            return [St("defer", label=g.fresh("d"))]
        if c == "meawait":
            t = g.fresh("T")
            scope["handles"].append(t)
            return [St("meawait", var=t)]
        if c == "hcancel":
            return [St("hcancel", var=r.choice(scope["handles"]))]
        if c == "spawnkill":
            return [St("spawnkill", var=r.choice(scope["handles"]), kk=int(g.fresh("k")[1:]),
                       d=r.choice(["-1.0", "-1.0", "0.0", "0.1", "0.2"]))]
        if c == "spawnawait":
            return [St("spawnawait", var=r.choice(scope["handles"]), kk=int(g.fresh("k")[1:]))]
        if c == "kdefer":
            h = r.choice(scope["handles"])
            kill = h if r.random() < 0.7 else None
            aw = h if (kill is None or r.random() < 0.3) else None
            lab = g.fresh("kd")
            return [St("defer", label=lab, kill=kill, aw=aw, kk=g.n, kk2=g.n + 1000)]
        if c == "callh":
            v = g.fresh("V")
            scope["vals"].append(v)
            return [St("callh", var=v, val=r.choice(scope["vals"][:-1]), kk=g.n, d=g.dur())]
        if c == "spawnh":
            t = g.fresh("T")
            scope["tasks"].append(t)
            return [St("spawnh", tvar=t, val=r.choice(scope["vals"]), kk=g.n, d=g.dur())]
        if c == "await":
            t = r.choice(scope["tasks"]); scope["tasks"].remove(t)
            v = g.fresh("V")
            scope["vals"].append(v)
            return [St("await", var=v, tvar=t)]
        if c == "cancel":
            t = r.choice(scope["tasks"]); scope["tasks"].remove(t)
            return [St("cancel", tvar=t)]
        if c == "branch":
            body, _ = self.block(scope, depth + 1, r.randint(1, 3), lead_sleep=r.random() < 0.6)
            body.append(St("print", label=g.fresh("bp")))
            if r.random() < 0.6:
                body.insert(0, St("defer", label=g.fresh("bd")))
            return [St("branch", body=body)]
        if c in ("rush", "race", "sync"):
            na = r.choice([2, 2, 3])
            arms = []
            for ai in range(na):
                body, sc = self.block(scope, depth + 1, r.randint(0, 3), lead_sleep=True)
                if r.random() < 0.5:
                    body.insert(0, St("defer", label=g.fresh("ad")))
                body.append(St("print", label=g.fresh("ap")))
                arms.append((body, r.choice(sc["vals"])))
            v = g.fresh("V")
            scope["vals"].append(v)
            return [St("conc", kind=c, var=v, arms=arms, pick=r.randrange(na))]
        if c == "gcall":
            v = g.fresh("V")
            scope["vals"].append(v)
            return [St("gcall", var=v, fn=r.randrange(self.ngf), idn=g.n)]
        if c == "fcall":
            v = g.fresh("V")
            scope["vals"].append(v)
            return [St("fcall", var=v, fn=r.randrange(self.nfns), n=r.randint(0, 1))]
        raise ValueError(c)

    def function(self, i):
        r = self.r
        scope = {"vals": ["X"], "tasks": [], "handles": [], "events": []}
        body, sc = self.block(scope, 0, r.randint(3, 6))
        if r.random() < 0.3:
            t = self.g.fresh("T")
            body.insert(0, St("meawait", var=t))
        if r.random() < 0.7:
            body.append(St("sleep", d=r.choice(["0.5", "1.0"])))
        return Fn(f"G{i}", body, r.choice(sc["vals"]))


def emit_gfn(f, i, generic):
    ty = "t" if generic else "int"
    name = f"G{i}" if generic else f"Gi{i}"
    head = (f"{name}(X:t, Tag:string, N:int, Me:sticky_event(task(t)) where t:type)<suspends>:t ="
            if generic else f"{name}(X:int, Tag:string, N:int, Me:sticky_event(task(int)))<suspends>:int =")
    lines = [head] + emit_block(f.body, 4) + [f"    {f.ret}"]
    return [l.replace("\u00a7TY\u00a7", ty).replace("\u00a7G\u00a7", "G" if generic else "Gi") for l in lines]


# ---------------------------------------------------------------- emitter
def emit_block(stmts, ind):
    out = []
    for s in stmts:
        out.extend(emit_stmt(s, ind))
    return out


def emit_stmt(s, ind):
    p = " " * ind
    k = s.k
    if k == "print":
        return [p + f'Print("{{Tag}} {s.label} {{N}}")']
    if k == "sleep":
        return [p + f"Sleep({s.d})"]
    if k == "defer":
        out = [p + "defer:", p + f'    Print("{{Tag}} {s.label} {{N}}")']
        if getattr(s, "kill", None):
            out.append(p + f"    StartKill({s.kill}, Tag, {s.kk})")
        if getattr(s, "aw", None):
            out.append(p + f"    StartAwait({s.aw}, Tag, {s.kk2})")
        return out
    if k == "branch":
        return [p + "branch:"] + emit_block(s.body, ind + 4)
    if k == "conc":
        tv = s.var + "s" if s.kind == "sync" else s.var
        out = [p + f"{tv} := {s.kind}:"]
        for body, val in s.arms:
            out.append(p + "    block:")
            out.extend(emit_block(body, ind + 8))
            out.append(p + f"        {val}")
        if s.kind == "sync":
            out.append(p + f"{s.var} := {tv}({s.pick})")
        return out
    if k == "spawnh":
        if s.kk % 2:
            return [p + f'{s.tvar} := SpH({s.val}, Tag, {s.kk}, {s.d})']
        return [p + f'{s.tvar} := spawn{{Hd({s.val}, Tag, {s.kk}, {s.d})}}']
    if k == "callh":
        return [p + f'{s.var} := Hd({s.val}, Tag, {s.kk}, {s.d})']
    if k == "await":
        return [p + f"{s.var} := {s.tvar}.Await()"]
    if k == "cancel":
        return [p + f"{s.tvar}.Cancel()"]
    if k == "event":
        return [p + f"{s.evar} := {'sticky_event' if s.sticky else 'event'}({s.ty}){{}}"]
    if k == "spawnw":
        return [p + f"{s.tvar} := spawn{{{'Ws' if s.sticky else 'Wt'}({s.evar}, Tag, {s.kk})}}"]
    if k == "signal":
        return [p + f"{s.evar}.Signal({s.val})"]
    if k == "evawait":
        return [p + f"{s.var} := {s.evar}.Await()"]
    if k == "meawait":
        return [p + f"{s.var} := Me.Await()"]
    if k == "hcancel":
        return [p + f"{s.var}.Cancel()"]
    if k == "spawnkill":
        return [p + f"spawn{{Killer({s.var}, Tag, {s.kk}, {s.d})}}"]
    if k == "spawnawait":
        return [p + f"spawn{{Awaiter({s.var}, Tag, {s.kk})}}"]
    if k == "gcall":
        return [p + f"var {s.var}:\u00a7TY\u00a7 = X", p + "if (N > 0):",
                p + f'    I{s.idn} := \u00a7G\u00a7{s.fn}(X, "{{Tag}}g", N - 1, Me)', p + f"    set {s.var} = I{s.idn}"]
    if k == "fcall":
        return [p + f'{s.var} := F{s.fn}(X, X, X, "{{Tag}}f", {s.n}\u00a7RF\u00a7)']
    if k == "rec":
        i, w, t = f"I{s.idn}", f"W{s.idn}", f"T{s.idn}x"
        if s.wrap == "tup":
            a, b, suf = "(X, Y)", "(Y, X)", "t"
            unwrap = f"set {s.var} = {i}(0)"
        else:
            suf, mk, unw = WRAPS[s.wrap]
            a, b = mk("X"), mk("Y")
            unwrap = unw(i, w, s.var)
        zw = {"opt": "option{Z}", "arr": "array{Z}", "box": "bx(u){V := Z}", "tup": "(Z, Z)", "same": "Z"}[s.uwrap]
        call = f'F{s.fn}({a}, {b}, {zw}, "{{Tag}}{suf}", N - 1\u00a7RF\u00a7)'
        out = [p + f"var {s.var}:t = X", p + "if (N > 0):"]
        if s.spawn:
            out.append(p + f"    {t} := spawn{{{call}}}")
            out.extend(emit_block(s.mid, ind + 4))
            if s.cancel:
                out.append(p + f"    {t}.Cancel()")
            else:
                out.append(p + f"    {i} := {t}.Await()")
                out.append(p + "    " + unwrap)
        else:
            out.append(p + f"    {i} := {call}")
            out.append(p + "    " + unwrap)
        return out
    raise ValueError(k)


PRELUDE = '''pt := class:
    K:int
bx(t:type) := class:
    V:t
ShO(O:?int):string = if (V := O?) then "o{V}" else "none"
ShA(A:[]int):string = if (V := A[0]) then "a{V}x{A.Length}" else "empty"
ShT(P:tuple(int, string)):string = "{P(0)}{P(1)}"
Hd(X:t, Tag:string, K:int, D:float where t:type)<suspends>:t =
    defer:
        Print("{Tag} h{K} defer")
    Print("{Tag} h{K} go")
    Sleep(D)
    Print("{Tag} h{K} done")
    X
SpH(X:t, Tag:string, K:int, D:float where t:type):task(t) = spawn{Hd(X, Tag, K, D)}
Wt(E:event(t), Tag:string, K:int where t:type)<suspends>:t =
    defer:
        Print("{Tag} w{K} defer")
    V := E.Await()
    Print("{Tag} w{K} woke")
    V
Ws(E:sticky_event(t), Tag:string, K:int where t:type)<suspends>:t =
    defer:
        Print("{Tag} w{K} defer")
    V := E.Await()
    Print("{Tag} w{K} woke")
    V
Killer(T:task(t), Tag:string, K:int, D:float where t:type)<suspends>:void =
    defer:
        Print("{Tag} k{K} defer")
    Sleep(D)
    T.Cancel()
    Print("{Tag} k{K} cancelled")
    Sleep(0.1)
    Print("{Tag} k{K} end")
Awaiter(T:task(t), Tag:string, K:int where t:type)<suspends>:void =
    defer:
        Print("{Tag} a{K} defer")
    T.Await()
    Print("{Tag} a{K} got")
StartKill(T:task(t), Tag:string, K:int where t:type):void = spawn{Killer(T, Tag, K, -1.0)}
StartAwait(T:task(t), Tag:string, K:int where t:type):void = spawn{Awaiter(T, Tag, K)}
'''


def fix_tup_model():
    pass


def generate(seed):
    rng = random.Random(seed)
    nf = rng.randint(1, 3)
    g = Gen(rng, nf, 2)
    g.evprof = (seed % 2 == 0)
    fns = []
    for i in range(nf):
        body, sc = g.block({"vals": ["X", "Y"], "uvals": ["Z"], "tasks": [], "events": []}, 0, False, rng.randint(2, 6))
        ret = rng.choice(sc["vals"])
        fns.append(Fn(f"F{i}", body, ret))
    # (functions holding their own task's handle, in about half the programs)
    gfns = []
    if rng.random() < 0.55:
        gg = GGen(g, rng.randint(1, 2), nf)
        gfns = [gg.function(i) for i in range(gg.ngf)]
    # Main jobs
    jobs = []
    keys = list(INSTS)
    nj = rng.randint(2, 4)
    mstmts = []
    vid = 1
    for j in range(nj):
        mode = rng.choice(["seq", "seq", "spawn", "sync", "race"])
        if mode in ("seq", "spawn"):
            inst = rng.choice(keys)
            job = (rng.randrange(nf), inst, vid, vid + 1, f"m{j}", rng.randint(0, int(os.environ.get("MAXN", "3")))); vid += 2
            mstmts.append((mode, [job]))
        else:
            inst = rng.choice(keys)
            arms = []
            for a in range(2):
                ia = inst if mode == "race" else rng.choice(keys)
                arms.append((rng.randrange(nf), ia, vid, vid + 1, f"m{j}{'ab'[a]}", rng.randint(0, 2))); vid += 2
            mstmts.append((mode, arms))
        if rng.random() < 0.3:
            mstmts.append(("sleep", rng.choice(DURS)))
        if gfns and (j == 0 or rng.random() < 0.4):
            generic = rng.random() < 0.6
            inst = rng.choice(keys) if generic else "int"
            mstmts.append(("self", (rng.randrange(len(gfns)), generic, inst, vid, f"s{j}", rng.randint(0, 2),
                                    rng.random() < 0.25)))
            vid += 2
    if gfns and rng.random() < 0.5:
        mstmts.append(("sleep", "1.0"))
    return (fns, gfns), mstmts


def emit_refining_block(stmts, depth):
    out = []
    for s in stmts:
        branch = s.k == 'branch'
        rush = s.k == 'conc' and s.kind == 'rush'
        if not depth or not (branch or rush):
            out.extend(emit_stmt(s, 4))
            continue
        for level, (name, obj) in enumerate([('RO', 'RP'), ('RI', 'RQ')][:depth]):
            bind = f'{s.var} := ' if rush and level == 0 else ''
            out.append(' ' * (4 + level * 4) + bind + f'if ({name} := scope_dup[{obj}]):')
        inner = s.var + 'Lifted' if rush else None
        node = St('conc', var=inner, kind=s.kind, arms=s.arms) if rush else s
        out.extend(emit_stmt(node, 4 + depth * 4))
        if rush:
            out.append(' ' * (4 + depth * 4) + inner)
            for level in reversed(range(depth)):
                out += [' ' * (4 + level * 4) + 'else:', ' ' * (8 + level * 4) + 'X']
    return out


def emit_program(fns, mstmts, refining=0, waiting_returns=False):
    fns, gfns = fns
    prelude = PRELUDE
    if waiting_returns:
        prelude = prelude.replace('Hd(X:t,', 'HdValue(X:t,')
        prelude += '''Hd(X:t, Tag:string, K:int, D:float where t:type)<suspends>:t =
    for(A:=0|1,B:=0|1):
        return HdValue(X, Tag, K, D)
    X
'''
    out = [prelude.rstrip("\n")]
    if refining:
        out += ['scope_pair(a:type, b:type) := class {}',
                'scope_dup(t:type) := class(scope_pair(t, t)) {}']
    for i, f in enumerate(gfns):
        out.extend(emit_gfn(f, i, True))
        out.extend(emit_gfn(f, i, False))
    for f in fns:
        ps = ', RP:scope_pair(ra, rb), RQ:scope_pair(rc, rd)' if refining else ''
        ts = ', ra:type, rb:type, rc:type, rd:type' if refining else ''
        out.append(f"{f.name}(X:t, Y:t, Z:u, Tag:string, N:int{ps} where t:type, u:type{ts})<suspends>:t =")
        out.extend(emit_refining_block(f.body, refining))
        out.append('    ' + f.ret)
    out.append("Main()<suspends>:void =")
    pend = []
    for idx, (mode, arg) in enumerate(mstmts):
        if mode == "sleep":
            out.append(f"    Sleep({arg})")
            continue

        def call(job):
            fi, inst, a, b, tag, dep = job
            mk = INSTS[inst][1]
            uk = list(INSTS)[(a * 7 + dep) % len(INSTS)]
            return f'F{fi}({mk(a)}, {mk(b)}, {INSTS[uk][1](a + 500)}, "{tag}", {dep}\u00a7RF\u00a7)'
        if mode == "self":
            gi, generic, inst, a, tag, dep, aw = arg
            out.append(f"    ME{idx} := sticky_event(task({INSTS[inst][0]})){{}}")
            out.append(f'    MT{idx} := spawn{{{"G" if generic else "Gi"}{gi}({INSTS[inst][1](a)}, "{tag}", {dep}, ME{idx})}}')
            out.append(f"    ME{idx}.Signal(MT{idx})")
            if aw:
                pend.append((idx, (gi, inst, a, a, tag, dep)))
            continue
        if mode == "seq":
            job = arg[0]
            out.append(f"    R{idx} := {call(job)}")
            out.append(f'    Print("{job[4]} = {INSTS[job[1]][2](f"R{idx}")}")')
        elif mode == "spawn":
            job = arg[0]
            out.append(f"    MT{idx} := spawn{{{call(job)}}}")
            pend.append((idx, job))
        elif mode == "sync":
            out.append(f"    S{idx} := sync:")
            for job in arg:
                out.append(f"        {call(job)}")
            for a, job in enumerate(arg):
                out.append(f"    S{idx}x{a} := S{idx}({a})")
                out.append(f'    Print("{job[4]} = {INSTS[job[1]][2](f"S{idx}x{a}")}")')
        elif mode == "race":
            out.append(f"    R{idx} := race:")
            for job in arg:
                out.append(f"        {call(job)}")
            out.append(f'    Print("{arg[0][4]}|{arg[1][4]} = {INSTS[arg[0][1]][2](f"R{idx}")}")')
    for idx, job in pend:
        out.append(f"    MR{idx} := MT{idx}.Await()")
        out.append(f'    Print("{job[4]} = {INSTS[job[1]][2](f"MR{idx}")}")')
    out.append('    Print("main end")')
    extra = ', scope_dup(int){}, scope_dup(string){}' if refining else ''
    return ("\n".join(out) + "\n").replace('\u00a7RF\u00a7', extra)


def model_program(fns, mstmts):
    global S
    S = Sched()
    fns, gfns = fns
    FNS.clear(); GFNS.clear()
    for i, f in enumerate(fns):
        FNS[i] = f
    for i, f in enumerate(gfns):
        GFNS[i] = f

    def main():
        fr = Frame({})
        pend = []
        try:
            for idx, (mode, arg) in enumerate(mstmts):
                if mode == "sleep":
                    yield from m_sleep(arg)
                    continue

                def cgen(job):
                    fi, inst, a, b, tag, dep = job
                    return m_call(FNS[fi], {"X": a, "Y": b, "Z": a + 500, "Tag": tag, "N": dep})

                def show(job, v):
                    return INSTS[job[1]][3](v)
                if mode == "self":
                    gi, generic, inst, a, tag, dep, aw = arg
                    ev = Event(True)
                    t = m_spawn(m_call(GFNS[gi], {"X": a, "Tag": tag, "N": dep, "Me": ev}))
                    m_signal(ev, t)
                    if aw:
                        pend.append(((gi, inst, a, a, tag, dep), t))
                    continue
                if mode == "seq":
                    v = yield from cgen(arg[0])
                    S.p(f"{arg[0][4]} = {show(arg[0], v)}")
                elif mode == "spawn":
                    pend.append((arg[0], m_spawn(cgen(arg[0]))))
                else:
                    fakefr = Frame({"Tag": "?", "N": 0})
                    arms = []
                    st = St("conc", kind=mode, var="_", arms=[], pick=0)
                    v = yield from conc_gens(mode, [cgen(j) for j in arg], fakefr)
                    if mode == "sync":
                        for a, job in enumerate(arg):
                            S.p(f"{job[4]} = {show(job, v[a])}")
                    else:
                        S.p(f"{arg[0][4]}|{arg[1][4]} = {show(arg[0], v)}")
            for job, t in pend:
                v = yield from m_await_task(t)
                S.p(f"{job[4]} = {INSTS[job[1]][3](v)}")
            S.p("main end")
        finally:
            stop_all(fr)
    code = S.run(main())
    return S.out, code


def conc_gens(kind, gens, fr):
    """sync/race over ready-made arm generators (Main's arms)."""
    pend = []
    results = [None] * len(gens)
    winner = None; won = False
    finished = False
    for i, g in enumerate(gens):
        try:
            next(g); pend.append((i, g))
        except StopIteration as e:
            results[i] = e.value
            if kind != "sync":
                winner = e.value; won = True
                break
    try:
        if kind == "sync":
            while pend:
                yield
                for item in list(pend):
                    try:
                        next(item[1])
                    except StopIteration as e:
                        results[item[0]] = e.value; pend.remove(item)
            finished = True
            return tuple(results)
        while not won:
            yield
            for item in list(pend):
                try:
                    next(item[1])
                except StopIteration as e:
                    winner = e.value; won = True; pend.remove(item)
                    break
        finished = True
        for item in reversed(pend):
            item[1].close()
        pend = []
        return winner
    finally:
        if not finished:
            for item in reversed(pend):
                item[1].close()


def main():
    seed = int(sys.argv[1]); outdir = sys.argv[2]
    fns, mstmts = generate(seed)
    src = emit_program(fns, mstmts, refining=(1 + bool(seed & 4)) if seed & 2 else 0,
                       waiting_returns=bool(seed & 8))
    with open(os.path.join(outdir, f"g{seed}.verse"), "w") as f:
        f.write(src)
    try:
        out, code = model_program(fns, mstmts)
        exp = "".join(l + "\n" for l in out) + f"exit={code}\n"
    except RuntimeError as e:
        exp = f"MODEL ERROR {e}\n"
    with open(os.path.join(outdir, f"g{seed}.expected"), "w") as f:
        f.write(exp)


if __name__ == "__main__":
    main()
