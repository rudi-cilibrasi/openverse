#!/usr/bin/env python3
"""Event resumption (#513; the Book's rule since awaiters run inside
Signal): random programs with a model of the expected output (from the
reviews of #533 and #539).

usage: event_fifo.py SEED OUT.exp > PROGRAM.verse

Actors: Main itself, tasks spawned by Main, branches of Main, tasks spawned
by a task in its first run, branches inside a spawned task, and the arms of
a sync or race in a task of their own, each with its own turn. At each tick
exactly one free actor acts: it starts awaiting an event, or signals one.
A woken actor prints, may at once signal another event (a chain), then
sleeps to its next step. Expected (the Book's API, event's Signal): each
Signal's waiters go on in the order they began waiting, each until it waits
again, inside the Signal: a chain's own waiters inside the chain's Signal,
before the next waiter of the outer one (depth first), and the signaller
goes on after them. The programs are generated as for the earlier rule
(FIFO after the signaller's run, breadth first), whose woken sets are the
same; only the order of the output differs.
"""
import random, sys

seed = int(sys.argv[1]); out_e = sys.argv[2]
rng = random.Random(seed)
NEV = rng.choice([1, 2, 3])
NACT = rng.randint(2, 7)
kinds = ["main"] + [rng.choice(["spawn", "spawn", "branch", "nested", "subbranch", "arm", "arm"]) for _ in range(NACT)]
# nested/subbranch need a parent spawn: parent is the first earlier "spawn"
parent = {}
for i, k in enumerate(kinds):
    if k in ("nested", "subbranch"):
        ps = [j for j in range(1, i) if kinds[j] == "spawn"]
        if not ps:
            kinds[i] = "spawn"
        else:
            parent[i] = rng.choice(ps)
PDEEP = rng.choice([0.0, 0.0, 0.3])
deep = [rng.random() < PDEEP for _ in kinds]
names = ["Main"] + [f"A{i}" for i in range(1, len(kinds))]
N = rng.randint(8, 30)
# simulation
free_at = [0] * len(kinds)          # tick after which actor may act (acts at tick > free_at)
waiting = [None] * len(kinds)       # event or None
waitq = {e: [] for e in range(NEV)} # actors waiting on e, in wait order
steps = [[] for _ in kinds]         # per actor: list of (tick, kind, ev, chain_ev)
expected = []
def wake(e, t, queue):
    for a in waitq[e]:
        waiting[a] = None
        steps[a][-1].append(t)
        queue.append((a, e))
    waitq[e] = []
actions = []                        # (tick, actor, kind, event), in order
for t in range(1, N + 1):
    cands = [a for a in range(len(kinds)) if waiting[a] is None and free_at[a] < t]
    if not cands:
        continue
    a = rng.choice(cands)
    e = rng.randrange(NEV)
    if rng.random() < 0.55:
        actions.append((t, a, "await", e))
        steps[a].append([t, "await", e, None])
        waiting[a] = e
        waitq[e].append(a)
        expected.append(f"w {names[a]} {e}")
    else:
        actions.append((t, a, "signal", e))
        steps[a].append([t, "signal", e, None])
        free_at[a] = t
        expected.append(f"s {names[a]} {e} {t}")
        queue = []
        wake(e, t, queue)
        expected.append(f"r {names[a]} {e}")
        i = 0
        while i < len(queue):
            b, eb = queue[i]; i += 1
            expected.append(f"got {names[b]} {eb} {t}")
            free_at[b] = t
            # find b's await step and maybe give it a chain signal
            if rng.random() < 0.3:
                e2 = rng.randrange(NEV)
                steps[b][-1][3] = e2
                expected.append(f"cs {names[b]} {e2}")
                wake(e2, t, queue)
                expected.append(f"cr {names[b]} {e2}")
# final signals: wake everyone left, from a dedicated task
fin_ticks = []
for k, e in enumerate(range(NEV)):
    t = N + 1 + k
    fin_ticks.append((t, e))
    expected.append(f"s Fin {e} {t}")
    queue = []
    wake(e, t, queue)
    expected.append(f"r Fin {e}")
    for b, eb in queue:
        expected.append(f"got {names[b]} {eb} {t}")
END = N + NEV + 4
expected.append("end")
# the expected output: the actions replayed with each Signal's round run
# inside it, depth first (the chains the generation above chose)
expected = []
waitq2 = {e: [] for e in range(NEV)}
step_at = [0] * len(kinds)
pending_step = {}
def run_round(e, t):
    rnd = waitq2[e]
    waitq2[e] = []
    for b in rnd:
        k = pending_step.pop(b)
        expected.append(f"got {names[b]} {e} {t}")
        ce = steps[b][k][3]
        if ce is not None:
            expected.append(f"cs {names[b]} {ce}")
            run_round(ce, t)
            expected.append(f"cr {names[b]} {ce}")
for (t, a, kind, e) in actions:
    k = step_at[a]; step_at[a] += 1
    if kind == "await":
        expected.append(f"w {names[a]} {e}")
        waitq2[e].append(a)
        pending_step[a] = k
    else:
        expected.append(f"s {names[a]} {e} {t}")
        run_round(e, t)
        expected.append(f"r {names[a]} {e}")
for (t, e) in fin_ticks:
    expected.append(f"s Fin {e} {t}")
    run_round(e, t)
    expected.append(f"r Fin {e}")
expected.append("end")

L = []
def emit(s): L.append(s)
evparams = ", ".join(f"E{e}:event(int)" for e in range(NEV))
evargs = ", ".join(f"E{e}" for e in range(NEV))
if any(deep):
  emit("Deep(E:event(int), N:int)<suspends>:int =")
  emit("    if (N > 0) then Deep(E, N - 1) else E.Await()")
  emit("D1(E:event(int))<suspends>:int = D2(E)")
  emit("D2(E:event(int))<suspends>:int = D3(E)")
  emit("D3(E:event(int))<suspends>:int = D4(E)")
  emit("D4(E:event(int))<suspends>:int = D5(E)")
  emit("D5(E:event(int))<suspends>:int = D6(E)")
  emit("D6(E:event(int))<suspends>:int = E.Await()")

# Steps after a wake: we need Sleep(next - wake); the wake tick is the value.
def body2(a, ind, children):
    out = []
    p = " " * ind
    cur = 0
    for st in steps[a]:
        t, kind, e, ce = st[:4]
        out.append(f"{p}Sleep({t - cur}.0 / 30.0)")
        if kind == "await":
            out.append(f'{p}Print("w {names[a]} {e}")')
            if deep[a]:
                call = rng.choice([f"Deep(E{e}, {rng.randint(3, 8)})", f"D1(E{e})"])
            else:
                call = f"E{e}.Await()"
            out.append(f"{p}V{t} := {call}")
            out.append(f'{p}Print("got {names[a]} {e} {{V{t}}}")')
            if ce is not None:
                out.append(f'{p}Print("cs {names[a]} {ce}")')
                out.append(f"{p}E{ce}.Signal(V{t})")
                out.append(f'{p}Print("cr {names[a]} {ce}")')
            cur = st[4] if len(st) > 4 else 10**6
        else:
            out.append(f'{p}Print("s {names[a]} {e} {t}")')
            out.append(f"{p}E{e}.Signal({t})")
            out.append(f'{p}Print("r {names[a]} {e}")')
            cur = t
    return out, cur

for a in range(1, len(kinds)):
    if kinds[a] in ("spawn", "nested"):
        emit(f"Actor{a}({evparams})<suspends>:void =")
        # children: nested spawns and subbranches
        for c in range(1, len(kinds)):
            if parent.get(c) == a and kinds[c] == "nested":
                emit(f"    spawn{{Actor{c}({evargs})}}")
        for c in range(1, len(kinds)):
            if parent.get(c) == a and kinds[c] == "subbranch":
                emit("    branch:")
                lines, _ = body2(c, 8, [])
                for l in lines: emit(l)
                emit("        Sleep(1000.0)")
        lines, cur = body2(a, 4, [])
        for l in lines: emit(l)
        # stay alive (for subbranches) until END
        emit(f"    Sleep({END - cur}.0 / 30.0)")
arms = [a for a in range(1, len(kinds)) if kinds[a] == "arm"]
if arms:
    emit(f"Host({evparams})<suspends>:void =")
    emit("    " + rng.choice(["sync", "race"]) + ":")
    for a in arms:
        emit("        block:")
        lines, cur = body2(a, 12, [])
        for l in lines: emit(l)
        emit(f"            Sleep({END - cur}.0 / 30.0)")
    if len(arms) < 2:
        emit("        block:")
        emit(f"            Sleep({END}.0 / 30.0)")
emit(f"Fin({evparams})<suspends>:void =")
cur = 0
for (t, e) in fin_ticks:
    emit(f"    Sleep({t - cur}.0 / 30.0)")
    emit(f'    Print("s Fin {e} {t}")')
    emit(f"    E{e}.Signal({t})")
    emit(f'    Print("r Fin {e}")')
    cur = t
emit("Main()<suspends>:void =")
for e in range(NEV):
    emit(f"    E{e} := event(int){{}}")
# start order: random order of spawns and branches of Main, and Fin
starts = [a for a in range(1, len(kinds)) if kinds[a] in ("spawn", "branch")] + ["Fin"] + (["Host"] if arms else [])
rng.shuffle(starts)
for a in starts:
    if a == "Fin":
        emit(f"    spawn{{Fin({evargs})}}")
    elif a == "Host":
        emit(f"    spawn{{Host({evargs})}}")
    elif kinds[a] == "spawn":
        emit(f"    spawn{{Actor{a}({evargs})}}")
    else:
        lines, _ = body2(a, 8, [])
        if not lines:
            continue
        emit("    branch:")
        for l in lines: emit(l)
lines, cur = body2(0, 4, [])
for l in lines: emit(l)
emit(f"    Sleep({END - cur}.0 / 30.0)")
emit('    Print("end")')
sys.stdout.write("\n".join(L) + "\n")
open(out_e, "w").write("exit=0\n" + "\n".join(expected) + "\n")
