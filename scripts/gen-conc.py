#!/usr/bin/env python3
"""Random openverse programs that stress the concurrency lowering (#156).

usage: gen-conc.py SEED   (deterministic per seed; prints one program)

A program combines
  - suspends helpers that sleep, print and defer;
  - a parametric class box(t) with a suspends method overridden by a generic
    subclass and by a class that fixes the type argument (#142, #171), and an
    immediate method overridden the same way, reached through a holder's
    field (frame-resident receivers, #179) and from generic code;
  - generic suspends functions with branch, rush, race, sync, spawn and
    defer (specialised at each type they are used at, #174);
  - spawns of plain calls and of dispatched methods (#173), awaited and
    cancelled, nested spawns (#180), and of methods every class fixes, in
    generic code (#204);
  - a subscribable_event with a function and a method subscribed (#210);
  - rush losers that outlive the rush, branches nested in branches (#187);
  - a class keeping one type argument and fixing another, overriding with a
    narrower result (#198).
Main prints everything it computes. Every program ends: sleeps are short,
and nothing waits forever.
"""
import random
import sys

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
R = random.Random(seed)
out = []


def emit(level, text):
    out.append("    " * level + text)


def dur():
    return R.choice(["0.0", "0.1", "0.2", "0.5", "1.0"])


NW = R.randint(2, 4)
# helpers W0..: Wi(N:int)<suspends>:int
for i in range(NW):
    emit(0, f"W{i}(N:int)<suspends>:int =")
    if R.random() < 0.5:
        emit(1, "defer:")
        emit(2, f'Print("W{i} defer {{N}}")')
    emit(1, f"Sleep({dur()})")
    if R.random() < 0.5:
        emit(1, f'Print("W{i} {{N}}")')
    emit(1, f"N + {i}")

emit(0, "Take(T:task(int))<suspends>:int = T.Await() + 1")

# the class hierarchy
emit(0, "box(t:type) := class:")
emit(1, "V:t")
emit(1, "Get()<suspends>:t =")
emit(2, f"Sleep({dur()})")
emit(2, "V")
emit(1, "Peek():t = V")
emit(0, "sub(t:type) := class(box(t)):")
emit(1, "Get<override>()<suspends>:t =")
if R.random() < 0.6:
    emit(2, "defer:")
    emit(3, 'Print("sub get defer")')
emit(2, f"Sleep({dur()})")
emit(2, "V")
emit(0, "int_box := class(box(int)):")
emit(1, "Get<override>()<suspends>:int =")
emit(2, f"Sleep({dur()})")
emit(2, "V + 100")
emit(1, "Peek<override>():int = V + 1000")
emit(0, "holder(t:type) := class:")
emit(1, "B:box(t)")
# an abstract hierarchy whose classes all fix the type argument (#157 placeholders)
emit(0, "expr(t:type) := class<abstract>:")
emit(1, "Eval()<suspends>:t")
emit(0, "lit := class(expr(int)):")
emit(1, "N:int")
emit(1, "Eval<override>()<suspends>:int =")
emit(2, f"Sleep({dur()})")
emit(2, "N")
emit(0, "neg := class(expr(int)):")
emit(1, "E:expr(int)")
emit(1, "Eval<override>()<suspends>:int = -E.Eval()")
emit(0, "word := class(expr(string)):")
emit(1, "S:string")
emit(1, 'Eval<override>()<suspends>:string = S')
emit(0, "EvalAll(Es:[]expr(t), X:t where t:type)<suspends>:t =")
emit(1, "var R:t = X")
emit(1, "for (E : Es):")
emit(2, "set R = E.Eval()")
if R.random() < 0.5:
    emit(1, "branch:")
    emit(2, f"Sleep({dur()})")
    emit(2, 'Print("evalall branch")')
emit(1, "R")
# spawning and racing a method that every class fixes, in code generic over
# the class: compiled at each type (#204)
emit(0, "SpawnEval(E:expr(t), F:expr(t) where t:type)<suspends>:t =")
emit(1, "T := spawn{E.Eval()}")
if R.random() < 0.5:
    emit(1, "U := spawn{F.Eval()}")
    emit(1, "U.Cancel()" if R.random() < 0.5 else "UV := U.Await()")
if R.random() < 0.5:
    emit(1, "race:")
    emit(2, "T.Await()")
    emit(2, "F.Eval()")
else:
    emit(1, "T.Await()")
# an interface with a field at different places (#157 accessors)
emit(0, "slot(t:type) := interface:")
emit(1, "var Item:t")
emit(0, "islot := class(slot(int)):")
emit(1, "A:int = 0")
emit(0, "sslot := class(slot(string)):")
emit(1, "B:string = \"b\"")
emit(1, "C:int = 1")
emit(0, "Bump(S:slot(t), X:t where t:type)<suspends>:t =")
emit(1, f"Sleep({dur()})")
emit(1, "set S.Item = X")
emit(1, f"Sleep({dur()})")
emit(1, "S.Item")
# a class that fixes one type argument and keeps the other, overriding with
# a narrower result (#198)
emit(0, "pr(a:type, b:type) := class:")
emit(1, "A:a")
emit(1, "B:b")
emit(1, "First()<suspends>:a = A")
emit(1, "Me()<suspends>:pr(a, b) = Self")
emit(0, "ipr(b:type) := class(pr(int, b)):")
emit(1, "First<override>()<suspends>:int =")
if R.random() < 0.5:
    emit(2, "defer:")
    emit(3, 'Print("ipr first defer")')
emit(2, f"Sleep({dur()})")
emit(2, "A + 1")
emit(1, "Me<override>()<suspends>:ipr(b) =")
emit(2, f"Sleep({dur()})")
emit(2, "Self")
emit(0, "PrUse(P:pr(a, b), X:a where a:type, b:type)<suspends>:a =")
emit(1, "Q := P.Me()")
if R.random() < 0.5:
    emit(1, "race:")
    emit(2, "Q.First()")
    emit(2, "block:")
    emit(3, f"Sleep({dur()})")
    emit(3, "X")
else:
    emit(1, "Q.First()")
# events
emit(0, "Waiter(E:event(int), K:int)<suspends>:int =")
emit(1, "V := E.Await()")
emit(1, 'Print("waiter {K} got {V}")')
emit(1, "V + K")
# a function with a named parameter
emit(0, "Named(N:int, ?Extra:int = 5)<suspends>:int =")
emit(1, f"Sleep({dur()})")
emit(1, "N + Extra")
# return from an arm, and from a rush loser after the rush
emit(0, "ArmReturn(N:int)<suspends>:int =")
emit(1, "Q := rush:")
emit(2, "block:")
emit(3, f"Sleep({dur()})")
emit(3, "N")
emit(2, "block:")
emit(3, "defer:")
emit(4, 'Print("arm return defer")')
emit(3, f"Sleep({dur()})")
emit(3, "return N + 50")
emit(1, f"Sleep({dur()})")
emit(1, "Q")


def wcall(arg):
    return f"W{R.randrange(NW)}({arg})"


def int_stmt(level, n, allow_roots):
    """A statement printing an int computed by suspends code."""
    k = R.randrange(13 if allow_roots else 6)
    if k >= 9:
        v = f"V{len(out)}"
        if k == 9:
            emit(level, f"{v} := event(int){{}}")
            emit(level, f"{v}T := spawn{{Waiter({v}, {n})}}")
            emit(level, f"Sleep({dur()})")
            emit(level, f"{v}.Signal({n} * 2)")
            emit(level, f'Print("event {{{v}T.Await()}}")')
        elif k == 10:
            emit(level, f'Print("named {{Named({n})}} {{Named({n}, ?Extra := 1)}}")')
        elif k == 11:
            emit(level, f'Print("armreturn {{ArmReturn({n})}}")')
        else:
            emit(level, f"{v} := sync:")
            emit(level + 1, "block:")
            emit(level + 2, "branch:")
            emit(level + 3, "defer:")
            emit(level + 4, 'Print("arm branch defer")')
            emit(level + 3, f"Sleep({dur()})")
            emit(level + 2, wcall(n))
            emit(level + 1, wcall(n))
            emit(level, f'Print("sync arms {{{v}(0)}}")')
        return
    v = f"V{len(out)}"
    if k == 0:
        emit(level, f'Print("{{{wcall(n)}}}")')
    elif k == 1:
        emit(level, f"{v} := race:")
        emit(level + 1, wcall(n))
        emit(level + 1, "block:")
        emit(level + 2, f"Sleep({dur()})")
        emit(level + 2, f"{R.randint(0, 9)}")
        emit(level, f'Print("race {{{v}}}")')
    elif k == 2:
        emit(level, f"{v} := sync:")
        emit(level + 1, wcall(n))
        emit(level + 1, wcall(f"{n} + 1"))
        emit(level, f'Print("sync {{{v}(0)}} {{{v}(1)}}")')
    elif k == 3:
        emit(level, f"{v} := spawn{{{wcall(n)}}}")
        if R.random() < 0.4:
            emit(level, f"Sleep({dur()})")
            emit(level, f"{v}.Cancel()")
            emit(level, 'Print("cancelled")')
        else:
            emit(level, f'Print("awaited {{{v}.Await()}}")')
    elif k == 4:
        emit(level, "for (I := 1..2):")
        emit(level + 1, f'Print("loop {{{wcall("I")}}}")')
    elif k == 5:
        emit(level, "defer:")
        emit(level + 1, f'Print("defer {{{n}}}")')
    elif k == 6:
        emit(level, "branch:")
        emit(level + 1, "defer:")
        emit(level + 2, 'Print("branch defer")')
        emit(level + 1, f"Sleep({dur()})")
        if R.random() < 0.4:
            emit(level + 1, "branch:")
            emit(level + 2, "defer:")
            emit(level + 3, 'Print("inner branch defer")')
            emit(level + 2, f"Sleep({dur()})")
        emit(level + 1, 'Print("branch ran")')
    elif k == 7:
        emit(level, f"{v} := rush:")
        emit(level + 1, wcall(n))
        emit(level + 1, "block:")
        emit(level + 2, "defer:")
        emit(level + 3, 'Print("rush arm defer")')
        emit(level + 2, f"Sleep({dur()})")
        emit(level + 2, f"{R.randint(0, 9)}")
        emit(level, f'Print("rush {{{v}}}")')
    else:
        # a spawn in a spawned call's arguments
        emit(level, f"{v} := spawn{{Take(spawn{{{wcall(n)}}})}}")
        emit(level, f'Print("nested {{{v}.Await()}}")')


# generic functions G0..: G(X:t, H:holder(t), N:int)<suspends>:t
NG = R.randint(1, 3)
for j in range(NG):
    emit(0, f"G{j}(X:t, H:holder(t), N:int where t:type)<suspends>:t =")
    for _ in range(R.randint(1, 4)):
        int_stmt(1, "N", True)
    if R.random() < 0.5:
        emit(1, f"P{j} := H.B.Peek()")
    k = R.randrange(4)
    if k == 0:
        emit(1, "X")
    elif k == 1:
        emit(1, "H.B.Get()")
    elif k == 2:
        emit(1, "if (N > 2) then H.B.Get() else X")
    else:
        emit(1, "H.B.Peek()")

# a generic function calling another at its own type (specialised in turn)
emit(0, "Chain(X:t, H:holder(t), N:int where t:type)<suspends>:t =")
emit(1, f"G{R.randrange(NG)}(X, H, N)")

# a function spawning a dispatched method on a closed receiver
emit(0, "Kick(B:box(int)):task(int) = spawn{B.Get()}")

# a subscribable_event (#210): a function and a method subscribed,
# signalled, cancelled, awaited
emit(0, "evlog := class:")
emit(1, "var Sum:int = 0")
emit(1, "On(X:int):void =")
emit(2, "set Sum += X")
emit(0, 'EvShow(X:int):void = Print("ev {X}")')
emit(0, "EvRun(N:int)<suspends>:void =")
emit(1, "E := subscribable_event(int){}")
emit(1, "L := evlog{}")
emit(1, "S1 := E.Subscribe(EvShow)")
emit(1, "S2 := E.Subscribe(L.On)")
for _ in range(R.randint(1, 4)):
    k = R.randrange(4)
    if k == 0:
        emit(1, f"E.Signal(N + {R.randint(0, 9)})")
    elif k == 1:
        emit(1, R.choice(["S1.Cancel()", "S2.Cancel()"]))
    elif k == 2:
        emit(1, "race:")
        emit(2, 'Print("evaw {E.Await()}")')
        emit(2, "block:")
        emit(3, f"Sleep({dur()})")
        emit(3, f"E.Signal({R.randint(10, 19)})")
        emit(3, f"Sleep({dur()})")
    else:
        emit(1, f"if (S3 := E.Subscribe(EvShow), N > {R.randint(0, 9)}) then E.Signal(N) else E.Signal(-N)")
emit(1, 'Print("evsum {L.Sum}")')
emit(0, "Main()<suspends>:void =")
receivers = [("int", "int_box{V := %d}"), ("int", "sub(int){V := %d}"), ("int", "box(int){V := %d}"),
             ("string", 'box(string){V := "s%d"}'), ("string", 'sub(string){V := "t%d"}')]
for _ in range(R.randint(2, 6)):
    c = R.randrange(11)
    if c == 10:
        emit(1, f"EvRun({R.randint(1, 9)})")
        continue
    if c == 9:
        n = R.randint(1, 9)
        if R.random() < 0.5:
            emit(1, f'Print("spawneval {{SpawnEval(lit{{N := {n}}}, neg{{E := lit{{N := {n + 1}}}}})}}")')
        else:
            emit(1, f'Print("spawneval {{SpawnEval(word{{S := "w{n}"}}, word{{S := "v{n}"}})}}")')
        continue
    if c == 8:
        n = R.randint(1, 9)
        if R.random() < 0.5:
            emit(1, f'Print("pr {{PrUse(ipr(string){{A := {n}, B := "x"}}, 0)}}")')
        else:
            emit(1, f'Print("pr {{PrUse(pr(int, logic){{A := {n}, B := true}}, 0)}}")')
        continue
    if c == 4:
        n = R.randint(1, 9)
        emit(1, f'Print("evalall {{EvalAll(array{{lit{{N := {n}}}, neg{{E := lit{{N := {n + 1}}}}}}}, 0)}}")')
        continue
    if c == 5:
        n = R.randint(1, 9)
        emit(1, f'Print("bump {{Bump(islot{{Item := {n}}}, {n + 1})}} {{Bump(sslot{{Item := "a"}}, "z")}}")')
        continue
    if c == 6:
        t, mk = R.choice(receivers)
        n = R.randint(1, 9)
        x = str(n) if t == "int" else f'"x{n}"'
        emit(1, f'Print("chain {{Chain({x}, holder({t}){{B := {mk % n}}}, {n})}}")')
        continue
    if c == 7:
        n = R.randint(1, 9)
        emit(1, f'Print("words {{EvalAll(array{{word{{S := "w{n}"}}}}, "none")}}")')
        continue
    if c == 0:
        int_stmt(1, str(R.randint(1, 9)), False)
    elif c == 1:
        t, mk = R.choice(receivers)
        n = R.randint(1, 9)
        x = str(n) if t == "int" else f'"x{n}"'
        emit(1, f'Print("G {{G{R.randrange(NG)}({x}, holder({t}){{B := {mk % n}}}, {n})}}")')
    elif c == 2:
        mk = R.choice(["int_box{V := %d}", "sub(int){V := %d}", "box(int){V := %d}"])
        emit(1, f'Print("kick {{Kick({mk % R.randint(1, 9)}).Await()}}")')
    else:
        emit(1, f"Sleep({dur()})")
emit(1, 'Print("end")')
print("\n".join(out))
