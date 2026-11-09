#!/usr/bin/env python3
"""Random Verse programs whose generic <suspends> functions call each other
at ever bigger types (polymorphic recursion), with branch, rush, race, sync,
spawn, Await, Cancel and defer at those types: generic task roots (#244).

usage: gen-conc-poly.py SEED   (deterministic per seed; prints one program)

Written for the review of #249. scripts/fuzz-conc-poly.sh runs each program
with and without OPENVERSE_GENERIC_ROOTS=1, Lean against C.
"""
import random
import sys
R = random.Random(int(sys.argv[1]))
out = []
def emit(l, s): out.append("    " * l + s)
def dur(): return R.choice(["0.1", "0.2", "0.3", "0.5", "1.0"])
NF = R.randint(1, 3)
uid = [0]
def tag():
    uid[0] += 1
    return f"s{uid[0]}"
def grow(x):
    return R.choice([f"array{{{x}}}", f"option{{{x}}}", f"({x}, N)", f"array{{{x}, {x}}}"])
emit(0, "Leaf(X:t, D:float, Tag:string where t:type)<suspends>:t =")
emit(1, "defer:")
emit(2, 'Print("leaf {Tag} unwound")')
emit(1, "Sleep(D)")
emit(1, 'Print("leaf {Tag}")')
emit(1, "X")
emit(0, "Two(A:a, B:b, Tag:string where a:type, b:type)<suspends>:int =")
emit(1, "Sleep(0.2)")
emit(1, 'Print("two {Tag}")')
emit(1, "2")
for j in range(NF):
    emit(0, f"F{j}(X:t, N:int where t:type)<suspends>:int =")
    tasks = []
    used_branch = False
    for _ in range(R.randint(1, 5)):
        k = R.randrange(9)
        tg = tag()
        if k == 0:
            emit(1, "branch:")
            if R.random() < 0.5:
                emit(2, "defer:")
                emit(3, f'Print("branch {tg} N={{N}} unwound")')
            emit(2, f"Sleep({dur()})")
            if R.random() < 0.5:
                emit(2, f'Y{tg} := Leaf({grow("X")}, {dur()}, "b{tg}")')
            emit(2, f'Print("branch {tg} N={{N}}")')
            if R.random() < 0.3:
                emit(2, "branch:")
                emit(3, f"Sleep({dur()})")
                emit(3, f'Print("inner branch {tg} N={{N}}")')
        elif k == 1:
            emit(1, f"R{tg} := rush:")
            emit(2, "block:")
            emit(3, f"Sleep({dur()})")
            emit(3, "1")
            emit(2, "block:")
            emit(3, f'Z{tg} := Leaf(X, {dur()}, "r{tg}")')
            emit(3, "2")
            emit(1, f'Print("rush {tg} {{R{tg}}}")')
        elif k == 2:
            emit(1, f"Q{tg} := race:")
            emit(2, "block:")
            emit(3, f'Z{tg} := Leaf({grow("X")}, {dur()}, "q{tg}")')
            emit(3, "1")
            emit(2, "block:")
            emit(3, f"Sleep({dur()})")
            emit(3, "2")
            emit(1, f'Print("race {tg} {{Q{tg}}}")')
        elif k == 3:
            emit(1, f"P{tg} := sync:")
            emit(2, f'Leaf(X, {dur()}, "y{tg}")')
            emit(2, f'Two(X, {grow("X")}, "y{tg}")')
        elif k == 4 or k == 5:
            v = f"T{tg}"
            if R.random() < 0.5:
                emit(1, f'{v} := spawn{{Leaf({grow("X")}, {dur()}, "t{tg}")}}')
            else:
                emit(1, f'{v} := spawn{{Two({grow("X")}, X, "t{tg}")}}')
            tasks.append(v)
        elif k == 6:
            emit(1, "defer:")
            emit(2, f'Print("F{j} defer {tg} N={{N}}")')
        elif k == 7 and tasks:
            v = R.choice(tasks)
            if R.random() < 0.5:
                emit(1, f"{v}.Cancel()")
            else:
                emit(1, f"{v}.Await()")
        else:
            emit(1, f"Sleep({dur()})")
    calls = []
    for _ in range(R.randint(1, 2)):
        g = R.randrange(NF)
        if R.random() < 0.3:
            calls.append(f"spawn{{F{g}({grow('X')}, N - 1)}}.Await()")
        else:
            calls.append(f"F{g}({grow('X')}, N - 1)")
    emit(1, f"if (N > 0) then 1 + {' + '.join(calls)} else 0")
emit(0, "Main()<suspends>:void =")
d = R.randint(1, 3)
if R.random() < 0.4:
    emit(1, f'C := spawn{{F{R.randrange(NF)}("s", {d})}}')
    emit(1, f"Sleep({dur()})")
    emit(1, "C.Cancel()")
    emit(1, 'Print("cancelled C")')
emit(1, f'Print("result {{F0(1, {d})}}")')
emit(1, "Sleep(3.0)")
emit(1, 'Print("end")')
print("\n".join(out))
