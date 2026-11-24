#!/usr/bin/env python3
"""Generate a random Verse program over ints beyond 64 bits (#724) and the
output Verse gives it, computed with Python's unbounded ints under the Verse
VM's rules (Epic's UEFN 43.12 with the Verse VM, docs/LANGUAGE.md, "int"):
`+`, `-`, `*`, negation and `Abs` exact; `Floor(X / Y)`, `Ceil(X / Y)`,
`Quotient[X, Y]` and `Mod[X, Y]` (Euclidean) exact, failing on a zero
divisor; comparisons, `=` and `<>` exact; `set +=`, `-=`, `*=`; ints as map
keys; an index or a range bound beyond 64 bits; `X * 1.0`, the nearest double
(Python's float(X), ties to even; past the largest double, Inf); rationals
`X / Y` and their `Floor`, `Ceil`; and algebraic laws, which hold. The values
are printed in decimal by a function of the program (`Show`, 18 digits at a
time), since `ToString` of an int beyond 64 bits is a runtime error; a
quarter of the seeds end with such a `ToString`, so the program ends with
exit 2 and `error: overflow`.

usage: gen-bigint.py SEED OUT.verse OUT.expected
(OUT.expected is the output, then `exit=N`, then stderr's lines)
"""
import math
import random
import sys
from fractions import Fraction

seed, out_verse, out_expected = int(sys.argv[1]), sys.argv[2], sys.argv[3]
rng = random.Random(seed)
LO, HI = -2 ** 63, 2 ** 63 - 1


def fits(x):
    return LO <= x <= HI


def lit(x):
    """An int literal of the program (it fits in 64 bits)."""
    assert fits(x)
    return f"({LO + 1} - 1)" if x == LO else (f"({x})" if x < 0 else str(x))


def operand64():
    k = rng.random()
    if k < 0.3:
        return rng.choice([0, 1, -1, 2, -2, 3, HI, LO, HI - 1, LO + 1, 10 ** 18, -(10 ** 18),
                           2 ** 32, 2 ** 62, -(2 ** 62)])
    if k < 0.6:
        return rng.randint(-1000, 1000)
    return rng.randint(LO, HI)


def flit(d):
    """A float literal of the double d (finite), or Inf / -Inf."""
    if math.isinf(d):
        return "Inf" if d > 0 else "-Inf"
    return "%.17e" % d


def nearest(x):
    try:
        return float(x)
    except OverflowError:
        return math.inf if x > 0 else -math.inf


def euclid(a, b):
    r = a % abs(b)
    return (a - r) // b, r


env = {}
names = []
lines, out = [], []


def var(v, code):
    name = f"V{len(names)}"
    lines.append(f"    {name}:int = {code}")
    env[name] = v
    names.append(name)
    return name


for _ in range(rng.randint(3, 5)):
    x = operand64()
    var(x, lit(x))
# values beyond 64 bits: products, sums and negations of the others
for _ in range(rng.randint(3, 6)):
    a, b, c = rng.choice(names), rng.choice(names), rng.choice(names)
    k = rng.random()
    if k < 0.4:
        var(env[a] * env[b] * env[c], f"{a} * {b} * {c}")
    elif k < 0.6:
        var(env[a] * env[b] + env[c], f"{a} * {b} + {c}")
    elif k < 0.8:
        var(-(env[a] * env[b]) - env[c], f"-({a} * {b}) - {c}")
    else:
        var(abs(env[a]) * abs(env[b]) * abs(env[a]) * abs(env[b]),
            f"Abs({a}) * Abs({b}) * Abs({a}) * Abs({b})")

ARITH = ["+", "-", "*"]


def expr(depth):
    """A random int expression: its text and its value."""
    if depth == 0 or rng.random() < 0.3:
        n = rng.choice(names)
        return n, env[n]
    k = rng.random()
    if k < 0.6:
        (ta, a), (tb, b) = expr(depth - 1), expr(depth - 1)
        op = rng.choice(ARITH)
        return f"({ta} {op} {tb})", {"+": a + b, "-": a - b, "*": a * b}[op]
    if k < 0.75:
        ta, a = expr(depth - 1)
        return f"(-{ta})", -a
    if k < 0.85:
        ta, a = expr(depth - 1)
        return f"Abs({ta})", abs(a)
    (ta, a), (tb, b) = expr(depth - 1), expr(depth - 1)
    if k < 0.92:
        return f"Min({ta}, {tb})", min(a, b)
    return f"Max({ta}, {tb})", max(a, b)


def small(t, v):
    """Keep magnitudes moderate (at most about 600 bits) so a run stays quick.
    Every value the program prints with `Show` passes this test, so the
    expected output never holds an int of more than 181 digits (Python refuses
    to format one of more than 4300, and `Show` of one takes a long time)."""
    return abs(v).bit_length() <= 600


for i in range(rng.randint(12, 30)):
    tag = f"S{i}"
    k = rng.random()
    if k < 0.25:
        t, v = expr(3)
        if not small(t, v):
            continue
        lines.append(f'    Print("{tag} {{Show({t})}}")')
        out.append(f"{tag} {v}")
    elif k < 0.4:
        (ta, a), (tb, b) = expr(2), expr(1)
        if rng.random() < 0.1:
            tb, b = "0", 0
        f = rng.choice(["Quotient", "Mod", "Floor", "Ceil"])
        if f in ("Quotient", "Mod"):
            call = f"{f}[{ta}, {tb}]"
            res = None if b == 0 else euclid(a, b)[0 if f == "Quotient" else 1]
        else:
            call = f"{f}({ta} / {tb})"
            res = None if b == 0 else (a // b if f == "Floor" else -((-a) // b))
        # the result too: Mod of a negative by a long divisor is as long as the divisor
        if not small(ta, a) or (res is not None and not small(call, res)):
            continue
        lines.append(f'    if (Q := {call}) then Print("{tag} {{Show(Q)}}") else Print("{tag} fails")')
        out.append(f"{tag} {res}" if res is not None else f"{tag} fails")
    elif k < 0.55:
        (ta, a), (tb, b) = expr(2), expr(2)
        op = rng.choice(["<", "<=", ">", ">=", "=", "<>"])
        if rng.random() < 0.3:
            tb, b = ta, a
        holds = {"<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b, "=": a == b, "<>": a != b}[op]
        lines.append(f'    if ({ta} {op} {tb}) then Print("{tag} yes") else Print("{tag} no")')
        out.append(f"{tag} {'yes' if holds else 'no'}")
    elif k < 0.65:
        # algebraic laws on ints beyond 64 bits
        (ta, a), (tb, b) = expr(2), expr(2)
        law = rng.randrange(6)
        if law == 0:
            cond = f"({ta} + {tb}) - {tb} = {ta}"
        elif law == 1:
            if b == 0:
                continue
            cond = f"Q := Quotient[{ta}, {tb}], R := Mod[{ta}, {tb}], Q * {tb} + R = {ta}, R >= 0, R < Abs({tb})"
        elif law == 2:
            if b == 0:
                continue
            cond = f"Quotient[{ta} * {tb}, {tb}] = {ta}"
        elif law == 3:
            cond = f"{ta} * {tb} = {tb} * {ta}, -(-{ta}) = {ta}, Abs({ta}) = Max({ta}, -{ta})"
        elif law == 4:
            if b == 0:
                continue
            cond = f"Floor({ta} / {tb}) <= Ceil({ta} / {tb}), Ceil({ta} / {tb}) - Floor({ta} / {tb}) <= 1"
        else:
            if abs(a).bit_length() > 200 or abs(b).bit_length() > 200:
                continue
            cond = f"BitXor(BitXor({ta}, {tb}), {tb}) = {ta}, BitAnd({ta}, {tb}) + BitOr({ta}, {tb}) = {ta} + {tb}"
        lines.append(f'    if ({cond}) then Print("{tag} law") else Print("{tag} no law")')
        out.append(f"{tag} law")
    elif k < 0.72:
        # compound assignment
        (ta, a), (tb, b), (tc, c) = expr(1), expr(1), expr(1)
        if not small(f"W{i}", (a + b) * c - a):
            continue
        lines.append(f"    var W{i}:int = {ta}")
        lines.append(f"    set W{i} += {tb}")
        lines.append(f"    set W{i} *= {tc}")
        lines.append(f"    set W{i} -= {ta}")
        lines.append(f'    Print("{tag} {{Show(W{i})}}")')
        out.append(f"{tag} {(a + b) * c - a}")
    elif k < 0.79:
        # ints beyond 64 bits as map keys, found by values computed another way
        (ta, a), (tb, b) = expr(2), expr(2)
        if a == b or not small(ta, a) or not small(tb, b):
            continue
        lines.append(f'    M{i}:[int]string = map{{{ta} => "first", {tb} => "second"}}')
        lines.append(f'    if (X := M{i}[({ta} + 1) - 1]) then Print("{tag} {{X}}") else Print("{tag} missing")')
        lines.append(f'    if (X := M{i}[{tb} * 1]) then Print("{tag} {{X}}") else Print("{tag} missing")')
        lines.append(f'    if (X := M{i}[{ta} + {tb} + 1]) then Print("{tag} {{X}}") else Print("{tag} missing")')
        out.append(f"{tag} first")
        out.append(f"{tag} second")
        out.append(f"{tag} " + ("first" if a + b + 1 == a else "second" if a + b + 1 == b else "missing"))
    elif k < 0.84:
        # an index and a range beyond 64 bits
        ta, a = expr(2)
        if not small(ta, a):
            continue
        lines.append(f'    if (X := array{{10, 20, 30}}[{ta}]) then Print("{tag} {{X}}") else Print("{tag} no element")')
        out.append(f"{tag} {[10, 20, 30][a]}" if 0 <= a < 3 else f"{tag} no element")
        lines.append(f'    for (I := {ta}..{ta} + 2) {{ Print("{tag} {{Show(I - {ta})}} {{Show(I)}}") }}')
        out += [f"{tag} {j} {a + j}" for j in range(3)]
    elif k < 0.92:
        # the nearest double
        ta, a = expr(2)
        if not small(ta, a):
            continue
        d = nearest(a)
        lines.append(f'    if ({ta} * 1.0 = {flit(d)}) then Print("{tag} float") else Print("{tag} other float")')
        out.append(f"{tag} float")
    else:
        # a rational of ints beyond 64 bits
        (ta, a), (tb, b) = expr(2), expr(1)
        if b == 0 or not small(ta, a):
            continue
        q = Fraction(a, b)
        lines.append(f'    if (R := {ta} / {tb}, F := Floor(R), C := Ceil(R)) then Print("{tag} {{Show(F)}} {{Show(C)}}") '
                     f'else Print("{tag} fails")')
        out.append(f"{tag} {math.floor(q)} {math.ceil(q)}")

exit_code, err = 0, ""
if rng.random() < 0.25:
    # ToString of an int beyond 64 bits: the overflow error ends the program
    big = [n for n in names if not fits(env[n])]
    if big:
        n = rng.choice(big)
        lines.append(f'    Print("{{{n}}}")')
        lines.append('    Print("not reached")')
        exit_code, err = 2, "error: overflow"

prelude = '''# a generated program of ints beyond 64 bits (scripts/gen-bigint.py, seed {seed})
Digits18(X:int):string =
    var S:string = "{{X}}"
    loop:
        if (S.Length >= 18) then break
        set S = "0" + S
    S

Show(X:int):string =
    if (X >= -9223372036854775807, X <= 9223372036854775807) then "{{X}}"
    else if (X < 0) then "-" + Show(-X)
    else if (Q := Quotient[X, 1000000000000000000], R := Mod[X, 1000000000000000000]) then Show(Q) + Digits18(R)
    else "?"

Main():void =
'''
with open(out_verse, "w") as f:
    f.write(prelude.format(seed=seed))
    f.write("\n".join(lines) + "\n")
with open(out_expected, "w") as f:
    f.write("".join(l + "\n" for l in out) + f"exit={exit_code}\n" + (err + "\n" if err else ""))
