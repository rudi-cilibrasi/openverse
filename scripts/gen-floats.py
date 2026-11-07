#!/usr/bin/env python3
"""Generate a random Verse program over floats (#127) and the output Verse
gives it, computed by Python's IEEE doubles under Verse's rules: one NaN,
equal to itself; no negative zero; Min/Max NaN when either is; Round ties to
even; Floor/Ceil/Round/Int fail on NaN, an infinity or out of the int range;
ToString the shortest repr ("Inf", "-Inf", "NaN").

usage: gen-floats.py SEED OUT.verse OUT.expected
"""
import math
import random
import sys

seed, out_verse, out_expected = int(sys.argv[1]), sys.argv[2], sys.argv[3]
rng = random.Random(seed)


def canon(x):
    if math.isnan(x):
        return math.nan
    if x == 0.0:
        return 0.0
    return x


def show(x):
    x = canon(x)
    if math.isnan(x):
        return "NaN"
    if math.isinf(x):
        return "Inf" if x > 0 else "-Inf"
    return repr(x)


def lit():
    """A float literal (text, value)."""
    k = rng.random()
    if k < 0.15:
        t = f"{rng.randint(0, 9)}.{rng.randint(0, 9)}"
    elif k < 0.3:
        t = f"{rng.randint(0, 10**6)}.{rng.randint(0, 999)}"
    elif k < 0.45:
        t = f"0.{rng.randint(0, 10**8):08d}"
    elif k < 0.6:
        t = f"{rng.randint(1, 9)}.{rng.randint(0, 99)}e{rng.choice('+-')}{rng.randint(0, 320)}"
    elif k < 0.7:
        t = f"{rng.randint(1, 10**15)}.0"
    else:
        t = f"{rng.randint(0, 999)}.{rng.randint(0, 999)}"
    return t, canon(float(t))


def eq(a, b):
    return (math.isnan(a) and math.isnan(b)) or a == b


def to_int(kind, x):
    if math.isnan(x) or math.isinf(x):
        return None
    v = {"Floor": math.floor, "Ceil": math.ceil, "Round": round, "Int": math.trunc}[kind](x)
    return v if -2**63 <= v < 2**63 else None


def fmin(a, b):
    return math.nan if math.isnan(a) or math.isnan(b) else (b if b < a else a)


def fmax(a, b):
    return math.nan if math.isnan(a) or math.isnan(b) else (b if a < b else a)


# variables: name -> value
env = {}
lines = []
out = []
names = []


def pick():
    return rng.choice(names)


n = rng.randint(4, 8)
for i in range(n):
    t, v = lit()
    neg = rng.random() < 0.3
    name = f"V{i}"
    lines.append(f"    {name}:float = {'-' if neg else ''}{t}")
    env[name] = canon(-v if neg else v)
    names.append(name)

for i in range(rng.randint(10, 25)):
    k = rng.random()
    a, b = pick(), pick()
    x, y = env[a], env[b]
    name = f"W{i}"
    if k < 0.5:
        op = rng.choice(["+", "-", "*", "/"])
        if op == "+":
            v = x + y
        elif op == "-":
            v = x - y
        elif op == "*":
            v = x * y
        else:
            if y == 0.0:
                v = math.nan if (x == 0.0 or math.isnan(x)) else math.copysign(math.inf, x) * (1.0 if not math.copysign(1.0, y) < 0 else -1.0)
            else:
                v = x / y
        lines.append(f"    {name}:float = {a} {op} {b}")
    elif k < 0.6:
        m = rng.randint(-50, 50)
        v = m * x
        lines.append(f"    {name}:float = {m} * {a}")
    elif k < 0.7:
        v = -x
        lines.append(f"    {name}:float = -{a}")
    elif k < 0.8:
        f = rng.choice(["Abs", "Min", "Max"])
        if f == "Abs":
            v = abs(x)
            lines.append(f"    {name}:float = Abs({a})")
        else:
            v = fmin(x, y) if f == "Min" else fmax(x, y)
            lines.append(f"    {name}:float = {f}({a}, {b})")
    else:
        # a conversion, in a failure context
        f = rng.choice(["Floor", "Ceil", "Round", "Int"])
        r = to_int(f, x)
        lines.append(f'    if (I := {f}[{a}]) then Print("{f} {{I}}") else Print("{f} fails")')
        out.append(f"{f} {r}" if r is not None else f"{f} fails")
        continue
    env[name] = canon(v)
    names.append(name)
    lines.append(f'    Print("{name} = {{{name}}}")')
    out.append(f"{name} = {show(env[name])}")
    if rng.random() < 0.4:
        c, d = pick(), pick()
        op = rng.choice(["=", "<>", "<", "<=", ">", ">="])
        p, q = env[c], env[d]
        res = {"=": eq(p, q), "<>": not eq(p, q), "<": p < q, "<=": p <= q, ">": p > q, ">=": p >= q}[op]
        lines.append(f'    if ({c} {op} {d}) then Print("{c} {op} {d}") else Print("not {c} {op} {d}")')
        out.append(f"{c} {op} {d}" if res else f"not {c} {op} {d}")

with open(out_verse, "w") as f:
    f.write(f"# a generated float program (scripts/gen-floats.py, seed {seed})\nMain():void =\n")
    f.write("\n".join(lines) + "\n")
with open(out_expected, "w") as f:
    f.write("\n".join(out) + "\n")
