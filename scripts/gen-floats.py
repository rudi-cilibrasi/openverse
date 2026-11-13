#!/usr/bin/env python3
"""Generate a random Verse program over floats (#127) and the output Verse
gives it, computed by Python's IEEE doubles under Verse's rules: one NaN,
equal to itself; no negative zero; Min/Max NaN when either is; Round ties to
even; Floor/Ceil/Round/Int fail on NaN or an infinity (a result out of the int
range is a runtime error, so the generator leaves those out);
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
        # (a literal that rounds to infinity is refused: up to e+307 on the
        # way up, down to subnormals and zero on the way down)
        m, d, sign = rng.randint(1, 9), rng.randint(0, 99), rng.choice('+-')
        t = f"{m}.{d}e{sign}{rng.randint(0, 307 if sign == '+' else 320)}"
    elif k < 0.7:
        t = f"{rng.randint(1, 10**15)}.0"
    else:
        t = f"{rng.randint(0, 999)}.{rng.randint(0, 999)}"
    return t, canon(float(t))


def fdiv(x, y):
    """IEEE division (Python raises on a zero divisor; there is no -0 here)."""
    if y == 0.0:
        if math.isnan(x) or x == 0.0:
            return math.nan
        return math.copysign(math.inf, x)
    return x / y


def eq(a, b):
    return (math.isnan(a) and math.isnan(b)) or a == b


def to_int(kind, x):
    if math.isnan(x) or math.isinf(x):
        return None
    v = {"Floor": math.floor, "Ceil": math.ceil, "Round": round, "Int": math.trunc}[kind](x)
    return v if -2**63 <= v < 2**63 else None


def fmin(a, b):
    return math.nan if math.isnan(a) or math.isnan(b) else (b if b < a else a)


def c1(f):
    """A one-argument libm function with C's special values (Python raises)."""
    def g(x):
        try:
            return f(x)
        except OverflowError:
            return math.inf
        except ValueError:
            return math.nan
    return g


def c_log(x):
    if math.isnan(x) or x < 0:
        return math.nan
    if x == 0.0:
        return -math.inf
    return math.log(x)


def c_sqrt(x):
    return math.nan if (math.isnan(x) or x < 0) else math.sqrt(x)


def odd_int(y):
    # (every double of magnitude 2^53 or more is an even integer)
    return math.isfinite(y) and y == math.floor(y) and math.fmod(y, 2.0) != 0.0


def c_pow(x, y):
    try:
        return math.pow(x, y)
    except OverflowError:
        # (C: the result keeps the base's sign when the power is an odd integer,
        # so a negative base overflows to -Inf, not Inf)
        return -math.inf if x < 0 and odd_int(y) else math.inf
    except (ValueError, ZeroDivisionError):
        # (C: pow(±0, y<0) = ±Inf, -Inf only for -0 and an odd integer y; a negative
        # base to a non-integer power is NaN)
        if x == 0.0 and y < 0:
            return -math.inf if math.copysign(1.0, x) < 0 and odd_int(y) else math.inf
        return math.nan


def clamp1(x):
    return x if math.isnan(x) else max(-1.0, min(1.0, x))


MATH1 = {
    "Sqrt": c_sqrt, "Exp": c1(math.exp), "Ln": c_log, "Sin": c1(math.sin), "Cos": c1(math.cos),
    "Tan": c1(math.tan), "ArcSin": lambda x: math.asin(clamp1(x)), "ArcCos": lambda x: math.acos(clamp1(x)),
    "ArcTan": math.atan,
}


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
    name = f"V{i}"
    if rng.random() < 0.12:
        # a constant (#132)
        c, v = rng.choice([("PiFloat", math.pi), ("Inf", math.inf), ("-Inf", -math.inf), ("NaN", math.nan)])
        lines.append(f"    {name}:float = {c}")
        env[name] = canon(v)
        names.append(name)
        continue
    t, v = lit()
    neg = rng.random() < 0.3
    lines.append(f"    {name}:float = {'-' if neg else ''}{t}")
    env[name] = canon(-v if neg else v)
    names.append(name)

for i in range(rng.randint(10, 25)):
    k = rng.random()
    a, b = pick(), pick()
    x, y = env[a], env[b]
    name = f"W{i}"
    if k < 0.45:
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
    elif k < 0.52:
        m = rng.randint(-50, 50)
        v = m * x
        lines.append(f"    {name}:float = {m} * {a}")
    elif k < 0.58:
        v = -x
        lines.append(f"    {name}:float = -{a}")
    elif k < 0.75:
        # a mathematical function (#132)
        f = rng.choice(sorted(MATH1) + ["Pow", "ArcTan2", "Log"])
        if f == "Log":
            # (Log(Base, X) is Ln(X) / Ln(Base))
            v = fdiv(c_log(y), c_log(x))
            lines.append(f"    {name}:float = Log({a}, {b})")
        elif f == "Pow":
            v = c_pow(x, y)
            lines.append(f"    {name}:float = Pow({a}, {b})")
        elif f == "ArcTan2":
            v = math.atan2(x, y)
            lines.append(f"    {name}:float = ArcTan({a}, {b})")
        else:
            v = MATH1[f](x)
            lines.append(f"    {name}:float = {f}({a})")
    elif k < 0.8:
        f = rng.choice(["Abs", "Min", "Max"])
        if f == "Abs":
            v = abs(x)
            lines.append(f"    {name}:float = Abs({a})")
        else:
            v = fmin(x, y) if f == "Min" else fmax(x, y)
            lines.append(f"    {name}:float = {f}({a}, {b})")
    elif k < 0.86:
        # IsFinite (#132), in a failure context
        if math.isnan(x) or math.isinf(x):
            out.append("not finite")
        else:
            out.append(f"finite {show(x)}")
        lines.append(f'    if (F := IsFinite[{a}]) then Print("finite {{F}}") else Print("not finite")')
        continue
    else:
        # a conversion, in a failure context
        f = rng.choice(["Floor", "Ceil", "Round", "Int"])
        r = to_int(f, x)
        if r is None and not (math.isnan(x) or math.isinf(x)):
            continue   # out of range: the overflow error, which ends the program
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
        # (NaN <= NaN and NaN >= NaN succeed, #132)
        res = {"=": eq(p, q), "<>": not eq(p, q), "<": p < q, "<=": p <= q or eq(p, q), ">": p > q,
               ">=": p >= q or eq(p, q)}[op]
        lines.append(f'    if ({c} {op} {d}) then Print("{c} {op} {d}") else Print("not {c} {op} {d}")')
        out.append(f"{c} {op} {d}" if res else f"not {c} {op} {d}")

with open(out_verse, "w") as f:
    f.write(f"# a generated float program (scripts/gen-floats.py, seed {seed})\nMain():void =\n")
    f.write("\n".join(lines) + "\n")
with open(out_expected, "w") as f:
    f.write("\n".join(out) + "\n")
