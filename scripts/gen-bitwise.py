#!/usr/bin/env python3
"""Generate a random Verse program of the bitwise functions and the output
Verse gives it, computed with Python's unbounded ints under the Book's rules
(ch. 4 and its API reference): BitAnd, BitOr, BitXor and BitNot of two's
complement bit patterns sign-extended without limit (Python's &, |, ^, ~);
BitShiftLeft[X, N] = X * 2^N and BitShiftRight[X, N] = floor(X / 2^N)
(Python's << and >>), both failing when N < 0; and openverse's 64-bit ints,
where a result out of range is the overflow error, which ends the program.
Every statement whose value would be out of range is left out but the last
one, which, with a quarter of the seeds, is a call whose result is out of
range: the program then ends with exit 2 and `error: overflow`.

usage: gen-bitwise.py SEED OUT.verse OUT.expected
(OUT.expected is the output, then `exit=N`, then stderr's lines)
"""
import random
import sys

seed, out_verse, out_expected = int(sys.argv[1]), sys.argv[2], sys.argv[3]
rng = random.Random(seed)
LO, HI = -2 ** 63, 2 ** 63 - 1


def fits(x):
    return LO <= x <= HI


def operand():
    """An int64, often at an edge: a sign, a power of two, its neighbours."""
    k = rng.random()
    if k < 0.25:
        return rng.choice([0, 1, -1, 2, -2, HI, LO, HI - 1, LO + 1, 12345, -12345])
    if k < 0.55:
        p = rng.randint(0, 62)
        return rng.choice([1, -1]) * (2 ** p) + rng.choice([-1, 0, 0, 1])
    if k < 0.75:
        return rng.randint(-1000, 1000)
    return rng.randint(LO, HI)


def lit(x):
    # (the most negative int is no literal: write it as an expression)
    return f"({LO + 1} - 1)" if x == LO else (f"({x})" if x < 0 else str(x))


def count():
    k = rng.random()
    if k < 0.15:
        return rng.choice([-1, -2, -63, -64, LO, -(2 ** 31)])
    if k < 0.75:
        return rng.randint(0, 64)
    return rng.choice([65, 100, 1000, 10 ** 9, HI])


def shl(x, n):
    if n < 0:
        return None
    if x == 0:
        return 0
    if n > 64:
        return 2 ** 64  # (out of range: a stand-in, never printed)
    return x << n


def shr(x, n):
    if n < 0:
        return None
    return x >> min(n, 64)


env = {}      # variable -> value
lines, out = [], []
names = []
for i in range(rng.randint(3, 6)):
    v = operand()
    name = f"V{i}"
    lines.append(f"    {name}:int = {lit(v)}")
    env[name] = v
    names.append(name)

end_error = rng.random() < 0.25
stmts = rng.randint(8, 24)
for i in range(stmts):
    a, b = rng.choice(names), rng.choice(names)
    x, y = env[a], env[b]
    k = rng.random()
    name = f"W{i}"
    if k < 0.45:
        f = rng.choice(["BitAnd", "BitOr", "BitXor", "BitNot"])
        if f == "BitNot":
            v, e = ~x, f"BitNot({a})"
        else:
            v = {"BitAnd": x & y, "BitOr": x | y, "BitXor": x ^ y}[f]
            e = f"{f}({a}, {b})"
        lines.append(f"    {name}:int = {e}")
        env[name] = v
        names.append(name)
        lines.append(f'    Print("{name} = {{{name}}}")')
        out.append(f"{name} = {v}")
    elif k < 0.8:
        f = rng.choice(["BitShiftLeft", "BitShiftRight"])
        n = count()
        v = shl(x, n) if f == "BitShiftLeft" else shr(x, n)
        if v is not None and not fits(v):
            continue
        lines.append(f'    if (S := {f}[{a}, {lit(n)}]) then Print("{name} {{S}}") else Print("{name} fails")')
        out.append(f"{name} {v}" if v is not None else f"{name} fails")
        if v is not None:
            lines.append(f"    {name}:int = {f}[{a}, {lit(n)}] or 0")
            env[name] = v
            names.append(name)
    else:
        # the laws: De Morgan, xor twice, and with a shift
        c = rng.choice(names)
        z = env[c]
        law = rng.randrange(3)
        if law == 0:
            ok = ~(x & y) == (~x | ~y)
            lines.append(f'    if (BitNot(BitAnd({a}, {b})) = BitOr(BitNot({a}), BitNot({b}))) then Print("law") else Print("no law")')
        elif law == 1:
            ok = (x ^ y) ^ z == x ^ (y ^ z)
            lines.append(f'    if (BitXor(BitXor({a}, {b}), {c}) = BitXor({a}, BitXor({b}, {c}))) then Print("law") else Print("no law")')
        else:
            if not fits((x | y) - (x & y)):
                continue
            ok = (x | y) - (x & y) == x ^ y
            lines.append(f'    if (BitOr({a}, {b}) - BitAnd({a}, {b}) = BitXor({a}, {b})) then Print("law") else Print("no law")')
        out.append("law" if ok else "no law")

exit_code, err = 0, ""
if end_error:
    # a call whose result is out of range: the overflow error ends the program
    a = rng.choice(names)
    x = env[a]
    if x != 0:
        n = rng.choice([63, 64, 65, 1000, HI])
        if not fits(x << min(n, 65)):
            lines.append(f'    if (S := BitShiftLeft[{a}, {lit(n)}]) then Print("unreachable {{S}}")')
            lines.append('    Print("not reached")')
            exit_code, err = 2, "error: overflow"

with open(out_verse, "w") as f:
    f.write(f"# a generated bitwise program (scripts/gen-bitwise.py, seed {seed})\nMain():void =\n")
    f.write("\n".join(lines) + "\n")
with open(out_expected, "w") as f:
    f.write("".join(l + "\n" for l in out) + f"exit={exit_code}\n" + (err + "\n" if err else ""))
