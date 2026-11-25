#!/usr/bin/env python3
"""Test vectors for runtime/src/bigint.c, computed with Python's unbounded ints
(an independent reference): the int operations of Prim.apply
(OpenVerse/Core/Prims.lean) on operands around and far beyond 64 bits,
comparisons, the nearest double (Python's float(int) rounds to nearest, ties
to even, and raises OverflowError past the largest double), the low 64 bits,
and the four-int rational forms. Division cases include ones for which
Knuth's algorithm D (32-bit limbs) adds the divisor back, found by running
its quotient estimate here.

usage: gen-bigint-vectors.py SEED > FILE   (runtime/tests/test_bigint.c reads FILE)

Each line is a case; numbers are written in hexadecimal with a leading '-'
when negative:
  op NAME A B RC R            RC is ok or fail (a zero divisor); B is 0 for neg, abs
  cmp A B C                   C is -1, 0 or 1
  dbl A BITS                  BITS: the IEEE bits of the nearest double
  low A BITS                  A mod 2^64
  rat NAME A B C D RC P Q     a/b NAME c/d, reduced; RC ok, fail or overflow
"""
import math
import random
import struct
import sys

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)
B32 = 1 << 32


def h(x):
    return ("-" if x < 0 else "") + format(abs(x), "x")


def structured_magnitude(words):
    """A magnitude of `words` 64-bit words, its 32-bit limbs often 0, 1,
    all ones or a single high bit, which reach the rare paths of division."""
    limbs = []
    for _ in range(2 * words):
        k = rng.random()
        if k < 0.5:
            limbs.append(rng.choice([0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE]))
        else:
            limbs.append(rng.getrandbits(32))
    x = sum(l << (32 * i) for i, l in enumerate(limbs))
    return x


def operand():
    k = rng.random()
    if k < 0.2:
        return rng.choice([0, 1, -1, 2, -2, 2 ** 63, -(2 ** 63), 2 ** 63 - 1, -(2 ** 63) + 1,
                           2 ** 63 + 1, -(2 ** 63) - 1, 2 ** 64, -(2 ** 64), 2 ** 64 - 1,
                           2 ** 64 + 1, 2 ** 32, 2 ** 32 - 1, 2 ** 96, 2 ** 127 - 1,
                           2 ** 128, -(2 ** 128) + 1, 3, 7, 10 ** 18, 10 ** 19, 10 ** 40])
    if k < 0.3:
        return rng.randint(-(2 ** 63), 2 ** 63 - 1)
    if k < 0.4:
        p = rng.randint(0, 260)
        return rng.choice([1, -1]) * (2 ** p) + rng.choice([-1, 0, 1])
    x = structured_magnitude(rng.randint(1, 6)) if rng.random() < 0.6 else \
        rng.getrandbits(rng.randint(1, 400))
    return -x if rng.random() < 0.5 else x


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def op_result(name, a, b):
    if name == "add":
        return a + b
    if name == "sub":
        return a - b
    if name == "mul":
        return a * b
    if name == "neg":
        return -a
    if name == "abs":
        return abs(a)
    if b == 0:
        return None
    if name == "floordiv":
        return a // b
    if name == "ceildiv":
        return -((-a) // b)
    # Euclidean: a = b q + r with 0 <= r < |b|
    r = a % abs(b)
    if name == "modulo":
        return r
    return (a - r) // b


def limbs_of(x, n=None):
    out = []
    while x:
        out.append(x & (B32 - 1))
        x >>= 32
    if n is not None:
        out += [0] * (n - len(out))
    return out


def knuth_adds_back(u, v):
    """Whether algorithm D on |u| / |v| (32-bit limbs) adds the divisor back."""
    u, v = abs(u), abs(v)
    vl = limbs_of(v)
    n = len(vl)
    if n < 2 or u < v:
        return False
    s = 32 - vl[-1].bit_length()
    vn = limbs_of(v << s, n)
    un = limbs_of(u << s, len(limbs_of(u)) + 1)
    m = len(limbs_of(u)) - n
    vv = v << s
    back = False
    for j in range(m, -1, -1):
        num = un[j + n] * B32 + un[j + n - 1]
        qhat, rhat = divmod(num, vn[n - 1])
        while qhat >= B32 or qhat * vn[n - 2] > B32 * rhat + un[j + n - 2]:
            qhat -= 1
            rhat += vn[n - 1]
            if rhat >= B32:
                break
        cur = sum(un[j + i] << (32 * i) for i in range(n + 1))
        if cur < qhat * vv:
            back = True
            cur += vv
        cur -= qhat * vv
        for i in range(n + 1):
            un[j + i] = (cur >> (32 * i)) & (B32 - 1)
    return back


def nearest_double_bits(x):
    try:
        d = float(x)
    except OverflowError:
        d = math.inf if x > 0 else -math.inf
    return struct.unpack("<Q", struct.pack("<d", d))[0]


def rational(name, a, b, c, d):
    if b <= 0 or d <= 0:
        return "overflow", None
    if name == "add":
        n, den = a * d + c * b, b * d
    elif name == "sub":
        n, den = a * d - c * b, b * d
    elif name == "mul":
        n, den = a * c, b * d
    else:
        if c == 0:
            return "fail", None
        n, den = a * d, b * c
    g = math.gcd(n, den)
    p, q = n // g, den // g
    if q < 0:
        p, q = -p, -q
    return "ok", (p, q)


lines = []
OPS = ["add", "sub", "mul", "neg", "abs", "floordiv", "ceildiv", "quotient", "modulo"]
for _ in range(2500):
    name = rng.choice(OPS)
    a = operand()
    b = 0 if name in ("neg", "abs") else operand()
    if name in ("floordiv", "ceildiv", "quotient", "modulo") and rng.random() < 0.3:
        # a quotient that fits exactly, and its neighbours
        b = b or 3
        a = b * operand() + rng.choice([0, 0, 1, -1])
    r = op_result(name, a, b)
    lines.append(f"op {name} {h(a)} {h(b)} " + ("fail 0" if r is None else f"ok {h(r)}"))

# divisions where algorithm D adds back (rare at random: searched for)
found, tries = 0, 0
while found < 60 and tries < 200000:
    tries += 1
    v = structured_magnitude(rng.randint(1, 3))
    if v >> 32 == 0:
        continue
    u = structured_magnitude(rng.randint(2, 6))
    if not knuth_adds_back(u, v):
        continue
    found += 1
    for name in ("floordiv", "ceildiv", "quotient", "modulo"):
        su, sv = rng.choice([1, -1]) * u, rng.choice([1, -1]) * v
        lines.append(f"op {name} {h(su)} {h(sv)} ok {h(op_result(name, su, sv))}")
if found < 60:
    sys.exit(f"gen-bigint-vectors: only {found} add-back divisions found")

for _ in range(800):
    a = operand()
    b = rng.choice([a, -a, a + 1, a - 1, operand()])
    lines.append(f"cmp {h(a)} {h(b)} {(a > b) - (a < b)}")

for _ in range(600):
    k = rng.random()
    if k < 0.3:
        # near a tie between two doubles: a 53-bit odd multiple of a power of
        # two, half a unit added, and a little more or less
        p = rng.randint(1, 1000)
        m = rng.getrandbits(53) | (1 << 52)
        a = (m << p) + rng.choice([0, 1 << (p - 1), (1 << (p - 1)) - 1, (1 << (p - 1)) + 1])
    elif k < 0.4:
        a = rng.choice([2 ** 1024, 2 ** 1024 - 2 ** 970, 2 ** 1024 - 2 ** 971, 2 ** 1024 - 2 ** 970 - 1,
                        2 ** 2000, 2 ** 63, 2 ** 64 - 1, 2 ** 64 + 2 ** 11, 2 ** 64 + 2 ** 11 + 1])
    else:
        a = operand()
    a = a if rng.random() < 0.5 else -a
    lines.append(f"dbl {h(a)} {nearest_double_bits(a):x}")

for _ in range(200):
    a = operand()
    lines.append(f"low {h(a)} {a % 2 ** 64:x}")

for _ in range(500):
    name = rng.choice(["add", "sub", "mul", "quotient"])
    a, c = operand(), operand()
    b = abs(operand()) or 1
    d = abs(operand()) or 1
    if rng.random() < 0.05:
        b = -b
    if name == "quotient" and rng.random() < 0.05:
        c = 0
    rc, pq = rational(name, a, b, c, d)
    lines.append(f"rat {name} {h(a)} {h(b)} {h(c)} {h(d)} {rc} " +
                 (f"{h(pq[0])} {h(pq[1])}" if pq else "0 0"))

sys.stdout.write("\n".join(lines) + "\n")
