#!/usr/bin/env python3
"""Check libm against independent decimal formulas and rounded Lerp stages.

The 800-digit oracle retains even the smallest binary64 arguments in
exp/ln formulas. Host math.sinh/cosh/... are deliberately not used.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import math
import random
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
UNARY = ['Sinh', 'Cosh', 'Tanh', 'ArSinh', 'ArCosh', 'ArTanh']


def canon(x):
    return 0.0 if x == 0 else x


def unary_oracle(name, x):
    if math.isnan(x):
        return math.nan
    a = abs(x)
    sign = -1 if x < 0 else 1
    if name == 'ArCosh' and x < 1:
        return math.nan
    if name == 'ArTanh' and a >= 1:
        return sign * math.inf if a == 1 else math.nan
    if math.isinf(x):
        return {'Sinh': x, 'Cosh': math.inf, 'Tanh': float(sign),
                'ArSinh': x, 'ArCosh': math.inf}[name]
    if name in ['Sinh', 'Cosh'] and a > 711:
        return sign * math.inf if name == 'Sinh' else math.inf
    if name == 'Tanh' and a >= 20:
        return float(sign)
    with localcontext() as ctx:
        ctx.prec = 800
        d = Decimal.from_float(a)
        if name in ['Sinh', 'Cosh', 'Tanh']:
            e = d.exp()
            inv = (-d).exp()
            value = ((e - inv) / 2 if name == 'Sinh' else
                     (e + inv) / 2 if name == 'Cosh' else (e - inv) / (e + inv))
        elif name == 'ArSinh':
            value = (d + (d * d + 1).sqrt()).ln()
        elif name == 'ArCosh':
            value = (d + (d * d - 1).sqrt()).ln()
        else:
            value = ((1 + d) / (1 - d)).ln() / 2
        return canon(float(value) * (1 if name in ['Cosh', 'ArCosh'] else sign))


def lerp_oracle(a, b, p):
    # Round at each source operation, including overflow and invalid products.
    with localcontext() as ctx:
        ctx.prec = 800
        for signal in ctx.traps:
            ctx.traps[signal] = False
        d = Decimal.from_float
        q = canon(float(Decimal(1) - d(p)))
        left = canon(float(d(a) * d(q)))
        right = canon(float(d(b) * d(p)))
        return canon(float(d(left) + d(right)))


def literal(x):
    if math.isnan(x):
        return 'NaN'
    if math.isinf(x):
        return '-Inf' if x < 0 else 'Inf'
    return repr(x)


def scale_of(want):
    """The power of two that makes the expected value an integer near 2^60
    (2^1074 for zero), so that ToString's six digits show every bit of a
    result within a few ulps of it: multiplying by a power of two is exact."""
    if not math.isfinite(want):
        return 0
    if want == 0:
        return 1074
    return 60 - math.frexp(want)[1]


def scaled(expr, s):
    """`expr` times 2^s, as a product of float literals each a power of two
    of a normal magnitude."""
    out = f'({expr})'
    while s != 0:
        k = max(-1000, min(1000, s))
        out += f' * {repr(2.0 ** k)}'
        s -= k
    return out


def unscale(line, s):
    """The float a printed `scaled` value stands for."""
    if line in ('NaN', 'Inf', '-Inf'):
        return float(line.replace('Inf', 'inf').replace('NaN', 'nan'))
    return float(Fraction(line) / Fraction(2) ** s)


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


def ordered(x):
    n = bits(x)
    return ~n if n >> 63 else n | (1 << 63)


def exact_unary(name, x):
    return (abs(x) < sys.float_info.min or math.isinf(x) or
            (name == 'ArCosh' and x == 1))


def cases(count, first):
    tiny = math.ulp(0.0)
    inputs = [0.0, -0.0, tiny, -tiny, 1e-320, -1e-320, 1e-20, -1e-20,
              1.9246247400168677e-13, -1.9246247400168677e-13,
              0.5, -0.5, 1.0, -1.0, math.nextafter(1.0, 0.0),
              math.nextafter(1.0, math.inf), 2.0, -2.0, 20.0, -20.0,
              710.0, -710.0, 710.4758600739439, 711.0, 1e308, -1e308,
              sys.float_info.max, math.inf, -math.inf, math.nan]
    rows = [(f'{name}({literal(x)})', unary_oracle(name, x), exact_unary(name, x))
            for name in UNARY for x in inputs]
    triples = [(0.0, 10.0, p) for p in [0.0, -0.0, 1.0, 0.5, -1.0, 2.0]]
    triples += [(1e308, -1e308, 0.5), (1e308, 1e308, 3.0),
                (1e308, -1e308, 0.0), (1e308, -1e308, 1.0),
                (tiny, tiny, 0.5), (-tiny, tiny, 0.5),
                (0.0, 1.0, tiny), (2.0, 2.0, math.inf)]
    for special in [math.inf, -math.inf, math.nan]:
        for p in [0.0, 1.0, 0.5]:
            triples += [(special, 1.0, p), (1.0, special, p)]
        triples.append((1.0, 2.0, special))
    for seed in range(first, first + count):
        rng = random.Random(seed)
        x = struct.unpack('>d', struct.pack('>Q', rng.getrandbits(64)))[0]
        name = UNARY[seed % len(UNARY)]
        rows.append((f'{name}({literal(x)})', unary_oracle(name, x), exact_unary(name, x)))
        a, b = [rng.choice(inputs) if seed % 3 == 0 else rng.uniform(-1e100, 1e100)
                for _ in range(2)]
        p = rng.choice(inputs) if seed % 2 == 0 else rng.uniform(-3, 3)
        triples.append((a, b, p))
    rows += [(f'Lerp({literal(a)},{literal(b)},{literal(p)})', lerp_oracle(a, b, p), True)
             for a, b, p in triples]
    return rows


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rows = cases(count, first)
    with tempfile.TemporaryDirectory(prefix='openverse-float-math-') as directory:
        tmp = Path(directory)
        # Keep source/evaluator depth independent of the nightly case count.
        for offset in range(0, len(rows), 128):
            batch = rows[offset:offset + 128]
            # (ToString prints six digits after the point: each value is
            # printed times a power of two, which shows all its bits)
            source = 'Main():void=\n' + ''.join(f'    Print("{{{scaled(e, scale_of(w))}}}")\n'
                                                for e, w, _ in batch)
            src, bc = tmp / 'p.verse', tmp / 'p.vbc'
            src.write_text(source)
            lean = subprocess.run([ROOT / '.lake/build/bin/openverse', 'run', src, '--emit', bc],
                                  capture_output=True, text=True, timeout=120)
            c = None if lean.returncode else subprocess.run([ROOT / 'runtime/build/cverse', bc],
                                                            capture_output=True, text=True, timeout=120)
            reason = None
            if lean.returncode or lean.stderr or c is None or (c.returncode, c.stdout, c.stderr) != (lean.returncode, lean.stdout, lean.stderr):
                reason = f'Lean/C mismatch: Lean={lean.returncode, lean.stdout, lean.stderr}; C={c}'
            elif len(lean.stdout.splitlines()) != len(batch):
                reason = 'output count differs from oracle'
            else:
                for line, (expr, want, exact) in zip(lean.stdout.splitlines(), batch):
                    actual = unscale(line, scale_of(want))
                    good = (line == 'NaN') if math.isnan(want) else (actual == want) if math.isinf(want) else (
                        math.isfinite(actual) and abs(ordered(actual) - ordered(want)) <= (0 if exact else 2))
                    # (a zero prints without a sign: there is no negative zero)
                    if actual == 0 and line != '0.000000':
                        good = False
                    if math.isfinite(actual):
                        if expr.startswith('Cosh(') and actual < 1:
                            good = False
                        if expr.startswith('Tanh(') and abs(actual) > 1:
                            good = False
                        if expr.startswith('ArCosh(') and actual < 0:
                            good = False
                    if not good:
                        reason = f'{expr}: got {line}, expected {want!r}'
                        break
            if reason:
                saved = ROOT / f'fuzz-float-math-{first}-{offset}.verse'
                saved.write_text(source)
                raise SystemExit(f'float-math: {reason}; saved {saved.name}')
    print(f'float-math: {len(rows)} independent decimal/edge oracles '
          f'({count} random cases from seed {first}), Lean and C matched')


if __name__ == '__main__':
    main()
