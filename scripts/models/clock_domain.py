"""Independent clock oracle: exact rational binary64 quantization.

No VM imports or host-float arithmetic determine admission or tick counts.
Host floats only construct and format source inputs and order infinite timers.
"""
from fractions import Fraction
import math
import struct


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


def value(b):
    return struct.unpack('>d', struct.pack('>Q', b))[0]


def nearest_even(n, d):
    quotient, remainder = divmod(n, d)
    return quotient + (remainder * 2 > d or
                       (remainder * 2 == d and quotient % 2 == 1))


def pow2(exponent):
    return Fraction(2**exponent, 1) if exponent >= 0 else Fraction(1, 2**(-exponent))


def rational(b):
    sign = -1 if b >> 63 else 1
    exponent, mantissa = (b >> 52) & 2047, b & ((1 << 52) - 1)
    if exponent == 2047:
        return None
    significand = mantissa if exponent == 0 else mantissa + (1 << 52)
    return sign * Fraction(significand) * pow2(-1074 if exponent == 0 else exponent - 1075)


def binary64_nearest(x):
    """Round a nonnegative rational to binary64; None represents infinity."""
    assert x >= 0
    if not x:
        return Fraction(0)
    n, d = x.numerator, x.denominator
    exponent = n.bit_length() - d.bit_length()
    if x < pow2(exponent):
        exponent -= 1
    if exponent > 1023:
        return None
    step = pow2(max(exponent - 52, -1074))
    quotient = nearest_even(n * step.denominator, d * step.numerator)
    rounded = quotient * step
    return None if rounded >= pow2(1024) else rounded


def classify(b):
    exponent, mantissa = (b >> 52) & 2047, b & ((1 << 52) - 1)
    if exponent == 2047:
        immediate = mantissa != 0 or b >> 63 != 0
        return dict(kind='immediate' if immediate else 'indefinite',
                    ticks=0 if immediate else None)
    seconds = rational(b)
    if seconds < 0:
        return dict(kind='immediate', ticks=0)
    product = binary64_nearest(seconds * 30)
    if product is None:
        return dict(kind='unsupported-finite', ticks=None, product='Inf')
    rounded = nearest_even(product.numerator, product.denominator)
    if rounded >= 2**63:
        return dict(kind='unsupported-finite', ticks=None,
                    product=str(product), rounded=str(rounded))
    return dict(kind='finite', ticks=max(1, rounded),
                product=str(product), rounded=str(rounded))


def source(b):
    x = value(b)
    if math.isnan(x):
        return 'NaN'
    if x == math.inf:
        return '1.0/0.0'
    if x == -math.inf:
        return '-(1.0/0.0)'
    if abs(x) >= 2**53 and math.isfinite(x):
        return str(int(x)) + '.0'
    return repr(x)


def pair_oracle(a, b):
    first, second = classify(a), classify(b)
    output = []
    for label, result in [('A', first), ('B', second)]:
        if result['kind'] == 'unsupported-finite':
            return dict(exit=2, stdout=''.join(output), stderr='error: user\n')
        if result['kind'] == 'immediate':
            output.append(label + '\n')
    ordered = sorted([('A', first), ('B', second)],
                     key=lambda x: (x[1]['ticks'] if x[1]['ticks'] is not None else math.inf, x[0]))
    for label, result in ordered:
        if result['kind'] == 'finite':
            output.append(label + '\n')
    if any(result['kind'] == 'indefinite' for result in (first, second)):
        return dict(exit=2, stdout=''.join(output), stderr='error: user\n')
    return dict(exit=0, stdout=''.join(output) + 'done\n', stderr='')


def boundary():
    low, high = 0, 0x7fefffffffffffff
    while low < high:
        mid = (low + high + 1) // 2
        if classify(mid)['kind'] == 'finite':
            low = mid
        else:
            high = mid - 1
    return low


# A complete period covers each IEEE input class in all four source contexts.
VALUES = [0, 1, 0x8000000000000000, 0x8000000000000001, bits(-1.0),
          0xfff0000000000000, 0x7ff8000000000000, 0x7ff0000000000000,
          bits(999999999999999.0), bits(1e15), bits(1e16),
          0x439111111111110f, 0x4391111111111110, 0x4391111111111111,
          0x4391111111111112, 0x7fefffffffffffff]
VALUES += [b for x in (.05, .15, .25) for b in (bits(x)-1, bits(x), bits(x)+1)]
PERIOD = len(VALUES) * 4


def literal(b):
    return '(0.0/0.0)' if math.isnan(value(b)) else '(' + source(b) + ')'


def generate(seed):
    import random
    rng = random.Random(seed)
    slot = (seed - 1) % PERIOD
    index, context = slot % len(VALUES), slot // len(VALUES)
    a, b = VALUES[index], rng.choice(VALUES)
    ca = classify(a)
    header, prefix, before = '', '', ''
    if index % 3 == 0:
        header = 'Round(X:float)<decides><computes>:int=99\n'
        before = '    if(R:=Round[0.25]) then Print("custom {R}")\n'
        prefix = 'custom 99\n'
    elif index % 3 == 1:
        header = 'Round(X:string)<computes>:string=X\n'
        before = '    Print(Round("custom"))\n'
        prefix = 'custom\n'
    body = header + 'Main()<suspends>:void=\n' + before
    status, stderr = 0, ''
    if context == 0:
        body += ('    sync:\n        block:\n            Sleep(' + literal(a) + ')\n'
                 '            Print("A")\n        block:\n            Sleep(' + literal(b) + ')\n'
                 '            Print("B")\n    Print("done")\n')
        expected = pair_oracle(a, b)
        return body, expected | {'stdout': prefix + expected['stdout']}
    if context == 1:
        steps = 3
        body += ('    sync:\n        block:\n            Sleep(' + literal(a) + ')\n'
                 '            Print("timer")\n        block:\n            Print("peer")\n')
        for j in range(1, steps+1):
            body += f'            Sleep(0.0)\n            Print("tick {j}")\n'
        body += '    Print("done")\n'
        if ca['kind'] == 'unsupported-finite':
            out, status, stderr = '', 2, 'error: user\n'
        else:
            out = ('timer\n' if ca['kind'] == 'immediate' else '') + 'peer\n'
            for j in range(1, steps+1):
                if ca['kind'] == 'finite' and ca['ticks'] == j:
                    out += 'timer\n'
                out += f'tick {j}\n'
            if ca['kind'] == 'indefinite':
                status, stderr = 2, 'error: user\n'
            else:
                if ca['kind'] == 'finite' and ca['ticks'] > steps:
                    out += 'timer\n'
                out += 'done\n'
    elif context == 2:
        body += ('    race:\n        block:\n            defer:Print("cleanup")\n'
                 '            Print("timer")\n            Sleep(' + literal(a) + ')\n'
                 '            Print("timer done")\n        block:\n            Print("peer")\n'
                 '            Sleep(0.0)\n            Print("peer done")\n    Print("done")\n')
        if ca['kind'] == 'unsupported-finite':
            out, status, stderr = 'timer\n', 2, 'error: user\n'
        elif ca['kind'] == 'immediate':
            out = 'timer\ntimer done\ncleanup\ndone\n'
        elif ca['kind'] == 'finite' and ca['ticks'] == 1:
            out = 'timer\npeer\ntimer done\ncleanup\ndone\n'
        else:
            out = 'timer\npeer\npeer done\ncleanup\ndone\n'
    else:
        largest = 0x4391111111111110
        tail = bits(68.23333333333333)
        sequences = [[largest, tail], [largest, tail, 0],
                     [largest, tail, bits(-1.0), 0x7ff8000000000000],
                     [largest, largest], [bits(1e15), bits(1e15)],
                     [largest, bits(68.2), bits(1.0/30.0), 1],
                     [largest, 0x7ff0000000000000], [0, largest+1]]
        sequence = sequences[index % len(sequences)]
        now, out = 0, ''
        for j, v in enumerate(sequence):
            body += f'    Sleep({literal(v)})\n    Print("step {j}")\n'
            if status:
                continue
            c = classify(v)
            if c['kind'] in ('unsupported-finite', 'indefinite'):
                status, stderr = 2, 'error: user\n'
            elif c['kind'] == 'finite' and now + c['ticks'] > 2**63-1:
                status, stderr = 2, 'error: overflow\n'
            else:
                now += c['ticks']
                out += f'step {j}\n'
        body += '    Print("done")\n'
        if not status:
            out += 'done\n'
    return body, dict(exit=status, stdout=prefix+out, stderr=stderr)
