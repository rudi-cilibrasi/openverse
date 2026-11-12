#!/usr/bin/env python3
"""Check reference-scheduler traces and distinguish stalls from clock overflow.

Goldens record explicit reference policies, not inferred engine behavior.
Finite controls distinguish suspended-program termination and numeric limits
from a parser/type error or a test which can never finish. Both compiler
profiles must preserve the same admitted scheduler traces and bytecode.
"""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
override = os.environ.get('OV_SCHEDULER_COMMAND')
OV = shlex.split(override) if override else [str(ROOT / '.lake/build/bin/openverse')]
CV = ROOT / 'runtime/build/cverse'
checks = 0


def run(args):
    return subprocess.run([str(x) for x in args], cwd=ROOT, capture_output=True,
                          text=True, timeout=30)


def require(condition, message):
    global checks
    if not condition:
        raise SystemExit(message)
    checks += 1


with tempfile.TemporaryDirectory(prefix='openverse-scheduler-conformance-') as directory:
    tmp = Path(directory)

    def trace(label, source, expected):
        output = tmp / 'program.vbc'
        output.unlink(missing_ok=True)
        result = run(OV + ['run', source, '--emit', output])
        require((result.returncode, result.stdout, result.stderr) == expected,
                f'{label}: wrong Lean trace: '
                f'{result.returncode,result.stdout,result.stderr}; expected {expected}')
        require(output.exists(), f'{label}: source was not compiled')
        code = output.read_bytes()
        c = run([CV, output])
        require((c.returncode, c.stdout, c.stderr) == expected,
                f'{label}: wrong C trace: {c.returncode,c.stdout,c.stderr}')
        profile = run(OV + ['run', source, '--no-choice', '--emit', output])
        require((profile.returncode, profile.stdout, profile.stderr) == expected,
                f'{label}: wrong choice-free trace: '
                f'{profile.returncode,profile.stdout,profile.stderr}')
        require(output.read_bytes() == code, f'{label}: profile changed scheduler bytecode')

    fixtures = sorted((ROOT / 'tests/verse').glob('scheduler_audit_*.verse'))
    require(len(fixtures) == 11, f'expected the eleven documented scheduler cases, got {len(fixtures)}')
    for fixture in fixtures:
        stdout, code = fixture.with_suffix('.expected').read_text().rsplit('exit=', 1)
        stderr = fixture.with_suffix('.stderr')
        trace(fixture.stem, fixture,
              (int(code.strip()), stdout, stderr.read_text() if stderr.exists() else ''))

    controls = [
        ('deadlock', 'Sleep(Inf)', 'Sleep(0.0)', 'waiting\nafter\n'),
        ('clock_bounds', '1000000000000000.0', '999999999999999.0',
         'below cutoff\nabove cutoff\n'),
        ('clock_overflow', 'I=400', 'I=2', 'before\nafter\n'),
    ]
    for name, old, new, stdout in controls:
        text = (ROOT / f'tests/verse/scheduler_audit_{name}.verse').read_text()
        require(text.count(old) == 1, f'{name}: ambiguous finite-control substitution')
        source = tmp / 'finite.verse'
        source.write_text(text.replace(old, new))
        trace(name + ' finite control', source, (0, stdout, ''))

print(f'scheduler-conformance: {checks} checks, {len(fixtures)} reference traces and '
      f'{len(controls)} finite controls agree in Lean/C and both source profiles')
