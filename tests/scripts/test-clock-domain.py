#!/usr/bin/env python3
"""Check bounded reference-clock traces against an independent rational model."""
import importlib.util
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('clock_domain', ROOT / 'scripts/models/clock_domain.py')
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)
count = int(sys.argv[1]) if len(sys.argv) > 1 else model.PERIOD
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
override = os.environ.get('OV_CLOCK_COMMAND')
compiler = shlex.split(override) if override else [str(ROOT / '.lake/build/bin/openverse')]
checks = 0


def run(args, timeout=30):
    command = [str(a) for a in args]
    process = subprocess.Popen(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(command, timeout, stdout, stderr)
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


with tempfile.TemporaryDirectory(prefix='openverse-clock-domain-') as directory:
    tmp = Path(directory)

    def check(label, source, expected):
        global checks
        code = None
        for profile in ([], ['--no-choice']):
            output = tmp / 'program.vbc'
            output.unlink(missing_ok=True)
            q = run(compiler + ['run', source, '--emit', output] + profile)
            if (q.returncode, q.stdout, q.stderr) != (expected['exit'], expected['stdout'], expected['stderr']):
                raise AssertionError(f'{label}, {profile}: Lean={q.returncode,q.stdout,q.stderr}; expected={expected}')
            if not output.exists():
                raise AssertionError(f'{label}: no fresh bytecode')
            c = run([ROOT / 'runtime/build/cverse', output])
            if (c.returncode, c.stdout, c.stderr) != (expected['exit'], expected['stdout'], expected['stderr']):
                raise AssertionError(f'{label}, {profile}: C={c.returncode,c.stdout,c.stderr}; expected={expected}')
            actual = output.read_bytes()
            if code is not None and code != actual:
                raise AssertionError(f'{label}: source profile changed clock bytecode')
            code = actual
            checks += 2

    fixtures = sorted((ROOT / 'tests/verse').glob('clock_domain_*.verse'))
    for source in fixtures:
        stdout, status = source.with_suffix('.expected').read_text().rsplit('exit=', 1)
        stderr = source.with_suffix('.stderr')
        expected = dict(exit=int(status.strip()), stdout=stdout,
                        stderr=stderr.read_text() if stderr.exists() else '')
        check(source.stem, source, expected)
    for seed in range(first, first + count):
        program, expected = model.generate(seed)
        source = tmp / 'model.verse'
        source.write_text(program)
        try:
            check(f'clock seed {seed}', source, expected)
        except (AssertionError, subprocess.TimeoutExpired):
            saved = ROOT / f'fuzz-clock-domain-{seed}.verse'
            saved.write_text(program)
            saved.with_suffix('.expected.json').write_text(json.dumps(expected, indent=2) + '\n')
            raise
print(f'clock-domain: {checks} Lean/C checks, {len(fixtures)} fixtures and {count} model programs '
      f'from seed {first}, both source profiles and identical bytecode')
