#!/usr/bin/env python3
"""Run source-level overload-domain oracles and compare both runtimes."""
import importlib.util
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('overload_shapes', root / 'scripts/models/overload_shapes.py')
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)
count = int(sys.argv[1]) if len(sys.argv) > 1 else model.PERIOD
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
# The override supports fresh Lean-module testing before a native rebuild.
override = os.environ.get('OV_OVERLOAD_COMMAND')
compiler = shlex.split(override) if override else [str(root / '.lake/build/bin/openverse')]
accepted = refused = 0


def fail(seed, program, expected, message):
    saved = root / f'fuzz-overload-shapes-{seed}.verse'
    saved.write_text(program)
    saved.with_suffix('.expected.json').write_text(json.dumps(expected, indent=2) + '\n')
    raise SystemExit(f'overload mismatch seed {seed}, saved {saved.name}; {message}; expected={expected}')


with tempfile.TemporaryDirectory(prefix='openverse-overload-shapes-') as directory:
    source = Path(directory) / 'program.verse'
    bytecode = Path(directory) / 'program.vbc'
    # A missing callee deep inside an argument must not make tuple retries
    # repeatedly recheck the whole invalid producer. Keep its real diagnostic.
    for kind in ['unknown', 'type_error']:
        nested = root / f'tests/errors/overload_shapes_nested_{kind}.verse'
        diagnostic = nested.read_text().splitlines()[0].removeprefix('# expect: ')
        try:
            check = subprocess.run(compiler + ['check', str(nested)], cwd=root,
                                   capture_output=True, text=True, timeout=5)
        except subprocess.TimeoutExpired:
            raise SystemExit('overload nesting regression: invalid producer exceeded 5 seconds')
        if check.returncode != 4 or check.stdout or diagnostic not in check.stderr:
            raise SystemExit(f'overload nesting diagnostic changed: {check.returncode,check.stdout,check.stderr}')
    for seed in range(first, first + count):
        program, expected = model.generate(seed)
        source.write_text(program)
        bytecode.unlink(missing_ok=True)
        try:
            result = subprocess.run(compiler + ['run', str(source), '--emit', str(bytecode)],
                                    cwd=root, capture_output=True, text=True, timeout=45)
        except subprocess.TimeoutExpired:
            fail(seed, program, expected, 'compiler timeout')
        c = None
        valid = result.returncode == expected['exit']
        if expected['exit'] == 4:
            valid &= (not result.stdout and expected['diagnostic'] in result.stderr
                      and not bytecode.exists())
            refused += 1
        else:
            valid &= result.stdout == expected['stdout'] and not result.stderr
            if bytecode.exists():
                try:
                    c = subprocess.run([str(root / 'runtime/build/cverse'), str(bytecode)],
                                       capture_output=True, text=True, timeout=30)
                except subprocess.TimeoutExpired:
                    fail(seed, program, expected, 'C runtime timeout')
                valid &= (c.returncode, c.stdout, c.stderr) == (0, expected['stdout'], '')
            else:
                valid = False
            accepted += 1
        if not valid:
            fail(seed, program, expected,
                 f'Lean={result.returncode,result.stdout,result.stderr}; '
                 f'C={None if c is None else (c.returncode,c.stdout,c.stderr)}')
print(f'overload-shapes: {count} programs from seed {first}, {accepted} accepted in Lean/C, '
      f'{refused} expected refusals, both declaration orders and seven contexts, no mismatches')
