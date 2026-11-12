#!/usr/bin/env python3
"""Check packed and explicit controls against independently computed traces."""
import importlib.util
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('call_packing', ROOT / 'scripts/models/call_packing.py')
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)
count = int(sys.argv[1]) if len(sys.argv) > 1 else model.PERIOD
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
compiler = shlex.split(os.environ.get('OV_COMMAND', str(ROOT / '.lake/build/bin/openverse')))
with tempfile.TemporaryDirectory(prefix='ov-call-packing-') as directory:
    source, bytecode = (Path(directory) / name for name in ('program.verse', 'program.vbc'))
    # Adaptation must not create calls that fit two admitted declarations.
    for left, right in (
            ('P:tuple(int)', 'X:int'),
            ('P:tuple()', ''),
            ('P:[]int', 'X:int,Y:int'),
            ('P:t where t:type', 'X:int,Y:string'),
            ('P:tuple(int)', 'P:tuple(tuple(int))'),
            ('P:void', 'X:string,Y:string')):
        for params in ((left, right), (right, left)):
            program = f'F({params[0]}):int=1\nF({params[1]}):int=2\nMain():void={{}}\n'
            source.write_text(program)
            bytecode.unlink(missing_ok=True)
            result = subprocess.run(compiler + ['run', str(source), '--emit', str(bytecode)],
                                    cwd=ROOT, capture_output=True, text=True, timeout=30)
            if (result.returncode != 4 or result.stdout or bytecode.exists()
                    or 'parameters a call cannot tell apart' not in result.stderr):
                saved = ROOT / 'fuzz-call-packing-overlap.verse'
                saved.write_text(program)
                raise SystemExit(f'packed overload overlap: bad refusal, saved {saved.name}: {result.stderr}')
    # Successful and invalid nesting must not repeatedly elaborate inner
    # singleton operands. Check real diagnostics as well as the time bound.
    for name, depth, leaf, diagnostic in (
            ('valid', 48, '1', None),
            ('unknown', 24, 'Missing()', "unknown function 'Missing'"),
            ('generic', 24, 'Bad()', 'cannot infer type parameter t of Bad'),
            ('field', 24, 'Box{}', "has no default value and must be given"),
            ('type', 24, '"bad"', 'expected int, found string')):
        expression = leaf
        for _ in range(depth):
            expression = f'One({expression})'
        program = ('Bad(?X:[]t=array{} where t:type)<computes>:int=X.Length\n'
                   'Box:=class{V:int}\n'
                   'One(P:tuple(int))<computes>:int=P(0)\n'
                   'Main():void=Print("{' + expression + '}")\n')
        source.write_text(program)
        bytecode.unlink(missing_ok=True)
        try:
            result = subprocess.run(compiler + ['run', str(source), '--emit', str(bytecode)],
                                    cwd=ROOT, capture_output=True, text=True, timeout=5)
            valid = ((result.returncode, result.stdout, result.stderr) == (0, '1\n', '')
                     if diagnostic is None else result.returncode == 4 and not result.stdout
                     and diagnostic in result.stderr and not bytecode.exists())
            if diagnostic is None and valid:
                c = subprocess.run([str(ROOT / 'runtime/build/cverse'), str(bytecode)],
                                   capture_output=True, text=True, timeout=5)
                valid = (c.returncode, c.stdout, c.stderr) == (0, '1\n', '')
        except subprocess.TimeoutExpired:
            valid = False
        if not valid:
            saved = ROOT / f'fuzz-call-packing-deep-{name}.verse'
            saved.write_text(program)
            raise SystemExit(f'nested singleton {name}: oracle/5-second bound failed, saved {saved.name}')
    for seed in range(first, first + count):
        program, expected = model.generate(seed)
        source.write_text(program)
        bytecode.unlink(missing_ok=True)
        try:
            lean = subprocess.run(compiler + ['run', str(source), '--emit', str(bytecode)],
                                  cwd=ROOT, capture_output=True, text=True, timeout=30)
            c = subprocess.run([str(ROOT / 'runtime/build/cverse'), str(bytecode)],
                               capture_output=True, text=True, timeout=30) if bytecode.exists() else None
            valid = c is not None and all((r.returncode, r.stdout, r.stderr) == (0, expected, '') for r in (lean, c))
            details = f'Lean={lean.returncode,lean.stdout,lean.stderr}; C={None if c is None else (c.returncode,c.stdout,c.stderr)}'
        except subprocess.TimeoutExpired:
            valid, details = False, 'timeout'
        if not valid:
            saved = ROOT / f'fuzz-call-packing-{seed}.verse'
            saved.write_text(program)
            saved.with_suffix('.expected').write_text(expected + 'exit=0\n')
            raise SystemExit(f'call packing seed {seed}, saved {saved.name}: {details}; expected={expected!r}')
print(f'call packing: {count} programs from seed {first}, packed/explicit controls and exact Lean/C traces passed')
