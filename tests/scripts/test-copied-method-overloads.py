#!/usr/bin/env python3
"""Check copied method lists against typed controls and complete source oracles."""
from pathlib import Path
import importlib.util
import subprocess
import sys
import tempfile
# (#515: Epic's default effect written out in every program this writes)
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts/models'))
import default_effect  # noqa: E402
default_effect.install()

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'copied_method_model', root/'tests/scripts/copied-method-overload-model.py')
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)
compiler = root/'.lake/build/bin/openverse'
runtime = root/'runtime/build/cverse'
count = 0
with tempfile.TemporaryDirectory(prefix='openverse-copied-methods-') as directory:
    temporary = Path(directory)
    for name, copied, control, expected in model.cases():
        for label, text in [('control', control), ('copied', copied)]:
            source = temporary/f'{name}-{label}.verse'
            source.write_text(text)
            bytecode = source.with_suffix('.vbc')
            lean = subprocess.run([str(compiler), 'run', str(source), '--emit', str(bytecode)],
                                  capture_output=True, timeout=30)
            assert (lean.returncode, lean.stdout.decode(), lean.stderr) == (0, expected, b''), (
                name, label, 'Lean source oracle', lean.returncode, lean.stdout, lean.stderr)
            c = subprocess.run([str(runtime), str(bytecode)], capture_output=True, timeout=30)
            assert (c.returncode, c.stdout.decode(), c.stderr) == (0, expected, b''), (
                name, label, 'C source oracle', c.returncode, c.stdout, c.stderr)
        count += 1
        print('copied method overload:', name, 'typed control and complete Lean/C oracle')
print(f'copied method overload conformance passed ({count} cases)')
