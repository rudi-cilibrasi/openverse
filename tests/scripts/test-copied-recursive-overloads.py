#!/usr/bin/env python3
"""Check copied recursive selection against explicit typed loops and a model."""
from pathlib import Path
import importlib.util
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('model', root/'tests/scripts/copied-recursive-overload-model.py')
model = importlib.util.module_from_spec(spec)
# dataclass annotations need the defining module registered during import.
import sys
sys.modules[spec.name] = model
spec.loader.exec_module(model)
compiler = root/'.lake/build/bin/openverse'
runtime = root/'runtime/build/cverse'
with tempfile.TemporaryDirectory(prefix='openverse-copied-recursive-') as directory:
    temporary = Path(directory)
    for name in model.CASES:
        outputs = []
        for control in [True, False]:
            label = 'control' if control else 'copied'
            source = temporary/f'{name}-{label}.verse'
            source.write_text(model.source(name, control))
            bytecode = source.with_suffix('.vbc')
            lean = subprocess.run([str(compiler), 'run', str(source), '--emit', str(bytecode)], capture_output=True, timeout=60)
            assert lean.returncode == 0, (name, label, lean.stderr.decode())
            c = subprocess.run([str(runtime), str(bytecode)], capture_output=True, timeout=60)
            assert (c.returncode, c.stdout, c.stderr) == (lean.returncode, lean.stdout, lean.stderr), (name, label, 'VM mismatch')
            output = lean.stdout.decode()
            values = ''.join(line+'\n' for line in output.splitlines() if line.startswith(('for<', 'first<', 'option<')))
            assert values == model.oracle(name), (name, label, 'independent value/order oracle', values, model.oracle(name))
            outputs.append((lean.stdout, lean.stderr))
        assert outputs[0] == outputs[1], (name, 'explicit control differs, including effects/cleanup/default order')
        print('copied recursive overload:', name, 'all three consumers, both VMs, explicit trace and value oracle')
print('copied recursive overload conformance passed')
