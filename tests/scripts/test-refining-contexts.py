#!/usr/bin/env python3
"""Compare a refining-cast model and its source controls in Lean and C."""
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
count = int(sys.argv[1]) if len(sys.argv) > 1 else 144
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
compiler = root / '.lake/build/bin/openverse'
runtime = root / 'runtime/build/cverse'
model = sys.argv[3] if len(sys.argv) > 3 else 'gadt_contexts.py'
generator = root / 'scripts/models' / model
label = {'gadt_task_order.py': 'refining-task-order',
         'gadt_waiting_contexts.py': 'waiting-defaults'}.get(model, 'refining-contexts')

def invoke(command):
    return subprocess.run(list(map(str, command)), cwd=root,
                          capture_output=True, text=True, timeout=30)

with tempfile.TemporaryDirectory(prefix='openverse-refining-contexts-') as directory:
    tmp = Path(directory)
    for seed in range(first, first + count):
        oracle = None
        for control in [False, True]:
            source = tmp / 'p.verse'
            expected = tmp / 'p.expected'
            bytecode = tmp / 'p.vbc'
            generated = invoke(['python3', '-I', generator, seed, expected,
                                *(['--control'] if control else [])])
            if generated.returncode:
                raise SystemExit(f'{label}: generator failed at seed {seed}: {generated.stderr}')
            source.write_text(generated.stdout)
            want = expected.read_text()
            if oracle is not None and oracle != want:
                raise SystemExit(f'{label}: source/control oracle differs at seed {seed}')
            oracle = want
            lean = invoke([compiler, 'run', source, '--emit', bytecode])
            bad = f'exit={lean.returncode}\n' + lean.stdout != want or bool(lean.stderr)
            c = None if lean.returncode else invoke([runtime, bytecode])
            bad = bad or c is None or (c.returncode, c.stdout, c.stderr) != (lean.returncode, lean.stdout, lean.stderr)
            if bad:
                name = f'fuzz-{label}-{seed}' + ('-control' if control else '')
                (root / (name + '.verse')).write_text(generated.stdout)
                (root / (name + '.expected')).write_text(want)
                raise SystemExit(f'{label}: mismatch at seed {seed}, saved {name}.verse; '
                                 f'Lean={lean.returncode, lean.stdout, lean.stderr}; '
                                 f'C={None if c is None else (c.returncode, c.stdout, c.stderr)}')
print(f'{label}: {count} source/control pairs from seed {first}, '
      f'{4 * count} Lean/C comparisons matched the independent oracle')
