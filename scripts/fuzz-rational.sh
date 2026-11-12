#!/usr/bin/env bash
# Exact rational operators against Python's arbitrary-precision Fraction model.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
n="${1:-120}"; first="${2:-1}"
python3 - "$root" "$n" "$first" <<'PY'
from pathlib import Path
import subprocess,sys,tempfile
root=Path(sys.argv[1]);count=int(sys.argv[2]);first=int(sys.argv[3])
ov=root/'.lake/build/bin/openverse';cv=root/'runtime/build/cverse'
with tempfile.TemporaryDirectory(prefix='openverse-rational-') as directory:
    tmp=Path(directory)
    for seed in range(first,first+count):
        source,expected,bytecode=[tmp/f'p.{ext}' for ext in ['verse','expected','vbc']]
        gen=subprocess.run(['python3','-I',str(root/'scripts/models/rational_arith.py'),str(seed),str(expected)],capture_output=True,text=True,timeout=10)
        if gen.returncode:raise SystemExit(f'rational generator failed seed {seed}: {gen.stderr}')
        source.write_text(gen.stdout)
        r=subprocess.run([str(ov),'run',str(source),'--emit',str(bytecode)],capture_output=True,text=True,timeout=30)
        want=expected.read_text();actual=f'exit={r.returncode}\n'+r.stdout
        c=None if r.returncode==4 else subprocess.run([str(cv),str(bytecode)],capture_output=True,text=True,timeout=30)
        stderr='error: overflow\n' if r.returncode==2 else ''
        if actual!=want or r.stderr!=stderr or c is None or (c.returncode,c.stdout,c.stderr)!=(r.returncode,r.stdout,r.stderr):
            saved=root/f'fuzz-rational-{seed}.verse';saved.write_text(gen.stdout)
            saved.with_suffix('.expected').write_text(want)
            raise SystemExit(f'rational mismatch seed {seed}, saved {saved.name}; Lean={r.returncode,r.stdout,r.stderr}; C={None if c is None else (c.returncode,c.stdout,c.stderr)}; expected={want!r}')
print(f'fuzz-rational: {count} programs from seed {first}, exact Fraction oracles and Lean/C agree')
PY
