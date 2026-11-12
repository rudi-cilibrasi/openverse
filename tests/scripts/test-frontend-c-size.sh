#!/usr/bin/env bash
# Keep the browser compiler's reachable front-end units within its optimized budget.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
python3 - "$root/.lake/build/ir" <<'PY'
from pathlib import Path
import re
import sys

ir = Path(sys.argv[1])
budget = 8 * 1024 * 1024
seen = set()
sizes = []

def visit(module):
    if not module.startswith('OpenVerse.Front.') or module in seen:
        return
    seen.add(module)
    path = ir.joinpath(*module.split('.')).with_suffix('.c')
    if not path.is_file():
        raise SystemExit(f'frontend-c-size: missing {path}; run lake build first')
    sizes.append((path.stat().st_size, path.relative_to(ir)))
    with path.open() as source:
        header = ''.join(source.readline() for _ in range(3))
    for dependency in re.findall(r'\bimport (?:all )?([A-Za-z_]\w*(?:\.\w+)*)', header):
        visit(dependency)

visit('OpenVerse.Front.Elab')
oversized = [(size, path) for size, path in sizes if size > budget]
if oversized:
    for size, path in sorted(oversized, reverse=True):
        print(f'frontend-c-size: {path}: {size} bytes exceeds {budget}', file=sys.stderr)
    raise SystemExit(1)
largest, path = max(sizes)
print(f'frontend-c-size: {len(sizes)} units; largest {path}: {largest} bytes <= {budget}')
PY
