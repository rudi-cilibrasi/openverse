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
function_budget = 1024 * 1024
seen = set()
sizes = []
functions = []
definitions = re.compile(
    rb'(?m)^(?:LEAN_EXPORT |static )?(?:lean_object\*|uint\d+_t|int\d+_t|double|float|size_t|void)'
    rb'\s+([A-Za-z0-9_]+)\([^;\n]*\)\s*\{')

def visit(module):
    if not module.startswith('OpenVerse.Front.') or module in seen:
        return
    seen.add(module)
    path = ir.joinpath(*module.split('.')).with_suffix('.c')
    if not path.is_file():
        raise SystemExit(f'frontend-c-size: missing {path}; run lake build first')
    sizes.append((path.stat().st_size, path.relative_to(ir)))
    data = path.read_bytes()
    matches = list(definitions.finditer(data))
    if not matches:
        raise SystemExit(f'frontend-c-size: no generated C definitions found in {path}')
    for i, match in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(data)
        functions.append((end - match.start(), path.relative_to(ir), match.group(1).decode('ascii')))
    with path.open() as source:
        header = ''.join(source.readline() for _ in range(3))
    for dependency in re.findall(r'\bimport (?:all )?([A-Za-z_]\w*(?:\.\w+)*)', header):
        visit(dependency)

visit('OpenVerse.Front.Elab')
oversized = [(size, path) for size, path in sizes if size > budget]
large_functions = [(size, path, name) for size, path, name in functions if size > function_budget]
if oversized or large_functions:
    for size, path in sorted(oversized, reverse=True):
        print(f'frontend-c-size: {path}: {size} bytes exceeds {budget}', file=sys.stderr)
    for size, path, name in sorted(large_functions, reverse=True):
        print(f'frontend-c-size: {path}: {name}: {size} bytes exceeds function budget {function_budget}', file=sys.stderr)
    raise SystemExit(1)
largest, path = max(sizes)
print(f'frontend-c-size: {len(sizes)} units; largest {path}: {largest} bytes <= {budget}')
size, path, name = max(functions)
print(f'frontend-c-size: largest function {path}: {name}: {size} bytes <= {function_budget}')
PY
