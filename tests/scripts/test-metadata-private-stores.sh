#!/usr/bin/env bash
# Native API classifications and complete C traces retain the fixed budget.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 - <<'PY'
import json
import resource
import shlex
import subprocess
import tempfile
from pathlib import Path


def limits():
    inherited = resource.getrlimit(resource.RLIMIT_AS)
    cap = min([4 * 1024**3] +
              [value for value in inherited if value != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def bounded(args):
    return subprocess.run(args, check=True, text=True, capture_output=True,
                          timeout=15, preexec_fn=limits)


with tempfile.TemporaryDirectory(prefix="openverse-metadata-private-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("metadata private-store: unrecognized Lake linker inputs")
    # Copied Lake caches can retain response paths into another worktree.
    # Such a link would silently validate that tree's provenance checker.
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            try:
                Path(arg).resolve().relative_to(build)
            except ValueError:
                raise SystemExit(f"metadata private-store: stale foreign linker input: {arg}")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataPrivateStores.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    bounded([str(binary), "--ownership"])
    count = int(bounded([str(binary), "--count"]).stdout)
    for index in range(count):
        bounded([str(binary), str(index), str(work)])
    programs = sorted(work.glob("*.vbc"))
    if len(programs) != 52:
        raise SystemExit(f"metadata private-store: expected 52 admitted artifacts, got {len(programs)}")
    for program in programs:
        result = bounded(["runtime/build/cverse", str(program)])
        if result.stdout != program.with_suffix(".expected").read_text() or result.stderr:
            raise SystemExit(f"metadata private-store: incomplete C trace for {program.name}")
print("metadata private stores passed (20 cases, 80 classifications, 12 ownership models, 52 complete C traces)")
PY
