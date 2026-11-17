#!/usr/bin/env bash
# Check private-cell alias and payload transfers through the actual metadata API.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
# The native response file and every imported public layout must agree.
lake build
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


with tempfile.TemporaryDirectory(prefix="openverse-metadata-cell-flow-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("metadata cell flow: unrecognized Lake linker inputs")
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            path = Path(arg).resolve()
            if not path.is_relative_to(build):
                raise SystemExit(f"metadata cell flow: stale foreign linker input: {arg}")
            if not path.exists():
                raise SystemExit(f"metadata cell flow: missing linker input: {arg}")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataCellFlow.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    result = subprocess.run([str(binary)], text=True, capture_output=True,
                            timeout=15, preexec_fn=limits)
    if result.returncode or result.stderr:
        raise SystemExit(f"metadata cell flow failed ({result.returncode}):\n"
                         f"{result.stdout}{result.stderr}")
    print("private cell flow: 150 API classifications passed (15s, 4 GiB)")
PY
