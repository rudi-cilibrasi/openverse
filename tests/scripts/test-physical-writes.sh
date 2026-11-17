#!/usr/bin/env bash
# The actual native annotation pass must retain the Core write certificate.
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


with tempfile.TemporaryDirectory(prefix="openverse-physical-writes-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("physical writes: unrecognized Lake linker inputs")
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            try:
                Path(arg).resolve().relative_to(build)
            except ValueError:
                raise SystemExit(f"physical writes: stale foreign linker input: {arg}")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/PhysicalWrites.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    for flags in ([], ["--scale"]):
        result = subprocess.run([str(binary), *flags], check=True, text=True,
                                capture_output=True, timeout=15, preexec_fn=limits)
        if result.stderr:
            raise SystemExit(f"physical writes: unexpected stderr: {result.stderr}")
        print(result.stdout, end="")
PY
