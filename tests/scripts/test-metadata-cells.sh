#!/usr/bin/env bash
# Exercise the actual private-cell abstract heap, including its native scale path.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
lake build OpenVerse.Front.MetadataCells
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


with tempfile.TemporaryDirectory(prefix="openverse-metadata-cells-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("metadata cells: unrecognized Lake linker inputs")
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            path = Path(arg).resolve()
            try:
                path.relative_to(build)
            except ValueError:
                raise SystemExit(f"metadata cells: stale foreign linker input: {arg}")
            if not path.exists():
                raise SystemExit(f"metadata cells: missing linker input: {arg}")
    args[0] = str(source)
    # The domain can be checked before its integration into the front end.
    if not any("/MetadataCells.c.o" in arg for arg in args):
        domain = work / "domain.o"
        subprocess.run(["lake", "env", "leanc", "-O3", "-c",
                        ".lake/build/ir/OpenVerse/Front/MetadataCells.c",
                        "-o", str(domain)], check=True)
        args.insert(1, str(domain))
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataCells.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    for flags in ([], ["--scale"]):
        result = subprocess.run([str(binary), *flags], check=True, text=True,
                                capture_output=True, timeout=15, preexec_fn=limits)
        if result.stderr:
            raise SystemExit(f"metadata cells: unexpected stderr: {result.stderr}")
        print(result.stdout, end="")
PY
