#!/usr/bin/env bash
# Preserve grounded source/control metadata roles and complete VM outputs.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
# The native response file and every imported public layout must agree.
lake build
make -C runtime
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


with tempfile.TemporaryDirectory(prefix="openverse-metadata-logical-cells-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("logical cell source: unrecognized Lake linker inputs")
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            path = Path(arg).resolve()
            if not path.is_relative_to(build):
                raise SystemExit(f"logical cell source: stale foreign linker input: {arg}")
            if not path.exists():
                raise SystemExit(f"logical cell source: missing linker input: {arg}")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataLogicalCells.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    artifacts = work / "artifacts"
    artifacts.mkdir()
    try:
        result = subprocess.run([str(binary), str(artifacts)], text=True, capture_output=True,
                                timeout=15, preexec_fn=limits)
    except subprocess.TimeoutExpired as error:
        raise SystemExit(f"logical cell source timed out:\n{error.stdout!r}\n{error.stderr!r}")
    if result.returncode or result.stderr:
        raise SystemExit(f"logical cell source failed ({result.returncode}):\n"
                         f"{result.stdout}{result.stderr}")
    programs = sorted(artifacts.glob("*.vbc"))
    if len(programs) != 120:
        raise SystemExit(f"logical cell source: expected 120 artifacts, got {len(programs)}")
    for program in programs:
        expected = program.with_suffix(".expected").read_text()
        run = subprocess.run(["runtime/build/cverse", str(program)], text=True,
                             capture_output=True, timeout=15, preexec_fn=limits)
        if run.returncode or run.stderr or run.stdout != expected:
            raise SystemExit(f"logical cell C oracle failed: {program.name}: "
                             f"{run.returncode}: {run.stdout!r} {run.stderr!r}")
    print("logical cell source: 168 API classifications, 120 matching Lean/C oracle pairs (15s, 4 GiB)")
PY
