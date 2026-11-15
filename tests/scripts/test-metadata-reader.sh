#!/usr/bin/env bash
# Run the compiler-API resource regression natively, after the proof build
# and before parallel checks compete for its fixed time/memory allowance.
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

with tempfile.TemporaryDirectory(prefix="openverse-metadata-reader-") as work:
    work = Path(work)
    source = work / "reader.c"
    binary = work / "reader"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("metadata-reader: unrecognized Lake linker inputs")
    args[0] = str(source)
    response = work / "reader.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataReader.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)

    def limits():
        inherited = resource.getrlimit(resource.RLIMIT_AS)
        cap = min([4 * 1024 ** 3] +
                  [value for value in inherited if value != resource.RLIM_INFINITY])
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    count = int(subprocess.check_output([str(binary), "--count"], text=True,
                                        timeout=15, preexec_fn=limits))
    for index in range(count):
        try:
            # Each real/metadata source pair has the original diagnostic's
            # own 15-second / 4-GB allowance.
            result = subprocess.run([str(binary), str(index)], text=True,
                                    capture_output=True, timeout=15, preexec_fn=limits)
        except subprocess.TimeoutExpired:
            raise SystemExit(f"metadata-reader: case {index} exceeded unchanged 15-second bound")
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    print(f"metadata reader contracts passed ({count} real/metadata pairs)")
PY
