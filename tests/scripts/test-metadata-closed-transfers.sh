#!/usr/bin/env bash
# Check closed transfers without omitting incoming private aliases or argument effects.
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


with tempfile.TemporaryDirectory(prefix="openverse-metadata-closed-transfers-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("metadata closed transfers: unrecognized Lake linker inputs")
    build = (Path.cwd() / ".lake/build").resolve()
    for arg in args:
        if ".lake/build/" in arg:
            path = Path(arg).resolve()
            if not path.is_relative_to(build):
                raise SystemExit(f"metadata closed transfers: stale foreign linker input: {arg}")
            if not path.exists():
                raise SystemExit(f"metadata closed transfers: missing linker input: {arg}")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/MetadataClosedTransfers.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    for flags in ([],):
        result = subprocess.run([str(binary), *flags], text=True, capture_output=True,
                                timeout=15, preexec_fn=limits)
        if result.returncode or result.stderr:
            raise SystemExit(f"metadata closed transfers failed ({result.returncode}):\n"
                             f"{result.stdout}{result.stderr}")
    print("closed transfers: 19 typed API classifications passed (15s, 4 GiB)")
PY

# Ordinary reference-returning recursion must stay within the same native
# budget even when its consumer is an independently validated dormant root.
make -s -C runtime
python3 - <<'PYRUN'
import resource
import subprocess
import tempfile
from pathlib import Path

root = Path.cwd()
def limits():
    inherited = resource.getrlimit(resource.RLIMIT_AS)
    cap = min([4 * 1024**3] + [v for v in inherited if v != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
def run(args):
    p = subprocess.run(list(map(str, args)), text=True, capture_output=True,
                       timeout=15, preexec_fn=limits)
    assert p.returncode == 0 and not p.stderr, (args, p)
    return p.stdout
with tempfile.TemporaryDirectory(prefix='openverse-closed-data-runtime-') as tmp:
    for name in ('live', 'dormant'):
        source = root / f'tests/verse/metadata_recursive_data_{name}.verse'
        expected = source.with_suffix('.expected').read_text()
        assert expected.endswith('exit=0\n')
        expected = expected[:-len('exit=0\n')]
        for profile in ([], ['--extended-defaults']):
            bytecode = Path(tmp) / 'data.vbc'
            bytecode.unlink(missing_ok=True)
            assert run([root/'.lake/build/bin/openverse', 'run', source, *profile, '--emit', bytecode]) == expected
            assert run([root/'runtime/build/cverse', bytecode]) == expected
print('closed transfers: recursive data live/dormant, both profiles and VMs passed (15s, 4 GiB)')
PYRUN
