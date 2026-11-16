#!/usr/bin/env bash
# Check selected-world conditional producers through the compiler API and
# both VMs, with fixed native per-program time/address-space budgets.
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
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))


def bounded(command):
    return subprocess.run(command, capture_output=True, text=True, check=True,
                          timeout=15, preexec_fn=limits)


with tempfile.TemporaryDirectory(prefix="openverse-refined-conditional-") as temporary:
    work = Path(temporary)
    source = work / "api.c"
    binary = work / "api"
    args = shlex.split(Path(".lake/build/bin/openverse.rsp").read_text())
    if not args or not args[0].endswith("Main.c.o.export"):
        raise SystemExit("conditional-choice: unrecognized Lake linker inputs")
    args[0] = str(source)
    response = work / "api.rsp"
    response.write_text("\n".join(json.dumps(arg) for arg in args) + "\n")
    subprocess.run(["lake", "env", "lean", "-j1", "-c", str(source),
                    "tests/lean/RefinedConditionalChoice.lean"], check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-o", str(binary),
                    "@" + str(response)], check=True)
    count = int(bounded([str(binary), "--count"]).stdout)
    for index in range(count):
        bounded([str(binary), str(index), str(work)])
    bounded([str(binary), "--shape", str(work)])
    programs = sorted(work.glob("*.vbc"))
    if len(programs) != 23:
        raise SystemExit(f"conditional-choice: expected 23 admitted API artifacts, got {len(programs)}")
    for program in programs:
        actual = bounded(["runtime/build/cverse", str(program)]).stdout
        if actual != program.with_suffix(".expected").read_text():
            raise SystemExit(f"conditional-choice: incomplete C trace for {program.name}")

    fixture = Path("tests/verse/class_cast_refine_conditional_choice_snapshot.verse").read_text()
    original = "then((L.V,R.V)|(L.V+1,R.V))"
    if original not in fixture:
        raise SystemExit("conditional-choice: resource fixture branch changed")
    sizes = []
    for width in [2, 8, 32]:
        alternatives = "|".join(f"(L.V+{index},R.V)" for index in range(width))
        text = fixture.replace(original, "then(" + alternatives + ")")
        path = work / f"width-{width}.verse"
        bytecode = path.with_suffix(".vbc")
        path.write_text(text)
        expected = "prefix\nprefix\n" + "".join(
            f"{saved + index} 7\n" for saved in [3, 99] for index in range(width)) + "final 99\n"
        actual = bounded([".lake/build/bin/openverse", "run", str(path),
                          "--emit", str(bytecode)]).stdout
        c_actual = bounded(["runtime/build/cverse", str(bytecode)]).stdout
        if actual != expected or c_actual != expected:
            raise SystemExit(f"conditional-choice: wrong complete width-{width} trace")
        sizes.append(bytecode.stat().st_size)
    if sizes[-1] > 4 * 1024**2 or sizes[-1] > 20 * sizes[0]:
        raise SystemExit(f"conditional-choice: excessive branch growth {sizes}")
    print(f"conditional selected-world contracts passed: {count} real/metadata pairs, "
          f"{len(programs)} complete C traces, widths 2/8/32 bytecode {sizes}")
PY
