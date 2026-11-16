#!/usr/bin/env python3
"""Invocation-local scalar returns, including complete cleanup/rollback traces."""
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OV = ROOT / '.lake/build/bin/openverse'
CV = ROOT / 'runtime/build/cverse'


def limits():
    inherited = resource.getrlimit(resource.RLIMIT_AS)
    cap = min([4 * 1024 ** 3] +
              [value for value in inherited if value != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def run(args):
    return subprocess.run([str(arg) for arg in args], capture_output=True,
                          text=True, timeout=15, preexec_fn=limits)


fixtures = sorted((ROOT / 'tests/verse').glob('multi_return_boundary_*.verse'))
fixtures += [ROOT / 'tests/verse' / f'multi_return_{name}.verse'
             for name in ('loop', 'expression')]
with tempfile.TemporaryDirectory(prefix='openverse-return-boundaries-') as tmp:
    tmp = Path(tmp)
    for source in fixtures:
        expected = source.with_suffix('.expected').read_text()
        assert expected.endswith('exit=0\n'), source
        expected = expected[:-len('exit=0\n')]
        warnings = source.with_suffix('.warnings')
        warnings = warnings.read_text() if warnings.exists() else ''
        for profile in ([], ['--extended-defaults']):
            bytecode = tmp / 'boundary.vbc'
            result = run([OV, 'run', source, *profile, '--emit', bytecode])
            assert result.returncode == 0 and result.stdout == expected, (source, profile, result)
            assert result.stderr.replace(str(source) + ':', '') == warnings, (source, result.stderr)
            result = run([CV, bytecode])
            assert result.returncode == 0 and result.stdout == expected and not result.stderr, (source, profile, result)
    # Independent scalar controls use ordinary returns and explicit arrays;
    # their invocation returns do not cross a multi-value inlining boundary.
    control = tmp / 'control.verse'
    control.write_text('''Loop(X:int)<transacts>:[]int=
    for(I:=1..X):
        if(I=2):return array{I}
    array{X,X+1}
Initializer(X:int)<transacts>:[]int=
    Y:=if(X>2)then(return array{0})else X*10
    array{Y,Y+1}
Main()<transacts>:void=
    for(V:Loop(3)){Print("l {V}")}
    for(V:Loop(1)){Print("l {V}")}
    for(V:Initializer(3)){Print("i {V}")}
    for(V:Initializer(1)){Print("i {V}")}
''')
    expected = 'l 2\nl 1\nl 2\ni 0\ni 10\ni 11\n'
    for profile in ([], ['--extended-defaults']):
        bytecode = tmp / 'control.vbc'
        result = run([OV, 'run', control, *profile, '--emit', bytecode])
        assert result.returncode == 0 and result.stdout == expected and not result.stderr, result
        result = run([CV, bytecode])
        assert result.returncode == 0 and result.stdout == expected and not result.stderr, result
print(f'return boundaries passed ({len(fixtures)} contracts, scalar controls, both profiles and VMs)')
