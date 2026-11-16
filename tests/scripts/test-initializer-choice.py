#!/usr/bin/env python3
"""Preserve lazy initializer arms, cleanup scope and one shared suffix."""
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
    result = subprocess.run([str(arg) for arg in args], capture_output=True,
                            text=True, timeout=15, preexec_fn=limits)
    assert result.returncode == 0 and not result.stderr, (args, result)
    return result.stdout


with tempfile.TemporaryDirectory(prefix='openverse-initializer-suffix-') as tmp:
    tmp = Path(tmp)
    sizes = []
    for count in (17, 32, 64):
        # Both normal initializer values reach this same return prefix. The
        # enclosing registration runs per produced value, including rejection
        # and selection through the caller's first-success condition.
        source = ('F(N:int)<transacts>:int=\n'
                  '    defer:Print("out {N}")\n'
                  '    Y:=if(N<0)then(return -1)else(10|20)\n')
        for index in range(count):
            source += f'    if(N={index}):return Y+{index}\n'
        source += f'    Y+{count}|Y+{count+1}\n'
        inputs = (-1, 0, count // 2, count - 1, count)
        source += 'Main()<transacts>:void=\n    for(N:array{'
        source += ','.join(map(str, inputs))
        source += '}){for(V:=F(N)){Print("v {V}")}}\n'
        source += (f'    if(V:=F({count//2}),V={20+count//2})'
                   'then Print("first {V}")else Print("bad")\n'
                   '    if(V:=F(0),V=999)then Print("bad")else Print("none")\n')
        expected = ''
        for n in inputs:
            values = [-1] if n < 0 else [
                y + n + extra for y in (10, 20)
                for extra in ((0,) if n < count else (0, 1))]
            expected += ''.join(f'out {n}\nv {value}\n' for value in values)
        expected += f'out {count//2}\nfirst {20+count//2}\nnone\n'
        path = tmp / f'{count}.verse'
        path.write_text(source)
        for profile in ([], ['--extended-defaults']):
            bytecode = tmp / f'{count}-{len(profile)}.vbc'
            assert run([OV, 'run', path, *profile, '--emit', bytecode]) == expected
            assert run([CV, bytecode]) == expected
            if not profile:
                sizes.append(bytecode.stat().st_size)
    assert sizes[2] < 3 * sizes[1], sizes
    print(f'initializer shared suffix growth passed (17/32/64 guards; bytes {sizes})')

fixtures = sorted((ROOT / 'tests/verse').glob('multi_return_initializer_choice_*.verse'))
for source in fixtures:
    expected = source.with_suffix('.expected').read_text()
    assert expected.endswith('exit=0\n'), source
    expected = expected[:-len('exit=0\n')]
    with tempfile.TemporaryDirectory(prefix='openverse-initializer-contract-') as tmp:
        for profile in ([], ['--extended-defaults']):
            bytecode = Path(tmp) / 'initializer.vbc'
            assert run([OV, 'run', source, *profile, '--emit', bytecode]) == expected, (source, profile, 'Lean')
            assert run([CV, bytecode]) == expected, (source, profile, 'C')

for source in sorted((ROOT / 'tests/errors').glob('multi_return_initializer_choice_*.verse')):
    expected = next(line.removeprefix('# expect: ') for line in source.read_text().splitlines()
                    if line.startswith('# expect: '))
    for profile in ([], ['--extended-defaults']):
        result = subprocess.run([str(OV), 'run', str(source), *profile], capture_output=True,
                                text=True, timeout=15, preexec_fn=limits)
        assert result.returncode == 4 and str(source) + ':' + expected in result.stderr, (source, profile, result)
print(f'initializer choice contracts passed ({len(fixtures)} complete contracts, source scope refusals, both profiles and VMs)')
