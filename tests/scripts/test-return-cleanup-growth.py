#!/usr/bin/env python3
"""Keep branch-local cleanup and mutable return prefixes within fixed resources."""
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
    result = subprocess.run([str(a) for a in args], capture_output=True,
                            text=True, timeout=15, preexec_fn=limits)
    assert result.returncode == 0, (args, result.returncode, result.stderr)
    assert not result.stderr, (args, result.stderr)
    return result.stdout


with tempfile.TemporaryDirectory(prefix='openverse-return-cleanup-') as tmp:
    tmp = Path(tmp)
    sizes = []
    # Every guard registers cleanup and mutates a local before returning two
    # values. Calls reach the first, middle and last guards and the fallthrough.
    # The outer/late registrations detect accidental changes of defer scope.
    for count in (17, 32, 64):
        source = 'F(N:int)<transacts>:int=\n'
        source += '    var Saved:int=10\n    defer:Print("outer {Saved}")\n'
        for i in range(count):
            source += (f'    if(N={i}):\n'
                       f'        defer:Print("inner {i} {{Saved}}")\n'
                       f'        set Saved+={i}\n'
                       '        return Saved|Saved+1\n')
        source += '    defer:Print("late {Saved}")\n    Saved|Saved+1\n'
        inputs = (0, count // 2, count - 1, count)
        source += 'Main()<transacts>:void=for(N:array{' + ','.join(map(str, inputs))
        source += '}){for(V:=F(N)){Print("v {V}")}}\n'
        expected = ''
        for n in inputs:
            value = 10 + n if n < count else 10
            for returned in (value, value + 1):
                expected += (f'inner {n} {value}\n' if n < count else f'late {value}\n')
                expected += f'outer {value}\nv {returned}\n'
        path = tmp / f'{count}.verse'
        path.write_text(source)
        for profile in ([], ['--extended-defaults']):
            bytecode = tmp / f'{count}-{len(profile)}.vbc'
            run([OV, 'emit', path, *profile, '-o', bytecode])
            assert run([OV, 'run', path, *profile]) == expected, (count, profile, 'Lean')
            assert run([CV, bytecode]) == expected, (count, profile, 'C')
            if not profile:
                sizes.append(bytecode.stat().st_size)
    # Doubling source size must not multiply the generated continuation tree.
    assert sizes[2] < 3 * sizes[1], sizes
    print(f'return cleanup growth passed (17/32/64 guards, both profiles and VMs; bytes {sizes})')

# Mixing plain returns with a later choice-bearing cleanup return must also
# expose nested exclusive selections to the enclosing consumer. Exercise all
# original large-return semantic fixtures in both compiler profiles here.
for source in sorted((ROOT / 'tests/verse').glob('multi_return_many*.verse')):
    expected = source.with_suffix('.expected').read_text()
    assert expected.endswith('exit=0\n'), source
    expected = expected[:-len('exit=0\n')]
    with tempfile.TemporaryDirectory(prefix='openverse-return-contract-') as tmp:
        bytecode = Path(tmp) / 'return.vbc'
        for profile in ([], ['--extended-defaults']):
            actual = run([OV, 'run', source, *profile, '--emit', bytecode])
            assert actual == expected, (source.name, profile, 'Lean')
            assert run([CV, bytecode]) == expected, (source.name, profile, 'C')
print('large return semantic contracts passed (9 fixtures, both profiles and VMs)')
