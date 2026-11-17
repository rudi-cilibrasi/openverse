#!/usr/bin/env python3
"""Preserve lazy loop return operands, shared captures and cleanup boundaries."""
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


with tempfile.TemporaryDirectory(prefix='openverse-loop-operands-') as tmp:
    tmp = Path(tmp)
    sizes = []
    for count in (17, 32, 64):
        # One owned return site, many lazy operands; the enclosing cleanup
        # runs per yielded value, and rejected alternatives leave no output.
        source = ('F(N:int)<transacts>:int=\n'
                  '    defer:Print("out {N}")\n'
                  '    for(I:=1..N):\n'
                  '        if(I=2):return ' + '|'.join(f'N+{i}' for i in range(count)) + '\n'
                  '    N|N+1\nMain()<transacts>:void=\n'
                  '    for(V:=F(3)){Print("v {V}")}\n'
                  '    for(V:=F(1)){Print("short {V}")}\n')
        source += f'    if(V:=F(3),V={3+count-1})then Print("first {{V}}")else Print("bad")\n'
        source += '    if(V:=F(3),V=999)then Print("bad")else Print("none")\n'
        expected = ''.join(f'out 3\nv {3+i}\n' for i in range(count))
        expected += f'out 1\nshort 1\nout 1\nshort 2\nout 3\nfirst {3+count-1}\nnone\n'
        path = tmp / f'{count}.verse'
        path.write_text(source)
        for profile in ([], ['--extended-defaults']):
            bytecode = tmp / 'growth.vbc'
            assert run([OV, 'run', path, *profile, '--emit', bytecode]) == expected
            assert run([CV, bytecode]) == expected
            if not profile:
                sizes.append(bytecode.stat().st_size)
    assert sizes[2] < 3 * sizes[1], sizes
    print(f'loop operand growth passed (17/32/64 alternatives; bytes {sizes})')

# Two fallthrough paths per guard must share the later guards. A continuation
# copied into both paths would grow exponentially despite the tiny runtime.
with tempfile.TemporaryDirectory(prefix='openverse-loop-return-guards-') as tmp:
    tmp = Path(tmp)
    for nested in (False, True):
        sizes = []
        for count in (17, 32, 64):
            source = 'F(N:int)<transacts>:int=\n    defer:Print("out {N}")\n    for(I:=1..2):\n        if(I=2):\n'
            for i in range(count):
                if nested:
                    source += f'            if(N>={i}):\n                if(N={i}):\n                    defer:Print("branch {{N}}")\n                    return N|N+1\n'
                else:
                    source += f'            if(N={i}):\n                defer:Print("branch {{N}}")\n                return N|N+1\n'
            source += '    N+2|N+3\nMain()<transacts>:void=\n'
            inputs = (0, count//2, count-1, count)
            source += '    for(N:array{' + ','.join(map(str, inputs)) + '}){for(V:=F(N)){Print("v {V}")}}\n'
            source += f'    if(V:=F({count//2}),V={count//2+1})then Print("first {{V}}")else Print("bad")\n'
            source += '    if(V:=F(0),V=999)then Print("bad")else Print("none")\n'
            expected = ''
            for n in inputs:
                for value in ((n,n+1) if n<count else (n+2,n+3)):
                    if n<count: expected += f'branch {n}\n'
                    expected += f'out {n}\nv {value}\n'
            expected += f'branch {count//2}\nout {count//2}\nfirst {count//2+1}\nnone\n'
            path = tmp / f'{nested}-{count}.verse'
            path.write_text(source)
            for profile in ([], ['--extended-defaults']):
                bytecode = tmp / 'guards.vbc'
                assert run([OV, 'run', path, *profile, '--emit', bytecode]) == expected
                assert run([CV, bytecode]) == expected
                if not profile: sizes.append(bytecode.stat().st_size)
        # N frame alternatives each carry an N-option continuation tuple:
        # this ABI has quadratic size, while repeated fallthrough expansion
        # would be exponential. Time and memory limits remain fixed above.
        assert sizes[2] < 4*sizes[1], sizes
        print(f'loop return guard growth passed (nested={nested}, 17/32/64 guards; bytes {sizes})')

fixtures = sorted((ROOT / 'tests/verse').glob('multi_return_loop_operand_*.verse'))
for source in fixtures:
    expected = source.with_suffix('.expected').read_text()
    assert expected.endswith('exit=0\n'), source
    expected = expected[:-len('exit=0\n')]
    with tempfile.TemporaryDirectory(prefix='openverse-loop-operand-contract-') as tmp:
        for profile in ([], ['--extended-defaults']):
            bytecode = Path(tmp) / 'initializer.vbc'
            assert run([OV, 'run', source, *profile, '--emit', bytecode]) == expected, (source, profile, 'Lean')
            assert run([CV, bytecode]) == expected, (source, profile, 'C')

print(f'loop operand contracts passed ({len(fixtures)} complete contracts, both profiles and VMs)')

# Original source checking precedes helper extraction and packet rewriting.
refusals = [
    ('decides', 'F(N:int)<decides>:int=\n    for(I:=1..N):\n        if(I=2):return I|I+1\n    N|N+1\nMain():void={}\n', 'return in a <decides> function must be in tail position'),
    ('failure', 'F(N:int):int=\n    for(I:=1..N):\n        if(I=2):\n            Z:=option{return I|I+1}\n            0\n    N|N+1\nMain():void={}\n', 'return cannot leave a failure context'),
    ('scope', 'F(N:int):int=\n    for(I:=1..N):\n        if(I=2):return Hidden|I\n    Hidden:=1\n    N|N+1\nMain():void={}\n', "unknown identifier 'Hidden'"),
]
for name, message in [('heap-write', 'sets a var field'), ('heap-read', 'reads a var field'),
                      ('heap-allocate', 'constructs an object that has a var field'),
                      ('lookalike', 'sets a var field')]:
    for suffix in ('', '-control'):
        path = ROOT/'tests/fixtures/loop-return-operands'/f'computes-{name}{suffix}.verse'
        refusals.append((name+suffix, path.read_text(), message))
with tempfile.TemporaryDirectory(prefix='openverse-loop-refusals-') as tmp:
    for name, text, message in refusals:
        path = Path(tmp) / (name+'.verse')
        path.write_text(text)
        for profile in ([], ['--extended-defaults']):
            bytecode = Path(tmp) / (name+'.vbc')
            result = subprocess.run([str(OV), 'run', str(path), *profile, '--emit', str(bytecode)],
                                    capture_output=True, text=True, timeout=15, preexec_fn=limits)
            assert result.returncode == 4 and message in result.stderr and not bytecode.exists(), (name, profile, result)
    source = ROOT/'tests/fixtures/loop-return-operands/loop-signal-policy.verse'
    for profile in ([], ['--extended-defaults']):
        bytecode = Path(tmp)/'signal.vbc'
        assert run([OV, 'run', source, *profile, '--emit', bytecode]) == 'value 2\nvalue 3\nafter\n'
        assert run([CV, bytecode]) == 'value 2\nvalue 3\nafter\n'
        bytecode.unlink()
        result = subprocess.run([str(OV), 'run', str(source), *profile, '--signal-no-rollback', '--emit', str(bytecode)],
                                capture_output=True, text=True, timeout=15, preexec_fn=limits)
        assert result.returncode == 4 and 'event.Signal' in result.stderr and 'failure context' in result.stderr and not bytecode.exists(), result
print('loop operand source checking and Signal policy passed before bytecode emission')
