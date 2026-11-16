#!/usr/bin/env python3
"""Bound role classification while preserving enclosing cleanup semantics (#678)."""
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
    result = subprocess.run([str(a) for a in args], text=True, capture_output=True,
                            timeout=15, preexec_fn=limits)
    assert result.returncode == 0 and not result.stderr, (args, result)
    return result.stdout


def registration(index, mutate):
    if mutate:
        return ('    defer:\n        set Saved+=1\n'
                f'        Print("scope {index} {{Saved}}")\n')
    return f'    defer:Print("scope {index}")\n'


def oracle(count, inputs, mutate):
    output = ''
    for selected in inputs:
        reached = min(selected + 1, count)
        saved = 10 + selected if selected < count else 10
        # Each alternative's operand is saved before cleanup; the second
        # operand sees mutations made by the first alternative's cleanup.
        for alternative in range(2):
            returned = saved + alternative
            for index in reversed(range(reached)):
                if mutate:
                    saved += 1
                output += f'scope {index}' + (f' {saved}' if mutate else '') + '\n'
            output += f'v {returned}\n'
    return output


with tempfile.TemporaryDirectory(prefix='openverse-enclosing-cleanup-') as tmp:
    tmp = Path(tmp)
    for mutate in (False, True):
        sizes = []
        for count in (17, 32, 64):
            inputs = (0, count // 2, count - 1, count)
            source = 'F(N:int)<transacts>:int=\n    var Saved:int=10\n'
            for index in range(count):
                source += registration(index, mutate)
                source += (f'    if(N={index}):\n        set Saved+={index}\n'
                           '        return Saved|Saved+1\n')
            source += '    Saved|Saved+1\n'
            source += ('Main()<transacts>:void=for(N:array{' + ','.join(map(str, inputs)) +
                       '}){for(V:=F(N)){Print("v {V}")}}\n')
            # Independent straight-line controls write only the reached
            # registrations, with no returning conditional prefix.
            control = ''
            for selected in inputs:
                control += f'C{selected}()<transacts>:int=\n    var Saved:int=10\n'
                for index in range(min(selected + 1, count)):
                    control += registration(index, mutate)
                if selected < count:
                    control += f'    set Saved+={selected}\n'
                control += '    Saved|Saved+1\n'
            control += 'Main()<transacts>:void=\n'
            for selected in inputs:
                control += f'    for(V:=C{selected}()){{Print("v {{V}}")}}\n'
            expected = oracle(count, inputs, mutate)
            print(f'checking count={count} mutating={mutate}', flush=True)
            path = tmp / f'prefix-{count}-{mutate}.verse'
            short = tmp / 'control.verse'
            path.write_text(source)
            short.write_text(control)
            for profile in ([], ['--extended-defaults']):
                for program in (path, short):
                    bytecode = tmp / 'program.vbc'
                    run([OV, 'emit', program, *profile, '-o', bytecode])
                    assert run([OV, 'run', program, *profile]) == expected, (count, mutate, profile, program, 'Lean')
                    assert run([CV, bytecode]) == expected, (count, mutate, profile, program, 'C')
                    if program == path and not profile:
                        sizes.append(bytecode.stat().st_size)
            # Cleanup code can grow quadratically with the reached prefix;
            # doubling guard count must not produce explosive growth.
        assert sizes[2] < 5 * sizes[1], sizes
        print(f'enclosing cleanup growth passed (mutating={mutate}; 17/32/64 guards; bytes {sizes})')
print('enclosing cleanup contracts passed (first/middle/last/fallthrough, independent controls, both profiles/VMs)')

# First-success search rolls back a rejected candidate's cleanup/output and
# restores the mutable return operand before trying its next alternative.
prefix = 'F(N:int)<transacts>:int=\n    var Saved:int=10\n'
for index in range(17):
    prefix += registration(index, True)
    prefix += (f'    if(N={index}):\n        set Saved+={index}\n'
               '        return Saved|Saved+1\n')
prefix += '    Saved|Saved+1\n'
control = 'F(N:int)<transacts>:int=\n    var Saved:int=10\n'
for index in range(9):
    control += registration(index, True)
control += '    set Saved+=8\n    Saved|Saved+1\n'
with tempfile.TemporaryDirectory(prefix='openverse-enclosing-rollback-') as tmp:
    tmp = Path(tmp)
    for target in (19, 100):
        main = (f'Main()<transacts>:void=\n    var Count:int=0\n'
                f'    if(V:=F(8),set Count+=1,V={target}):\n'
                '        Print("found {V} {Count}")\n'
                '    else:\n        Print("none {Count}")\n'
                '    Print("after {Count}")\n')
        expected = 'none 0\nafter 0\n'
        if target == 19:
            expected = ''.join(f'scope {index} {27-index}\n' for index in reversed(range(9)))
            expected += 'found 19 1\nafter 1\n'
        for name, body in (('prefix', prefix), ('control', control)):
            source = tmp / f'{name}-{target}.verse'
            source.write_text(body + main)
            bytecode = source.with_suffix('.vbc')
            for profile in ([], ['--extended-defaults']):
                assert run([OV, 'run', source, *profile, '--emit', bytecode]) == expected, (target, name, profile, 'Lean')
                assert run([CV, bytecode]) == expected, (target, name, profile, 'C')
print('enclosing cleanup rollback passed (17 guards, rejected-first/all-rejected searches, both profiles/VMs)')
