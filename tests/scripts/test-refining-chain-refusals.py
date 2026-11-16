#!/usr/bin/env python3
"""Check bounded diagnostics and unchanged execution of refining if chains."""
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
                          text=True, timeout=20, preexec_fn=limits)


def source(count, first, complete, void=False):
    code = ('pair(a:type,b:type):=class{A:a;B:b}\n'
            'dup(t:type):=class(pair(t,t)){C:int=0}\n'
            'F(P:pair(a,b),N:int where a:type,b:type)<transacts>:' +
            ('void' if void else 'int') + '=\n')
    for i in range(count):
        cast = f'D{i}:=dup[P]'
        conditions = f'{cast},N={i}' if first else f'N={i},{cast}'
        value = f'Print("arm {i} {{D{i}.C}}")' if void else f'D{i}.C+{i}'
        code += f'    {"if" if i == 0 else "else if"}({conditions})then {value}\n'
    if complete:
        code += '    else -1\n'
    code += 'Main()<transacts>:void=\n'
    for argument in ['dup(int){A:=1,B:=2,C:=3}', 'pair(int,string){A:=1,B:="x"}']:
        call = f'F({argument},4)'
        code += '    ' + (call if void else f'Print("{{{call}}}")') + '\n'
    return code


with tempfile.TemporaryDirectory(prefix='openverse-refining-chain-') as work:
    work = Path(work)
    for first in [False, True]:
        for count in [15, 32]:
            for complete, void in [(False, False), (True, False), (False, True)]:
                # Rejecting incomplete int chains must retain ordinary
                # incomplete conditionals whose result is discarded.
                if void and count != 15:
                    continue
                length = 6 if void else count
                path = work / f'chain-{first}-{length}-{complete}-{void}.verse'
                path.write_text(source(length, first, complete, void))
                for profile in [[], ['--extended-defaults']]:
                    bytecode = work / 'chain.vbc'
                    bytecode.unlink(missing_ok=True)
                    result = run([OV, 'run', path, *profile, '--emit', bytecode,
                                  '--fuel', '200000'])
                    label = (first, length, complete, void, profile)
                    if not complete and not void:
                        assert result.returncode == 4, (label, result)
                        assert 'expected int, found void' in result.stderr, (label, result)
                        assert not bytecode.exists(), (label, 'refusal emitted bytecode')
                        continue
                    expected = 'arm 4 3\n' if void else '7\n-1\n'
                    assert result.returncode == 0 and result.stdout == expected, (label, result)
                    native = run([CV, bytecode, '--fuel', '200000'])
                    assert native.returncode == 0 and native.stdout == expected, (label, native)
print('refining chains passed (15/32 typed arms, first/later casts, refusals and Lean/C controls)')
