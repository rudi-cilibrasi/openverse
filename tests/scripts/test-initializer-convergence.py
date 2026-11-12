#!/usr/bin/env python3
"""Initializer admission plus independent extended-default/control oracles."""
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OV = ROOT / '.lake/build/bin/openverse'
CV = ROOT / 'runtime/build/cverse'
COUNT = int(sys.argv[1]) if len(sys.argv) > 1 else 96
FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 1
checks = 0


def invoke(args):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True,
                          text=True, timeout=30)


def require(ok, label, detail=''):
    global checks
    if not ok:
        raise SystemExit(f'initializer-convergence: {label}: {detail}')
    checks += 1


def model(seed, control):
    rng = random.Random(seed)
    shape = seed % 3
    n, tag, first = rng.randint(-3, 3), rng.randint(1, 30), rng.randint(1, 20)
    source = ('Log(N:int)<transacts>:int={Print("arg {N}");N}\n'
              'Make(X:t,N:int where t:type)<transacts>:t={Print("default {N}");X}\n'
              'Get(N:int)<transacts><decides>:int={Print("try {N}");N>=0;N+3}\n')
    kind = ['struct', 'class', 'interface'][shape]
    name = 'data' if shape == 0 else 'base'
    source += f'{name}(t:type):={kind}:\n    Before:int\n    Empty:[]t'
    source += ('\n    Value:int\n' if control else
               f'=Make(array{{}},{tag})\n    Value:int=Get[{n}]\n')
    if shape == 0:
        ty, element = 'data(int)', '4'
    elif shape == 1:
        source += 'data(u:type):=class(base(tuple(int,u))){}\n'
        ty, element = 'data(string)', '(4,"s")'
    else:
        source += 'data(u:type):=class(base(?u)){}\n'
        ty, element = 'data(int)', 'option{4}'
    source += 'Main()<transacts>:void=\n'
    want = []
    for i in range(3):
        provided = {'Before': f'Log({first+i})'}
        if control or i == 2:
            provided['Empty'] = f'array{{{element}}}' if i == 2 else f'Make(array{{}},{tag})'
        if control or i != 0:
            provided['Value'] = f'Log({first+10})' if i == 1 else f'Get[{n+(i==2)}]'
        items = list(provided.items())
        rng.shuffle(items)
        fields = ','.join(f'{key}:={value}' for key, value in items)
        source += (f'    if(0<=0,C{i}:={ty}{{{fields}}})then '
                   f'Print("value {{C{i}.Before}} {{C{i}.Empty.Length}} {{C{i}.Value}}") '
                   f'else Print("empty {i}")\n')
        value = first + 10 if i == 1 else n + (i == 2) + 3
        succeeds = i == 1 or n + (i == 2) >= 0
        if succeeds:
            want.append(f'arg {first+i}')
            if i != 2:
                want.append(f'default {tag}')
            want.append(f'arg {first+10}' if i == 1 else f'try {n+(i==2)}')
            want.append(f'value {first+i} {int(i==2)} {value}')
        else:
            # The complete failed construction, including earlier argument
            # and default output, belongs to the surrounding transaction.
            want.append(f'empty {i}')
    return source, ''.join(x+'\n' for x in want)


with tempfile.TemporaryDirectory(prefix='openverse-initializer-') as directory:
    tmp = Path(directory)
    source, bytecode = tmp / 'Case.verse', tmp / 'Case.vbc'

    def runtime(text, flags, want, label):
        source.write_text(text)
        bytecode.write_bytes(b'previous artifact')
        lean = invoke([OV, 'run', source, *flags, '--emit', bytecode])
        require((lean.returncode, lean.stdout, lean.stderr) == (0, want, ''),
                label, f'{lean.returncode,lean.stdout,lean.stderr}\n{text}')
        c = invoke([CV, bytecode])
        require((c.returncode, c.stdout, c.stderr) == (0, want, ''),
                label+' C', (c.returncode, c.stdout, c.stderr))
        return bytecode.read_bytes()

    legacy = {'unused_helper': '', 'generic_helper': '0\n', 'method': '42\n',
              'indirect': '42\n', 'constant_call': '42\n', 'infinite': '',
              'hidden_first': ''}
    for fixture in sorted((ROOT / 'tests/errors').glob('initializer_convergence_*.verse')):
        text = fixture.read_text()
        needle = text.splitlines()[0].removeprefix('# expect: ')
        stem = fixture.stem.removeprefix('initializer_convergence_')
        for profile in [[], ['--no-choice']]:
            if stem == 'hidden_first' and profile:
                continue
            source.write_text(text)
            for command in [['check', source, *profile], ['core', source, *profile],
                            ['emit', source, *profile, '-o', bytecode],
                            ['run', source, *profile, '--emit', bytecode]]:
                bytecode.write_bytes(b'previous artifact')
                result = invoke([OV, *command])
                require(result.returncode == 4 and not result.stdout and needle in result.stderr,
                        fixture.stem, (result.returncode, result.stdout, result.stderr))
                require(bytecode.read_bytes() == b'previous artifact', fixture.stem+' artifact')
            runtime(text, ['--extended-defaults', *profile], legacy[stem], fixture.stem+' extension')

    for fixture in sorted((ROOT / 'tests/verse').glob('initializer_convergence_*.verse')):
        text = fixture.read_text()
        want, status = fixture.with_suffix('.expected').read_text().rsplit('exit=', 1)
        require(status.strip() == '0', fixture.stem+' oracle')
        for profile in [[], ['--no-choice']]:
            if profile and fixture.stem.endswith(('choice_literal', 'choice_function')):
                continue
            strict = runtime(text, profile, want, fixture.stem)
            extended = runtime(text, ['--extended-defaults', *profile], want, fixture.stem+' extension')
            require(strict == extended, fixture.stem+' mode bytecode')

    # An unused imported default has the same admission boundary and retains
    # the dependency's source position in its diagnostic.
    dependency = tmp / 'Dependency.verse'
    dependency.write_text('Helper()<computes>:int=42\nc:=class{N:int=Helper()}\n')
    source.write_text('using{"Dependency.verse"}\nMain():void={}\n')
    result = invoke([OV, 'check', source])
    require(result.returncode == 4 and 'requires convergence' in result.stderr and
            'Dependency.verse' in result.stderr, 'unused import', result.stderr)

    for seed in range(FIRST, FIRST+COUNT):
        text, want = model(seed, False)
        control, control_want = model(seed, True)
        require(want == control_want, f'model {seed} oracle identity')
        for profile in [[], ['--no-choice']]:
            source.write_text(text)
            result = invoke([OV, 'check', source, *profile])
            require(result.returncode == 4 and not result.stdout and
                    'requires convergence' in result.stderr, f'model {seed} boundary', result.stderr)
            runtime(text, ['--extended-defaults', *profile], want, f'model {seed} extension')
            runtime(control, profile, want, f'model {seed} explicit control')

print(f'initializer-convergence: {checks} checks; {COUNT} independent model/control pairs '
      f'from seed {FIRST}, both profiles and VMs; imports/artifact preservation/CLI boundary')
