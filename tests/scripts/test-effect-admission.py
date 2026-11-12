#!/usr/bin/env python3
"""Check effect refusals before execution/emission against executable controls.

Stripping annotation tags produces source controls with independent stdout
oracles. Imports retain the bad declaration even when unused. Both runtimes
run the admitted controls; rejected input must leave existing output intact.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
override = os.environ.get('OV_EFFECT_COMMAND')
OV = shlex.split(override) if override else [str(ROOT / '.lake/build/bin/openverse')]
CV = ROOT / 'runtime/build/cverse'
SPECS = ('computes reads writes allocates transacts decides suspends converges predicts '
         'no_rollback dictates diverges succeeds fails varies native native_callable fictional_effect').split()
TAGS = re.compile(r'<(?:' + '|'.join(SPECS) + r')>')
CONTROL_OUTPUT = {'predicts_type': '1\n', 'continuation_type': '1 1\n2 1\n'}
checks = 0


def run(args):
    return subprocess.run([str(x) for x in args], cwd=ROOT,
                          capture_output=True, text=True, timeout=30)


def require(ok, message):
    global checks
    if not ok:
        raise SystemExit(message)
    checks += 1


with tempfile.TemporaryDirectory(prefix='openverse-effect-admission-') as directory:
    tmp = Path(directory)
    output = tmp / 'program.vbc'

    def reject(source, needle, command, sentinel=False, extra=()):
        output.unlink(missing_ok=True)
        if sentinel:
            output.write_bytes(b'existing output must survive a refusal')
        args = OV + [command, source]
        if command == 'emit':
            args += ['-o', output]
        elif command == 'run':
            args += ['--emit', output]
        result = run(args + list(extra))
        require(result.returncode == 4 and not result.stdout and needle in result.stderr,
                f'wrong refusal: {args}; {result.returncode,result.stdout,result.stderr}')
        require(output.read_bytes() == b'existing output must survive a refusal' if sentinel
                else not output.exists(), f'refused source changed bytecode output: {source}')
        return result

    def accepted(source, stdout):
        output.unlink(missing_ok=True)
        result = run(OV + ['run', source, '--emit', output])
        require((result.returncode, result.stdout, result.stderr) == (0, stdout, ''),
                f'control failed: {source}; {result.returncode,result.stdout,result.stderr}; expected {stdout!r}')
        require(output.exists(), f'control emitted no bytecode: {source}')
        c = run([CV, output])
        require((c.returncode, c.stdout, c.stderr) == (0, stdout, ''),
                f'C control mismatch: {source}; {c.returncode,c.stdout,c.stderr}')

    fixtures = sorted((ROOT / 'tests/errors').glob('effect_admission_*.verse'))
    require(bool(fixtures), 'no effect admission fixtures')
    for fixture in fixtures:
        source = fixture.read_text()
        needle = source.splitlines()[0].removeprefix('# expect: ')
        for command in ['check', 'core', 'emit', 'run']:
            reject(fixture, needle, command, sentinel=command == 'emit')
        reject(fixture, needle, 'check', extra=['--no-choice'])
        # These annotations are semantically refused, rather than rejected
        # because the surrounding program was already malformed.
        control = tmp / 'control.verse'
        control.write_text(TAGS.sub('', source))
        name = fixture.stem.removeprefix('effect_admission_')
        accepted(control, CONTROL_OUTPUT.get(name, ''))
        # Every loaded source definition is checked, not only the entry path.
        dependency = tmp / 'Dependency.verse'
        root = tmp / 'Root.verse'
        dependency.write_text(source.replace('Main()', 'Imported()'))
        root.write_text('using{"Dependency.verse"}\nMain():void={}\n')
        result = reject(root, needle, 'check')
        require('Dependency.verse' in result.stderr, f'import location missing: {result.stderr}')
        dependency.write_text(TAGS.sub('', dependency.read_text()))
        accepted(root, '')

    plain = tmp / 'Plain.verse'
    plain.write_text('Good()<computes>:int=1\nMain():void=Print("entry ran")\n')
    expression = 'F:type{_()<predicts>:int}=Good'
    for command in ['run', 'emit']:
        reject(plain, '<predicts>', command, sentinel=True, extra=['do', expression])

    # Preserve real heap/callback enforcement after the admission pass.
    contexts = (ROOT / 'tests/verse/effect_admission_contexts.verse').read_text()
    missing = tmp / 'MissingPermission.verse'
    missing.write_text(contexts.replace('<reads><writes>', '<reads>', 1))
    reject(missing, '<writes>', 'check')
    missing.write_text(contexts.replace('F:type{_(:int)<reads><writes>:int} = B.Bump',
                                        'F:type{_(:int)<reads>:int} = B.Bump'))
    reject(missing, 'writes', 'check')
    for fixture in sorted((ROOT / 'tests/verse').glob('effect_admission_*.verse')):
        expected = fixture.with_suffix('.expected').read_text()
        stdout, code = expected.rsplit('exit=', 1)
        require(int(code.strip()) == 0, f'control oracle must succeed: {fixture}')
        accepted(fixture, stdout)

print(f'effect-admission: {checks} checks, {len(fixtures)} refusals with executable Lean/C controls, '
      'CLI/output/import/API-entry boundaries preserved')
