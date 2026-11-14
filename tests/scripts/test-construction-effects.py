#!/usr/bin/env python3
"""Check construction budgets against an independent heap-set oracle.

Empty data types isolate the declared contract from actual body operations.
Unused inheritance/default definitions must be checked too. Accepted programs
run in both VMs, and rejected CLI commands must preserve existing output.
"""
import itertools
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
override = os.environ.get('OV_CONSTRUCTION_COMMAND')
OV = shlex.split(override) if override else [str(ROOT / '.lake/build/bin/openverse')]
CV = ROOT / 'runtime/build/cverse'
HEAP = ('reads', 'writes', 'allocates')
BUDGETS = [frozenset(k for i, k in enumerate(HEAP) if mask & (1 << i))
           for mask in range(8)]
checks = 0
cases = 0


def tags(effects):
    return ''.join(f'<{k}>' for k in HEAP if k in effects) if effects else '<computes>'


def run(args):
    return subprocess.run([str(x) for x in args], cwd=ROOT, capture_output=True,
                          text=True, timeout=30)


def require(condition, message):
    global checks
    if not condition:
        raise SystemExit(message)
    checks += 1


with tempfile.TemporaryDirectory(prefix='openverse-construction-effects-') as directory:
    tmp = Path(directory)
    source = tmp / 'Case.verse'
    output = tmp / 'Case.vbc'

    def case(label, text, admitted, needle='', stdout='ok\n', profile=False, extended=False):
        global cases
        cases += 1
        source.write_text(text)
        output.write_bytes(b'existing bytecode')
        extra = ['--no-choice'] if profile else []
        if extended:
            extra.append('--extended-defaults')
        result = run(OV + ['run', source, '--emit', output] + extra)
        if admitted:
            require((result.returncode, result.stdout, result.stderr) == (0, stdout, ''),
                    f'{label}: expected admission; {result.returncode,result.stdout,result.stderr}\n{text}')
            require(output.read_bytes() != b'existing bytecode', f'{label}: no bytecode')
            c = run([CV, output])
            require((c.returncode, c.stdout, c.stderr) == (0, stdout, ''),
                    f'{label}: wrong C trace: {c.returncode,c.stdout,c.stderr}')
        else:
            require(result.returncode == 4 and not result.stdout and needle in result.stderr,
                    f'{label}: expected refusal containing {needle!r}; '
                    f'{result.returncode,result.stdout,result.stderr}\n{text}')
            require(output.read_bytes() == b'existing bytecode', f'{label}: output changed')
        return result

    main = 'Main():void=Print("ok")\n'
    # For every heap subset, a caller pays the declared budget even if the
    # class/struct is empty. An empty interface constrains its implementors.
    for kind, required, caller in itertools.product(('class', 'struct'), BUDGETS, BUDGETS):
        text = (f'data:={kind}{tags(required)}{{}}\n'
                f'Use(){tags(caller)}:int={{Value:=data{{}};1}}\n' + main)
        case(f'{kind} call {required}/{caller}', text, required <= caller,
             'declared construction budget', profile=True)

    for parent_kind, child_kind in [('class', 'class'), ('interface', 'class'),
                                    ('interface', 'interface')]:
        for parent, child in itertools.product(BUDGETS, repeat=2):
            text = (f'parent:={parent_kind}{tags(parent)}{{}}\n'
                    f'child:={child_kind}{tags(child)}(parent){{}}\n' + main)
            case(f'{parent_kind}/{child_kind} {parent}/{child}', text,
                 parent <= child, 'declared by parent parent')

    # Defaults are definitions, not a promise checked only if omitted by a
    # constructor call. Function calls pay their declared heap family too.
    for kind, required, budget in itertools.product(('class', 'interface', 'struct'),
                                                   BUDGETS, BUDGETS):
        text = (f'Default(){tags(required)}:int=7\n'
                f'data:={kind}{tags(budget)}{{Value:int=Default()}}\n' + main)
        case(f'{kind} default {required}/{budget}', text, required <= budget,
             "default of field 'Value' of data", extended=True)

    for spelling in ['', '<public>', '<transacts>', '<reads><writes><allocates>']:
        for kind in ['class', 'struct']:
            text = (f'data:={kind}{spelling}{{}}\n'
                    'Use()<computes>:int={Value:=data{};1}\n' + main)
            case(f'default budget {kind}{spelling}', text, False,
                 'declared construction budget')

    for kind, effect in itertools.product(('class', 'interface', 'struct'),
                                          ('decides', 'suspends')):
        case(f'invalid {kind}/{effect}', f'data:={kind}<{effect}>{{}}\n' + main,
             False, f'<{effect}> is not allowed')

    for kind in ('class', 'interface', 'struct'):
        for spelling, needle in [('<computes><computes>', 'duplicate effect specifier'),
                                 ('<computes><transacts>', 'they exclude each other')]:
            case(f'{kind} conflicting budget {spelling}', f'data:={kind}{spelling}{{}}\n' + main,
                 False, needle)

    # <computes> is exclusive and <reads>, <writes>, <allocates> additive
    # (Book of Verse ch. 13): <computes> with some of them is the budget of
    # those, as without it
    for kind, required, caller in itertools.product(('class', 'struct'), BUDGETS[1:], BUDGETS):
        text = (f'data:={kind}<computes>{tags(required)}{{}}\n'
                f'Use(){tags(caller)}:int={{Value:=data{{}};1}}\n' + main)
        case(f'{kind} call <computes>{tags(required)}/{caller}', text, required <= caller,
             'declared construction budget', profile=True)

    case('diamond union refused', 'left:=interface<reads>{}\nright:=interface<writes>{}\n'
         'child:=class<reads>(left,right){}\n' + main,
         False, 'declared by parent right')
    case('diamond union admitted', 'root:=interface<computes>{}\n'
         'left:=interface<reads>(root){}\nright:=interface<writes>(root){}\n'
         'child:=class<reads><writes>(left,right){}\n' + main, True)

    for shape in ('<unique>', '{var N:int=0}'):
        for budget in BUDGETS:
            declaration = (f'data:=class{tags(budget)}{shape}{{}}' if shape == '<unique>'
                           else f'data:=class{tags(budget)}{shape}')
            case(f'allocation {shape}/{budget}', declaration + '\n' + main,
                 'allocates' in budget, 'construction of data')

    for fixture in sorted((ROOT / 'tests/errors').glob('construction_effects_*.verse')):
        text = fixture.read_text()
        needle = text.splitlines()[0].removeprefix('# expect: ')
        case(fixture.stem, text, False, needle)
        # Source budgets are independent of reachability, including imports.
        dependency = tmp / 'Dependency.verse'
        dependency.write_text(text.replace('Main()', 'Imported()'))
        result = case(fixture.stem + ' imported', 'using{"Dependency.verse"}\n' + main,
                      False, needle)
        require('Dependency.verse' in result.stderr, f'{fixture}: lost imported location')

        # Erasing heap annotations widens both data and function contracts.
        # These controls establish that the enclosing source remains valid.
        for tag in ('computes', 'reads', 'writes', 'allocates', 'transacts'):
            text = text.replace(f'<{tag}>', '')
        case(fixture.stem + ' widened control', text, True, stdout='', extended=True)

    for fixture in sorted((ROOT / 'tests/verse').glob('construction_effects_*.verse')):
        expected = fixture.with_suffix('.expected').read_text()
        stdout, exit_code = expected.rsplit('exit=', 1)
        require(int(exit_code.strip()) == 0, f'{fixture}: nonzero oracle')
        args = fixture.with_suffix('.args')
        extended = args.exists() and '--extended-defaults' in args.read_text().splitlines()
        case(fixture.stem, fixture.read_text(), True, stdout=stdout, extended=extended)

print(f'construction-effects: {checks} checks across {cases} cases, '
      'declared calls/defaults/inheritance and Lean/C traces agree')
