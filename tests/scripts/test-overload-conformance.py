#!/usr/bin/env python3
"""Run the pinned overloading matrix; --include-gaps reports known deviations.

Passing cases use the normal suite's output/status or diagnostic oracle. Known
gaps retain both the upstream expectation and the measured current behavior:
they are reported as GAP, never PASS. A fix is reported as RESOLVED; a different
failure is an audit failure. This runner does not execute an Epic compiler.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / 'tests/conformance/overloading/matrix.json'
OV = ROOT / '.lake/build/bin/openverse'
CV = ROOT / 'runtime/build/cverse'


def run(command):
    return subprocess.run([str(x) for x in command], cwd=ROOT,
                          capture_output=True, text=True, timeout=30)


def matches(result, expected):
    return (result.returncode == expected['exit']
            and result.stdout == expected.get('stdout', '')
            and (expected.get('diagnostic', '') in result.stderr
                 if 'diagnostic' in expected else result.stderr == ''))


def suite_oracle(path):
    if path.parent.name == 'errors':
        want = next(line.removeprefix('# expect: ')
                    for line in path.read_text().splitlines()
                    if line.startswith('# expect: '))
        return {'exit': 4, 'diagnostic': want}
    content = path.with_suffix('.expected').read_text()
    stdout, status = content.rsplit('exit=', 1)
    return {'exit': int(status.strip()), 'stdout': stdout}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--include-gaps', action='store_true',
                        help='also measure deviations without calling them passes')
    parser.add_argument('--report', type=Path, help='write observations as JSON')
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    ids = [case['id'] for case in manifest['cases']]
    if len(ids) != len(set(ids)):
        raise ValueError('matrix case identifiers must be unique')
    observations = []
    counts = {'PASS': 0, 'GAP': 0, 'RESOLVED': 0, 'FAIL': 0}
    with tempfile.TemporaryDirectory(prefix='ov-overloading-') as directory:
        for case in manifest['cases']:
            gap = case['classification'] == 'known-gap'
            if gap and not args.include_gaps:
                continue
            path = ROOT / case['path']
            expected = case['expected'] if gap else suite_oracle(path)
            bytecode = Path(directory) / (case['id'] + '.vbc')
            try:
                result = run([OV, 'run', path, '--emit', bytecode])
                compatible = matches(result, expected)
                # Compilation errors must precede bytecode emission.
                if result.returncode == 4 and bytecode.exists():
                    raise AssertionError('rejected source emitted bytecode')
                # Check an actual output oracle, not merely agreement between VMs.
                if bytecode.exists():
                    c_result = run([CV, bytecode])
                    if (c_result.returncode, c_result.stdout, c_result.stderr) != (
                            result.returncode, result.stdout, result.stderr):
                        raise AssertionError('Lean and C observations differ')
                elif result.returncode != 4:
                    raise AssertionError('execution without emitted bytecode')
                if compatible:
                    status = 'RESOLVED' if gap else 'PASS'
                elif gap and matches(result, case['observed']):
                    status = 'GAP'
                else:
                    status = 'FAIL'
                observation = {'id': case['id'], 'status': status,
                               'exit': result.returncode, 'stdout': result.stdout,
                               'stderr': result.stderr.replace(str(ROOT) + '/', '')}
            except (subprocess.TimeoutExpired, AssertionError) as error:
                status = 'FAIL'
                observation = {'id': case['id'], 'status': status, 'error': str(error)}
            observations.append(observation)
            counts[status] += 1
            suffix = f" #{case['issue']}" if gap else ''
            print(f"{status} {case['id']}{suffix}")
            if status == 'FAIL':
                print(json.dumps(observation, indent=2))
                print('expected:', json.dumps(expected))
    print(f"overloading: {counts['PASS']} passing, {counts['GAP']} known gaps, "
          f"{counts['RESOLVED']} resolved gaps, {counts['FAIL']} failures; "
          'no Epic engine runs')
    if args.report:
        args.report.write_text(json.dumps({'reference': manifest['reference'],
                                          'counts': counts, 'cases': observations},
                                         indent=2) + '\n')
    return int(counts['FAIL'] != 0)


if __name__ == '__main__':
    raise SystemExit(main())
