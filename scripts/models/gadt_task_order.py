#!/usr/bin/env python3
"""Interleaved source-task roots keep chronological, hierarchical cleanup.

--control replaces refining casts with Boolean guards for the preceding compiler.
The oracle sorts source roots by start time, then drains each owned subtree.
Every 64 consecutive seeds cover both cast outcomes, opened types, nested
helpers, owned children, both sibling orders and explicit/implicit source exit.
"""
from pathlib import Path
import random
import sys

seed = int(sys.argv[1])
rng = random.Random(seed)
control = '--control' in sys.argv[3:]
hit = bool(seed % 2)
owned = bool((seed // 2) % 2)
nested = bool((seed // 4) % 2)
text = bool((seed // 8) % 2)
reverse = bool((seed // 16) % 2)
explicit = bool((seed // 32) % 2)
n = rng.randint(3, 20)
value = n if hit else 0
roots = [('A', 0.0), ('B', 0.1 if reverse else 0.2), ('C', 0.2 if reverse else 0.1)]
lines = ['joined', 'source']
for name, _ in sorted(roots, key=lambda root: root[1], reverse=True):
    if name == 'A' and owned:
        lines.append(f'AA {value}')
    lines.append('C' if name == 'C' else f'{name} {value}')
Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')

print('''root(t:type):=class{}
extra(t:type,u:type):=class(root(t)){C:int}
Use(P:root(t),Q:root(s),Hit:logic,N:int where t:type,s:type)<suspends>:void=
    defer:Print("source")
    sync:
        block:''')
guard = 'Hit?' if control else 'D:=extra[P]'
for condition, number in [(guard, 'N' if control else 'D.C'), (None, '0')]:
    print('            ' + (f'if({condition}):' if condition else 'else:'))
    indent = '                '
    if nested:
        print(indent + ('if(1=1):' if control else 'if(E:=extra[Q]):'))
        indent += '    '
    print(indent + 'branch:')
    print(indent + f'    defer:Print("A {{{number}}}")')
    if owned:
        # Start AA after both sibling roots: its owner A still drains last.
        print(indent + '    Sleep(0.25)')
        print(indent + '    branch:')
        print(indent + f'        defer:Print("AA {{{number}}}")')
        print(indent + '        Sleep(10.0)')
    print(indent + '    Sleep(10.0)')
    print(indent + f'Sleep({0.1 if reverse else 0.2})')
    print(indent + 'branch:')
    print(indent + f'    defer:Print("B {{{number}}}")')
    print(indent + '    Sleep(10.0)')
print(f'''        block:
            Sleep({0.2 if reverse else 0.1})
            branch:
                defer:Print("C")
                Sleep(10.0)
            Sleep(0.2)
    Print("joined")''')
if explicit:
    print('    return')
t, u = ('string', 'int') if text else ('int', 'string')
source = f'extra({t},{u}){{C:={n}}}' if hit else f'root({t}){{}}'
print(f'''Main()<suspends>:void=
    P:root({t})={source}
    Q:root({u})=extra({u},{t}){{C:={n+2}}}
    Use(P,Q,{"true" if hit else "false"},{n})''')
