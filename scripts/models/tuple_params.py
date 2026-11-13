#!/usr/bin/env python3
"""Destructured tuple parameters.

usage: tuple_params.py SEED EXPECTED

Prints a random program and writes what docs/research/tuple-parameters.md
predicts to EXPECTED: `exit=N`, then the output, or `exit=4` and a part of the
refusal message. The model is written from that note, not from the compiler:

- a parenthesized group of parameters is one parameter of its tuple type;
  groups nest, and the body sees each name bound to its element;
- it is given as a tuple literal, a tuple variable, or within the whole
  argument list as one tuple;
- arguments run in the order written, a later default after them, and a
  later default may use a destructured name;
- the function is a value of the type with a tuple parameter there, and a
  method destructures as a function does;
- a group and a tuple parameter of the same types are indistinct overloads.

Modes, by seed: 0 direct calls, 1 a function value, 2 a method, 3 the whole
argument list as one tuple, 4 a refusal.
"""
import random
import sys

rng = random.Random(int(sys.argv[1]))
out_path = sys.argv[2]
mode = int(sys.argv[1]) % 5
counter = [0]


def fresh():
    counter[0] += 1
    return f'N{counter[0]}'


def make_item(depth):
    """A parameter: ('leaf', name) or ('group', [items])."""
    if depth < 2 and rng.random() < 0.45:
        return ('group', [make_item(depth + 1) for _ in range(rng.randrange(2, 4))])
    return ('leaf', fresh())


items = [make_item(0) for _ in range(rng.randrange(1, 4))]
if not any(k == 'group' for k, _ in items):
    items[rng.randrange(len(items))] = ('group', [make_item(1), make_item(1)])


def param_text(item):
    kind, x = item
    if kind == 'leaf':
        return f'{x}:int'
    return '(' + ', '.join(param_text(i) for i in x) + ')'


def type_text(item):
    kind, x = item
    if kind == 'leaf':
        return 'int'
    return 'tuple(' + ', '.join(type_text(i) for i in x) + ')'


def leaves(item):
    kind, x = item
    return [x] if kind == 'leaf' else [n for i in x for n in leaves(i)]


names = [n for i in items for n in leaves(i)]
with_default = rng.random() < 0.5
dsrc = rng.sample(names, min(2, len(names)))
k = rng.randrange(1, 9)
default_text = f'{dsrc[0]} * 10 + {dsrc[-1]} + {k}'
params = ', '.join(param_text(i) for i in items) + (f', ?D:int = {default_text}' if with_default else '')
body = '"' + ' '.join(f'{{{n}}}' for n in names) + (' D={D}' if with_default else '') + '"'
prog = ['''log := class:
    var N:int = 0
    Next(What:string, V:int)<transacts>:int =
        set N += 1
        Print(What)
        V''']
lines = []
main = ['Main():void =', '    L := log{}']
value_iter = iter(range(3, 10_000, 7))


def arg_for(item, env, log, prefix, as_var):
    """The argument text for `item` (`as_var`: groups bound to variables
    first, in `main`), filling `env` with leaf values and `log` with the
    order their logging calls run."""
    kind, x = item
    if kind == 'leaf':
        v = next(value_iter) % 10
        env[x] = v
        log.append(f'{prefix}{x}')
        return f'L.Next("{prefix}{x}", {v})'
    inner = [arg_for(i, env, log, prefix, False) for i in x]
    text = '(' + ', '.join(inner) + ')'
    if as_var:
        var = f'V{len(main)}'
        main.append(f'    {var} := {text}')
        return var
    return text


def call(callee, whole=False):
    env = {}
    pre_log = []      # logged while binding variables, before the call
    log = []
    args = []
    if whole:
        whole_text = '(' + ', '.join(arg_for(i, env, pre_log, 'a', False) for i in items) + ')'
        var = f'W{len(main)}'
        main.append(f'    {var} := {whole_text}')
        args = [var]
    else:
        for i in items:
            as_var = i[0] == 'group' and rng.random() < 0.4
            target = pre_log if as_var else log
            args.append(arg_for(i, env, target, 'a', as_var))
    given_d = with_default and not whole and rng.random() < 0.4
    if given_d:
        d = next(value_iter) % 10
        args.append(f'?D := L.Next("aD", {d})')
        log.append('aD')
        env['D'] = d
    elif with_default:
        env['D'] = env[dsrc[0]] * 10 + env[dsrc[-1]] + k
    lines.extend(pre_log)
    main.append(f'    Print({callee}({", ".join(args)}))')
    lines.extend(log)
    lines.append(' '.join(str(env[n]) for n in names) + (f' D={env["D"]}' if with_default else ''))


if mode == 4:
    group = next(i for i in items if i[0] == 'group')
    others = [param_text(i) if i is not group else f'P:{type_text(i)}' for i in items]
    prog.append(f'F({params}):string = {body}')
    prog.append(f'F({", ".join(others)}):string = "tuple"')
    main.append('    Print("bad")')
    print('\n'.join(prog + main))
    with open(out_path, 'w') as f:
        f.write('exit=4\nF is defined twice with parameters a call cannot tell apart\n')
    sys.exit(0)

if mode == 2:
    prog.append(f'''holder := class:
    M({params}):string = {body}''')
    main.append('    H := holder{}')
    for _ in range(rng.randrange(1, 3)):
        call('H.M')
else:
    prog.append(f'F({params}):string = {body}')
    if mode == 1:
        ty = 'type{_(' + ', '.join(':' + type_text(i) for i in items) + \
            (', ?D:int = 0' if with_default else '') + '):string}'
        main.append(f'    G:{ty} = F')
        for _ in range(rng.randrange(1, 3)):
            call('G')
    else:
        for _ in range(rng.randrange(1, 3)):
            call('F', whole=(mode == 3))
main.append('    Print("count {L.N}")')
lines.append(f'count {sum(1 for x in lines if x.startswith("a"))}')
print('\n'.join(prog + main))
with open(out_path, 'w') as f:
    f.write('exit=0\n' + ''.join(line + '\n' for line in lines))
