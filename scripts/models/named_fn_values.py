#!/usr/bin/env python3
"""Function values of functions with named parameters (#503).

usage: named_fn_values.py SEED EXPECTED

Prints a random program and writes what the documented rules predict to
EXPECTED: `exit=N`, then the output, or `exit=4` and a part of the refusal
message. The model is written from docs/research/named-function-values.md
and docs/LANGUAGE.md, not from the compiler:

- a function, or a method bound to its receiver, is a value of a function
  type with its positional parameters whose names are among its own, that
  leaves out only named parameters with defaults and lets callers omit only
  those; names match by name, in any order;
- a call through a value gives the positional arguments, then named ones in
  any order: every name its type requires, only names it has;
- the explicit arguments run in the order written, then each omitted default
  once, at the call, in declaration order and the function's scope: earlier
  parameters, a module constant, the receiver's current fields, and the
  override of the receiver's dynamic class;
- the receiver runs once, when the value is made;
- a failed <decides> call leaves no output and no change.

Modes, by seed: 0 a function at a type, 1 through a function taking it and
one returning it, 2 the function's own type (unannotated), 3 a bound method
(live field, maybe an override), 4 <decides> calls that may fail, 5 a
refusal (a type or a call the rules exclude).
"""
import random
import sys

rng = random.Random(int(sys.argv[1]))
out_path = sys.argv[2]
mode = int(sys.argv[1]) % 6
lines = []          # predicted output
POOL = ['A', 'B', 'C', 'D', 'E']
base = rng.randrange(1, 9)
method = mode == 3
decides = mode == 4
npos = rng.randrange(1 if decides else 0, 3)
names = rng.sample(POOL, rng.randrange(1, 5))          # declaration order


def default_expr(i, with_field):
    """A default for the i-th named parameter: (Verse text, evaluator)."""
    x = names[i]
    earlier = names[:i]
    choices = ['lit', 'base', 'log']
    if npos:
        choices.append('pos')
    if earlier:
        choices += ['named', 'lognamed']
    if with_field:
        choices.append('field')
    c = rng.choice(choices)
    k = rng.randrange(1, 10)
    if c == 'lit':
        return str(k), lambda env, log: k
    if c == 'base':
        return 'Base', lambda env, log: base
    if c == 'pos':
        j = rng.randrange(npos)
        return f'P{j} + {k}', lambda env, log: env[f'P{j}'] + k
    if c == 'named':
        y = rng.choice(earlier)
        return f'{y} * 2', lambda env, log: env[y] * 2
    if c == 'field':
        return f'Speed + {k}', lambda env, log: env['$speed'] + k
    if c == 'log':
        def ev(env, log, k=k):
            log.append(f'default {x}')
            return k
        return f'L.Next("default {x}", {k})', ev
    y = rng.choice(earlier)

    def ev(env, log, y=y):
        log.append(f'default {x}')
        return env[y] + 1
    return f'L.Next("default {x}", {y} + 1)', ev


def make_params(with_field, has_default=None):
    """Named parameters: (name, Verse default text or None, evaluator)."""
    out = []
    for i, x in enumerate(names):
        d = rng.random() < 0.65 if has_default is None else has_default[i]
        if d:
            text, ev = default_expr(i, with_field)
            out.append((x, text, ev))
        else:
            out.append((x, None, None))
    return out


params = make_params(method)
defaults = [p[1] is not None for p in params]
# (an override's defaults: the same parameters, its own default expressions)
override = method and rng.random() < 0.5
oparams = make_params(True, defaults) if override else None
limit = rng.randrange(3, 8)


def signature(ps):
    pos = ['L:log'] + [f'P{j}:int' for j in range(npos)]
    named = [f'?{x}:int' + (f' = {t}' if t is not None else '') for x, t, _ in ps]
    return ', '.join(pos + named)


body = '"' + ' '.join([f'{{P{j}}}' for j in range(npos)] + [f'{x}={{{x}}}' for x in names]) + '"'
effects = '<transacts><decides>' if decides else '<transacts>'


def result(env, prefix=''):
    return prefix + ' '.join([str(env[f'P{j}']) for j in range(npos)] + [f'{x}={env[x]}' for x in names])


def type_text(tnamed):
    """tnamed: [(name, optional)] in the type's written order."""
    ps = [':log'] + [':int'] * npos + [f'?{x}:int' + (' = 0' if o else '') for x, o in tnamed]
    return 'type{_(' + ', '.join(ps) + ')' + effects + ':string}'


def type_shown(tnamed):
    """As a message shows it: named parameters in order of name, the default
    effects (<transacts>) unwritten."""
    ps = [':log'] + [':int'] * npos + [f'?{x}:int' + (' = …' if o else '') for x, o in sorted(tnamed)]
    return 'type{_(' + ', '.join(ps) + ')' + ('<decides>' if decides else '') + ':string}'


def valid_type():
    tn = []
    for (x, t, _) in params:
        if t is None:
            tn.append((x, False))
        else:
            r = rng.randrange(3)
            if r == 1:
                tn.append((x, False))
            elif r == 2:
                tn.append((x, True))
    rng.shuffle(tn)
    return tn


counter = [0]       # L.N
speed = [1]
arg_values = iter(range(11, 10_000, 7))


def call(tnamed, fn_params, prefix=''):
    """A call through a value of type tnamed: its text and the predicted
    output (logs and result), or None when a <decides> call fails."""
    given = [x for x, o in tnamed if not o or rng.random() < 0.5]
    rng.shuffle(given)
    pos_vals = [next(arg_values) % 10 for _ in range(npos)]
    if decides and rng.random() < 0.5:
        pos_vals[0] = limit + rng.randrange(0, 3)    # fails
    named_vals = {x: next(arg_values) % 10 for x in given}
    args = ['L'] + [f'L.Next("pos {j}", {v})' for j, v in enumerate(pos_vals)] + \
        [f'?{x} := L.Next("arg {x}", {named_vals[x]})' for x in given]
    log = [f'pos {j}' for j in range(npos)] + [f'arg {x}' for x in given]
    env = {f'P{j}': v for j, v in enumerate(pos_vals)}
    env.update(named_vals)
    env['$speed'] = speed[0]
    for x, t, ev in fn_params:
        if x not in env:
            env[x] = ev(env, log)
    ok = not decides or pos_vals[0] < limit
    text = ', '.join(args)
    if ok:
        counter[0] += len(log)
        return text, log + [result(env, prefix)]
    return text, None


prog = []
prog.append('''log := class:
    var N:int = 0
    Next(What:string, V:int)<transacts>:int =
        set N += 1
        Print(What)
        V''')
prog.append(f'Base:int = {base}')
br = (lambda a: f'[{a}]') if decides else (lambda a: f'({a})')
main = ['Main():void =', '    L := log{}']


def emit_call(fname, tnamed, fn_params, prefix=''):
    text, pred = call(tnamed, fn_params, prefix)
    if decides:
        main.append(f'    if (R := {fname}{br(text)}) then Print(R) else Print("failed")')
        lines.extend(pred if pred is not None else ['failed'])
    else:
        main.append(f'    Print({fname}{br(text)})')
        lines.extend(pred)


if method:
    prog.append(f'''game := class:
    var Speed:int = 1
    M({signature(params)}){effects}:string = {body}''')
    if override:
        prog.append(f'''fast := class(game):
    M<override>({signature(oparams)}){effects}:string = "fast " + {body}''')
    prog.append(f'''MakeGame():game =
    Print("receiver")
    {'fast' if override else 'game'}{{}}''')
    t = valid_type()
    main.append('    G := MakeGame()')
    lines.append('receiver')
    speed[0] = rng.randrange(1, 9)
    main.append(f'    set G.Speed = {speed[0]}')
    main.append(f'    F:{type_text(t)} = G.M')
    main.append('    Print("bound")')
    lines.append('bound')
    use = oparams if override else params
    for _ in range(rng.randrange(1, 4)):
        emit_call('F', t, use, 'fast ' if override else '')
        speed[0] = rng.randrange(1, 9)
        main.append(f'    set G.Speed = {speed[0]}')
else:
    if decides:
        prog.append(f'Fn({signature(params)}){effects}:string =\n    P0 < {limit}\n    {body}')
    else:
        prog.append(f'Fn({signature(params)}){effects}:string = {body}')
    if mode == 5:
        req = [x for x, t, _ in params if t is None]
        opt = [x for x, t, _ in params if t is not None]
        absent = [x for x in POOL if x not in names]
        kinds = ['extra'] + (['omit'] if req else []) + (['optional'] if req else []) + \
            ['call_unknown'] + (['call_missing'] if req else [])
        kind = rng.choice(kinds)
        t = valid_type()
        if kind == 'extra':
            t = t + [(rng.choice(absent), rng.random() < 0.5)] if absent else t
            if not absent:
                kind = 'call_unknown'
        if kind == 'omit':
            t = [(x, o) for x, o in t if x != req[0]]
        if kind == 'optional':
            t = [(x, o or x == req[0]) for x, o in t]
        own = [(x, tx is not None) for x, tx, _ in params]
        if kind in ('extra', 'omit', 'optional'):
            msg = f'expected {type_shown(t)}, found {type_shown(own)}'
            main.append(f'    F:{type_text(t)} = Fn')
            main.append('    Print("bad")')
        else:
            main.append(f'    F:{type_text(t)} = Fn')
            args = ['L'] + ['1'] * npos
            if kind == 'call_unknown':
                bad = rng.choice(absent + [x for x in opt if x not in [y for y, _ in t]] or ['Z'])
                args.append(f'?{bad} := 1')
                args += [f'?{x} := 2' for x, o in t if not o]
                msg = f'a value of type {type_shown(t)} has no parameter ?{bad}'
            else:
                miss = [x for x, o in t if not o][0]
                args += [f'?{x} := 2' for x, o in t if not o and x != miss]
                msg = f'a value of type {type_shown(t)} needs the argument ?{miss}'
            main.append(f'    Print(F({", ".join(args)}))')
        print('\n'.join(prog + main))
        with open(out_path, 'w') as f:
            f.write(f'exit=4\n{msg}\n')
        sys.exit(0)
    if mode == 2:
        t = [(x, tx is not None) for x, tx, _ in params]     # its own type
        main.append('    F := Fn')
        for _ in range(rng.randrange(1, 4)):
            emit_call('F', t, params)
    elif mode == 1:
        t = valid_type()
        prog.append(f'''Make():{type_text(t)} = Fn''')
        calls = []
        for _ in range(rng.randrange(1, 3)):
            text, pred = call(t, params)
            calls.append(f'    Print(G({text}))')
            lines.extend(pred)
        prog.append(f'Apply(L:log, G:{type_text(t)}):void =\n' + '\n'.join(calls))
        main.append('    Apply(L, Fn)')
        main.append('    F := Make()')
        emit_call('F', t, params)
    else:
        t = valid_type()
        main.append(f'    F:{type_text(t)} = Fn')
        for _ in range(rng.randrange(1, 4)):
            emit_call('F', t, params)
main.append('    Print("count {L.N}")')
lines.append(f'count {counter[0]}')
print('\n'.join(prog + main))
with open(out_path, 'w') as f:
    f.write('exit=0\n' + ''.join(line + '\n' for line in lines))
