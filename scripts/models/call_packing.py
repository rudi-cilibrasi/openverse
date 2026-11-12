#!/usr/bin/env python3
"""Source call models, with numeric and trace oracles independent of the compiler."""
import random


SHAPES = ('tuple', 'singleton', 'empty', 'array', 'generic_array', 'nested')
CONTEXTS = ('top', 'method', 'dispatch', 'qualified', 'super', 'constructor',
            'function_value', 'spawn', 'multi', 'recursive')
PERIOD = len(SHAPES) * len(CONTEXTS)


def generate(seed):
    rng = random.Random(seed)
    index = (seed - 1) % PERIOD
    shape = SHAPES[index % len(SHAPES)]
    context = CONTEXTS[index // len(SHAPES)]
    a, b, c = (rng.randrange(1, 30) for _ in range(3))
    if context == 'recursive':
        return f'''Range(P:tuple(int,int))<computes><decides>:int=
    P(0)<=P(1)
    P(0)|Range[P(0)+1,P(1)]
Main():void=
    for(X:=Range[{a},{a+2}]): Print("result {{X}}")
''', ''.join(f'result {x}\n' for x in range(a, a + 3))

    params, where = '', ''
    if shape == 'tuple':
        ty, args, expr, answer = 'tuple(int,int)', [a, b], 'P(0)*10+P(1)', a*10+b
    elif shape == 'singleton':
        ty, args, expr, answer = 'tuple(int)', [a], 'P(0)*3', a*3
    elif shape == 'empty':
        ty, args, expr, answer = 'tuple()', [], str(a), a
    elif shape == 'array':
        ty, args, expr, answer = '[]int', [a, b, c], 'P.Length', 3
    elif shape == 'generic_array':
        ty, args, expr, answer = '[]t', [a, b], 'P.Length', 2
        where = ' where t:type'
    else:
        ty, args, expr, answer = 'tuple(int,tuple(int,int))', [a, (b, c)], 'P(0)*10+P(1)(0)*3+P(1)(1)', a*10+b*3+c

    named = context != 'function_value'
    params = 'P:' + ty
    if named:
        params += ',?A:int,?B:int,?D:int=block{Print("default");A+B}'
        expr += '+A+B+D'
        answer += 2*(a+b)
    params += where
    fx = '<suspends>' if context == 'spawn' else ''
    body = '    Print("body")\n'
    if context == 'spawn':
        body = '    defer{Print("cleanup")}\n' + body + '    Sleep(0.01)\n'
    body += '    ' + expr + ('|(' + expr + ')+1' if context == 'multi' else '') + '\n'
    header = '''Mark(Name:string,V:int):int=block{Print(Name);V}
Single(P:tuple(u) where u:type):tuple(u)=P
'''
    target, receiver = 'F', False
    if context in ('top', 'spawn', 'multi'):
        header += f'F({params}){fx}:int=\n' + body
    elif context == 'constructor':
        header += 'out:=class{Value:int}\n'
        header += f'F<constructor>({params}):=out:\n    Value:=block{{Print("body");{expr}}}\n'
    elif context == 'function_value':
        header += f'F({params}):int=\n' + body
        target = 'G'
    else:
        receiver = True
        if context == 'qualified':
            header += f'i:=interface:\n    F({params}):int\n'
            header += 'base:=class(i):\n' + f'    (i:)F<override>({params}):int=\n'
            header += ''.join('    '+line+'\n' for line in body.splitlines())
            target = 'Get().(i:)F'
        else:
            header += f'base:=class:\n    F({params}):int=\n'
            header += ''.join('    '+line+'\n' for line in body.splitlines())
            if context == 'dispatch':
                header += 'sub:=class(base):\n' + f'    F<override>({params}):int=\n'
                header += ''.join('    '+line+'\n' for line in body.splitlines())
            elif context == 'super':
                forward = 'P' + (',?A:=A,?B:=B,?D:=D' if named else '')
                header += 'sub:=class(base):\n' + f'    Parent({params}):int=(super:)F({forward})\n'
                target = 'Get().Parent'
        if target == 'F':
            target = 'Get().F'
        actual = 'sub' if context in ('dispatch', 'super') else 'base'
        declared = 'sub' if context == 'super' else 'base'
        header += f'Get():{declared}=block{{Print("receiver");{actual}{{}}}}\n'

    def arg(value, label):
        if isinstance(value, tuple):
            return '(' + ','.join(arg(v, label + str(i)) for i, v in enumerate(value)) + ')'
        return f'Mark("{label}",{value})'

    fields = [arg(value, f'arg{i}') for i, value in enumerate(args)]
    explicit = ','.join(fields)
    if shape == 'singleton':
        control = 'Wrap(' + fields[0] + ')'
    elif shape == 'empty':
        control = '()'
    elif shape in ('array', 'generic_array'):
        control = 'array{' + explicit + '}'
    else:
        control = '(' + explicit + ')'
    suffix = f',?B:=Mark("B",{b}),?A:=Mark("A",{a})' if named else ''
    # A comma before named arguments is needed only with a positional value.
    packed_call = explicit + (suffix if explicit else suffix.removeprefix(','))
    control_call = control + suffix
    main = 'Main()' + ('<suspends>' if context == 'spawn' else '') + ':void=\n'
    if shape == 'singleton':
        main += '    Wrap:type{_(:int):tuple(int)}=Single\n'
    if context == 'function_value':
        closed = ty.replace('[]t', '[]int')
        main += f'    G:type{{_(:{closed}):int}}=F\n'
    for i, call_args in enumerate((packed_call, control_call)):
        call = f'{target}({call_args})'
        if context == 'constructor':
            call += '.Value'
        if context == 'spawn':
            main += f'    T{i}:=spawn{{{call}}}\n    R{i}:=T{i}.Await()\n    Print("result {{R{i}}}")\n'
        elif context == 'multi':
            main += f'    for(X{i}:={call}): Print("result {{X{i}}}")\n'
        else:
            main += f'    Print("result {{{call}}}")\n'

    labels = []
    for i, value in enumerate(args):
        labels.extend([f'arg{i}{j}' for j in range(len(value))] if isinstance(value, tuple) else [f'arg{i}'])
    trace = (['receiver'] if receiver else []) + labels
    if named:
        trace += ['B', 'A', 'default']
    trace += ['body']
    if context == 'spawn':
        trace += ['cleanup']
    trace += [f'result {answer}']
    if context == 'multi':
        trace += [f'result {answer+1}']
    return header + main, ('\n'.join(trace) + '\n') * 2
