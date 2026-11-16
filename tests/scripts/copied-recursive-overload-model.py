#!/usr/bin/env python3
"""Copied recursive overload programs and separately spelled source controls."""
import argparse
from dataclasses import dataclass


@dataclass(frozen=True)
class Case:
    definitions: str
    inputs: tuple
    values: tuple
    threshold: int = 0
    decides: bool = False
    extra: str = ''
    call_argument: str = 'A'


SELF = '''$I(N:int)<computes>:int=if(N=0)then 0 else($I(N-1)|N)
$S(S:string)<computes>:string=S|S+"!"
'''
CASES = {
    'self': Case(SELF, (('1', 'I'), ('"s"', 'S')), ((0, 1), ('s', 's!'))),
    'string-first': Case(SELF, (('""', 'S'), ('1', 'I')), (('', '!'), (0, 1))),
    'indirect': Case('''$I(N:int)<computes>:int=Step(N)
Step(N:int)<computes>:int=if(N=0)then 0 else(Step(N-1)|N)
$S(S:string)<computes>:string=S|S+"!"
''', (('1', 'I'), ('"s"', 'S')), ((0, 1), ('s', 's!'))),
    'mutual': Case('''$I(N:int)<computes>:int=if(N=0)then 0 else(N|Peer(N-1))
Peer(N:int)<computes>:int=if(N=0)then 9 else(N*10|$I(N-1))
$S(S:string)<computes>:int=$I(S.Length)
''', (('2', 'I'), ('"xx"', 'S')), ((2, 10, 0), (2, 10, 0)), 5),
    'unused-recursive-member': Case('''$I(N:int)<computes>:int=N|N+1
$S(S:string)<computes>:string=S|S+"!"
$U(N:int,K:int)<computes>:int=if(K=0)then 0 else($U(N,K-1)|N)
''', (('1', 'I'), ('"s"', 'S')), ((1, 2), ('s', 's!'))),
    'eager': Case('''$I(N:int)<computes><decides>:int=
    N>=0
    if(N=0)then 0 else($I[N-1]+(1|2))
$S(S:string)<computes><decides>:int=
    S.Length>0
    S.Length|S.Length+10
''', (('1', 'I'), ('"s"', 'S')), ((1, 2), (1, 11)), 1, True),
    'generic-tuple': Case('''$I(V:t,K:int where t:type)<computes>:t=if(K=0)then V else($I(V,K-1)|V)
$S(S:string)<computes>:string=S|S+"!"
''', (('(1,1)', 'I'), ('"s"', 'S')), ((1, 1), ('s', 's!'))),
    'generic-named-default': Case('''$I(V:t,K:int,?Y:t=block{Z:t=V;Z} where t:type)<computes>:t=
    if(K=0)then Y else(Y|$I(V,K-1,?Y:=Y))
$S(S:string)<computes>:string=S|S+"!"
''', (('(1,1)', 'I'), ('"s"', 'S')), ((1, 1), ('s', 's!'))),
    'defaults': Case('''Arg(V:t where t:type)<transacts>:t=block{Print("arg");V}
Default(N:int)<transacts>:int=block{Print("default {N}");N+10}
$I(N:int,?D:int=Default(N))<transacts>:int=
    if(N=0)then D else(N|$I(N-1,?D:=D))
$S(S:string,?D:int=Default(S.Length))<transacts>:int=$I(S.Length,?D:=D)
''', (('1', 'I'), ('"s"', 'S')), ((1, 11), (1, 11)), 5, call_argument='Arg(A)'),
    'supplied-default': Case('''Arg(V:t where t:type)<transacts>:t=block{Print("arg");V}
Default(N:int)<transacts>:int=block{Print("default {N}");N+10}
Given()<transacts>:int=block{Print("given");20}
$I(N:int,?D:int=Default(N))<transacts>:int=
    if(N=0)then D else(N|$I(N-1,?D:=D))
$S(S:string,?D:int=Default(S.Length))<transacts>:int=$I(S.Length,?D:=D)
''', (('1', 'I'), ('"s"', 'S')), ((1, 20), (1, 20)), 5, extra=',?D:=Given()', call_argument='Arg(A)'),
    'cleanup': Case('''$I(N:int)<transacts>:int=
    Print("enter {N}")
    defer{Print("leave {N}")}
    if(N=0)then 0 else(N|$I(N-1))
$S(S:string)<transacts>:int=$I(S.Length)
''', (('1', 'I'), ('"s"', 'S')), ((1, 0), (1, 0))),
    'returns': Case('''$I(N:int)<transacts>:int=
    defer{Print("outer {N}")}
    if(N=0):
        defer{Print("base")}
        return 7|8
    N|$I(N-1)
$S(S:string)<transacts>:int=$I(S.Length)
''', (('1', 'I'), ('"s"', 'S')), ((1, 7, 8), (1, 7, 8)), 5),
    'early-argument': Case('''Early(N:int)<transacts>:int=
    Print("early {N}")
    if(N<0):return N
    N|N+100
$I(N:int,E:int)<transacts>:int=if(N=0)then E else($I(N-1,E)|N+E)
$S(S:string,E:int)<transacts>:int=S.Length+E|S.Length+E+1
''', (('1', 'I'), ('"s"', 'S')), ((-1, 0), (0, 1)), extra=',Early(-1)'),
    'many-argument': Case('''Early(N:int)<transacts>:int=
    Print("early {N}")
    if(N<0):return N
    N|N+100
$I(N:int,E:int)<transacts>:int=if(N=0)then E else($I(N-1,E)|N+E)
$S(S:string,E:int)<transacts>:int=S.Length+E|S.Length+E+1
''', (('1', 'I'), ('"s"', 'S')), ((1, 2, 101, 102), (2, 3, 102, 103)), extra=',Early(1)'),
}


def source(name, control):
    case = CASES[name]
    names = {'I': 'IntValues' if control else 'Values',
             'S': 'StringValues' if control else 'Values',
             'U': 'UnusedValues' if control else 'Values'}
    definitions = case.definitions
    for key, value in names.items():
        definitions = definitions.replace('$'+key, value)
    def call(which):
        function = names[which]
        arguments = case.call_argument+case.extra
        return function+('['+arguments+']' if case.decides else '('+arguments+')')
    head = definitions+'\nDup(V:t where t:type)<computes>:t=V|V\n'
    head += f'Accept(N:int)<computes><decides>:void=N>{case.threshold}\n'
    head += 'Accept(S:string)<computes><decides>:void=S.Length>1\n'
    inputs = case.inputs
    if control:
        for index, (argument, which) in enumerate(inputs):
            head += f'Pick{index}()<transacts>:?string=option{{A:=Dup({argument});V:={call(which)};Accept[V];"{{V}}"}}\n'
        clauses = [(f'A:=Dup({argument}),V:={call(which)}', which) for argument, which in inputs]
        main = 'Main()<transacts>:void=\n'
        for clause, _ in clauses:
            main += f'    for({clause}):Print("for<{{V}}>")\n'
        for index, (clause, _) in enumerate(clauses):
            main += ('    if' if index == 0 else '    else if')+f'({clause},Accept[V]):Print("first<{{V}}>")\n'
        main += '    O:=option{Pick0()? or Pick1()?}\n'
    else:
        alternatives = '|'.join(f'Dup({argument})' for argument, _ in inputs)
        clause = f'A:={alternatives},V:={call("I")}'
        main = f'Main()<transacts>:void=\n    for({clause}):Print("for<{{V}}>")\n'
        main += f'    if({clause},Accept[V],Shown:="{{V}}"):Print("first<{{Shown}}>")\n'
        main += f'    O:=option{{A:={alternatives};V:={call("I")};Accept[V];Shown:="{{V}}";Shown}}\n'
    main += '    if(V:=O?)then Print("option<{V}>")else Print("none")\n'
    return head+main


def oracle(name):
    case = CASES[name]
    values = [v for row in case.values for _ in range(2) for v in row]
    accepted = lambda v: len(v)>1 if isinstance(v, str) else v>case.threshold
    first = next(v for v in values if accepted(v))
    return ''.join(f'for<{v}>\n' for v in values)+f'first<{first}>\noption<{first}>\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['list', 'source', 'oracle'])
    parser.add_argument('case', nargs='?')
    parser.add_argument('--control', action='store_true')
    args = parser.parse_args()
    if args.action == 'list':
        print('\n'.join(CASES))
    elif args.action == 'source':
        print(source(args.case, args.control), end='')
    else:
        print(oracle(args.case), end='')
