#!/usr/bin/env python3
"""Source and independent output oracles for heterogeneous producer sharing."""
import sys


def source(kind, count):
    if kind == 'waiting':
        lines = ['link:=class<unique>:', '    Code:int', '    Next:?link',
                 'trace:=class<unique>:', '    var Head:?link=false',
                 '    Note(Code:int):void=set Head=option{link{Code:=Code,Next:=Head}}']
        for name, number in [('a', 1), ('b', 2)]:
            lines += [name+':=class<computes>:', '    T:trace', f'    N:int={number}',
                      '    M():int=', f'        T.Note({number}01)',
                      f'        defer{{T.Note({number}19)}}',
                      f'        (block{{T.Note({number}11);N}})|(block{{T.Note({number}12);N+10}})']
    else:
        lines = []
        for name, number in [('a', 1), ('b', 2)]:
            lines += [name+':=class<computes>:', f'    N:int={number}']
            if kind == 'recursive':
                lines += ['    M(K:int)<computes><decides>:int=', '        K>=0', '        (N+K)|M[K-1]']
            elif kind in ['generic', 'generic-local']:
                lines += ['    M(V:t where t:type)<computes>:t=V|V']
            else:
                values = 'N' if kind == 'mixed' and name == 'b' else 'N|N+10'
                lines += ['    M()<computes>:int='+values]
    lines += ['Dup(V:t where t:type)<computes>:t=V|V']
    call = lambda i: (f'A{i}.M[1]' if kind == 'recursive' else
                      f'A{i}.M(A{i}.N)' if kind in ['generic', 'generic-local'] else f'A{i}.M()')
    ctor = '{T:=T}' if kind == 'waiting' else '{}'
    clauses = ','.join(f'A{i}:=Dup(a{ctor})|Dup(b{ctor}),X{i}:={call(i)}' for i in range(count))
    if kind == 'generic-local':
        for i in range(count):
            clauses = clauses.replace(f'X{i}:=A{i}.M(A{i}.N)', f'Z{i}:=A{i}.N+1,X{i}:=A{i}.M(Z{i})')
    value = '+'.join(f'X{i}+A{i}.N' for i in range(count))
    if kind == 'failure':
        lines += ['cell:=class{var N:int=0}', 'Use(C:cell)<decides>:void=',
                  f'    Rows:=for({clauses}):', '        set C.N+=1',
                  '        C.N<2', '        '+value, '    {}', 'Main():void=',
                  '    C:=cell{}', '    if(Use[C])then Print("bad")else Print("failed {C.N}")']
    elif kind == 'first':
        lines += ['Main():void=', f'    if({clauses},V:={value})then Print("{{V}}")else Print("none")']
    elif kind == 'option':
        lines += ['Main():void=', f'    O:=option{{{clauses};{value}}}', '    Print("{O? or -1}")']
    elif kind == 'waiting':
        lines += ['Main()<suspends>:void=', '    T:=trace{}', f'    Rows:=for({clauses}):',
                  '        Score:='+value, '        defer{T.Note(500+Score)}',
                  '        T.Note(300+Score)', '        Sleep(0.001)', '        T.Note(400+Score)',
                  '        Score', '    var Sum:int=0', '    for(R:Rows):set Sum+=R',
                  '    var Cursor:?link=T.Head', '    var Chunk:string=""', '    var Used:int=0',
                  '    loop:', '        if(Current:=Cursor?):', '            set Chunk+="{Current.Code},"',
                  '            set Used+=1', '            set Cursor=Current.Next', '            if(Used=128):',
                  '                Print(Chunk)', '                set Chunk=""', '                set Used=0',
                  '        else:', '            if(Used>0):Print(Chunk)', '            break',
                  '    Print("{Rows.Length} {Sum}")']
    else:
        lines += ['Main():void=', f'    Rows:=for({clauses}):{value}', '    Print("{Rows.Length}")',
                  '    var Sum:int=0', '    for(R:Rows):set Sum+=R', '    Print("{Sum}")']
    return '\n'.join(lines)+'\n'


def oracle(kind, count):
    if kind in ['first', 'option']:
        return f'{2*count}\n'
    if kind == 'failure':
        return 'failed 0\n'
    if kind == 'waiting':
        events, values = [], []
        def walk(level, score):
            if level == count:
                events.extend([300+score, 400+score, 500+score]); values.append(score)
                return
            for tag in [1, 1, 2, 2]:
                events.append(tag*100+1)
                for choice in [0, 1]:
                    events.extend([tag*100+11+choice, tag*100+19])
                    walk(level+1, score+2*tag+10*choice)
        walk(0, 0)
        reverse = list(reversed(events))
        chunks = ''.join(''.join(f'{event},' for event in reverse[i:i+128])+'\n'
                         for i in range(0, len(reverse), 128))
        return chunks+f'{len(values)} {sum(values)}\n'
    per_value = {'recursive': [3, 2, 3, 2, 5, 4, 5, 4],
                 'generic': [2, 2, 2, 2, 4, 4, 4, 4],
                 'generic-local': [3, 3, 3, 3, 5, 5, 5, 5],
                 'mixed': [2, 12, 2, 12, 4, 4]}.get(kind, [2, 12, 2, 12, 4, 14, 4, 14])
    rows = len(per_value)**count
    total = count*sum(per_value)*len(per_value)**(count-1)
    return f'{rows}\n{total}\n'


if __name__ == '__main__':
    action, kind, count = sys.argv[1], sys.argv[2], int(sys.argv[3])
    assert action in ['source', 'oracle'] and count > 0
    sys.stdout.write((source if action == 'source' else oracle)(kind, count))
