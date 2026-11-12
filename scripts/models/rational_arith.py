#!/usr/bin/env python3
"""Exact Fraction oracle for rational operators, order, rollback and updates."""
from fractions import Fraction
from pathlib import Path
import random
import sys

rng=random.Random(int(sys.argv[1]))
MIN,MAX=-(1<<63),(1<<63)-1
mode=rng.randrange(6)
op=rng.choice(['+','-','*','/','neg'])

def lit(n):return '(-9223372036854775807-1)' if n==MIN else str(n)
def fits(q):return MIN<=q.numerator<=MAX and 1<=q.denominator<=MAX
def integer():return rng.choice([MIN,MIN+1,-MAX,-2,-1,0,1,2,MAX-1,MAX,rng.randrange(-100,101)])
def fraction():
    while True:
        q=Fraction(integer(),rng.choice([1,2,3,7,MAX-1,MAX,rng.randrange(1,101)]))
        if fits(q):return q

a,b=fraction(),fraction()
if mode==1:
    op,a,b=rng.choice([
        ('+',Fraction(1,MAX),Fraction(MAX-1,MAX)),
        ('+',Fraction(MAX,MAX-1),Fraction(MIN,MAX-1)),
        ('-',Fraction(MIN),Fraction(MIN)),
        ('*',Fraction(MAX,2),Fraction(2,MAX)),
        ('/',Fraction(MIN),Fraction(MIN)),
        ('*',Fraction(0),Fraction(MIN)),
        ('+',Fraction(MAX),Fraction(-MAX))])
elif mode==2:
    op,a,b=rng.choice([
        ('+',Fraction(MAX),Fraction(1)),('-',Fraction(MIN),Fraction(1)),
        ('*',Fraction(MIN),Fraction(-1)),('/',Fraction(1),Fraction(MIN)),
        ('*',Fraction(1,MAX),Fraction(1,MAX)),('neg',Fraction(MIN),Fraction(1)),
        ('/',Fraction(MIN),Fraction(-1))])
elif mode==3:
    op=rng.choice(['+','-','*','/','neg'])
    if op=='/' and rng.choice([True,False]):b=Fraction(0)
elif mode==4:
    op=rng.choice(['+','-','*','/'])
    if op=='/' and rng.choice([True,False]):b=Fraction(0)
elif mode==5:
    op=rng.choice(['+','-','*','/'])
    b=Fraction(integer())

zero=op=='/' and b==0
if not zero:
    result={'+' :lambda:a+b,'-':lambda:a-b,'*':lambda:a*b,'/':lambda:a/b,'neg':lambda:-a}[op]()
else:result=None
overflow=result is not None and not fits(result)
lines=[]
status=2 if overflow else 0

def check_lines(q):
    return [f'ok {q.numerator//q.denominator} {-((-q.numerator)//q.denominator)}']
def verify(q,indent):
    return ' '*indent+f'Check(R,{lit(q.numerator)},{lit(q.denominator)})'

header='''Check(R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("ok {Floor(R)} {Ceil(R)}")else Print("bad")
cell:=class{var N:int=0;var R:rational=0}
'''
create=f'    if(A:={lit(a.numerator)}/{lit(a.denominator)},B:={lit(b.numerator)}/{lit(b.denominator)}):\n'
expr='-A' if op=='neg' else f'A{op}B'
# Also exercise mixed operators where an operand is an integer-valued rational.
if mode==0 and op!='neg':
    if a.denominator==1 and rng.choice([True,False]):expr=f'{lit(a.numerator)}{op}B'
    elif b.denominator==1 and rng.choice([True,False]):expr=f'A{op}{lit(b.numerator)}'

if mode in (0,1,2):
    program=header+'Main():void=\n'+create+'        Print("before")\n'+f'        if(R:={expr},true?):\n'
    program+=verify(result,12)+'\n' if not zero and not overflow else '            Print("bad")\n'
    program+='        else:\n            Print("zero")\n'
    lines=['before']+([] if overflow else ['zero'] if zero else check_lines(result))
elif mode==3:
    header+='''Arg(C:cell,X:rational,Tag:string):rational=
    set C.N+=1
    Print("{Tag} {C.N}")
    X
'''
    expr='-Arg(C,A,"left")' if op=='neg' else f'Arg(C,A,"left"){op}Arg(C,B,"right")'
    program=header+'Main():void=\n'+create+'''        C:=cell{}
        Print("before")
'''+f'''        if(R:={expr},false?)then Print("bad")else Print("reject {{C.N}}")
        if(R:={expr},true?):
'''
    program+=verify(result,12)+'\n' if not zero and not overflow else '            Print("bad")\n'
    program+='        else:\n            Print("zero")\n        Print("state {C.N}")\n'
    args=['left 1']+([] if op=='neg' else ['right 2'])
    lines=['before']+args if overflow else ['before','reject 0']+([] if zero else args)+(['zero','state 0'] if zero else check_lines(result)+[f'state {len(args)}'])
elif mode==4:
    header+='''Rhs(C:cell,X:rational):rational=
    set C.N+=1
    set C.R=99
    Print("rhs {C.N}")
    X
'''
    program=header+'Main():void=\n'+create+'''        C:=cell{R:=A}
        Print("before")
'''
    if op=='/':
        program+='        if(set C.R/=Rhs(C,B)):\n            R:=C.R\n'
        program+=verify(result,12)+'\n' if not zero and not overflow else '            Print("bad")\n'
        program+='        else:\n            Print("zero {C.N} {Floor(C.R)} {Ceil(C.R)}")\n'
    else:
        program+=f'        set C.R{op}=Rhs(C,B)\n        R:=C.R\n'
        program+=verify(result,8)+'\n' if not overflow else '        Print("bad")\n'
    lines=['before']+([] if zero else ['rhs 1'])+([] if overflow else [f'zero 0 {a.numerator//a.denominator} {-((-a.numerator)//a.denominator)}'] if zero else check_lines(result))
else:
    header+=f'''calc(h:type):=class:
    Hidden:h
    V:rational
    Apply(X:rational)<computes><decides>:rational=V{op}X
Bind(C:calc(h) where h:type)<computes>:type{{_(:int)<computes><decides>:rational}}=C.Apply
'''
    hidden='7' if rng.choice([True,False]) else '"hidden"'
    ty='int' if hidden=='7' else 'string'
    program=header+'Main():void=\n'+create+f'''        F:=Bind(calc({ty}){{Hidden:={hidden},V:=A}})
        Print("before")
        if(R:=F[{lit(b.numerator)}]):
'''
    program+=verify(result,12)+'\n' if not zero and not overflow else '            Print("bad")\n'
    program+='        else:\n            Print("zero")\n'
    lines=['before']+([] if overflow else ['zero'] if zero else check_lines(result))

print(program)
Path(sys.argv[2]).write_text(f'exit={status}\n'+'\n'.join(lines)+'\n')
