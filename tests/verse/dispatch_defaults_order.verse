Note(S:string,N:int)<transacts>:int=
    Print("{S} {N}")
    N
base(t:type) := class:
    Act(X:t,?A:int=0,?B:int=0)<transacts>:int=A+B
ib := class(base(int)):
    Seed:int=3
    Act<override>(X:int,?A:int=Note("a",X+Seed),?B:int=Note("b",A+1))<transacts>:int=
        Print("body {X} {A} {B}")
        A+B
Invoke(P:base(t),X:t where t:type)<transacts>:void=
    Print("r {P.Act(X)}")
    Print("r {P.Act(X,?B:=Note("given-b",20))}")
    Print("r {P.Act(X,?B:=Note("first",20),?A:=Note("second",10))}")
Main()<transacts>:void=Invoke(ib{},4)
