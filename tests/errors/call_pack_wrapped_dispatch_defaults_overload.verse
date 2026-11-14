# expect: base has overloads of F a call cannot tell apart
base(t:type) := class:
    F(X:[]t,?N:int=0):int=N
    F(X:int,?N:int=0):int=N
ib := class(base(int)):
    Seed:int=4
    F<override>(X:[]int,?N:int=Seed+X.Length):int=N
    F<override>(X:int,?N:int=Seed+X):int=N
Run(t:type, P:base(t)):void=
    Print("{P.F(array{})}")
    Print("{P.F(7)}")
Main():void=Run(int, ib{})
