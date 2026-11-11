cell:=class{var N:int=0}
Step(C:cell):int=
    set C.N+=1
    Print("default {C.N}")
    C.N
box:=class:
    C:cell
    Same(X:t where t:type):t=X
Make(C:cell,?N:int=Step(C)):box=
    set C.N+=1
    Print("make {C.N}")
    box{C:=C}
Arg(C:cell,X:t where t:type):t=
    set C.N+=1
    Print("arg {C.N}")
    X
Apply(F:type{_(:t):t},X:t where t:type):t=F(X)
Main():void=
    C:=cell{}
    Print("result {Apply(Make(C).Same,Arg(C,7))} {C.N}")
