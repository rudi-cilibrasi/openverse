cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Same(X:u where u:type):u=
        set C.N+=1
        Print("same {C.N}")
        X
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Arg(C:cell,X:t where t:type):t=
    set C.N+=1
    Print("arg {C.N}")
    X
Apply(F:type{_(:t):t},X:t where t:type):t=F(X)
Run(B:box(t),X:u where t:type,u:type):u=Apply(Touch(B).Same,Arg(B.C,X))
Main():void=
    C:=cell{}
    B:=box(string){V:="tag",C:=C}
    Print("result {Apply(Touch(B).Same,Arg(C,7))}")
