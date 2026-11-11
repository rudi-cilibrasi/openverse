cell:=class{var N:int=0}
Id(X:t where t:type)<computes>:t=X
Mark(C:cell,X:t where t:type):t=
    set C.N+=1
    Print("arg {C.N}")
    X
Default(C:cell):int=
    set C.N+=1
    Print("default {C.N}")
    C.N
Twice(C:cell,?F:type{_(:t)<computes>:t},?X:t,?N:int=Default(C) where t:type):t=F(X)|F(X)
Run(C:cell,X:t where t:type):[]t=for{Twice(C,?F:=Id,?X:=Mark(C,X))}
Main():void=
    C:=cell{}
    R:=Run(C,7)
    Print("done {R.Length} {C.N}")
