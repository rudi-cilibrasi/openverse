counter:=class<allocates>:
    var N:int=0
    Add(X:int)<transacts>:int=
        set N+=X
        N
Apply(F:t where t:subtype(type{_(:int)<transacts>:int}))<computes>:int=F(7)
Main():void=
    C:=counter{}
    F:type{_(:int)<transacts>:int}=C.Add
    Print("{Apply(F)} {C.N}")
