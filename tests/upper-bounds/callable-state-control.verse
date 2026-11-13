counter:=class<allocates>:
    var N:int=0
    Add(D:int)<transacts>:int=
        set N+=D
        N
Get(F:type{_(:int)<transacts>:int},M:counter)<transacts>:type{_(:int)<transacts>:int}=
    set M.N=M.N*10+1
    F
Arg(M:counter)<transacts>:int=
    set M.N=M.N*10+2
    2
Apply(F:type{_(:int)<transacts>:int},M:counter)<transacts>:int=Get(F,M)(Arg(M))
box:=class<computes>:
    Fn:type{_(:int)<transacts>:int}
    Run(D:int)<transacts>:int=Fn(D)
Main():void=
    H:=counter{}
    M:=counter{}
    F:type{_(:int)<transacts>:int}=H.Add
    Print("first {Apply(F,M)} order {M.N}")
    if(Apply(F,M),false?)then Print("bad")else Print("rollback {H.N} {M.N}")
    B:=box{Fn:=F}
    Print("boxed {B.Run(3)}")
