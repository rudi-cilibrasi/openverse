Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Accept(Base:t,Value:u where t:type,u:subtype(t))<computes>:void={}
counter:=class<allocates>:
    var N:int=0
    Base()<transacts>:rational=
        set N+=1
        Print("base {N}")
        0
    BaseAny()<transacts>:any=
        set N+=1
        Print("any {N}")
        0
    Value()<transacts>:int=
        set N+=1
        Print("value {N}")
        7
Main():void=
    H:=counter{}
    R:=Upper(H.Base(),H.Value())
    if(R=7)then Print("numeric 7")else Print("bad")
    if(Upper(H.Base(),H.Value()),false?)then Print("bad")else Print("rolled numeric")
    Print("count {H.N}")
    Accept(H.BaseAny(),H.Value())
    Print("erased {H.N}")
    if(Accept(H.BaseAny(),H.Value()),false?)then Print("bad")else Print("rolled erase")
    Print("after {H.N}")
