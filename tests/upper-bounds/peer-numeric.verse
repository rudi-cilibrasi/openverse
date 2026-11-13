Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    A:rational=1
    R:=Upper(A,2)
    if(R=2)then Print("peer numeric")else Print("bad")
