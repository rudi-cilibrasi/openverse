Choose(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
Main():void=
    A:rational=1
    R:=Choose(7,A)
    if(R=7)then Print("numeric inferred")else Print("bad")
    Choose(2,"s")
    Print("any inferred")
