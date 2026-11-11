Id(X:t where t:type)<computes>:t=X
Levels(F:type{_(:t)<computes>:t},X:t,N:int where t:type)<computes>:int=
    Y:=F(X)
    if(N<1)then 0 else N|Levels(Id,Y,N-1)
Main():void=
    R:=for{Levels(Id,"s",3)}
    Print("count {R.Length}")
    for(N:R):Print("{N}")
