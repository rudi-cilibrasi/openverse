Walk(N:int,A:int)<computes>:int =
    P := (N-1,A+2)
    if(N>0) then (A | Walk(P)) else A
Main():void =
    for(V:=Walk(3,1)){Print("{V}")}
    if(V:=Walk(3,1),V>4)then Print("first {V}")
