Walk(N:int,A:int)<computes>:int = if(N>0) then (A | Hop((N-1,A+1,"hop"))) else A
Hop(N:int,A:int,S:string)<computes>:int = if(N>0) then (Walk((N-1,A+2)) | A+10) else A
Main():void =
    for(V:=Walk(3,0)){Print("{V}")}
    if(V:=Walk(3,0),V>2)then Print("first {V}")
