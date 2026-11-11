box(t:type) := class:
    Walk(P:tuple(int,int))<computes>:int = if(P(0)>0) then (P(1) | Self.Walk((P(0)-1,P(1)+1))) else P(1)
Main():void =
    if(V:=box(string){}.Walk((2,7)),V=8) then Print("first {V}")
    for(V:=box(string){}.Walk((2,7))){Print("all {V}")}
