Walk(P:tuple(int,int))<computes>:int = if(P(0)>0)then(P(1) | Walk((P(0)-1,P(1)+2)))else P(1)
Main():void =
    for(V:=Walk((2,1))){Print("{V}")}
    if(V:=Walk((2,1)),V>1)then Print("first {V}")
