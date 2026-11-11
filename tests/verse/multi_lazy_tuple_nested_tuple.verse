Walk(P:tuple(int,string),N:int)<computes>:string = if(N>0)then(P(1) | Walk(((P(0)+1,P(1)+"x"),N-1)))else P(1)
Main():void =
    for(V:=Walk((0,"s"),2)){Print(V)}
