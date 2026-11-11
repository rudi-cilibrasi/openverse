Walk(A:t,M:[t][]t,O:?t,N:int where t:subtype(comparable))<computes>:int = if(N>0) then (N+M.Length | Walk((A,map{},false,N-1))) else M.Length
Main():void =
    if(V:=Walk("s",map{},false,2),V=1) then Print("first {V}")
    for(V:=Walk(7,map{},false,2)){Print("all {V}")}
