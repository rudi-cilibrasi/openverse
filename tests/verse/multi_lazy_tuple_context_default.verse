Walk(A:t,Xs:[]t,N:int,?O:?t=false where t:type)<computes>:int = if(N>0) then (Xs.Length | Walk((A,array{},N-1))) else Xs.Length
Main():void =
    if(V:=Walk(7,array{8},2),V=0) then Print("first {V}")
    for(V:=Walk("s",array{"t"},2)){Print("all {V}")}
