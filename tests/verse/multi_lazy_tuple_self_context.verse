Walk(X:t,E:[]t,O:?t,N:int where t:type)<computes>:t =
    if(N>0) then (X | Walk((X,array{},false,N-1))) else X
Main():void =
    for(V:=Walk(7,array{},false,2)){Print("{V}")}
    if(V:=Walk("x",array{},false,2))then Print(V)
