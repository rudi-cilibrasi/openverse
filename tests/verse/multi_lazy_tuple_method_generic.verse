box(t:type) := class:
    Walk(X:t,Y:t,N:int)<computes>:t = if(N>0) then (X | Self.Walk((Y,X,N-1))) else X
Main():void =
    if(V:=box(int){}.Walk(3,4,2),V=4) then Print("first {V}")
    for(V:=box(int){}.Walk(3,4,2)){Print("all {V}")}
    for(V:=box(string){}.Walk("a","b",1)){Print(V)}
