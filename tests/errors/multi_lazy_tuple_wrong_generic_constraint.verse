# expect: must be comparable
Walk(X:t,Y:t,N:int where t:subtype(comparable))<computes>:t = if(N>0) then (X | Walk((Y,X,N-1))) else X
opaque := class {}
Main():void = for(V:=Walk(opaque{},opaque{},2)){Print("bad")}
