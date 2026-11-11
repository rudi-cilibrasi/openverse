# expect: expected int, found string
Walk(A:int,B:int,N:int)<computes>:int = if(N>0) then (A | Walk(("wrong",A,N-1))) else A
Main():void =
    if(V:=Walk(3,4,2),V=4) then Print("first {V}")
    O:=option{V:=Walk(3,4,2);V=4;V}
    if(V:=O?) then Print("option {V}")
    for(V:=Walk(3,4,2)){Print("all {V}")}
