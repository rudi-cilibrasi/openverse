# expect: a call of it with a tuple, in its own body, is not supported yet (#246)
# The existing recursive-argument limit is distinct from super tuple typing (#448).
box(t:type) := class:
    Walk(X:t,Y:t,N:int)<computes>:t = if(N>0) then (X | Self.Walk((Y,X,N-1))) else X
Main():void =
    if(V:=box(int){}.Walk(3,4,2),V=4) then Print("first {V}")
    for(V:=box(int){}.Walk(3,4,2)){Print("all {V}")}
