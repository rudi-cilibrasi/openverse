# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Walk(X:t,Y:t,N:int)<computes>:t = if(N>0) then (X | Walk(Y,X,N-1)) else X
mid(u:type) := class(base(u)):
    Walk<override>(X:u,Y:u,N:int)<computes>:u = (super:)Walk((X,Y,N))
Main():void =
    if(V:=mid(int){}.Walk(3,4,2),V=4) then Print("first {V}")
    O:=option{V:=mid(int){}.Walk(3,4,2);V=4;V}
    if(V:=O?) then Print("option {V}")
    for(V:=mid(int){}.Walk(3,4,2)){Print("all {V}")}