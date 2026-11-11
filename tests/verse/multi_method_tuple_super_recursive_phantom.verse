# Preserve recursive super normalization before lazy/eager lowering (#448).
base(t:type) := class:
    Walk(X:int,Y:int,N:int)<computes>:int = if(N>0) then (X | Walk(Y,X,N-1)) else X
mid(u:type) := class(base(u)):
    Walk<override>(X:int,Y:int,N:int)<computes>:int = (super:)Walk((X,Y,N))
Main():void =
    if(V:=mid(string){}.Walk(3,4,2),V=4) then Print("first {V}")
    O:=option{V:=mid(string){}.Walk(3,4,2);V=4;V}
    if(V:=O?) then Print("option {V}")
    for(V:=mid(string){}.Walk(3,4,2)){Print("all {V}")}
