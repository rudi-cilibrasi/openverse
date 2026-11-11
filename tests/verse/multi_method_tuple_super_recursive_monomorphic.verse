# Preserve recursive super normalization before lazy/eager lowering (#448).
base := class:
    Walk(X:int,Y:int,N:int)<computes>:int = if(N>0) then (X | Walk(Y,X,N-1)) else X
mid := class(base):
    Walk<override>(X:int,Y:int,N:int)<computes>:int = (super:)Walk((X,Y,N))
Main():void =
    if(V:=mid{}.Walk(3,4,2),V=4) then Print("first {V}")
    O:=option{V:=mid{}.Walk(3,4,2);V=4;V}
    if(V:=O?) then Print("option {V}")
    for(V:=mid{}.Walk(3,4,2)){Print("all {V}")}
