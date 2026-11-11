# A kept generic call reads its omitted default from the saved receiver.
box(t:type) := class:
    F:t
    Both(X:t,Y:t,?Z:t=F)<computes>:t = X | Z
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v,?Z:v=F)<computes>:v
Collect(P:box(u),X:u,Y:u,N:int where u:type)<computes>:[]u =
    R:=for(V:=P.Both((X,Y))){V}
    if(N>0) then (R | Collect(P,X,Y,N-1)) else R
Main():void = for(R:=Collect(box(string){F:="field"},"x","y",1),V:R){Print(V)}
