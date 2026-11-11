# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Both(X:t,Y:t)<computes>:t = X | Y
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v)<computes>:v
Walk(P:box(u),X:u,Y:u,N:int where u:type)<computes>:int =
    R:=for(V:=P.Both((X,Y))){V}
    if(N>0) then (R.Length | Walk(P,X,Y,N-1)) else R.Length
Main():void = for(V:=Walk(box(string){},"s","t",2)){Print("{V}")}
