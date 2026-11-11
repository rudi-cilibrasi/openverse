# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Both(X:t,Y:t)<computes>:t = X | Y
Walk(P:box(u),X:u,Y:u,N:int where u:type)<computes>:int =
    R:=for(V:=P.Both((X,Y))){V}
    if(N>0) then (R.Length | Walk(P,X,Y,N-1)) else R.Length
Main():void = for(V:=Walk(box(string){},"s","t",2)){Print("{V}")}
