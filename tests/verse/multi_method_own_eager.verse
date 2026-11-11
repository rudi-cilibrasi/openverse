# Recursive virtual choices retain eager generation and generic payloads.
base(t:type) := class:
    Value:t
    Scan(X:u,N:int where u:type)<computes>:tuple(t,u,int) =
        if(N>0)then((Value,X,N)|Self.Scan((X,N-1)))else(Value,X,0)
child(a:type) := class(base(a)):
    Scan<override>(X:b,N:int where b:type)<computes>:tuple(a,b,int) =
        if(N>0)then((Value,X,N+10)|(super:)Scan((X,N-1)))else(Value,X,0)
Main():void =
    B:base(int)=child(int){Value:=7}
    for(V:=B.Scan(("s",2))): Print("{V(0)} {V(1)} {V(2)}")
    if(V:=B.Scan(("s",2)),V(2)=1)then Print("first {V(0)} {V(1)}")
