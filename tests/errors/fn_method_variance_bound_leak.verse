# expect: must be comparable
box(t:type):=class:
    V:t
    Pair(X:t)<computes>:tuple(t,int)=(X,7)
Run(B:box(t),X:t where t:type)<computes><decides>:void=
    F:type{_(:t)<computes>:tuple(t,rational)}=B.Pair
    R:=F(X)
    R(0)=X
Main():void=
    if(Run[box(int){V:=7},7])then Print("wrong")
