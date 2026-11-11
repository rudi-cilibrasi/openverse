Pair(X:t,Y:u where t:type,u:type)<computes>:tuple(t,u)=(X,Y)
Flip(P:tuple(t,u) where t:type,u:type)<computes>:tuple(u,t)=(P(1),P(0))
Id(X:t where t:type)<computes>:t=X
Bind(X:t,Y:u where t:type,u:type)<computes>:type{_(:tuple(t,u))<computes>:tuple(t,u)}=Pair
Run(X:t,Y:u where t:type,u:type)<computes>:tuple(t,u)=
    F:type{_(:tuple(t,u))<computes>:tuple(t,u)}=Pair
    G:type{_(:t,:u)<computes>:tuple(u,t)}=Flip
    H:type{_(:t,:u)<computes>:tuple(t,u)}=Id
    A:=F((X,Y))
    B:=G(A(0),A(1))
    H(B(1),B(0))
Main():void=
    R:=Run(7,"s")
    F:=Bind("a",3)
    S:=F(("b",4))
    Print("{R(0)} {R(1)} {S(0)} {S(1)}")
