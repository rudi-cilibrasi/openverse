Id(X:t where t:type)<computes>:t=X
Pair(X:a,Y:b where a:type,b:type)<computes>:tuple(a,b)=(X,Y)
Empty(N:t where t:type)<computes>:[]t=array{}
Bind(X:t where t:type)<computes>:type{_(:t)<computes>:t}=Id
Use(X:t,Y:u where t:type,u:type)<computes>:tuple(t,u,int)=
    F:type{_(:t)<computes>:t}=Id
    G:type{_(:t,:u)<computes>:tuple(t,u)}=Pair
    H:type{_(:t)<computes>:[]t}=Empty
    R:=G(F(X),Y)
    (R(0),R(1),H(X).Length)
Main():void=
    R:=Use(7,"s")
    Print("{R(0)} {R(1)} {R(2)}")
    F:=Bind(9)
    Print("{F(12)}")
