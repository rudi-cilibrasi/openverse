Id(X:t where t:type)<computes>:t=X
Read(X:t,Y:u where t:type,u:type)<reads>:tuple(t,u)=
    F:type{_(:t,:u)<reads>:tuple(t,u)}=Id
    F(X,Y)
Async(X:t,Y:u where t:type,u:type)<computes><suspends>:tuple(t,u)=
    F:type{_(:t,:u)<computes><suspends>:tuple(t,u)}=Id
    F(X,Y)
Main()<suspends>:void=
    A:=Read(7,"s")
    B:=Async("x",9)
    Print("{A(0)} {A(1)} {B(0)} {B(1)}")
