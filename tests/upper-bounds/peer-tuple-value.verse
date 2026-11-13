Split(X:u where t:type,u:subtype(t))<computes>:u=X
Main():void=
    F:type{_(:int,:string)<computes>:tuple(int,string)}=Split
    R:=F(1,"s")
    Print("peer tuple {R(0)} {R(1)}")
