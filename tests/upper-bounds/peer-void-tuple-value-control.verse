Keep(X:tuple(int,string))<computes>:tuple(int,string)=X
Main():void=
    F:type{_(:int,:string)<computes>:tuple(int,string)}=Keep
    R:=F(1,"s")
    Print("{R(0)} {R(1)}")
