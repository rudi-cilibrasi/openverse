car:=class<computes>{}
CopyComparable(X:u where t:subtype(comparable),u:subtype(t))<computes>:u=X
Main():void=
    F:type{_(:car,:int)<computes>:tuple(car,int)}=CopyComparable
    R:=F(car{},1)
    Print("{R(1)}")
