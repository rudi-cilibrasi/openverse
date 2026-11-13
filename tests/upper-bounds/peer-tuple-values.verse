Upper(X:u where u:subtype(t),t:type)<computes>:t=X
Split(X:u where t:type,u:subtype(t))<computes>:u=X
CopyComparable(X:u where t:subtype(comparable),u:subtype(t))<computes>:u=X
Apply(F:type{_(:a,:b)<computes>:tuple(a,b)},A:a,B:b where a:type,b:type)<computes>:tuple(a,b)=F(A,B)
Make()<computes>:type{_(:int,:string)<computes>:tuple(int,string)}=Upper
Main():void=
    U:type{_(:int,:string)<computes>:tuple(int,string)}=Upper
    R:=U(1,"s")
    Print("tuple upper {R(0)} {R(1)}")
    C:=Apply(Split,2,"c")
    Print("tuple callback {C(0)} {C(1)}")
    E:=Make()(3,"e")
    Print("tuple escaped {E(0)} {E(1)}")
    K:type{_(:int,:string)<computes>:tuple(int,string)}=CopyComparable
    V:=K(4,"k")
    Print("tuple comparable {V(0)} {V(1)}")
