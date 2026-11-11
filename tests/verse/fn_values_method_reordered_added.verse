# Bound values preserve reordered and added parameters through escaping tuples.
base(t:type,u:type):=class:
    V:t
    Extra:u
    Same(X:t):t=V
child(a:type,b:type,c:type):=class(base(b,a)):
    Marker:c
    Same<override>(X:b):b=block{Print("child");X}
    Mark():c=Marker
    First():a=Extra
Bind(P:child(a,b,c) where a:type,b:type,c:type):tuple(type{_(:b):b},type{_():c},type{_():a})=
    (P.Same,P.Mark,P.First)
BindRoot(P:base(a,b) where a:type,b:type):type{_(:a):a}=P.Same
Main():void=
    P:=child(string,int,[]string){V:=7,Extra:="parent",Marker:=array{"marker"}}
    K:=Bind(P)
    F:=K(0)
    G:=K(1)
    H:=K(2)
    A:=BindRoot(P)
    Print("{F(9)} {G().Length} {H()} {A(10)}")
