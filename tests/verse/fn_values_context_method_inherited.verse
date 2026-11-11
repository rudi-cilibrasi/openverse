source(t:type):=interface:
    Get():t
    Pair(X:u where u:type):tuple(t,u)=(Get(),X)
box(t:type):=class(source(t)):
    V:t
    Get<override>():t=V
child(a:type):=class(box(a)):
    Get<override>():a=V
Apply(F:type{_(:a):tuple(b,a)},X:a,Hint:b where a:type,b:type):tuple(b,a)=F(X)
Run(B:source(t),X:u where t:type,u:type):tuple(t,u)=Apply(B.Pair,X,B.Get())
Main():void=
    R:=Run(child(string){V:="tag"},7)
    Print("{R(0)} {R(1)}")
