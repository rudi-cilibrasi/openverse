keyed(a:type):=interface:
    Same(X:a):a=X
reordered(u:type,v:type):=class(keyed(tuple(v,u))):
    Left:u
    Right:v
Bind(P:keyed(a) where a:type):type{_(:a):a}=P.Same
Main():void=
    F:=Bind(reordered(int,string){Left:=7,Right:="s"})
    R:=F(("value",9))
    Print("{R(0)} {R(1)}")
