# expect: must be comparable
box(t:type,u:type):=class:
    V:t
    Extra:u
    Same(X:t):t=X
    Nested(X:[]t):[]t=X
    Failable(X:t)<decides>:t=block{false?;X}
    Wait(X:[]t)<suspends>:[]t=block{Sleep(0.0);X}
    Generic(X:v where v:type):v=X
    Named(?X:t=V):t=X
Use(F:type{_(:a):a},X:a where a:type):logic=logic{F(X)=X}
Main():void=
    B:=box(int,string){V:=1,Extra:="s"}
    Use(B.Same,1)
