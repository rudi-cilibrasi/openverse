# expect: expected type
box(t:type,u:type):=class:
    V:t
    Extra:u
    Same(X:t):t=X
    Nested(X:[]t):[]t=X
    Failable(X:t)<decides>:t=block{false?;X}
    Wait(X:[]t)<suspends>:[]t=block{Sleep(0.0);X}
    Generic(X:v where v:type):v=X
    Named(?X:t=V):t=X
Main():void=
    B:=box(int,string){V:=1,Extra:="s"}
    F:type{_(:int)<computes>:int}=B.Same
    Print("bad")
