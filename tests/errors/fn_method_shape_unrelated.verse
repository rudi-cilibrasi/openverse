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
Bind(B:box(t,u) where t:type,u:type):type{_(:u):t}=B.Same
Main():void=Print("bad")
