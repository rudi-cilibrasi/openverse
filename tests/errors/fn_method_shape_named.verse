# expect: expected type{_(:int):int}, found type{_(?X:int = …):int}
# (Named takes ?X by name, not a positional argument, #503)
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
    F:type{_(:int):int}=B.Named
    Print("bad")
