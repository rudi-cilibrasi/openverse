box(t:type,h:type):=class:
    Extra:h
    Echo(X:t):t=X
Bind(B:box(tuple(),u) where u:type):type{_():tuple()}=B.Echo
Main():void=
    F:=Bind(box(tuple(),string){Extra:="hidden"})
    R:=F()
    Print("ok")
