pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Log(N:int):void=Print("signal {N}")
Use(P:pair(a,b),E:subscribable_event(int),C:cancelable where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        E.Signal(V)
        C.Cancel()
Main():void=
    E:=subscribable_event(int){}
    C:=E.Subscribe(Log)
    Use(dup(int){A:=1,B:=2},E,C)
    E.Signal(9)
