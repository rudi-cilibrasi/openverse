pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Two(N:int):int=N|N+1
Log(N:int):void=Print("signal {N}")
Use(P:pair(a,b),E:subscribable_event(int) where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        E.Signal(V)
Main():void=
    E:=subscribable_event(int){}
    C:=E.Subscribe(Log)
    Use(dup(int){A:=1,B:=2},E)
    Use(pair(int,string){A:=1,B:="s"},E)
    C.Cancel()
