pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
cell := class { var N:int=0 }
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Wait(N:int)<suspends>:int =
    Sleep(0.0)
    N
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    Event:=event(int){}
    branch:
        V:=Event.Await()
        set Total+=100
        Print("signal observed {V} {Total}")
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        set Total+=A+B
        Event.Signal(Total)
        Sleep(-1.0)
        Print("signal body {A} {B} {Total}")
    Print("signal done {Total}")
    Sleep(0.2)
    Print("signal final {Total}")
Main()<suspends>:void=Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
