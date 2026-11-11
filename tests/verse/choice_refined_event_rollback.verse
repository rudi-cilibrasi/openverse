pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
listener := class:
    var Sum:int=0
    Add(N:int):void=
        set Sum+=N
        Print("heard {N} {Sum}")
Use(P:pair(a,b),E:subscribable_event(int),L:listener where a:type,b:type)<decides>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        E.Signal(V)
        C:=E.Subscribe(L.Add)
        V=5
Main():void=
    E:=subscribable_event(int){}
    L:=listener{}
    C:=E.Subscribe(L.Add)
    if(Use[dup(int){A:=1,B:=2},E,L]):Print("unexpected")
    else:Print("failed {L.Sum}")
    E.Signal(1)
    Print("sum {L.Sum}")
