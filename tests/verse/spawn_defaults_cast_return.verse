pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) {}
base(t:type) := class:
    Go(X:t,?N:int=0)<suspends><transacts>:int=N
ib := class(base(int)):
    var Calls:int=0
    Go<override>(X:int,?N:int=block{set Calls+=1;Print("default {Calls}");X})<suspends><transacts>:int=
        Sleep(0.01)
        N
Start(P:pair(a,b),Q:base(c),X:c where a:type,b:type,c:type)<transacts>:task(int)=
    defer:Print("source cleanup")
    if(D:=dup[P]):
        for(A:=0|1):
            return spawn{Q.Go(X)}
    spawn{Q.Go(X,?N:=0)}
StartWaiting(P:pair(a,b),Q:base(c),X:c where a:type,b:type,c:type)<suspends><transacts>:task(int)=
    defer:Print("waiting cleanup")
    if(D:=dup[P]):
        Sleep(0.01)
        return spawn{Q.Go(X)}
    spawn{Q.Go(X,?N:=0)}
Main()<suspends><transacts>:void=
    C:=ib{}
    A:=Start(dup(int){A:=1,B:=2},C,7)
    Print("created {C.Calls}")
    Print("result {A.Await()}")
    B:=StartWaiting(dup(int){A:=1,B:=2},C,9)
    Print("created {C.Calls}")
    Print("result {B.Await()}")
