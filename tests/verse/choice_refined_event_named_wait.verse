pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
waiter := class:
    Signal(N:int)<suspends>:void=
        Print("before {N}")
        Sleep(0.1)
        Print("after {N}")
Use(P:pair(a,b),W:waiter where a:type,b:type)<suspends>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        W.Signal(V)
Main()<suspends>:void=Use(dup(int){A:=1,B:=2},waiter{})
