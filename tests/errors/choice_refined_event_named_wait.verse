# expect: waiter.Signal suspends: it can only be called in a <suspends> function
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
waiter := class:
    Signal(N:int)<suspends>:void=Sleep(0.0)
Use(P:pair(a,b),W:waiter where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        W.Signal(V)
Main():void=Use(dup(int){A:=1,B:=2},waiter{})
