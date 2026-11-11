# expect: the arguments of a spawned call cannot suspend
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Wait(N:int)<suspends>:int=block{Sleep(0.0);N}
Child(N:int)<suspends>:void=Sleep(0.0)
Use(P:pair(a,b) where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        T:=spawn{Child(Wait(V))}
Main():void=Use(dup(int){A:=1,B:=2})
