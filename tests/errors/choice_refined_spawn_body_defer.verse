# expect: spawn in a defer is not supported
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Child(N:int)<suspends>:void=Sleep(0.0)
Use(P:pair(a,b) where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        defer:T:=spawn{Child(V)}
        Print("end")
Main():void=Use(dup(int){A:=1,B:=2})
