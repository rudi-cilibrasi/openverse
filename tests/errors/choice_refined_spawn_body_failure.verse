# expect: spawn cannot be in a failure context
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Child(N:int)<suspends>:void=Sleep(0.0)
Use(P:pair(a,b) where a:type,b:type)<decides>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        T:=spawn{Child(V)}
        V=4
Main()<decides>:void=Use[dup(int){A:=1,B:=2}]
