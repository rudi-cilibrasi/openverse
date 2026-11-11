pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Child(N:int)<suspends>:void=
    Print("child {N}")
    Sleep(0.5)
    Print("done {N}")
Use(P:pair(a,b) where a:type,b:type)<suspends>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        T:=spawn{Child(V)}
        Sleep(0.1)
    Print("for done")
    Sleep(1.0)
Immediate(P:pair(a,b) where a:type,b:type):void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        T:=spawn{Child(V)}
    Print("immediate done")
Main()<suspends>:void=
    Use(dup(int){A:=1,B:=2})
    Immediate(dup(int){A:=1,B:=2})
    Sleep(1.0)
