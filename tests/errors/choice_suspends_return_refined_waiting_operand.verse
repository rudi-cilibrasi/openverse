# expect: first clause of an if's condition
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Wait(N:int)<suspends>:int =
    Sleep(0.01)
    N
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        return Wait(A+B)
    -1
Main()<suspends>:void = Print("{Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
