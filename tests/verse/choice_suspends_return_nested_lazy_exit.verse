pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    defer:Print("source")
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        for(L:=Lazy[2],L=1):
            Print("return {A} {B} {L}")
            return A*100+B*10+L
    -1
Main()<suspends>:void = Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
