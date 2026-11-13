pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

maker := class:
    Base:int=2
    Count(?N:int=Base)<transacts>:int = N|N+1
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[(N-1)]
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    R:=for(A:=if(D:=dup[P]) then(D.C|D.C+1) else 0,B:=if(E:=dup[Q]) then(E.C|E.C+1) else 0,L:=Lazy[1],V:=maker{}.Count(),L=0,V=3):
        set Total+=A+B
        Print("body {A} {B} {L} {V} {Total}")
        Total
    Print("source {Total} {R.Length}")
    Sleep(0.01)
Main()<suspends>:void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
