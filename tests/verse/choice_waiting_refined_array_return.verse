pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
cell := class { var N:int=0 }
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Wait(N:int)<suspends>:int =
    Sleep(0.0)
    N
Use(P:pair(a,b),Q:pair(c,d),First:b where a:type,b:type,c:type,d:type)<suspends>:[]b =
    defer:Print("array source")
    for(A:b=if(D:=dup[P])then(D.A|D.B)else P.B,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        defer:Print("array body")
        Sleep(0.0)
        return array{A}
    array{}
Main()<suspends>:void =
    R:=Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},1)
    for(V:R):Print("array {V}")
    S:=Use(pair(int,string){A:=1,B:="x"},dup(int){A:=1,B:=2},"x")
    for(V:S):Print("array {V}")
