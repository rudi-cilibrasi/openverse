pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
cell := class { var N:int=0 }
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Wait(N:int)<suspends>:int =
    Sleep(0.01)
    N
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    for(A:=if(D:=dup[P])then Lazy[D.C-2]else 0,(set Total+=A; true?),
        B:=if(E:=dup[Q])then Lazy[E.C-2]else 0):
        defer:
            set Total+=10
            Print("cleanup {Total}")
        Sleep(0.01)
        set Total+=B
        Print("lazy body {A} {B} {Total}")
        if(A=1,B=1)then return Total else A+B
    -1
Main()<suspends>:void =
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
