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
Operand(H:cell,N:int)<transacts><decides>:int =
    set H.N+=10
    Print("operand {N} {H.N}")
    N>5
    N
Use(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:
        set Total+=100
        set H.N+=100
        Print("source {Total} {H.N}")
    for(A:=if(D:=dup[P])then(D.C|D.C+1|D.C+2)else 0,set Total+=A,set H.N+=A,
        if(A>=5)then return Operand[H,A]else 0,
        B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        Sleep(0.0)
        set Total+=B
        set H.N+=B
        Print("body {A} {B} {Total} {H.N}")
    -1
Main()<suspends>:void =
    H:=cell{}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
