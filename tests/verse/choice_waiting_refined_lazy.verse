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
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    R:=for(A:=if(D:=dup[P])then Lazy[D.C-2]else 0,set Total+=A,
        B:=if(E:=dup[Q])then Lazy[E.C-2]else 0,B>0):
        Print("start {A} {B} {Total}")
        Sleep(0.01)
        set Total+=B
        Print("body {A} {B} {Total}")
        A+B
    Print("lazy {Total} {R.Length}")
Main()<suspends>:void =
    Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
    Use(pair(int,string){A:=1,B:="s"},dup(int){A:=1,B:=2})
