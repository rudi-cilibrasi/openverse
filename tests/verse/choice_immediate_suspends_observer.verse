pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
Run(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    branch:
        Sleep(0.1)
        set Total+=100
        Print("observer {Total}")
    Sleep(0.0)
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=V,
        W:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        set Total+=W
        Print("body {V} {W} {Total}")
    Sleep(0.2)
    Print("done {Total}")
Main()<suspends>:void =
    Run(dup(int){A:=1,B:=2},dup(string){A:="a",B:="b"})
    Run(pair(int,string){A:=1,B:="s"},dup(int){A:=1,B:=2})
