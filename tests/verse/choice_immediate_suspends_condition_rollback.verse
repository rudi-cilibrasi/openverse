pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=1
    branch:
        Sleep(0.25)
        Print("observe {Total}")
    R:=for(A:=if(D:=dup[P]) then(D.C|D.C+1) else 0,B:=if(E:=dup[Q]) then(E.C|E.C+1) else 0,set Total+=A,B=5):
        Print("body {A} {B} {Total}")
        Total
    Print("source {Total} {R.Length}")
    Sleep(0.5)
Main()<suspends>:void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
