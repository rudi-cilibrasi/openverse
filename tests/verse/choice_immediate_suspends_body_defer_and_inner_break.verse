pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    for(A:=if(D:=dup[P]) then(D.C|D.C+1) else 0,B:=if(E:=dup[Q]) then(E.C|E.C+1) else 0):
        defer:
            set Total+=1
            Print("defer {Total}")
        loop:
            set Total+=A+B
            break
        Print("body {Total}")
    Print("source {Total}")
    Sleep(0.0)
Main()<suspends>:void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
