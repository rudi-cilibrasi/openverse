pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
Use(P:pair(a,b),Start:b where a:type,b:type)<suspends>:b =
    var Value:b=Start
    var Total:int=0
    defer: Print("source {Total}")
    branch:
        Sleep(0.1)
        set Total+=100
        Print("observer {Total}")
    Sleep(0.2)
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        defer:
            set Value=Start
            set Total+=10
            Print("body cleanup {Total}")
        if(F:=dup[P]):
            set Value=F.A
            set Total+=V
            return Value
    Value
Main()<suspends>:void =
    Print("return {Use(dup(int){A:=1,B:=2},9)}")
    Print("return {Use(dup(string){A:="a",B:="b"},"z")}")
