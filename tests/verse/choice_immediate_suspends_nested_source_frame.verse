pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
Run(P:pair(a,b),Q:pair(c,d),X:a where a:type,b:type,c:type,d:type)<suspends>:a =
    var Value:a=X
    var Total:int=0
    branch:
        Sleep(0.1)
        set Total+=100
        Print("observer {Total}")
    Sleep(0.01)
    if(D:=dup[P]):
        for(V:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            set Value=D.B
            set Total+=V
            Print("body {V} {Total}")
    Sleep(0.2)
    Print("done {Total}")
    Value
Main()<suspends>:void =
    Print("result {Run(dup(int){A:=1,B:=2},dup(string){A:="a",B:="b"},9)}")
    Print("result {Run(dup(string){A:="a",B:="b"},dup(int){A:=1,B:=2},"z")}")
