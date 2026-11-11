pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer: Print("source {Total}")
    branch:
        Sleep(0.1)
        set Total+=100
        Print("observer {Total}")
    Sleep(0.2)
    loop:
        defer: Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0):
            defer:
                set Total+=10
                Print("outer {Total}")
            for(B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
                defer:
                    set Total+=20
                    Print("inner {Total}")
                set Total+=A+B
                if(B=5):return Total
        break
    -1
Main()<suspends>:void = Print("return {Use(dup(int){A:=1,B:=2},dup(string){A:="a",B:="b"})}")
