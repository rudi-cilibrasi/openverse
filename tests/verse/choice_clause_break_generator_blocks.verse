pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Two(N:int)<computes>:int=N|N+1
Use0(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[Q])then(D.C|D.C+1)else 0,set Total+=A,X:=block{if(A=4)then break;Y:=Two(3);Y},B:=if(E:=dup[P])then(E.C|E.C+1)else 0):Print("bad body")
        Print("bad suffix")
        break
    99

Test0()<suspends>:void=Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")

Use1(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        if(F:=dup[P]):
            for(A:=if(D:=dup[Q])then(D.C|D.C+1)else 0,set Total+=A,X:=block{if(A=4)then break;Y:=Two(3);Y},B:=if(E:=dup[P])then(E.C|E.C+1)else 0):Print("bad body")
            Print("bad suffix")
            break
        break
    99

Test1()<suspends>:void=Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
Main()<suspends>:void =
    Test0()
    Test1()
