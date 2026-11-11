pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Use0(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:
        set Total+=1000
        Print("source {Total}")
    loop:
        defer:
            set Total+=100
            Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then block{defer{set Total+=10;Print("clause {Total}")};break}else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            defer:Print("bad body cleanup")
            Print("bad")
        Print("bad suffix")
    99

Test0()<suspends>:void =
    H:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,X:=block{loop{set Total+=10;break};0},if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("bad suffix")
    99

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use2(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,X:=block{loop{set Total+=10;break};0},B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            Print("body {A} {B} {Total}")
        Print("rows {R.Length} {Total}")
        break
    99

Test2()<suspends>:void =
    H:=cell{}
    Print("result {Use2(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use3(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=5)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            loop:
                set Total+=10
                break
            Print("body {Total}")
        Print("bad suffix")
    99

Test3()<suspends>:void =
    H:=cell{}
    Print("result {Use3(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use4(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=5)then break else 0,X:=Two(0)):
            loop:
                defer:Print("inner {Total}")
                for(B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,set Total+=B,if(B=4)then break else 0,Y:=Two(8)):Print("bad inner")
                Print("bad inner suffix")
            Print("body {A} {X} {Total}")
        Print("bad suffix")
    99

Test4()<suspends>:void =
    H:=cell{}
    Print("result {Use4(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
    Test3()
    Test4()
