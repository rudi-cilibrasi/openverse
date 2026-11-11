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
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,X:=block{R:=for(B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,if(B=4)then break else 0,C:=Two(8)):Print("bad inner");R.Length},Y:=Two(8)):
            Print("bad outer")
        Print("bad suffix")
    99

Test0()<suspends>:void =
    H:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("outer {Total}")
        loop:
            defer:Print("inner {Total}")
            for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
            Print("bad inner suffix")
        Print("after inner {Total}")
        break
    99

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use2(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        if(F:=dup[P]):
            Sleep(0.0)
            for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("bad suffix")
    99

Test2()<suspends>:void =
    H:=cell{}
    Print("result {Use2(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use3(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    if(F:=dup[P]):
        Sleep(0.0)
        loop:
            defer:Print("loop {Total}")
            for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
            Print("bad suffix")
    99

Test3()<suspends>:void =
    H:=cell{}
    Print("result {Use3(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use4(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("outer {Total}")
        if(F:=dup[P]):
            Sleep(0.0)
            loop:
                defer:Print("inner {Total}")
                for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
                Print("bad inner suffix")
            Print("after inner {Total}")
            set Total+=100
            break
        Print("bad outer suffix")
    99

Test4()<suspends>:void =
    H:=cell{}
    Print("result {Use4(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use5(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(F:=dup[Q])then block{set Total+=F.C;break}else 0,B:=Two(4)):Print("bad")
        Print("bad suffix")
    99

Test5()<suspends>:void =
    H:=cell{}
    Print("result {Use5(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
    Test3()
    Test4()
    Test5()
