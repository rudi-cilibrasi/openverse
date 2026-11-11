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
        loop:
            defer:Print("local defer {Total}")
            for(A:=(Two(4)|Two(6)),set Total+=A,if(A=4)then break else 0,B:=(Two(4)|Two(6))):Print("bad")
            Print("bad suffix")
        Print("source {Total}")
    99

Test0()<suspends>:void =
    H:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts>:int =
    var Total:int=0
    defer:
        loop:
            defer:Print("local defer {Total}")
            for(A:=(Two(4)|Two(6)),set Total+=A,if(A=4)then break else 0,B:=(Two(4)|Two(6))):Print("bad")
            Print("bad suffix")
        Print("source {Total}")
    99

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use2():void =
    defer:
        loop:
            for(A:array{1,2},if(A=1)then break else 0):Print("bad body")
            Print("bad loop")
        Print("defer done")
    Print("body")

Test2():void=Use2()

Use3(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    var Total:int=0
    branch:
        loop:
            for(A:=(Two(4)|Two(6)),set Total+=A,if(A=4)then break else 0,B:=(Two(4)|Two(6))):Print("bad body")
            Print("bad loop")
        Print("branch {Total}")
    Sleep(0.1)
    Print("done {Total}")

Test3()<suspends>:void=Use3(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
    Test3()
