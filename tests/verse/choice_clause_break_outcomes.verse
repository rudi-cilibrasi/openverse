pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Use0(P:pair(a,b),Q:pair(c,d),H:cell,Returning:logic where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then block{if(Returning?)then return Total else break}else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("bad suffix")
    99

Test0()<suspends>:void =
    H:=cell{}
    Print("return {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H,true)} {H.N}")
    Print("break {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H,false)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    var Iteration:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        set Iteration+=1
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(Iteration=1)then A>99 else 0,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("again {Iteration}")
    99

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
