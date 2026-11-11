pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Use0(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:int =
    defer:Print("source {H.N}")
    loop:
        defer:Print("loop {H.N}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set H.N+=A,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,if(B=5)then break else 0):
            set H.N+=100
            Print("bad body")
            false?
            A
        Print("bad suffix")
    99

Test0():void =
    H:=cell{}
    if(R:=Use0[dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H])then Print("result {R} {H.N}")else Print("caught {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:int =
    defer:Print("source {H.N}")
    loop:
        defer:Print("loop {H.N}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set H.N+=A,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,if(B=4)then break else 0):
            set H.N+=100
            Print("bad body")
            false?
            A
        Print("bad suffix")
    99

Test1():void =
    H:=cell{}
    if(R:=Use1[dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H])then Print("result {R} {H.N}")else Print("caught {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
