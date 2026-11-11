# expect: first clause of an if's condition
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
ActWait(N:int)<suspends>:void =
    Sleep(0.1)
    Print("body {N}")
waiter := class:
    Act(N:int)<suspends>:void=ActWait(N)
Use(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    Worker:=waiter{}
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,set Total+=B,if(B=5)then break else 0):
            Worker.Act(Total)
        Print("bad suffix")
    99
Main()<suspends>:void =
    H:=cell{}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
