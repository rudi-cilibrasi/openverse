pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Use0(P:pair(a,b),Q:pair(c,d),X:t where a:type,b:type,c:type,d:type,t:type)<suspends>:t =
    loop:
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("bad suffix")
    X

Test0()<suspends>:void =
    P:=dup(int){A:=1,B:=2}
    Q:=dup(string){A:="s",B:="t"}
    Print("int {Use0(P,Q,7)}")
    Print("string {Use0(P,Q,"s")}")

Use1(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    defer:Print("source")
    loop:
        defer:Print("loop")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then break else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
        Print("bad suffix")
    Print("after")

Test1()<suspends>:void =
    Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
    Print("done")
Main()<suspends>:void =
    Test0()
    Test1()
