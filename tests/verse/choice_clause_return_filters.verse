pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Operand(H:cell,N:int)<transacts>:int =
    set H.N+=1
    Print("operand {N} {H.N}")
    N
Wait(N:int)<suspends>:int =
    Sleep(0.1)
    N
Use0(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,A>4,if(A=5)then return Total else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    -1

Test0()<suspends>:void =
    H:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,Print("filter {A}"),if(A=4)then return array{7}[9]else return Total,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    -1

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use2(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    defer:Print("source {H.N}")
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set H.N+=A,Print("filter {A}"),if(A=4)then return array{7}[9]else return H.N,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    -1

Test2()<suspends>:void =
    H:=cell{}
    Print("result {Use2(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use3(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,set Total+=B,B>4,if(B=5)then return Total else 0,C:=Two(8)):Print("bad")
    -1

Test3()<suspends>:void =
    H:=cell{}
    Print("result {Use3(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
    Test3()
