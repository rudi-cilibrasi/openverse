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
Use0(P:pair(a,b),Q:pair(c,d),X:t,Y:t where a:type,b:type,c:type,d:type,t:type)<suspends>:t =
    Sleep(0.0)
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then return X else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    Y

Test0()<suspends>:void =
    P:=dup(int){A:=1,B:=2}
    Q:=dup(string){A:="s",B:="t"}
    Print("int {Use0(P,Q,7,9)}")
    Print("string {Use0(P,Q,"s","t")}")

Use1(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:b =
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then return P.B else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    P.B

Test1()<suspends>:void =
    Q:=dup(string){A:="s",B:="t"}
    Print("int {Use1(dup(int){A:=1,B:=2},Q)}")
    Print("string {Use1(dup(string){A:="s",B:="t"},Q)}")

Use2(P:pair(a,b),Q:pair(c,d),X:t,Y:t where a:type,b:type,c:type,d:type,t:type)<suspends>:[]t =
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then return array{X,Y}else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    array{}

Test2()<suspends>:void =
    P:=dup(int){A:=1,B:=2}
    Q:=dup(string){A:="s",B:="t"}
    I:=Use2(P,Q,7,9)
    S:=Use2(P,Q,"s","t")
    if(A:=I[0],B:=I[1]):Print("int {I.Length} {A} {B}")
    if(A:=S[0],B:=S[1]):Print("string {S.Length} {A} {B}")

Use3(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    defer:Print("source")
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,Print("clause {A}"),if(A=4)then return else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")

Test3()<suspends>:void =
    Use3(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
    Print("done")
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
    Test3()
