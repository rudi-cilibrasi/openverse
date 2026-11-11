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
    defer:Print("source")
    R:=for(if(true?)then return 7 else 0,A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    -1

Test0()<suspends>:void =
    H:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use1(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    Empty:[]int=array{}
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,if(A=4)then return Total else 0,X:Empty,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    -1

Test1()<suspends>:void =
    H:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")

Use2(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    Empty:[]int=array{}
    R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,set Total+=A,X:Empty,if(A=4)then return Total else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad")
    Print("rows {R.Length}")
    99

Test2()<suspends>:void =
    H:=cell{}
    Print("result {Use2(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
Main()<suspends>:void =
    Test0()
    Test1()
    Test2()
