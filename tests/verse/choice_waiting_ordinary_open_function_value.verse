Two(N:int):int=N|N+1
Early(N:int):int=
    if(N<0):return N
    N|N+1
Id(X:t where t:type)<computes>:t=X
Wait(X:t where t:type)<suspends>:t=
    Sleep(0.0)
    X
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Use(P:pair(a,b) where a:type,b:type)<suspends>:[]b=
    F:type{_(:b)<suspends>:b}=Wait
    G:type{_(:b)<computes>:b}=Id
    for(A:=(Two(1)|Two(3)),B:=Early(10)):
        F(G(P.B))
Main()<suspends>:void=
    R:=Use(dup(int){A:=1,B:=2})
    Print("int {R.Length} {R[0] or 0}")
    S:=Use(pair(int,string){A:=3,B:="s"})
    Print("string {S.Length} {S[0] or "empty"}")
