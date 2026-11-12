# expect: <writes>
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=10 }
token := class<allocates><unique>:
    V:int
    block:Print("alloc {V}")
Two(N:int)<computes>:int=N|N+1
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Read(H:cell,N:int)<reads>:int=H.N+N
Write(H:cell,N:int)<writes>:int =
    set H.N=N
    N
Allocate(H:cell,N:int)<allocates>:int =
    T:=token{V:=N}
    T.V
Waiting(H:cell,N:int)<suspends><writes>:int =
    Sleep(0.1)
    Write(H,N)
waiter := class:
    Value(H:cell,N:int)<suspends><writes>:int =
        Sleep(0.1)
        Write(H,N)
Use(P:pair(a,b),Q:pair(c,d),H:cell,W:waiter where a:type,b:type,c:type,d:type)<suspends><computes>:int =
    if(FR:=dup[P]):
        Sleep(0.0)
        for(A:=(Two(4)|Two(6)),B:=(Two(4)|Two(6))):return W.Value(H,A+B)
    -1
Main()<suspends>:void =
    H:=cell{}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H,waiter{})} {H.N}")
