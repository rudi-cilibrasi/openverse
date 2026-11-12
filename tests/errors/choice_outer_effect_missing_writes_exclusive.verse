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
Use(P:pair(a,b),Q:pair(c,d),R:pair(e,f),H:cell where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><computes>:int =
    if(F:=dup[P]):
        Sleep(0.0)
        for(A:=if(true?)then Two(4)else Two(9),B:=if(true?)then Two(4)else Two(9)):return Write(H,A+B)
    -1
Main()<suspends>:void =
    H:=cell{}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},dup(char){A:='a',B:='b'},H)} {H.N}")
